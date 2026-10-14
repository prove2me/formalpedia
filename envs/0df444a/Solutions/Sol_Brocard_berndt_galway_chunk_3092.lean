-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_3092
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T08:38:27.475979+00:00
-- url     : https://prove2.me/submissions/07be9e1c-09b2-4836-9365-ef0dd67641e6

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 555935251 ≤ n < 556115107 has `n! + 1` a square.
For every such `n` a prime `p > n + 1` (from a per-sub-range list, each prime certified by a
gcd against a product of all primes below its square root) with `j = p - 1 - n`,
`Q = (-1)^j j! mod p` and `N = Q (Q - 1) mod p` has `N ^ ((p - 1) / 2) ≡ -1 (mod p)`; by Wilson
`Q^2 (n! + 1) ≡ N`, so `n! + 1` is not a square mod `p`. Checked by the kernel
(`decide +kernel`) through the frame `BRFrame`. -/

set_option autoImplicit false
set_option linter.all false
set_option Elab.async false

namespace BRFrame

/-! ## 1. The criterion (Wilson + Euler)

For a prime `p = n + j + 1`, Wilson's theorem gives `n! * Q = -1` in `ZMod p` with
`Q = (-1) ^ j * j!`. If `n! + 1 = m ^ 2` then `Q * (Q - 1) = (Q * m) ^ 2` is a square, so its
`(p - 1) / 2`-th power is `0` or `1`, never `-1`. -/

theorem fact_split (p : ℕ) : ∀ j n : ℕ, n + j + 1 = p →
    (((p - 1).factorial : ℕ) : ZMod p) =
      ((n.factorial : ℕ) : ZMod p) * ((-1) ^ j * ((j.factorial : ℕ) : ZMod p)) := by
  intro j
  induction j with
  | zero =>
    intro n h
    have e : p - 1 = n := by omega
    rw [e]
    simp
  | succ j ih =>
    intro n h
    rw [ih (n + 1) (by omega), Nat.factorial_succ n, Nat.factorial_succ j]
    have h0 : ((n + 1 + (j + 1) : ℕ) : ZMod p) = 0 := by
      rw [show n + 1 + (j + 1) = p by omega]
      exact ZMod.natCast_self p
    push_cast at h0 ⊢
    linear_combination ((-1) ^ j * ((j.factorial : ℕ) : ZMod p) * ((n.factorial : ℕ) : ZMod p)) * h0

theorem crit (p n j m : ℕ) (hp : p.Prime) (hp3 : 3 ≤ p) (hj : n + j + 1 = p) (Q N : ℕ)
    (hQ : (Q : ZMod p) = (-1) ^ j * ((j.factorial : ℕ) : ZMod p))
    (hN : (N : ZMod p) = (Q : ZMod p) * ((Q : ZMod p) - 1))
    (he : (N : ZMod p) ^ ((p - 1) / 2) = -1) : Nat.factorial n + 1 ≠ m ^ 2 := by
  intro hm
  haveI := Fact.mk hp
  have hw : ((n.factorial : ℕ) : ZMod p) * (Q : ZMod p) = -1 := by
    rw [hQ, ← fact_split p j n hj]
    exact @ZMod.wilsons_lemma p _
  have hm' : ((n.factorial : ℕ) : ZMod p) + 1 = (m : ZMod p) ^ 2 := by
    have := congrArg (fun x : ℕ => (x : ZMod p)) hm
    push_cast at this
    exact this
  have hsq : (N : ZMod p) = ((Q : ZMod p) * (m : ZMod p)) ^ 2 := by
    rw [hN, mul_pow, ← hm']
    linear_combination (-(Q : ZMod p)) * hw
  have hodd : p % 2 = 1 := by
    rcases hp.eq_two_or_odd with h | h
    · omega
    · exact h
  have h2e : 2 * ((p - 1) / 2) = p - 1 := by omega
  rw [hsq, ← pow_mul, h2e] at he
  by_cases hx : (Q : ZMod p) * (m : ZMod p) = 0
  · rw [hx, zero_pow (by omega)] at he
    have h1 : (1 : ZMod p) = 0 := by linear_combination he
    exact one_ne_zero h1
  · rw [ZMod.pow_card_sub_one_eq_one hx] at he
    have h2 : ((2 : ℕ) : ZMod p) = 0 := by
      push_cast
      linear_combination he
    have hd : p ∣ 2 := (ZMod.natCast_eq_zero_iff _ _).1 h2
    have := Nat.le_of_dvd (by norm_num) hd
    omega

/-! ## 2. Modular powering: four windows (8, 7, 7, 7 bits; fast for `e < 2 ^ 29`; exact for all `e`) -/

def w7 (p a e : ℕ) : ℕ :=
  Nat.mod (Nat.mul (Nat.pow (Nat.mod (Nat.mul (Nat.pow (Nat.mod (Nat.mul (Nat.pow
    (Nat.mod (Nat.pow a (Nat.shiftRight e 21)) p) 128)
    (Nat.pow a (Nat.land (Nat.shiftRight e 14) 127))) p) 128)
    (Nat.pow a (Nat.land (Nat.shiftRight e 7) 127))) p) 128)
    (Nat.pow a (Nat.land e 127))) p

theorem win (p a x u d : ℕ) (hx : x ≡ a ^ u [MOD p]) :
    Nat.mod (Nat.mul (Nat.pow x 128) (Nat.pow a d)) p ≡ a ^ (u * 128 + d) [MOD p] := by
  refine (Nat.mod_modEq (x ^ 128 * a ^ d) p).trans ?_
  rw [pow_add, pow_mul]
  exact (hx.pow 128).mul_right _

theorem sh_div (e k : ℕ) : Nat.shiftRight e k = e / 2 ^ k := by
  show e >>> k = e / 2 ^ k
  rw [Nat.shiftRight_eq_div_pow]

theorem w7_spec (p a e : ℕ) : w7 p a e ≡ a ^ e [MOD p] := by
  have d14 : Nat.land (Nat.shiftRight e 14) 127 = e / 2 ^ 14 % 2 ^ 7 := by
    rw [sh_div]; exact Nat.and_two_pow_sub_one_eq_mod _ 7
  have d7 : Nat.land (Nat.shiftRight e 7) 127 = e / 2 ^ 7 % 2 ^ 7 := by
    rw [sh_div]; exact Nat.and_two_pow_sub_one_eq_mod _ 7
  have d0 : Nat.land e 127 = e % 2 ^ 7 := Nat.and_two_pow_sub_one_eq_mod _ 7
  unfold w7
  rw [d14, d7, d0, sh_div e 21]
  have h0 : Nat.mod (Nat.pow a (e / 2 ^ 21)) p ≡ a ^ (e / 2 ^ 21) [MOD p] := Nat.mod_modEq _ _
  have h1 := win p a _ _ (e / 2 ^ 14 % 2 ^ 7) h0
  have h2 := win p a _ _ (e / 2 ^ 7 % 2 ^ 7) h1
  have h3 := win p a _ _ (e % 2 ^ 7) h2
  refine h3.trans ?_
  have ee : ((e / 2 ^ 21 * 128 + e / 2 ^ 14 % 2 ^ 7) * 128 + e / 2 ^ 7 % 2 ^ 7) * 128 + e % 2 ^ 7 = e := by
    norm_num
    omega
  rw [ee]

/-! ## 3. The factorial table

`mkT W k j f acc` appends `f = j!`, `(j+1)!`, ... (`k` entries, `W` bits each) below `acc`, so in
`TB W J = mkT W (J + 1) 0 1 0` the entry `j` sits at bit `W * (J - j)`. Nothing is assumed about it:
`tabOK` checks every entry against a running factorial in the kernel. -/

def mkT (W : ℕ) (k : ℕ) : ℕ → ℕ → ℕ → ℕ :=
  Nat.rec (motive := fun _ => ℕ → ℕ → ℕ → ℕ) (fun _ _ acc => acc)
    (fun _ ih j f acc => ih (Nat.add j 1) (Nat.mul f (Nat.add j 1)) (Nat.lor (Nat.shiftLeft acc W) f)) k

def ext (T W M J j : ℕ) : ℕ := Nat.land (Nat.shiftRight T (Nat.mul W (Nat.sub J j))) M

/-- `tabOK T W M J k j f`: entries `j, j+1, ..., j+k-1` equal `f, f*(j+1), ...` -/
def tabOK (T W M J : ℕ) (k : ℕ) : ℕ → ℕ → Bool :=
  Nat.rec (motive := fun _ => ℕ → ℕ → Bool) (fun _ _ => true)
    (fun _ ih j f => Nat.beq (ext T W M J j) f && ih (Nat.add j 1) (Nat.mul f (Nat.add j 1))) k

theorem tabOK_sound (T W M J : ℕ) : ∀ k j, tabOK T W M J k j (Nat.factorial j) = true →
    ∀ i, j ≤ i → i < j + k → ext T W M J i = Nat.factorial i := by
  intro k
  induction k with
  | zero => intro j _ i h1 h2; omega
  | succ k ih =>
    intro j h i h1 h2
    have h' : (Nat.beq (ext T W M J j) (Nat.factorial j) &&
        tabOK T W M J k (Nat.add j 1) (Nat.mul (Nat.factorial j) (Nat.add j 1))) = true := h
    rw [Bool.and_eq_true] at h'
    by_cases hij : i = j
    · subst hij
      exact Nat.eq_of_beq_eq_true h'.1
    · have hf : Nat.mul (Nat.factorial j) (Nat.add j 1) = Nat.factorial (j + 1) := by
        show Nat.factorial j * (j + 1) = Nat.factorial (j + 1)
        rw [Nat.factorial_succ, Nat.mul_comm]
      have h2' := h'.2
      rw [hf] at h2'
      exact ih (j + 1) h2' i (by omega) (by omega)

/-! ## 4. Prime pools

`chk6 P T`: `6 ∣ P` and `6t+5`, `6t+7` share a factor with `P` for every `t < T`; then every prime
`q ≤ 6T+1` divides `P`. A number `q < Bd` with `gcd q P = 1` and every prime `r` with `r * r < Bd`
dividing `P` is prime. -/

def chk6 (P : ℕ) (T : ℕ) : Bool :=
  Nat.beq (Nat.mod P 6) 0 &&
  Nat.rec (motive := fun _ => Bool) true
    (fun t ih => !(Nat.beq (Nat.gcd (Nat.add (Nat.mul 6 t) 5) P) 1) &&
      !(Nat.beq (Nat.gcd (Nat.add (Nat.mul 6 t) 7) P) 1) && ih) T

theorem chk6_rec (P : ℕ) : ∀ T, Nat.rec (motive := fun _ => Bool) true
    (fun t ih => !(Nat.beq (Nat.gcd (Nat.add (Nat.mul 6 t) 5) P) 1) &&
      !(Nat.beq (Nat.gcd (Nat.add (Nat.mul 6 t) 7) P) 1) && ih) T = true →
    ∀ t, t < T → Nat.gcd (6 * t + 5) P ≠ 1 ∧ Nat.gcd (6 * t + 7) P ≠ 1 := by
  intro T
  induction T with
  | zero => intro _ t ht; omega
  | succ T ih =>
    intro h t ht
    simp only [Bool.and_eq_true, Bool.not_eq_true'] at h
    obtain ⟨⟨h5, h7⟩, hr⟩ := h
    by_cases htT : t = T
    · subst htT
      constructor
      · intro hc
        have : Nat.beq (Nat.gcd (Nat.add (Nat.mul 6 t) 5) P) 1 = true := by
          show Nat.beq (Nat.gcd (6 * t + 5) P) 1 = true
          rw [hc]; rfl
        rw [this] at h5; exact absurd h5 (by decide)
      · intro hc
        have : Nat.beq (Nat.gcd (Nat.add (Nat.mul 6 t) 7) P) 1 = true := by
          show Nat.beq (Nat.gcd (6 * t + 7) P) 1 = true
          rw [hc]; rfl
        rw [this] at h7; exact absurd h7 (by decide)
    · exact ih hr t (by omega)

theorem chk6_sound (P T : ℕ) (h : chk6 P T = true) :
    ∀ q : ℕ, q.Prime → (q ≤ 3 ∨ q ≤ 6 * T + 1) → q ∣ P := by
  unfold chk6 at h
  rw [Bool.and_eq_true] at h
  obtain ⟨h6, hr⟩ := h
  have h6' : P % 6 = 0 := Nat.eq_of_beq_eq_true h6
  have hall := chk6_rec P T hr
  intro q hq hb
  have hq2 := hq.two_le
  have hdvd : ∀ t, (q = 6 * t + 5 ∨ q = 6 * t + 7) → t < T → q ∣ P := by
    intro t ht htT
    rcases Nat.coprime_or_dvd_of_prime hq P with hc | hc
    · rcases ht with ht | ht
      · rw [ht] at hc; exact absurd hc (hall t htT).1
      · rw [ht] at hc; exact absurd hc (hall t htT).2
    · exact hc
  by_cases h23 : q ≤ 3
  · have : q = 2 ∨ q = 3 := by omega
    rcases this with e | e
    · subst e; omega
    · subst e; omega
  · have hb' : q ≤ 6 * T + 1 := by omega
    have hm : q % 6 = 1 ∨ q % 6 = 5 := by
      have h2 : ¬ 2 ∣ q := by
        intro hd
        have := (Nat.prime_dvd_prime_iff_eq Nat.prime_two hq).1 hd
        omega
      have h3 : ¬ 3 ∣ q := by
        intro hd
        have := (Nat.prime_dvd_prime_iff_eq Nat.prime_three hq).1 hd
        omega
      omega
    rcases hm with hm | hm
    · exact hdvd (q / 6 - 1) (Or.inr (by omega)) (by omega)
    · exact hdvd (q / 6) (Or.inl (by omega)) (by omega)

theorem prime_of_pool (P Bd q : ℕ) (hP : ∀ r : ℕ, r.Prime → r * r < Bd → r ∣ P) (h2 : 2 ≤ q)
    (hq : q < Bd) (hc : Nat.gcd q P = 1) : q.Prime := by
  by_contra hnp
  have hq1 : q ≠ 1 := by omega
  have hmp := Nat.minFac_prime hq1
  have hsq := Nat.minFac_sq_le_self (by omega) hnp
  have hsq' : q.minFac * q.minFac ≤ q := by rw [← pow_two]; exact hsq
  have hdP := hP q.minFac hmp (by omega)
  have hd : q.minFac ∣ Nat.gcd q P := Nat.dvd_gcd (Nat.minFac_dvd q) hdP
  rw [hc] at hd
  have := Nat.le_of_dvd one_pos hd
  have := hmp.two_le
  omega

/-- pools: `6` below `16`, `30030` below `196`, `P3` below `32761`, `P4` below `1024000000` -/
def pOK (P3 P4 p : ℕ) : Bool :=
  Nat.ble 5 p && cond (Nat.blt p 16) (Nat.beq (Nat.gcd p 6) 1)
    (cond (Nat.blt p 196) (Nat.beq (Nat.gcd p 30030) 1)
      (cond (Nat.blt p 32761) (Nat.beq (Nat.gcd p P3) 1)
        (Nat.blt p 1024000000 && Nat.beq (Nat.gcd p P4) 1)))

theorem blt_t {a b : ℕ} (h : a < b) : Nat.blt a b = true := by simpa using h

theorem blt_f {a b : ℕ} (h : ¬ a < b) : Nat.blt a b = false := by
  cases hb : Nat.blt a b
  · rfl
  · exact absurd (by simpa using hb) h

theorem P6_ok : chk6 6 0 = true := by decide +kernel
theorem P30030_ok : chk6 30030 2 = true := by decide +kernel

theorem pOK_sound (P3 P4 : ℕ) (h3 : chk6 P3 30 = true) (h4 : chk6 P4 5333 = true) (p : ℕ)
    (h : pOK P3 P4 p = true) : p.Prime ∧ 5 ≤ p := by
  unfold pOK at h
  rw [Bool.and_eq_true] at h
  obtain ⟨h5, h⟩ := h
  have h5' := Nat.le_of_ble_eq_true h5
  refine ⟨?_, h5'⟩
  by_cases c1 : p < 16
  · rw [blt_t c1, cond_true] at h
    exact prime_of_pool 6 16 p (fun r hr hrr => chk6_sound 6 0 P6_ok r hr (by
      left; by_contra hc; have : 4 * 4 ≤ r * r := Nat.mul_le_mul (by omega) (by omega); omega))
      (by omega) c1 (Nat.eq_of_beq_eq_true h)
  rw [blt_f c1, cond_false] at h
  by_cases c2 : p < 196
  · rw [blt_t c2, cond_true] at h
    exact prime_of_pool 30030 196 p (fun r hr hrr => chk6_sound 30030 2 P30030_ok r hr (by
      right; by_contra hc; have : 14 * 14 ≤ r * r := Nat.mul_le_mul (by omega) (by omega); omega))
      (by omega) c2 (Nat.eq_of_beq_eq_true h)
  rw [blt_f c2, cond_false] at h
  by_cases c3 : p < 32761
  · rw [blt_t c3, cond_true] at h
    exact prime_of_pool P3 32761 p (fun r hr hrr => chk6_sound P3 30 h3 r hr (by
      right; by_contra hc; have : 182 * 182 ≤ r * r := Nat.mul_le_mul (by omega) (by omega); omega))
      (by omega) c3 (Nat.eq_of_beq_eq_true h)
  rw [blt_f c3, cond_false, Bool.and_eq_true] at h
  have c4 := Nat.le_of_ble_eq_true h.1
  exact prime_of_pool P4 1024000000 p (fun r hr hrr => chk6_sound P4 5333 h4 r hr (by
      right; by_contra hc; have : 32000 * 32000 ≤ r * r := Nat.mul_le_mul (by omega) (by omega); omega))
      (by omega) c4 (Nat.eq_of_beq_eq_true h.2)

/-! ## 5. One `n`: the test

`fm`: `j!` from the table for `j ≤ J`, else from entry `J` by the loop `lp` (rare).
`nN = f * (f + s) mod p` with `f ≡ j! (mod p)`, `s = p - 1` (`j` even) or `1` (`j` odd); this is
`Q * (Q - 1)` for `Q = (-1)^j j!`. -/

def lp (p : ℕ) (k : ℕ) : ℕ → ℕ → ℕ :=
  Nat.rec (motive := fun _ => ℕ → ℕ → ℕ) (fun _ acc => acc)
    (fun _ ih i acc => ih (Nat.add i 1) (Nat.mod (Nat.mul acc (Nat.add i 1)) p)) k

theorem lp_spec (p : ℕ) : ∀ k i acc, acc ≡ Nat.factorial i [MOD p] →
    lp p k i acc ≡ Nat.factorial (i + k) [MOD p] := by
  intro k
  induction k with
  | zero => intro i acc h; exact h
  | succ k ih =>
    intro i acc h
    have e : lp p (k + 1) i acc = lp p k (Nat.add i 1) (Nat.mod (Nat.mul acc (Nat.add i 1)) p) := rfl
    rw [e]
    have h2 : Nat.mod (Nat.mul acc (Nat.add i 1)) p ≡ Nat.factorial (i + 1) [MOD p] := by
      refine (Nat.mod_modEq (acc * (i + 1)) p).trans ?_
      rw [Nat.factorial_succ, Nat.mul_comm (i + 1)]
      exact h.mul_right _
    have := ih (i + 1) _ h2
    rw [show i + 1 + k = i + (k + 1) by omega] at this
    exact this

def fm (T W M J p j : ℕ) : ℕ :=
  Bool.rec (motive := fun _ => ℕ) (lp p (Nat.sub j J) J (Nat.mod (ext T W M J J) p))
    (ext T W M J j) (Nat.ble j J)

theorem fm_spec (T W M J p j : ℕ) (hT : ∀ i, i ≤ J → ext T W M J i = Nat.factorial i) :
    fm T W M J p j ≡ Nat.factorial j [MOD p] := by
  unfold fm
  by_cases hj : j ≤ J
  · have hb : Nat.ble j J = true := by rw [Nat.ble_eq]; exact hj
    rw [hb]; dsimp only; rw [hT j hj]
  · have hb : Nat.ble j J = false := by
      cases h : Nat.ble j J
      · rfl
      · exact absurd (Nat.le_of_ble_eq_true h) hj
    rw [hb]; dsimp only
    have h0 : Nat.mod (ext T W M J J) p ≡ Nat.factorial J [MOD p] := by
      rw [hT J le_rfl]; exact Nat.mod_modEq _ _
    have := lp_spec p (Nat.sub j J) J _ h0
    rw [show J + Nat.sub j J = j by show J + (j - J) = j; omega] at this
    exact this

def nN (T W M J p j : ℕ) : ℕ :=
  Nat.mod (Nat.mul (fm T W M J p j) (Nat.add (fm T W M J p j)
    (Nat.sub p (Nat.add 1 (Nat.mul (Nat.land j 1) (Nat.sub p 2)))))) p

theorem cast_nN (T W M J p j : ℕ) (hT : ∀ i, i ≤ J → ext T W M J i = Nat.factorial i) (hp : 2 ≤ p) :
    ((nN T W M J p j : ℕ) : ZMod p) =
      ((-1) ^ j * ((j.factorial : ℕ) : ZMod p)) * (((-1) ^ j * ((j.factorial : ℕ) : ZMod p)) - 1) := by
  have hm : ((fm T W M J p j : ℕ) : ZMod p) = ((j.factorial : ℕ) : ZMod p) :=
    (ZMod.natCast_eq_natCast_iff _ _ _).2 (fm_spec T W M J p j hT)
  have hl : Nat.land j 1 = j % 2 := Nat.and_one_is_mod j
  unfold nN
  rw [show Nat.mod (Nat.mul (fm T W M J p j) (Nat.add (fm T W M J p j)
    (Nat.sub p (Nat.add 1 (Nat.mul (Nat.land j 1) (Nat.sub p 2)))))) p =
    (fm T W M J p j * (fm T W M J p j + (p - (1 + j % 2 * (p - 2))))) % p by rw [hl]; rfl]
  rw [ZMod.natCast_mod, Nat.cast_mul, Nat.cast_add, hm]
  rcases Nat.mod_two_eq_zero_or_one j with h | h
  · rw [h, zero_mul, add_zero, Nat.cast_sub (by omega), ZMod.natCast_self]
    have : Even j := Nat.even_iff.2 h
    rw [this.neg_one_pow]
    push_cast
    ring
  · rw [h, one_mul, show p - (1 + (p - 2)) = 1 by omega]
    have : Odd j := Nat.odd_iff.2 h
    rw [this.neg_one_pow]
    push_cast
    ring

theorem good_of (T W M J n p : ℕ) (hT : ∀ i, i ≤ J → ext T W M J i = Nat.factorial i)
    (hp : p.Prime) (hp5 : 5 ≤ p) (h1 : Nat.blt (Nat.add n 1) p = true)
    (h3 : Nat.beq (w7 p (nN T W M J p (Nat.sub p (Nat.add n 1))) (Nat.shiftRight p 1)) (Nat.sub p 1) = true)
    (m : ℕ) : Nat.factorial n + 1 ≠ m ^ 2 := by
  have h1' : n + 1 < p := Nat.le_of_ble_eq_true h1
  set j := Nat.sub p (Nat.add n 1) with hj
  have hjv : j = p - (n + 1) := rfl
  have hN := cast_nN T W M J p j hT (by omega)
  have hodd : p % 2 = 1 := by
    rcases hp.eq_two_or_odd with e | e
    · omega
    · exact e
  have hsh : Nat.shiftRight p 1 = (p - 1) / 2 := by
    rw [sh_div]
    omega
  have : NeZero p := ⟨by omega⟩
  have hw := w7_spec p (nN T W M J p j) (Nat.shiftRight p 1)
  rw [Nat.eq_of_beq_eq_true h3, hsh] at hw
  have he : ((nN T W M J p j : ℕ) : ZMod p) ^ ((p - 1) / 2) = -1 := by
    have := (ZMod.natCast_eq_natCast_iff _ _ _).2 hw
    push_cast at this
    rw [← this]
    show ((p - 1 : ℕ) : ZMod p) = -1
    rw [Nat.cast_sub (by omega), ZMod.natCast_self]
    simp
  exact crit p n j m hp (by omega) (by omega) ((-1) ^ j * ((j.factorial : ℕ) : ZMod p)).val
    (nN T W M J p j) (by rw [ZMod.natCast_zmod_val]) (by rw [ZMod.natCast_zmod_val]; exact hN) he

/-! ## 6. The prime stream

A stream is a head prime `ph` and the packed gaps `Gp` (8 bits each, gap / 2, low first).
`sp i ph Gp` is its `i`-th element. Once `Gp = 0` the stream is constant. `sOK` checks every
element against the pools. -/

def sp (i : ℕ) : ℕ → ℕ → ℕ :=
  Nat.rec (motive := fun _ => ℕ → ℕ → ℕ) (fun ph _ => ph)
    (fun _ ih ph Gp => ih (Nat.add ph (Nat.mul 2 (Nat.land Gp 255))) (Nat.shiftRight Gp 8)) i

theorem sp_zero (ph Gp : ℕ) : sp 0 ph Gp = ph := rfl

theorem sp_succ (i ph Gp : ℕ) :
    sp (i + 1) ph Gp = sp i (Nat.add ph (Nat.mul 2 (Nat.land Gp 255))) (Nat.shiftRight Gp 8) := rfl

theorem sp_const : ∀ i ph, sp i ph 0 = ph := by
  intro i
  induction i with
  | zero => intro ph; rfl
  | succ i ih =>
    intro ph
    rw [sp_succ]
    have e1 : Nat.add ph (Nat.mul 2 (Nat.land 0 255)) = ph := by
      show ph + 2 * (0 &&& 255) = ph
      simp
    have e2 : Nat.shiftRight 0 8 = 0 := by show 0 >>> 8 = 0; simp
    rw [e1, e2, ih]

def sOK (P3 P4 : ℕ) (f : ℕ) : ℕ → ℕ → Bool :=
  Nat.rec (motive := fun _ => ℕ → ℕ → Bool) (fun _ _ => false)
    (fun _ ih ph Gp => pOK P3 P4 ph && (Nat.beq Gp 0 ||
      ih (Nat.add ph (Nat.mul 2 (Nat.land Gp 255))) (Nat.shiftRight Gp 8))) f

def SP (ph Gp : ℕ) : Prop := ∀ i, (sp i ph Gp).Prime ∧ 5 ≤ sp i ph Gp

theorem sOK_sound (P3 P4 : ℕ) (h3 : chk6 P3 30 = true) (h4 : chk6 P4 5333 = true) :
    ∀ f ph Gp, sOK P3 P4 f ph Gp = true → SP ph Gp := by
  intro f
  induction f with
  | zero => intro ph Gp h; exact absurd h (by simp [sOK])
  | succ f ih =>
    intro ph Gp h
    have h' : (pOK P3 P4 ph && (Nat.beq Gp 0 ||
      sOK P3 P4 f (Nat.add ph (Nat.mul 2 (Nat.land Gp 255))) (Nat.shiftRight Gp 8))) = true := h
    rw [Bool.and_eq_true, Bool.or_eq_true] at h'
    obtain ⟨hp, hr⟩ := h'
    have hph := pOK_sound P3 P4 h3 h4 ph hp
    intro i
    cases i with
    | zero => exact hph
    | succ i =>
      rw [sp_succ]
      rcases hr with h0 | h1
      · have hG : Gp = 0 := Nat.eq_of_beq_eq_true h0
        subst hG
        have e1 : Nat.add ph (Nat.mul 2 (Nat.land 0 255)) = ph := by
          show ph + 2 * (0 &&& 255) = ph
          simp
        have e2 : Nat.shiftRight 0 8 = 0 := by show 0 >>> 8 = 0; simp
        rw [e1, e2, sp_const]
        exact hph
      · exact ih _ _ h1 i

theorem SP_next (ph Gp : ℕ) (h : SP ph Gp) :
    SP (Nat.add ph (Nat.mul 2 (Nat.land Gp 255))) (Nat.shiftRight Gp 8) := by
  intro i
  have := h (i + 1)
  rw [sp_succ] at this
  exact this

/-! ## 7. The walk

State: `n`, the prime stream `(ph, Gp)` (`ph` = the first prime `≥ n + 2`) and the record codes `R`
(low bits first). The code `t` (see `tsel`) selects the prime `sp t ph Gp` for `n`. The fuel is the
number of `n` still to check; at fuel `0` the walk requires `n = nE`. The body is written flat (lets,
`Bool.rec`) for kernel speed; `walk_succ` gives its meaning. -/

def wr (b : Bool) : Bool := b

/-- the record code: 2 bits `c`; `c < 3` gives `t = c`, else `t = 3 + ` the next 6 bits -/
def tsel (R : ℕ) : ℕ :=
  Bool.rec (motive := fun _ => ℕ) (Nat.add 3 (Nat.land (Nat.shiftRight R 2) 63)) (Nat.land R 3)
    (Nat.blt (Nat.land R 3) 3)

def rnx (R : ℕ) : ℕ :=
  Bool.rec (motive := fun _ => ℕ) (Nat.shiftRight R 8) (Nat.shiftRight R 2) (Nat.blt (Nat.land R 3) 3)

def adP (n ph Gp : ℕ) : ℕ :=
  Bool.rec (motive := fun _ => ℕ) ph (Nat.add ph (Nat.mul 2 (Nat.land Gp 255))) (Nat.blt ph (Nat.add n 3))

def adG (n ph Gp : ℕ) : ℕ :=
  Bool.rec (motive := fun _ => ℕ) Gp (Nat.shiftRight Gp 8) (Nat.blt ph (Nat.add n 3))

theorem SP_adv (n ph Gp : ℕ) (h : SP ph Gp) : SP (adP n ph Gp) (adG n ph Gp) := by
  unfold adP adG
  cases hb : Nat.blt ph (Nat.add n 3)
  · dsimp only; exact h
  · dsimp only; exact SP_next ph Gp h

noncomputable def walk (T W M J nE : ℕ) (f : ℕ) : ℕ → ℕ → ℕ → ℕ → Bool :=
  Nat.rec (motive := fun _ => ℕ → ℕ → ℕ → ℕ → Bool) (fun n _ _ _ => Nat.beq n nE)
    (fun _ ih n ph Gp R =>
      let c0 := Nat.land R 3
      let b0 := Nat.blt c0 3
      let t := Bool.rec (motive := fun _ => ℕ) (Nat.add 3 (Nat.land (Nat.shiftRight R 2) 63)) c0 b0
      let p := sp t ph Gp
      let j := Nat.sub p (Nat.add n 1)
      let fj := Bool.rec (motive := fun _ => ℕ) (lp p (Nat.sub j J) J (Nat.mod (ext T W M J J) p))
        (Nat.land (Nat.shiftRight T (Nat.mul W (Nat.sub J j))) M) (Nat.ble j J)
      Bool.rec (motive := fun _ => Bool) false
        (Bool.rec (motive := fun _ => Bool) false
          (wr (ih (Nat.add n 1)
            (Bool.rec (motive := fun _ => ℕ) ph (Nat.add ph (Nat.mul 2 (Nat.land Gp 255))) (Nat.blt ph (Nat.add n 3)))
            (Bool.rec (motive := fun _ => ℕ) Gp (Nat.shiftRight Gp 8) (Nat.blt ph (Nat.add n 3)))
            (Bool.rec (motive := fun _ => ℕ) (Nat.shiftRight R 8) (Nat.shiftRight R 2) b0)))
          (Nat.beq (w7 p (Nat.mod (Nat.mul fj (Nat.add fj (Nat.sub p (Nat.add 1 (Nat.mul (Nat.land j 1)
            (Nat.sub p 2)))))) p) (Nat.shiftRight p 1)) (Nat.sub p 1)))
        (Nat.blt (Nat.add n 1) p)) f

theorem walk_zero (T W M J nE n ph Gp R : ℕ) : walk T W M J nE 0 n ph Gp R = Nat.beq n nE := rfl

theorem walk_succ (T W M J nE f n ph Gp R : ℕ) :
    walk T W M J nE (f + 1) n ph Gp R =
      Bool.rec (motive := fun _ => Bool) false
        (Bool.rec (motive := fun _ => Bool) false
          (wr (walk T W M J nE f (Nat.add n 1) (adP n ph Gp) (adG n ph Gp) (rnx R)))
          (Nat.beq (w7 (sp (tsel R) ph Gp) (nN T W M J (sp (tsel R) ph Gp)
            (Nat.sub (sp (tsel R) ph Gp) (Nat.add n 1))) (Nat.shiftRight (sp (tsel R) ph Gp) 1))
            (Nat.sub (sp (tsel R) ph Gp) 1)))
        (Nat.blt (Nat.add n 1) (sp (tsel R) ph Gp)) := rfl

/-- `Cov A n`: no `x ∈ [A, n)` has `x! + 1` a square -/
def Cov (A n : ℕ) : Prop := ∀ x, A ≤ x → x < n → ∀ m, Nat.factorial x + 1 ≠ m ^ 2

theorem walk_sound (T W M J nE A : ℕ) (hT : ∀ i, i ≤ J → ext T W M J i = Nat.factorial i) :
    ∀ (f n ph Gp R : ℕ), walk T W M J nE f n ph Gp R = true → SP ph Gp → Cov A n → Cov A nE := by
  intro f
  induction f with
  | zero =>
    intro n ph Gp R h _ hC
    rw [walk_zero] at h
    rw [← Nat.eq_of_beq_eq_true h]
    exact hC
  | succ f ih =>
    intro n ph Gp R h hS hC
    rw [walk_succ] at h
    cases h1 : Nat.blt (Nat.add n 1) (sp (tsel R) ph Gp)
    · rw [h1] at h; dsimp only at h; exact absurd h (by decide)
    rw [h1] at h; dsimp only at h
    cases h3 : Nat.beq (w7 (sp (tsel R) ph Gp) (nN T W M J (sp (tsel R) ph Gp)
          (Nat.sub (sp (tsel R) ph Gp) (Nat.add n 1))) (Nat.shiftRight (sp (tsel R) ph Gp) 1))
          (Nat.sub (sp (tsel R) ph Gp) 1)
    · rw [h3] at h; dsimp only at h; exact absurd h (by decide)
    rw [h3] at h; dsimp only at h
    have hw : walk T W M J nE f (Nat.add n 1) (adP n ph Gp) (adG n ph Gp) (rnx R) = true := h
    refine ih _ _ _ _ hw (SP_adv n ph Gp hS) ?_
    intro x hx1 hx2 m
    by_cases hxn : x < n
    · exact hC x hx1 hxn m
    · have hxe : x = n := by
        have : x < n + 1 := hx2
        omega
      subst hxe
      exact good_of T W M J x _ hT (hS _).1 (hS _).2 h1 h3 m

/-- one sub-range: the prime stream passes the pools and the walk reaches `nE` -/
noncomputable def sub (P3 P4 T W M J nE f n ph Gp fs R : ℕ) : Bool :=
  sOK P3 P4 fs ph Gp && walk T W M J nE f n ph Gp R

theorem sub_sound (P3 P4 T W M J nE A f n ph Gp fs R : ℕ)
    (h3 : chk6 P3 30 = true) (h4 : chk6 P4 5333 = true)
    (hT : ∀ i, i ≤ J → ext T W M J i = Nat.factorial i)
    (h : sub P3 P4 T W M J nE f n ph Gp fs R = true) (hC : Cov A n) : Cov A nE := by
  unfold sub at h
  rw [Bool.and_eq_true] at h
  exact walk_sound T W M J nE A hT f n ph Gp R h.2 (sOK_sound P3 P4 h3 h4 fs ph Gp h.1) hC

theorem cov_init (A : ℕ) : Cov A A := fun x h1 h2 => absurd (lt_of_le_of_lt h1 h2) (lt_irrefl _)

theorem tab_all (T W M J : ℕ) (h : tabOK T W M J (J + 1) 0 1 = true) :
    ∀ i, i ≤ J → ext T W M J i = Nat.factorial i := by
  intro i hi
  exact tabOK_sound T W M J (J + 1) 0 (by simpa using h) i (by omega) (by omega)

/-- assemble a big number from 8192-bit groups, low group first -/
def asm (L : List ℕ) : ℕ :=
  List.rec (motive := fun _ => ℕ) 0 (fun a _ ih => Nat.lor a (Nat.shiftLeft ih 8192)) L

end BRFrame

namespace BRData

def TB : ℕ := BRFrame.mkT 1680 256 0 1 0

def MM : ℕ := Nat.sub (Nat.shiftLeft 1 1680) 1

theorem TOK : BRFrame.tabOK TB 1680 MM 255 256 0 1 = true := by decide +kernel

theorem TAB : ∀ i, i ≤ 255 → BRFrame.ext TB 1680 MM 255 i = Nat.factorial i :=
  BRFrame.tab_all TB 1680 MM 255 TOK

/-- the product of the primes up to 181 -/
def P3 : ℕ := 0x30e06b35ee39cf75358315a5c3b9b2bdd2e46e25fd10a14382537a2e71312

/-- the product of the primes up to 32000, in 8192-bit groups -/
def P4 : ℕ := BRFrame.asm [
  0xdf0c850baeddb2128ac9d0fd36dd0ec2f329ef90aca3308ae6b7bcedec1424921497fc345111e60cc412113537268a736f809fc9cefc2bcbe959a57ecf6fcdc7dc216df46f82fa5bf3720c4270cf6fb13e1dcf489d98985e4f734ee9fac8505c106eb7b2acdb6bb26b79b9cd02729d2a2b215b45d1ad39b752020674f4f03993d6c7a96c9df2c43cdd5fcdd4a2a82b5082c3e0eab548cededa2cc10cfb2c34e6f98c290160b64fdf83e7d3438e6077c84a97d92b85d47ac7b128a35167b6e0531f91938128b16ed40b0ea8ed276a4a879f7c745e779c2215fa0572e7a15cae72ee309c077cfb5b3d707818405d883f07d24cd50cd5cefb61fd23ae30b49766951623101af6e194dae9d45749c5926504c31b2e31d16b3a1d8d8f628e30e1137c5dd8637ac50c416fb56e780354d53f83146505e0b75b3fd791dfb6d1cccdf46dd3bacd8c80998bafeec517c181f3bb39e1a7ff75b63960e7e4fbfa4ab3cd18f8673b3d211d62f5e0b3e98f4fcf16bc36e8d7000957b714c4798645de1678e06a21c7cc25ca8fd857afcda85428c1cff131cba807766664cd1ef92b24719ad71a1cacc089d80d1baf2446d3f91edab2290690b4fb849083f3506e79ef43443cfe351c5874753757cdb387af230e22804870783e587646125c93d5e22899c55a15ce29a46aa788de770abed396e6fa35fc451018422e12cda42c1968eb0b94f01da5b9943508ea2fe4ba6651d5d47287366890f2cd535e3789780c5933d6df7e974200cef40380b365f780703c6c344beeb37d043d1ef50ebe5b4b1dc45ace9088eb5474968a0e3305d300ae7a40322ab01357e0cffcf44216a95c444ff2a19bac8a80242e5b642615b266fa3b82e4ebec98b03bd5f61703e03d249324888f88edca090f5ed1243e0a4675f6ae3953d13092b10e09246ac59dc44eba77e164dbfe0f4949818965554093616dc9e4d28ec2f4206870ee44b9ad38fba67c42730b4845e2204f42dcb968564cf342d81da1dbbcb2ad1f705abde27272ca6eb434e635441102a00bb1b3837369200971d33813d146a5507c16e5102a5474ae182d25b8f97aee76e787fb717b4826f264800d01b229407e10b46c31d717cace03707e9813842dde7b9c675f84a599ec1ee76abcbcd5643683142b3af9a5e3ba165a9c8a2d3a8d31de317adde8d146dae44c42d3d79b56996c6c55111ea3f81174d232c5ae8bcf0f11585f68cb32a6395e58907339157f0717bc3ea165222c9ec5363162cf78432b92d4ae5025439cbe242ad10e1460f96a3b9257bb1a9075a34866508f80116c20e59d9ef0bcc790262003e760d1d5a97248b955f6cc61eab2893f5cb8e57f2f293c308165efec92b10c382c1a7f4d7b6b32691a1b62141c02811f4b3027674bebab643b34a70f166e082f1a3489b265b5b1fee25e582b1b076210fe9a,
  0xea98014cae2ac4237f4b4213a735cb3415a1380744196e3371ef349273475b1a9a19eea2b2d83e892b4404ffc9ec8f00c804866f9a9ce72904a292c8101dcfff2039576180f44def879add63b1eccb590677693cae9f49dbf554c6ceba32faf6e84616a64ecc2681a2c895e1090378b6222b56e1bd9cb731fa2064f7b7f066b45169170ba0d08741bd1b0820d77238b47918f994c8aced205746fc0ff5ddd8cf95dd8ef62dd050286266519e45e40e5b2950b8b223c07f101ce162963018ecebd501267eaddb02f56ee6b654257d20d3bf13f73db708520ed0117af6564bb8b0a469856a8cc3e2cae84a242db11e2b060f957bfdc5baa0d4c74a319342609401e3be3e2cf7e1993561e8784857ff0965514a4a9f7a10dcbb1fea1c8cf72786bf6e32594aa1d4908db83d4dfb1c3f8cd9d7a4aa673346618dca07b597d1815974f7e7e86e6d40001b0442574f4404912ee91e38bd7d52aa3eb4ba0fbd5446f731b1baa64f5d05d16a29f33c5cf42cf1f8c2f1d0f96b9a325944e8f02b0169806f2efa153ceefd95679ff923ecc80ceafb98996c16305b5e644d2071399cb7883f6b8a85be82455a9824ef5c3288e149fd62ecee29447798e1f5ea7d3919c51b567ea37288bbefe5b6d943b1edeccad5d4a1284aeddf22256e16e5017fe48dda91d4a4172047b9b6ebdbb35f04afab8a3534b41b758159b035c092cc36876c6db744cdc4558288c5ada4a7c4ca4ef963e05eb3b79ee9f2ba92cca910e4fe4419e33cd12dbd87527274732251e53c0c447842cca8504abf89fb2a0fe66269142a99315d9cfd1cb18ff00a8c0cc9b7d21e6b2d9bba36823cae88b84340801e5c81472d1211357bf791b4b9a83cb8f885a19b4d93e68561301fa92d04eac64892047c44106b572731bc2bc586f7d428463bf12880ddf84b9bcb8b75d18f68f07b2d3a4529f33c265efaa9046e94f310aa9a47d70bf8cca38f0a707a6ce8c2756003dc094a30edb3a17ef3aa4894be8e5d72e22421f097677b90ef6274cb0fe493550d58529e9b9331d11bb641d336d163489ce32364bdf6ed4b327e5a56409b1e276f1ed03f5afc4b1f1eb46f50ea2bd818b6ce560fcf4033323b7f46aab313f4bc2688a9e8ccc1545c5c811b34d48d14308a334a169c2016d94e11129100571fa1dd1c841f5a7bfccbabbc545dba69de8cd04f05f4ad32d476559836d35aca9a7381fa618e0c7e7855e9cd829a0cabdbe9e3c01746e3ae03c2e18f4aa76ef419e3de8bfe4b21500785d9b6964477b8a840ec2cdc45f3227e280e2c5f8f6c6a26c3881003f03b9c89575763154d252dc974ecf290538b9105fcea649307d65a15a817627084c27089384b6073f28023d245a2d78437adc9909abf78ae77d00006f6386c40a33acffa01cdf3667bf58b5a38e6502cd21718fca0d04aeabb5d7635e4b4,
  0x1728b345ae1d105890be726995db87cb8d8643422401f2b9d4fd947140af5fdd89523ad14c14787386bde21dc9610b22e07e931ba28009eb69a71e1cfbc0df11d42c4526b66824c91f442c5636d120007e4d24e3bad931045a7365deef650235aae6a3996d4288b7a45118f689202f6eb7631f39ccfe3ed30df63f6dfa1eaea9abcfc0fbb1889d08158387786d5babb4711aeca73bc3b3e7f510660123273125559e32ae86789b3eea846b65e518bd1b82f86a68b6622dee93c66f28b57bb32c66c334eb0e4e18da04a01e1458f10bfb1b91ada31354048151dc2f7b5e1d35cd094790b3a592983b79c98f2002554d6ac0753e09d4c95de4b0a2dc4af58bc18ba1c404b3cf1f6f5e6353388ba00542736dafb6b3890ed4eb1aa021baa0a1027503756833e069161f3b5df47575a40f2ed8ae5cf84444b7fb646bd1ccb521788b5d39ee4e9492f45b5052f2f8d973d0e798ef2bea1edb9884c1f5ad82ff9f2da775d8c1abba03a5c92ff2c3ccc31a8afb22947e1d06745a05cf02d819e21c1b9eeb81560ef0e999cbf56d4bdb20ee9ae7563555bafaaa67efb0cb235529236a4abc3bbed82dcdf54e45470f179f2174157be3c2cad7e76c7b9fa12a3cedcea2a33cdb5facb5327aead5e2ee441ebfe4a944440623d53d4bdb3e5fa4e7f03a0f3ce18b1b2507fe33b65c49534c5ef0e31577cb2e11c80dd4827e40e09ce1cef2aa8a0b6d04973a6431ea0e721a266ed55b1d51682cf24816a6ef7c28d315fd2c4efd94b46caeb7fa54aa9b6e0b0061cbdd73b551b7a80783e8e600f9a9162f2199788c98a444e28ebb46b57043028fe6c474260640a987cbb7babaf34191506f6a669df1064bb5d3a4522f3706dd1a5615ca291b33cdcc418266d52fda48d187a9bd0c40513361bd5652581c1b2ab80879f9b9c802787745e17a9791fe2d94f2bbbf9e8bd08fed5d2fc21b095a1d18135390d99ffac0dba4a55c77a4ccdef9c1b63ab95770f5296498093b9806389530270a161a78b2759215b5156f0b69960117f858d201d20305aac1d8936d3d8c70293ead432613a327abd5d6b7ec767a694bccfceffb2f505bb0e8cf019e8ba6c25ba9c8a66d8ab729be0c889e5c33b9b003a2777b2ee1a7f1ac50a0b600f9df13abc417f92e56a627fec3318cfec09c3ce8ed11cd38beecc9fe62800f28b554bbb032d54ec3265b9510da2763ffbffa465ebba8541e162029eb43803ead99cc036eac2906e2508acfd0b87815960f33f1250c4c93c84772fcf343e319166a963b9438080e93537495f38e222f30b9388f432d57e061f06db832fc76cd7c2246cdbc725791eedbb0f020e4518bb711c9947fd13da39b34eeaa20b783fda7c7fd6bb5a6bfc5ae0aac9be0260efd746edb56cbad7adf1f59b4ef5590ebf5dc901afac752539f95fa616c0121643f4021b923b,
  0x3c458fee709566842171df4fdf91d1866173d1b733c3309816fb19e69ff4d6644f481709bd1680e21b432a184cfcde4bd4f9b43742cb46b2f3ffd58b5ca10366aa342a9454eedf37ffe61d5b7b01c242438d0aa617697b258e4b6e05f86953963e9b1fb21af5ca4ee94189cb1a9899de56581900c1cb81777ee13638ac508ece1dd9c8bf76060130ee98831d9c1fb6548e12387a276ccb9a1faf40a2ee45223252152bd2949b6b5a7ee3ed5c2879d3abcd1a50c7fafe7d7464053500e063887b01e11ff8f5c27000443e192c9ec6511816a4ef4f6c73c364b4b4e11e4b0f6f2bbe6941fc1002d33c2ea0d80d7c2e37e70d298651f344f10070630a47cd0f686b749590c52fe4333d58a21b210eb744d4e7df8a6d79ce7137a4ba9425114e86d112ff16e899cd2041bb3781489ce56232fa4de91c7ae07bd635bf1f0e554e20163b0a43ed81ab1095811abc702564c76b49adcbc3f5264e74823a695e1847b559021d6babbe9d6989a4eb4d5ff4dff6de9169bddcac984a8bf3d9f653c91cd620b187bdf4e086e2cff33827ccf543d72f80d31c0cfa9b0ec3344ac92fd84b3a3671009f4929fca57466981b49b59806ec5b95115c1d11b21099d94bf85ef0b7bdfdcf30ef86cc521e5a4d267c48da55d3b81706d40dd2e26357d7c865da72c94fd723e3cd37aab7bc2e17c9ae1368ca36ae70f1bb5432a861bc0a79709b81f23807835b1bd97dd958f89f546ca0e74a4d91f2231841b97abae7f63d1dfa52d8d2ecbeb25f730e389347efe4030f78f44b1349e216256ce33d6dcbfd14f9b722f85a32cfcc28fb734de661fad78e2c6065b1a970274a9d4c4b238078e5ef2675620ebe8efc5874a7560f17ae9186eba32895c80e9ab5a9367ceaab065805a41b340cf88a6316b15964530bdee05e98635f268eb9aefe7c81d872c1f52d89472c117d4ead5cabd5874110e0a849337c38acfc60a476b55091afdb9c59ea0200bc2c98cb8fafcdb89a5593e6169294a2d7ad79b4d4bd02449d332f5f101f8a95a668b28a9aa5d4ee6f63265932a22b93e6b08c3cb4ce49b2114839ae8d669db30e78886393dfa8e92535a3232ce2d3b388df674137547d46af3ac76aa08a3962b010a924cecef13be7fc1ee1f857c0c1b148c8350206d93cc1c26bdf2f2083e0632187a7170294c132c8c96452ed414567d17115f3d810463dc5845b0e4b2150676860213d04f9e6b1ee1530faab6ee6281c815dc26cd93cc02c8ed58742168b4bcfe102c25dcf152f8c36ededf5c24b756d43201d572e5ec91e785f50244eac7936a17ebe3e80d537492d9ddbfbc53ed3828000ae06dd1478f12304cfaeaf8b594901c5010f524a109d67422dcf2e00b03dddfcb9ee1060b28f0156ff8707686b109c780e98ff3732bd116d2f70c96ca688419b65cdc52070b6929bfff088a3be5f,
  0x33fb30670ccc9d9161ee291159b243d56af86e6c0d29675ffa2c459c998f0c513dd30d097fc73d45684ecd2c87d420a96eddb72894cfb6b134d8599ab23ca2ce27ef0706a741bda8807b24ea39ef3e5da8774e5f2219c3cbb5573bccfa96c4c5f9b3a11dd2cc735f288dc3a82281b63255a99bc8a5e1c55002df7fda7afac36a1d276383158d287c2a4db62276a331b0b14239ceb7b72b9229337e828e76bd3b13316c1bc98279fb890663222d6f91722909d219a67282cad6eed54326f5e3ea9b7aa50d70e0e9caeec704373d0bf36057bfed71c9e794676fcf07be1e1c0ad66e7790c09f157620dfca3e522db1ac9e18ff6aa4f5ee9f682e9b4a56211d5d51aa3fb19b25926b06393d3c4c47ae87ed8c52d4f19f54ba73ad3fa32cc3da4857c98d0fa5363a46671d532322b398f90422bd732d02d272ed70fbfd0cf7be141b677000847b96d192296c900eda94ea4023fdf00bf2e7a6a9381d832e4e1189a35136b481179ba243c5661a527b140c93d9997eb066a8554bb1b07ac04974f076092dfc159a231f26ff9e7fec54a1a4afc94c723cbc812012373c707e0c81c5783247e3416ec84e3a4aa240527a9339adade0e966d9acc3a1867b2e62b4ab1f43d342508113196ac649cf973d1f98067ebe3662022398d0617ba378bc09596a6403112db6adcca330e099daa38cf9f921c1459c9f97d4be291cb38007fc34a018edb5af08589e98b71ab0e99acfda859889c4a0360109261ff6e40c85327af396767fdac713adfe8caaec684bbcab3fea995f660af05b974c5ba6ebf52d1f8e2b31117cb8faf93a0e939836d3b6af25604d7d5b4f6e144a0485d0c5b5400d4713de63a2736fdbbd20ebb835cc9591b48e10764f4744729730117cf94bd42e70f0f2e86b609f59053a2f94f83d2c855f49bc0563edc62683301a6f1af059fbedbfcf1769c0e1fe4ce07b65de8b71ade682636d0abde0bd94cdde2e1cef86e715d495cddfcdf0e420d7fc6c7b523f6cc2a181df5c50d713f7142e22812e9b36d83d5c41a754fe1e2243d67bcc372a7bc1f7b3cd66155a6d68f2d78535f6ead61180b20a9b7345e87ee56618dcbe69453bfb5db4ed7337f698e5b98735b83d30c6b59ca226c04df477bae76bb50da3ba91f4f324c51588c99d2b8258edfe273d77883d519f5059f50178c73612660f88af6f622035e53bb5cb8421128833d0e2963696885b2672976bc22bdef66a3f79a1eeb5745b266abaae035f56d7da1f92773d588519cfb671cf7f840b8c0eece8eaafaa8cdc7bd8e95db47b86de2f99a5c118b3d336c0cf108f8b13199d11f183c61a0e7fe7d42a609536ad880d22ef9acd6e7a26f94aa1aaf1cddea57ca24edf80e18bb54dc9142b3f9de36aa66add5c83fa9a1b3827de04c3ac9a362fe20443937a0dc21250e8d6183c51a530b2ff77d24,
  0x556d7e991792de0f391465729fa66f7cb4cd30e9aeda0d488686bbeaccac9ce166df07cb523e600a3b36496464fd6e277847eea66bbfbbda8d20d01bd4dac96841254b0ff6c61a90385a3239eaab5887ebdd5a6bcf72691ab6644a094162fe467ce8c72e372883ce54ca28eb67362b5b180ca57cfc027037004145ac514e280b4249af145522f74ad3b0f6eb124e1ba8e994e4ddc0dbdd8cf3f80b42f338206e5313438d9856c4af110573fa215009a4a69f506da8f1fc03695d08ba2ea83ba5b5a7e289910d1ded13d31f5810300e41bc97799d709db61c06dd64bac664891f71d68e45800f73cda9d18f19015497d2048b5193e343f89677fa0fc96fac78929ca8a69f8eb195e7705bb820a2c1d044b922b3b6cd5504ff78a3cbededfb7f1ddaa0ed0869a39884c6f13673cd0cf984a8bfdb025a3bb1af56f4031d5d5b37016db05548dedce76724a7fd52bfdec469e49a2080da2082e93fb0e7b8984d7515b69b3237649436f27c00b00035ef33f41f982ea205940153bfc318e858a5987c952474bca14aac913b1b4ab909216ee44902547a558dee848dd30c0c77b4d2794e7b6b4757e9816025934a0ca36430fe238884e8e64fadbb0d3bcaba4a39af73014f4c5e97e70e5de24c3fd9d2783b3a430158d1a672220b22612a92cf52e32121f8a5aa83d3d87fcfed7751c93bad78d5787354ebe4574d159fff7971b47dc3e0bb5c71f97a51f75996eb949d7565f8e6a18beb27aab1db5b87394d2b1525140e3493920f7b50ea878a9be48bb9e59ffc3746855d8bdf084cf0ce93a39f6f14d5b3a7d76372b40e5870bd37b3449fe5689e]

theorem P3OK : BRFrame.chk6 P3 30 = true := by decide +kernel

theorem P4OK : BRFrame.chk6 P4 5333 = true := by decide +kernel

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 555936501 1250 555935251 555935257
    0xb01051c03080c1c06140108090d0309050a060906021c0b030a060902010512040605010501030b191a070803161d0a0603020c0f01060e0702010b1c1205220302040c0302040b 75
    0xd41410181e1075580d900b0810b1216004202184c040c084544102c0104815260301000036100d2142d161144008241e005556142c81900d00001c158001c4a6207201d03c0c0c07280c1e20101c03101b40b0507408d0320416035860300c0b03da00740c03100c1035016507600b0303800910028481811207030300004250182090201c00a0100029241c4510480c082e160f2610341131307103a00310780c89001144d100e407541c100500d02d9030525080400c002c1c0307400d00485010a02c6c0420100c00780c54004426a001e042d401d82190030700341800385c0ca8031140b01030403d007410034100307003c00b03000910705078040d521036451101c620069815921000f45211850a41040b080400894805450b01c031030141c0e805951342d5080260f624128410b05610b01425000e541429500e4880c2c0401d85145088030301e8010941c0d80d0003844450a01410001c0445907280f03608000c45e9013030100b4000030100030f8000d0800032681030031400d219076500700080c42e20140c02184250055104140110b00d02441401c640c0c01c420305d01142042d051102240d8148 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 555937751 1250 555936501 555936503
    0x20f060406050606160b0604060501170a02161a090c0a03030203030a2c01050a060918030f0c0b0106080f0c030105030703060902240c0607030911040e0a1e0b01051c 72
    0x41e102c0000540d00c0d1140c004940c0d5135080c0a107203141002d07903030900724004542992503622850414070001243d601c81d80d4900c19054158401c03540c82e46850341100001c3d481380c2002400c0e405812940004100d509007000384046040100b13141620701034902078100401c401603140304a000c21401c0c004a54000240d84d40a540b00da40000c0f03588060903108402c0c1c0c1da041820151600b80c00220b43c00d40c5042d00814080c2c403944800748801d07601c0d00d51030002e86010641110300346c2c80c401d600700e000c02d2050004191008083c2407035110350303055848210a4001c02d03000007011802c01014000c5040a0114050b880740c400d00c0c01a041d07505200000ea1500c406100c050040d589a00c50300e0159501c0040d81724101003505841d00181c1d0349030913209260b030030003c000e2606008034800142c59034001c2c041e41040c0703544101000c2041a04104000090014a0900d01544107600c2031800144000fa03042c03d001f40f405003551a4081d05c0e02c1d0042552005070040360080d0070104c02d00a801c1d2542520f08051 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 555939001 1250 555937751 555937763
    0x8040e01030b0924061f0306051504080604080d060306420b0d1b0e030706090e0601050309010f090503090a0f03050304121401051609060c0b0609060109080307050d0f020f0604 77
    0x95218132001a05c400d26402c070203102c01b811031541c48840c0d9010b03800b8a0441c0c0c000e5511031a0b6800014040a807401184034030111a000603001400003031220b0000c2c000d030361010b50001525170f00ca0b00c4d800c2c1203032886141c0114011100d005811010701e80e503000910640c403042402c80c803102201c014014404c40b84101c086640000c02d2040c16072019801040700d48102c3c81f2413554041e8003101c018648010f410a207402805030950100d01c0740e2190001c00300361901d60464040701d494040c01107070150301c0103028031815541c9940c986601c4406002e00d604143c0110010360312110040200301443c1166132103a04d4600400d1002c100149020007560111000c070101c1c100958881e08090503624040c41c4058840d500c1c0a0800c000d039034140380c050002c840781d40d5070744207100e8403018103540032640100c0140c111842000024141d00e00703030720065403006061400d90a402c1e030b1462200d10f1500311071812201d64121840f2840142da104041c01400e07040c0384000e0140c4115074900076264080504040c080c = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 555940251 1250 555939001 555939073
    0x4020d0308090a0501050a1b021615140c010501030c0b0a0c02190515030a0c080c180102011e0603060c0c022115090604030e15180d08040e01030b09 65
    0x30314410711032600d030260094020300540c54400d034140300410603444944c0300310f1104044d0034217943c400151418903111040c5171492540c1080d4860bc002d00c0d44c1100b0400300030103101941d18040c0018058501e6110078000800c0c1d40d41189015980f000d5141c101d0b1800b100107002e810306c3c059001c1c2d20815440d0f01580c03944410184c42600400340d1a4540001d60031551408020083c001d008000307510134070aa600801c5440300b80b000842c0c8811040e1480e6641e10414013049107601f484a0100071200740500000078881b40040f085004407129000e6585000e03035801040080c02501e010710310380c1c2042c901d801113024400d0b5000400d903c1c40e607403032030301c40e034014400a030f00c0342c1410007200325080c03400c1070114250300c5d000502c03070356410007210100c0000c0c0c460359030100a401e00715203170b510354500e04403540e0802400e58480c06940910329002903010480c04200d6001c10302e94030080014281031400c2c20044c2d811360602010608000c1c01c2c942d8103600a020403a402c401600380400c10394000c50041103 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 555941501 1250 555940251 555940261
    0x203160305130b0c0f060c070b150a0915031103010207080a081005090412021014070c030504090504060902010f02070605090f01030f0e160e040c0905070c050a0c060909020304020d0308 81
    0x100010082d00014051580004d642e04034480000e409000300600b41c08803038440c0c2d5150359140d80e40c0a00e0300c000b0902c1261001044402d400b01b1030440d04040c014015800c020307610410301040d10048441d213004610285c0051040c8001030044011604080d8000c0d4901340a95507184414840d1140c00c02c1003015040c081005800f40c40c6581c0001e1100608902140c2410300f02039048402d01084000907114003003031464148240e00036618150305103422103044c0e98854038261101000000d0880810070104000300d24031080307200303050146000e05c100054900d82840098002c0c1083d2201e0000c1d50703c158001c0207605d80c0f00007150745049055079000d000104210041c0e0107800c80004560040b0300f020140081c118000420a26801c042a0085005940c6842d059488401500c000d02040c080c03100602c9520340c2504503d800010742c0c50685007600141d10b603281000007400d01244d1214415030100110340d805a003070340140040503030840c41e50034a940007030086000e0b2035008003170080e0f10300010 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 555942751 1250 555941501 555941527
    0x3060c16080f070302010204062d030b0604030209010308040303180e010513090204090b040506010909080702040b181f321324121a0c090d0b07020d0203160305 70
    0xb181c808030b4001550700c0340c0716031074082c0c040c0d0460300035540010070181c2400d08107290310815540c1d0302101c2c1921903042040792005c60107030500030344258201d00200320003c0107840d0810b1060003180101c10072500d8a045180007840d10039094510104031070400c000b803100c40d00e1400e10504407003084420103c0300c010b415200b0701030710798008040d40c040d1400c4803200500038120022442148070b6801d0700c0c0c860780c90300c2c101003c44190350320240c600c441c203020410050405a03c04a114400105519041d030085800e020b003544044a01000070384607840209526001200b0328800362a940c9c04c2c03842602e060450b0040700700095041859503110302c0300c45400c1d98444001001d4000b46040e8148400d40300320030b456995001d80300100402070540600000c0c4001a1a55065103030b90141070100d45070488003101c1d82c1d4000240c01c25014034420401441da955075030707900f0309003984034020340409071620b01380c06802c2088142c1c56500b5500104007880d1414072002c10044d80030b50505003282c4540001c0d10b0303c = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 555944001 1250 555942751 555942757
    0x10e060d14060423030901080a02070506090307060c080105100518060a030e0f060601140f0d020703031406091017030405060409050130020111010207051507020c03060c1608 76
    0x3074015010301c060481415008120140304a0054101201c0c3d800400c1c1803804115010700d05810b5500700303218aa10381d43c0703d2a03a040c0c20000058016041c021141c40d0a405c1800645400c80e0a9100203403c9003007010b640204809602c407401c0c03d00039585480040380d03014026483e10010490b002900325811030488404001241d8040c0c6515121709a00320060000d0a185030040e2580c03061784810020400b000850610800042c2e45001c55044003c09042e040d130407604180c141848280f0140c1d100c030751144041c0654a02a5501180460240800d9016090040e040303500840ba16010003c1da00c039007800003030459511001847c614146032000900358041e40e00030962000380041c00084003003c039048981a02c00122030a6440840d140d054100f080c04454500c03054111446c4480141d8024100d00c9a00382100c0c1c0098074104455903601d04041c051031182d0205981d150901481650401040241c803205030001c25035420600d10780d00c0c160142da1018816916255500740410080d4026 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 555945251 1250 555944001 555944003
    0x71517160503010501200109080d11090d08070c030b1f0603020304050c1c0f0503031b071101080a09020d140d03091e02010905131e0911011224090507020c09010e060d 73
    0xb0446239445250620701d5900002c110f642071814024480c172303000100c404440e03112034005c10780140440542d0300cbc0b041c0d1b504591005d9420603c42c40e00040410101003079944a041403004d41036025070100e480d0b00032007c00d500807000301841403003040f0004000050008645001319a491903040c030040703910307801f46071a02006101d000400d00000410800002850184414078110074080c0d5140e82100800d01481c1c0014142e840794030b8050a465004e50202500200341d150003190b4000d19030003190315a01011800c403026030041d035800083c104180103400301a946840d0900040b8140d41b00c03d640b000030410382c003075102000d111600c2103a009102d0344008120160258808030049400403000b080d000c1c42000c00b1050304101d41c42031000502c10461030035440610321008900250045440d0500c0c00003003075010760b89186024003507914004408512010b02c541c01c01c0ea50074020038805883c0060000300c06d542c030400b144c8070b080d500e400b030243c191180282468080e58801000071413080710004 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 555946501 1250 555945251 555945253
    0x27151515092b062c15010609060c0605060a03050a03051b030a080114210c01020106140d02090c1c0605010809280507151716050301050120 61
    0xd41012518610805010360345411100002c0600d661600101249072a50352402c80300e800400540c005641070f8020300c0e807406007440c3c510001191480749400e09040c51050189640010401180440340c07100c01c41c050510361900060062420310003519003446080c004212548900001d5032070f03105e083c0d56000940c2c0200c03ca440c0c0501c0c5040162041c0c0c800b0004d015408401003403c0076940001007200c40c013494039a1101010f82c0307001c80c0c800c40c41d1002140a6800554189914204952103061211922040010b09410380648001900b1103850b64000c103030982e03d01400025640c5c6014407040300940513540700303ca40d03944445490031841210412109001424146820b000150b84400c050311005c0c0c8a5680030303102c42c0700880d0b641c00b85450000000c1212079a17440d06910039151101010f03c031b442141c08a81d250760251056010440c900310005110320500881c09601032042c54025002a950f680a02c1c0740f200300a01502c4140616410700181d220429803421010b0104c13200c144d80e0760 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 555947751 1250 555946501 555946519
    0x30c051603271a040e192c0c04180308041e050109030f030213030318080303041a061005040506130801090f1209050f0f0a0b03010b03271515 62
    0x1207800014280030700a090703120803160ba032000500d2000c80e8196410000e10098560720030682030b032549404c0b0468021951076100d07607c107000c007035180f0360520a050701d1050840401c10b80c00e076140c800c11a049a00c907509040c107400711689032070390040210782c051400f0051039a42c0d040420606200302180c088200e8090803200500c0b0065000c0f0115a110359610031400705540800c4090303001c0e02450b11452465844100f00203401285c08006180440d0b81c0c1061144e80c0380c45481c00e40e00704a8058441250341152007080d01400030341b00341e0281044030302030018000c42c0c2c03004246001c2c82c0a03c0780992400100404140d00310700c2e8000003030003c103009101d441e0130b920309070486036050b0b0021200364150612000000b4001d1050030241d5401078042065604018100840d0002e0342105075040304400401040c0741d000000290301a2040348081681c0303062074a003038404050101844140c1e409112001d50200402003103c040f00200c0c0e01103440341c1c4d03e851042c0081c24803109602a4007540c88 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 555949001 1250 555947751 555947807
    0x3030213080a1b031a04020f0d0503090a080304032d061d070524070f060507110c011e030f1103071701152a06060f0510030c051603 58
    0x101200361601c0f0f02450803810896002c40b075115002c07400000e04521581c20050300382030104220f81d0b8001c0c001046130045c649400007190041042c06015030b9035800000d1180c9140c20681c030814000c0109800561420745940c544031401150a0450840549440c180041d200300c84510b448103960443c40401281d200028003000c3d089040aa00c0440c0c0680d110020716458817040c00121040c0001e49e049031408242100385082d800410304032030280c42c40b903082c00854058411603124001c55101d407000b42070164801e500d02580c0c0742e1114100160240c000031205200340054220030f03d141808104e80c8801c003200e4005d003414000c0c005000d0f0000c01046049640306805c0c0c80a240d52040d1202d10707036210403c000c9201c0c0a00d0230480420a907002221045c041450b00e01000c0c48510316603d101d03401e9555010a0b101c09502070348422244010512039898042e40d65000c122590408012140da000c0c005002c0d40140181148014180390000f010315000b107410440c194001010795000045e1 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 555950251 1250 555949001 555949003
    0x60c0307020c0a15050d020f030c070302060a15090b010509041509060609120b0718030c051e280f0f06020708030a02030304081b0f1c0e0a030b040303021308 69
    0x104a440c48014411002595124101240102d00f900d94424002c0e090320038158007a0340f9a400134040d6481d0381e0b82086514624800140510b00407a0380c4c0d42031507500c040c00c0c10700034a4240d001c0c020f5182c0c41e1905070000054503a480d11070b000c541400c1b00104000d085540103952900400081035041410184131410910112407400243c66242204002e00740d00c921049507038206900400c440d9072566a403440110701e030f15001c1540410300d890161605c800c0708005101d08585e542c4100d80c041c2c50342c00180800d2800307200310114180b0b0811400c810000d20381c0004d00c40004001030140b2256180c0311030440c801900100070241002d010801c40b00c568503c4051101c407124490000140140c15001c01c8010001c422aa0510042d0b80114116240d5454441c0668049602806000116000103480b0316043c41451000e602d050054101c40d0200204503424801c410070b0f0200300103641460740f002d60f640c0100103050f683c000e0200c160f40e684030314040d00248a10418000a0040c0060008004030 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 555951501 1250 555950251 555950257
    0xd030e090a06060305090a0201020604061104031203050f0a0e0d0c060f02210c0705030d0203072a11041b030b0f090f25080c0a020a0c0f260a12020708060c 68
    0x869a03001c103c81d540d46d4041036156910b0603030090068001c1004a008142c681e00800071070701c150401036140c255255580c2000b01000010310b000f10781c03158100210035045115190b4080f104201c24070021050456641e00c501c8812500c10a1020585244007401110350140c1c180192020003190303940c0c12003d0300d8048806c1c41400d030b16403002410000300b9440452082d2411654400011400d00c0c1c08440088060f40000300311204002041d443c05040e140c9500800d50322100080210905c1e0149050014001503460556070141d42080305090188141004080b05041c0c00e190009202d01824001107010303400015055005038040144640400001e412034051901d9007500d40d06080103461181c0e02464064401e00402c9182c00001c900d21525802441c44041070720503140061155502c102000034103070010810710909020034446045440c00000c10f44041c90718000d1412407101c80c15548400c0c58200070701b01c010710160164107a0080100501a09603c815104945080f0b414140a60 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 555952751 1250 555951501 555951509
    0x6030f111b160b0c0f15161b03030b1003060608130c030f0507060f02060709061b061118030118020f150301080105060f01080907061d03030f040602060f010b090d030e090a06 76
    0x40a0160080740b185c0300014030a20f517079848241003081d80d540b01084081e100c1896022070910480e030b4080403400d05075082c1d030200780784240c60025803e4441c07010702034403542018802c004e05182c88400e00c8296044024158480d5184d0b411203400e03021440c0901c10141241c3c4020001111f484a1008020700401c603034058800c03507a00e179410403c000c903040760744d50f4054407440040b07103559400380315a84c896140210b80001a100c4120240700c5a0350b00703011200140c036481e107441004a07000302c0c2c00a1580310340c01e040070210001c0c4040002c03400104071a1050a80081c807174100401c1c0300c0282d03124416900030310341c013100070030ba201c3d03030756044050107800e0844040c3e22038900801d0b04081d0350701900095029507400780c000c3c400d15040c2034081d00c41c000c2003200c2e000c450520713251140701c40d60b042005021808210f044952154039242011389480406003562000702001001808005880000e944801c042190000f0202c09981416201c8628800c0311503008401002040148040340c0c01039005c60b = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 555954001 1250 555952751 555952753
    0x3140708030f0406080c2508091206010e010501050a1d01020f06040f02092508150a0305150901050906070c0c050d060207021806102303040b0106030f111b160b0c 71
    0x1681e01c02d0301b1039001b842100031030040404a02000104a40010444032006104440c400e207026020400641c032180d000c032544846500200040c440c01c4802c55520740140300030300307007181402d07529071002d0103014000f06000b003081943c2c002c00455070320030040c6d1140c01030031030155000d50800d4180781d56119040c0105038041c00f00718000c2402640c05000c000c1400000038900025508403c000700c0e1030b81805400d004620064071107119499070768264600045110f44010444c01140021500b0103140007800d1600592508041100c5440080344540e4007101c0d03850100485080c3d440d240088680d55080079070000e04d0074411004001066008040c124000c4409400e042c0c05801a04400e2100b22a210307004014480200c08407030040f24100c4c030011070a6207404c0715a04d5001828030342d81045806944545c0200c0040082035010b1007a074051107400641030160001c1da1408580500c50802080140c40e0300c004180c0b2084403c0c402d0054010302c96044920895941e051001d140c0c11201100f086 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 555955251 1250 555954001 555954017
    0x1091a220507120b0711030a0c0f0c0503060108010209040f060f06050d0608030a120b030715030e0102040918030f020a05210d0504030302190314010b13030b0708040c1d0103140708030f0406 83
    0x1600400000c0c8d8580f811240d64030001244281e4400f540400076a0040305c0405009002186175502440400d020708060000181c030340d80303401d080100752450a49100042c9181032000d1001414130f074228070a8400608180d030340c461044d1042d00040069078090003141c0804180303045401d5100b003010304c050740ca0355400d01043c180d050415464a95031301c2221902d1401440c0b800c07100340070750810b800d0320307007240001803c3c82d80d11600d407001d40c0c164841900202c1c0e28540211704041e08103100c0a01861684000e050420301ca031340d92a030341c160516401c154680d040300c5089280041004661580c2102c078003d22041c1407505d4050085c0d04603220442c40944101080c26003e4424402c11180a034281c01c481c80361703441d00520b00156070010101840b1403158140100100c0d28008446c0e02035999656001d001d4546400c0c0f18424000070b420407d4984e1140c0381300c00460072010840350540760002e450248800c01640120725200d520f41c89541203001c0490100c10003c02036000c2d100302c906584034800 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 555956501 1250 555955251 555955277
    0xf1e0c05011727010513021f0905040203040807050a03020c130e0c0d26041d0c07140f100207060501060e0a14010504030c0801091a220507120b07 64
    0x2401e4045000c50704415504800141065002e00101c3c9268032003c80d0345980c222010700d4040c00c0d52000c0310801c0c40b07071254070b14120460900050b500c7c03510310500c90803513462514140062810306a0300c10f05100f5600030002c5414040d051007224503083e4004121480d41c9a5850f01a440f00d1850113400c0c480c11511200b000039590501441d10069107030f0008d40900360341c1c034041142c00c0e0b031300700001c1d2105088510240e00360408014110180c0002c8118a61928a00f000c20107140b0b0800f0030b540440d07103d507003e000502c15481300b40d0724001d900c00c034101000d4074105001403800c404d410f07a8580c0c51091258006040a4990060103007071f01403181440b082e03807103001c107803200081920195040324041d07904000c401d84401c260802c51405141513450700da0750b074940112042d01500304e801c86941d81c0402c0c808107d501b81500481c040d9a080ca1180c52500780200300340650401042250402e48030301c3c8500b040418411040a0b100071505890020014140096080c100302c80d0074010034441d40410f0 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 555957751 1250 555956501 555956507
    0x7200d030e2103090a120c0507080d17042621010f27050103030e0102010e0a0312090303020c0109030306030201020d0c081902030d0e0d030b0f0603010b070f1e0c0501 73
    0x120b00405511035400e60702a8441c0609076000400c5075141c0d005030f0950394001410102a401042140d035104041d000003405d009080c169980d11010055000c003441d074020039081840d0340d028a000840d003980075541c90403da044050000d401400342d0684000040c498a03240b03000d404a503500d1280501e2b140c1d48103a40c041568404c0c0219400c00400b1841084220780006c1340c0350210344211200c416805501d0b2844064a03400c3e0411000300d001c00110f0282564244285082060920300070f10f001d0b2440d8902400700c0d0307900101c0074901510b07680d0038801d241c040d0701207807005900003000704401505402c00070010642c9000403801405411552150b43d4071a21640081d250090307a99440d1032800c1710045110290802010250300041c000722440b50302c01d05c03800c0008800080a844043c80e406802400c4414000b0114410041011050342d162074000070f0f0380c1074170300000c007090380c40c401c90811a04c1c0c0914a0300041000714207011a80380c0418881103005d0092160a10b00b41c3c03580c441c4015 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 555959001 1250 555957751 555957763
    0x150117070513050c0c010e0705270402060a0e0a0f0e06030304080c1e060d0e010b06130312020a0206030901062c04020f120313050a050a050102100507200d030e 70
    0x120b51026281028628904640c2e00c05a04001d00d640c2c00e92405034041100c0b820750b000300b10b8860b00340d00501000c00007802d001ca046441569124581075000169000c0860008000360020b401840c02141c0700780554023481c002560140002c08081031240e50b07a003d07e2006a160046450f03980040e0049906403c001081c0d60a03103d891010b0a00808468240b0a240b00d106602c40002000c413600058903440d040001e2603165040800031801c4c1c9030a5146900f500c1d407150b00c49009007410000001d03c00c2456001c0c070141d035400102c20003180c10750030040786400c14100001e54444000030a00400050540c080000c03604030210380d64000041c410280c041102800341010a01c2c0c40800003001071030300d8184035040300c0b4010400c0c03040c458050107041c61504034120f00803c8041801c0244990300d0030443c004010b101c12110400020309240000351a664a0544d02c00201d490f00080750845010b4541c1141a0301000b00405540c2c251075260b503543c00c03280440101191500f03181c100804004525 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 555960251 1250 555959001 555959009
    0x3040906081b0d150b04060b18030d0f12110c030307021b03010603020609040c091806030203010b0a12031b1a2a09010e0f0a090e060a060303170a0e15011707 69
    0x1000c034800305200d1404041c088000f5807036071042d0303100c01c08032309040343d1406031141d0701c060307a130018000d1032280c00e25140c100460b010342c0030300685400030081c10380c5c00f481046d5080c80301400810502140450800b2070301407401100d07054003020040160040d40050091391142d100c24505480003504010301d8200c5001d408060340141e000c00124090b8207150704041000e181502c2c0040501e0356480198180035039016a8411903a200c1c40e041056180034007030800c8100080b0341c000505840d201922041142d2920002c01340280b03000303d180c1d5548006864084660440840440c1c2402c040c50400a10012107a01300b841d0504000f003d805031042c6080d100481c0d152031402d241c41d1480c40195620310803021031036030040c00520001e20540303828007200000d041e4400301041d82c0315a0609607003842d90060000c00294a0544c080010941c449611040038422818180700c0c0c0e1651081d1a0103840702450040c6248075515602a540250149003030407102000c60121420001003401c40d264180c0d846 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 555961501 1250 555960251 555960263
    0x801080304030809010c0209101409090a020d21051306080405150a1d03030105010f05030f06210f06010e3405130b09030606010302191103040906081b0d 67
    0x1c18000a40e6680040c243d0b900141409516611a41c1c002204920211248580c075001c014042003d42a00d48542c2415541180c5401c43c51a04200d55680d4100c039010191044001100d65400e1040e210000c015001807070302e007651a40141c0300080c1c4180d202c0000140b203c04844000078446104440b001d000b10b611001519409880400c400042000070717120140e8156594029400008013203c11031000c00180e0155032258540b00015003044504003400c01482810000c1229500340001826402607080b21040c54915011404081d00d01d41808101c2c190b1082812200c2022000546181205c9240c040307042c41d0381c0c5041c18582036a00e103040e09540041c42c0c60181100c813800c4002c1d102c9506a41c074140342040c0011500f07000c00340b000d40c415060b0002c002450030315401e061058550000382800e066144c01d0942d4010091070141d985228104681101d02e04410300e424070844004104446052040030748036000c0580b80d40708080c02214042074442c1c914402d06220310869201c40d0008 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 555962751 1250 555961501 555961507
    0x4060302092e0528050a090608010e0a021c03170f0a0e0319030506030c0402161709090403110109061d1009110d03090b070803150a030b01050402090d0f0305070c0608010803 76
    0xc6190104d03000025400c000580320424003082945815031100000c1070140c40c046004c0385096541421541c0112801816402c501d4040e0056102e0740443c00c08071030030f180c8030a0885007609007207c440c05002c041c005012800b07030910800c4201d034455540902000310042240e5406001103a9580c4520015900e0803000e80c01a1028213002c0d2341b08035440310b409802e41f58116030000004049078084a8254226100401c01c8c0050140d2880c101800070041500b685c540070804002403550030009000034200600c0508034015260207400c2420120b6010782c1c1800906480340c503900c8180300c176030306502c0e0f64880d00d842540018207038013408011035040504a0003e18001c8188280d101d0380c502d040c2e080c008200d0300041c4041081004003003a50040215070303140e06140b070240c280d007100c030030f0041c1c030440c1844401c2c8003049580d00e0300ca044910850340182e071400070002082c08400501c00103001083d16680707940501d9048001854054807404110810035200c110030703510440d080c0902e01c070703940c028 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 555964001 1250 555962751 555962779
    0x309050d022a030a0b0108011413020a03080f071502090126010504050711060901020a2d0302090f0405090606040506010f080402090403030e011a0406151d04060302092e05 75
    0x480916400c2c0c000c0c00b0740d14444526264580c00a0003070780108041e03952140301c10b0030101060f0010343c02c400c0200020351000015000100542820f0001901081000440300f81521031201103840140d0f03c4440395500440ea400d42c40e00a403c140b0086020405041a41e0000400c40c44140d0506000503014451070f4201401d00c0002c050041100c0184204081d1812140e40d04014061103081303c24005680d844082c0d000070315101d0003054540802000742005007030309c00214400380c41d8003058900140c407940701200041020328000440ea41042c60101400701908000c6800ca01c20541a213003400315440f0030004680d0700d0040d000d0140000c54660101e401494043d418542080c000c0c5030204c0ea01250041c41421221041c940103d0700c6441d1610480074103244c00307800b0017040304c6035020b00242411403028000c0c4052100382d85441510031014016513840e80e0000700a5600503013801490b240600c8106020310f2242040100030480e140c51441900725210048183c5070041c0180480b2000 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 555965251 1250 555964001 555964063
    0x30e0414011503020f0705030904140601050d0b15070b1b07080d090303110d14010b040602070905040203070e070c0303270605070e09070903260306150c0d0309050d02 73
    0x100111410416030208501d1040080c0710f401b400c0785501032005180e8a0b031102080100b140c503e440c44c8417100a52404021440c5c1c1c00609444411100d80c00c01324683c2103980005031003c42418003845440d001044160900c15403101a5100e00c0381c144031100302000d001343d40d101501482c0e01c01811440100b04008000005410080c2d025209040118001541004030741558112010041d5042e80d0784000c0d09805458914190042c44c20056092405052480082d15079189028091046442c0e50101d42151410804840200180440103180b0b04021000a01d0300c5409003081e000241040c141c030a00b2013803503a13200d400009059020041c0c84007640d07005c0190100034118030500c0350103a0140c40310b0301c5440003d4031880c00e80e55480042070075864500b102500c0516403900c000c2c80c200e81401d4071140b0004482c1c100c1012600d0840386000f0310b500703410700e1184164080041c01544128401c1c503400d43c0083c0c00c0b1910034410390300e01071820b4200f00da550818940c8140304034814000d43e840814 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 555966501 1250 555965251 555965279
    0x1a04170309150a170411100e01080a0b12011407140a0207451109030c061b010f0f06061704020f0604051f17010b04030b19050403020703030e041401 65
    0x641031100107940c4400740c4441090080704e045d17581c45907102403203446d8544514007a0b100905d90034440b240000e0321000801c9640300401c107419155803401d217401a5a110b06981c012582010700910140f910011842d598003030a86175040410f81441f20040c0c0c0340e091209072101e07254283e0040c0704680c68a186c0b0364034100ca00d00410f074000c0749000445065211006000d00030302d1b0240f055244004212030620840b040d1030807890030054180501400d50390f001c03c1e007181000c01100e15940b10a0300007600c030841c600441c8505259071078281003001303d83c00c43e00b0a060311407901d0b0b0704211559849500b42da000610f0f400602d9101441000500185480c00030710040c4440681f0a5081545807404502d4804061601c4c04001917000d03146aa200d5000002418035145080d00d0f84555241c80502e6880d402140402004e400c0e200c0300103100b614010f00704003481043c6000500c15801c0034100a0f44801650006030001072082d1100d0301a41094043d0071802d031418600b03a8056842c008510305000 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 555967751 1250 555966501 555966517
    0x91e031202252c0c0a140a020a0203070501091202121614010206070f02031209010b1302031812030f1f03240e0705011103190815041a04020903071a0417030915 70
    0x140e41e1003400701b100c6083c00030700104282a0010010b88140380109840c045032030348030758100429144240900c0007500d2000c0d029a07419074100107900a05e200050038041e028000d8030080007045000150745901010004a0030820b80070399009171203102c0102c400c01141c0c0344040140e03008118620400400c0c2840545c442c0140000041d0501c4e604001000301032000490346a107a004800e001a4082801c0c1100403421071034000e21000c02c0b110303072b10001400018804181001900005001d1001842c241603580c140601883c64060720707880c052200580c2d04189441140081c920a14403080920a1010040e26280180301d82071030a40112074508000155000500040c05100035101c03140351034010400e403a0301c2b071190600d8410000c6400d91480345083c0e200314244241e00c0c4d28400d551507a2950540203032005681d4060700c03000720303150039140d41c00390255a40c0c229512000303960030000390003074071142e442d000c41c00041001c2c15980c82c01070518055125661000c1c8080284200008010311 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 555969001 1250 555967751 555967757
    0x150e0d0201201006080114040b040327031b0e131410050403020f0102090a0302011b020d1121030d050414011b091e031202252c0c0a 58
    0x1a03241da03041c40b4210040e24081c09644142c4403025190210b000d4000035180c0e074002040310220341c15000c220100b000e071018004250420224043c10320805029100c10a20070502c14410200b00390340c4030f450502c5c481540d0421000b0400050218241c40c000c0c03c60301c820f58070621a0702c1d101c15010585882810880c0c0960000c0001801e6100030303c615500c3c40124a4001030301d192a04010b418070755100c0321154683d00c1007280010b169511228501665028039169840c402c8865615025099450000e0352202e42d004e803d10800000030140441900b058070701c00101d02e0342c3c02102650747c00316038440c0d120790024440b0009006181d44150b9009004403140a40341110791105400c6803078029000b140e0a40464003002030981103a40640244028241800d5111111030b044116003190301008044c100f1200da1078103194401c0040005610016000036100740c1e040c0f0400c0b100302c1262250500c1e6045504542001604240c1d5812103407010b007065240c1c070b0760b0b550000122544114800d03418 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 555970251 1250 555969001 555969017
    0x1b05100c081b0a2c1809061918110f1507080d061502030d060f06021c03150b04031106040803032d0f101509050f130203090610150e0d0201 61
    0x25424680e5490b10f0294214442421400651000c2c0070782541d1085c0107100190400d03044c85400d40c00024030702c1e03128803090340000c05a000307101c034030010745028220040756400c0d040d440790038801030319001509990101e640e40612860034091000c034047c09061200405030038800c0c100450840c01c0207082d0f8000c0004001044d50700d030046111070740f41d103101c054010b070700104030350583c0c82c010702c59100a004414216150b0790300d0440002c0da141c2d501e049114a8022401910f0074142c081d41040d03000c40b8410b480d112889858406014140e0414441510000282e0350040c0c0d2600b410000c8900f61203162300a1441c0d41d4643d940c1c0311803800810b80c070420b03040311030f640045200301c1c2030102c0f030060f264420340391054140b400c400614511160451034083e030903415401c20998005403000d046450550304c001550040000040c4c0340710001509000c1d06000204200022002250b003902c114401000342e0318231900d034445c00100903514903022011840ea040081c450b45052001181c1042c414580744c06 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 555971501 1250 555970251 555970277
    0x20402070501050708011e1202100c060f0207021503010305060402011d0d03030e010c080105131e020d0b01020d180905060d050f03180108060a060f1b05100c081b0a 72
    0x10843e41c00f101d203240010580070041c44040c0d00060300c1c501141d1040c102c0c0380030701e050240c0c40780d0030140034200901c1460702c0052142c04034098070080010036000641002030202c482102006580301403000c901c1020f006640d8810301042c3d1096134103981d00000140389580e00d50f03005560042d0945c54003c40c008461000c0c508555405071700c4600c0500c2030340d012400620390400b203070a694000451000f80a401001400184c0380e07404683c01c0040b81244c0030404108031000c00c0035003035080d4a400f0400b40006100605405140c104002c180e401381c4c00c4801c0c241c07001c031040314030303903940480c45041500309002081a001035801064010303100820038a10000903a1740c852400c1c02091502c441500081010300482512101c2c20740c6c81c1000b0f007012940351500400082042071503004550a00c40300e8007010b0700c61441031601d500e98160440c0741c051041f51078103046030303034003980c8500c1402c10b03050054641d46c291003906521300415919010040c0c0310407040d03d955094111102030000c010035904105 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 555972751 1250 555971501 555971503
    0x10207080f010c031a03100b0402070515090f031201090f0204080615030607111510080601030f1707150c120204180b030303040302031608090d0303050603370204020705 74
    0xd10301d40c140000070b101d80301d1060180940b90652050b0003002c140000c0004c00340c40c041080d0201200c1000006421b100304c00001c1d000b40190311001c0e0880c490b81402004880d880712905000386410802c591552646844070355403803280f13330900304a4120b2003004200f03c3c00103400c424051002c503c805410180c40b45c20007441e04400b00c544074400d1300008402c1c038071410700b0311502d42c0220007403900008208821041a44d10103c00e2603042c520380103800000d40c07002d010b00145020b825040c05849995030f4a041c0070790420600b1106541011501d05103403021441241294201a031008031100350300300401000001304105604076050040b41180f030340400b8094402400a4070b603040c0d4054007035038020b40e51412600007005181c000c0d8010001d00003c00d400200703494052034001e0000c0f10990700c1d468614528000e090785c084e00304207100804c004144d01a0809032140314240d08550f0044280d0301103012a22080c89000b0540101d0450051491003110718141d07400d002610142c40c10aa559402d = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 555974001 1250 555972751 555972763
    0x2003190218130501050a0b09031c08090706030506100f0207090c0c11030a0327050d0309090b1f03020c280209010e04020913060b0a0e060a0801020f0904090201020708 73
    0x4030325006410342041418503020000120500b6004410851981840007081c05282d140c007500076004070210310011143d4041044c100c3d04841e000650300c03400925840648813050903038805485001c2c0003408103425129110b04c80c401c1900600451907900700600584018225441c148114010004007145403c1c0500500301400f02d999a10b801034040d5041a000c0341043c0071800384203410404c61140843e600000080081c04c40714074012044806004101c49450650700043e007000f0118022401c5c9500003018400300d0340003e00501c81000c401e0100441c0080d45420160719a10b88c05c00ea21013184a58060152200702c0f00c2151a0898005486201c403003612444c0c41c0c107000d070148101d04505000160300d00405c1c00c050b046c40b25041590020341a000002c00c3d06221020b00320b00725092210f150403107504030300701901ca0000a0307101c800704540c8410880d4583d010b400c501d500001e9001d814400c13100b415210081e134508000051040101400e060082641144620703880801c2d04c003000e100c8 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 555975251 1250 555974001 555974017
    0x60d1e140108010c020f070311060d0603060b09010918080c071206060611060c04120c03060f0c2a06090c0b0a020607090b0f0d05071e030212060420031902 68
    0x3403862641c5011070680c2503134a005690390842d0441c00c0144020707003001500d2000e81e91320030b00e00c001007000c000c0403828a000e541c2d84a0902820040300000b031100d183d2180030455029115601d050380c135814440c090320851b0f0861185040003141480104036528041d141c0458441c1c1500d45266170394408030000f000100d02030f02c506903903080400405070800144c0f5207819882010789070510305021044402d0051b40b1400d0500e10fa00b00b104c5081022001581c1d0155620a0b81080705180e040520b0009094070541c110100da102d95401c02c040c0e4089001d00c00b0700300046aa454120782175920f2001621842004030307800040d03100b0110b40310300020040d03c180301c00d03540100014a80b0800c0140b20b5951540547e481400400020811001940c00c85040b0b0030b80302004101c80c0c0b224074044a156481240e013078a88002c40075414006a03058004040800a81e0700581150704c64504110445062114200350b0703070b425803e40719070f00c041c0101460784011700c61441c6034000e086288102c140c0e482200 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 555976501 1250 555975251 555975281
    0x50403051e0f0f030d050601021f09030e04050c12010807050d021e0312120105011707030e0a0210030603020f0f0603131712220c06030f0f02041e080c060d1e 69
    0x1a00b0401c44217a2240700d500001c24401031004100c0401c802c00814280340640104640f142c07415824507024410302140702e000500200004d01c2e04045504242e008018292080c0d1580b0000040a0000080c8202601c01c0100810b440051781d030300b0050459154504061000c00d8015010015581803160320071203400a0906651401225401030701440140c0220703040c410351107410820880c5e00c0240075030104160500141c68150710b0307411440d0220b12070303000350300628081c0d40c001c0042d03040d004030045070b2080e20701c0600748a0400811034070300c1d2001c4243d0b42043d002d0001070301d0071181c510340e081302c1c070700450b41240c1103003600141c0e046a503c411080547c0449541c10b00c101139940040400400c3e003105070003010409195071341d083d000b600b03105d07030700425898281da07064206550b80003c5a001411784215502da580d002d08503a07551a914549629418103c07001400000200e030301c000000c00104004d16000c048012038004101e18041c84180e000707086c1c0950000506485482d0408110034 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 555977751 1250 555976501 555976507
    0x9060a0212040914100602190f02100908120301030f0305070206040e090106050a08010c020601170f030403060c020105071403010e0c071b030512070c17160e0105040b01050403051e0f0f03 82
    0x911803030013454090464121944030071700801c9180c0d400316640c00380310766400c008940e18034a410503940c05107500704040d60055003100c03041031032908001c4000461ba85601603915080031240380c00424002440b000d0218010308500300002449100140b150341e10060030749081640329186c0389040c031001c0f10412102e0b9920708080c400e034074001d00b902000b004034030020311020a00c440029103402041c450544009461408850024030a01181000c8035107030086a45882c5d17203051503406880000741000240d484c060108107801d00c100340d58800c1c1e425241800b407441c0d2038038403090342c07400004040ca1079103002401172070000303602104405003007002415094081803c5081c1a4140f03580e20428041d400420014200011043e020100803580941460620320226051190921540341c2a0066103030031840003040c1c0c0506602c3c200d0684034103035020400c0d02d0742c040054429105500015010780d00c09000e0750134203500c55002d00326609500041e03500c9408040420752811090480c9080150004 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 555979001 1250 555977751 555977771
    0x106030e070e04030539010b040e03030f0408090102012003040c1e0506160f1b0509011a090d120306030b0a0606201c080702012009060a02120409 64
    0x412440c009448100382500c09401c044d0340c081c00f0b521950f60075803c6c0c3e419180c0d2071113298a2001c00c218040c3c039034008183e1140019030a00380245400d10145110f2880c0c481d6046040e4000001d42c0e21801010f00740016a40704c07902c0e84401c0e81c00a6142904642d00d4801011107400ca0241600003402082c4449480b82041e00d014015110150401011429094008408002c1c562401000c480081c0c0750700ea034800c5030456608840c0d001d09030240c041000344c6024002c20940d1f805c3c5100c5440c05559440304c0544403030400400030400c0c8070b07000c44803d41c5071041046070004070040c901c03000010443c143e5606169034140f8002240505407010030f0380d80d0402c20611484001d65580b0903244002001082d0a01001820507495407000084e4500d0150131000e110300f0402207216502c2c030390240c800f115154800b0083c29841d045502c800154200516a80c120500848c40b401a04564a200b401c080105043c0f0000740c1001c204402144141c8000119a0b40d4200c02070002d085100d5001c1050208 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 555980251 1250 555979001 555979003
    0x703050a0206070806010f0e031516090816050f03030c1219050c03043b0a1a0d080a2708010b010f0f030f020f12070305090109170304050102120106030e 67
    0x2005102d0340071304c1003050801c0466a031210242e107842090b8103041c58000c40240101c0c2c6800d000390010704100041d0424002d0704140849081070452082d40d4bc2d04040351903010b96600d44804000c07805072030769208000e1101d864050604109200040d0440341002c070030702290791911440084010001100103403110402d000b142d07544407180881d081007407401121045c1196070703101c0c0e442617480701540c000c103007103002040380600d2203503d291a01d00b0201620303005e841011580252025825180750a40441d115151140d03400056000244a00d2012210707071103601007a484040141e00b00300000c0062140500360341040f440c1c441d102003155603900d05284c4698210396080a00c00e061050f0ba407004dc180701c1d40448902c0803104c6034a00440d8514102c6451f0002e4001c04051240900c0c012030034480000c245101c052180c1c045640611094407074007141400c0b075103440d0b0003804586a8410b4200449541c03401143c119102d107000518044403802e510110840030380211000a44441d541404120 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 555981501 1250 555980251 555980263
    0x50a060f030c0e060102031606060f090605030606041a030d181a16020607080f0a03060b03011a03090f010518060a02250609050714042012090f030703050a02 69
    0xd0050200d45500d420741d02c801004120328424a0301075524040024000d92007841a65143c02c0300c240c120280301c880f03181c103e0150405000700b103450081c8034400180e4001e82e0250008854000d400f41c41252511028080030788070f0341210100503001001034404a441c10018a90305035041c4ea180148540e0307207100481c41200781d5102080310608a0b00c54030501c1c14040c11500c0000280c80e40c40a5034031a84003207980b42c01090310180558001003504000380c4541360003080798607030039902000400d440b00c0420358070380800e00500342e2140e2802c840101402c1e0810040d600325008208403904214071404042c20344004072202c0c0d01d117000e0280c20410254007001140c0e00441c4040f0154140102d10100701c040c02c6c0c41c40c0f1050b071f002c0c0420031030030706011440e4408a00b0a40180545010b207484444c4d00d01c103424801400d9019038a0444000a050880c0780c00302001c910000700c1500d01010b42150701290400076114032403501540083c1a1280010801055040e10a84425803241d140320b4010341042 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 555982751 1250 555981501 555981509
    0x80609120a111f2307080106081305060c0d0e0a03120903030608030a02010e0d08060f0607150507090618030b0a05090708070305061005010c0317070e0d0606051f08040b0415090303050a06 82
    0x44e10681800000f82d00040c00c02c0c1901e03428a800909075a848503281c1215421440160142c0120703018004001048401040340544825050100001016040d030382c8071600c14001d00001c0e140c0c5081c4004819540004032802d0091a02286454443d02141e0440d44040b10f5007002d45e654030200d04003414103105411134050320b801c100500e442d040c404110f20121926509110f03c500150880c10840c01c9294841d0341c00c0103504c00c005500d0944030241c490070150203104c0119410449080410036034030035460681e9401000800d0340d442e22074104000e0000070f821145140a06480451300b03c03c00c012810003503004200410301c90500c04800440e540c0180c12660400c5001000400865000010040b400310449081c0fa195601c0c4038045900f8074121122a502c914001d652000380081604803078140c5000301c5865600b6070741e1682d5114000d888000400100b598a0700190114100821f80c0340e0060081c5400d8110844400700700c011648420002c5020030741d59424800c08021a1140070064 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 555984001 1250 555982751 555982811
    0x4020f131a12060d03050c0f0d09050a03051e010e03030c031f151808150915011214010609091406010f120f2307080609120a111f 57
    0x109040c0000e141c40d042000f0300440c000e881c5071221208040c491000c440078495000181e1301040c0400c42c0c4a610f91182149840020303c8400012406142c10f049080440340c2c0b0100400107250142c010507803000c11800c40010030b541e0341d0340d201301022081c00114800c00000402695a240c01d12040084a0302668480f06a800744401032003a14028203451071032880508040d118010103081c01090305c0000e4000601034000d410900300c81008514042c1c2c0260b2045080e115910b5070001c205035901400d10412001d40800b5008501280031003082c40401c200001c004150750791130307141e10010345804100442c1d4070071035000f0204a0840078006079024116031141c40d40300310f241c42c0500e00300840c0042c000d0301c586443c0c05403104005410517298400042e80074007078400703103c49020a4a500b118490751001e07019030320003d5540c000c0030580032469810240c03558201403e414007140c0c0c8000449607240144200800a092034200c054004280c24640001080c0c06500c0c003014109031100007546852 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 555985251 1250 555984001 555984007
    0x30a080a0b011d190b040501080603010c08010b0f0d150518090c1507061d1b030d0c140708030a0906030204050901050d050a0b0f16050c071404020f131a 67
    0x16a442502200f040300c02c0c2c1c42601140a8040003c1e5240045180050b048079078500006010550301c8003420895000340c031120416078801c0e0905084c0d070801e01c200c3d40014140d03001030044911400c042e014941c1460a041d044c20f194040c6001152105d180c040d40040b44404200841e1810503040c11940c0d0301450507282e54103041302829560f4044480d07862040025103036000c1d034000d051040d00c614503085101030160b1201168104c56050100d044e441107805070404104080b0361581c3c01101c4070343c0c050010322095031741d0041181d0a00c02403c2c1101c01710303841c001108003c0420401c2030040c100d0000903581c0c0e00d4000030064211900c40e4840f40916006020030022559610446070445106480715051100281703442401c0900b41d460040c02e03102c0010504c402c104001006511802030340c00b1088408808101c241c82ba4001c040074060241e0112000344445462128202800c100103400542400c00510902c42c0903004140303480300340302480000b044411800000001c103111703d240d0580c030b = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 555986501 1250 555985251 555985271
    0xc06020d0206010b03060d0c3f080313050a0c050a090e100b01140f03010905060603090c0f011407060f050a0203040c0605030417040e04020405010e070207030b09030912030a080a 78
    0x1440b00340500ca03982d00440d000c000941300c1d40f150301401c04d0f102d52180d611800c182e1141040100074408004030700d81070310080d849503072051800305801a007040c0c0c00075a901f401c2c17096541e8200c3d030f4801070040f400d450049840c0000210b00b00701d5504143d101c1c480026100742420140120bc4045510190b20340f0f05080f040d1500702d43c00300300d00200804444011032084d03020401039411280002c04141504000030f4988511260359002c0d60507201c0e09507051001c0c0d11840e041010900003901c800c12685c105014500e49458040c0328020311120604000c80e01d14182c0700360b00c070303e84c01182064a9994952460105001d00e607c0350a81c0311004400031800d60401d91914008060240101e1091100003c0807605000c82050054515140c1010701e80d500c1d41c941694100301e101c1038600324000c50909001141c00c001c5480c0283c2b0450180d80208401842d6403140036007680003400c0c0c1c240a0008208240036522404521180d0540c84802960f4500821030006c10b500e40081400c0c40703030b6113007640c03040f = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 555987751 1250 555986501 555986503
    0x80a0c14160506010e071803020622030215090102010b0d230111280309111306181b0c080415020c030a0506011809260705010e01090c06020d02 63
    0x4590580120103aa46801c507010140031480360559002c2c01d5441440c000003010344c01e0760300352403051461399100342d000c03039048042c4114100c9900000f0361068050107038100421028084c0f44100f03698024103050340360307aa004909405c07100c00000d944440001024065540c0900400150401c25a03039020030440c076481e02c0c000c20020017643e029240d11580019580c0009401030105100034592540d902e0b401c01c04454000e00e045201c1c20030007072030000c1c2040418000d214114141d5040317414201e0340140142080340e00c030380c1d41c0d4042c1c0d0f1051742c0f40030100304900440100d01c48699150750010300c0008514880c441004080d22082c20000c030401900005003181c1c0648049130202001d403811031901c5002641485840000c0d0f80d014860300e0000e0f420f004001a049048507080721150703c110f481c03000d540c0266004188042d080038008406000c0d800c0740410140c2d0340c10442d5050078186100c955401d425180591701001490b911980500d05102c8142c04d100c0041070540000c15a00c2c41d510800b0b = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 555989001 1250 555987751 555987767
    0x103180503180a03061406011d01350a05040203010e1f0b010c0b0a051008010c0507020631080c01080702060417040f0b13090603330e0c01080a0c 64
    0x440b4480c0c15010507402e01d912120420401303194012030602c0038000c0e0908141091508a40090001d6000320080c03041c40e42c031318038030144820180d40d69070500744428843d1248a80501c152114050903c40020084203241151340c0243d510304d0700454941800e0040500f91180c5484110b6aa080354265151030b80d20605004281102e0203804601074030240016625608805009450070a0322004c128030000c49a02580c8188010050780c80e2080e19150054203c074100640000494410024a405880d000d006062215521402e481c540c01710a00c00350884501c526403100250448502448600703014495a803a1642c00e103443d90040c60310501c0296200320241c806482944070305400f04048007924110350240200c40c540700d15944c0c1d6075840d817150307078480c524442ea4201602c0d40820207015038099001129040218082d480d1402e5500d0003801400342205a1440c8000a2a00422205d800f481842140b20000f8001065440c07001600050b03008151140c1549499041c0031310303603085080 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 555990251 1250 555989001 555989017
    0xc11041404150b0907030b1e01140705190f05060c070803040f050109021504060e090105010c0b2d0106021902031009150509011e020a0e040c030b15090103180503 71
    0x1000c0d108407000d15090b000f010751001580d00030540400f00905281c058222480d41c203015a0540d05000c140040f07a003104100590945c000740106440c41045000c1001820801d40188199402182e02d03040740300764030f6060001111411100d00d49002401800e0105641c41500000c9a92401e91250741d403481d1884020801001001d1516200091103001d40c0015242940034000100d00b164a5024400c035410510600d00010703102e8071603800c0c80c02e0002d071460490351706840740c030b900408a03907881c0400e110090101c1d03c0700710110030321500c4980c040820412140e0220050ba0107504248000703007440b000c003400e01265580b42441c0c0300181c400046d4072200c42d82c00e060000f504e203503070f18204580044580d101131040c0c2c10072091205408044d4004000040d1800030741002d203481e620315800b030380030750030003000071500c000d00e03586c100d04250704041c05c2c4048610780080c0105e03d81000440b03400350600320b01c0c00044041a256800d5030903200c0d541800601d0700c0d280c0394003400e96982558a20452030 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 555991501 1250 555990251 555990263
    0x1101170606030711010e06190f060e040822030309140103090302070e0702010204090e0c1002060408250605040b010e060d1509020a080706020312060d03020607200d0c11041404 77
    0x116404071341020b501900e2075a10070415101c1a00340752001a00403000d03040d581e03031701754a001190680840c20b4070070308003101ca11400103d10b0340e03600c0d1100f159a41082064640000c48042c038080d48005032080e01c80910700c41d40f00c1ca03c00d5401c282e801c20742c0c0c3c0c221034801ca040c986071004030000310f0740004e07581c0112540402e0303440340c595038004220702900a13580054a0982001b228443c000c02c0803030f6032002c2d80b1056980d80300344004448101d0b074a003400e0b180504001400c012500244041c485c803400c0441d0034100c2c2d002640a02d5685078100c03441220255101e1301c4c10001408a86d07000e8544680144049410b03101d03041d0070b503c440648150008803007903501e581d5581034046440b1a00101d004000c80002e5491003a0303104406501c070342c00141e43c142e07003c00304000998903142c1103a0003804a41c1590080809503914103040d104a600080c1d002c0005200020012282d6420044442004e806c2d40e52580b400c0300c103180c8407400311002440c0c0d030710540c140300da0303003c42041207211710f40d100b90042 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 555992751 1250 555991501 555991517
    0xa050c0709060e0a0f0f02210601170109022a030a1724270906060a140906040e0d0207060809150712020702060a081e2203030e0a11011706060307 64
    0x84c5c0c1020040c82c0f40d50107000041e0002c20103440782c01910740355a05004140e0312202041d5990401118903401860310040b0086c0500018081601b036a400307020021120f07106030000342c0d01c00b944140340c5140c0d40c0b46000c55038000240d480c2055405a0003800d000701096041c41e050030b12400030800010405400715807a0301c02400300c03c0741e0f5121291341000407541000000e1810320501400424681120800f9581c840c9001003103440c2840c0e11144201e921104100300320b0106442080141c3e5409000144d1142d115a4100a01e940510081c612842d0f41d40060045900d0050084d0210b0001050010103030002c107a075180d0082589033555000c0002c0c43c0c84084032100307500380b10090141010103500f1030303804142a88840d0b00704000602401c1c0d444e12451940ca80302004c03c8444c1400c030f85104201125596010b000c401c0c651044050314883e04000c601c007103070307111191314101e142e11003070f601e00c0c80b514100300070781d43c1044003c40400320003255140135203081c0010845621010b4458000c0011a03 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 555994001 1250 555992751 555992771
    0x6243201030f1409030a090b03060312030402190b040602010608030c190f050a030914040209100f0e0402071115040f0303050f120712060b13050904170a050c0709060e0a 74
    0x5a100f40790b10541007043d2030b120b081030304c0d02d44e999403c20b0304440007140700804041000200768043d0f910540340200208181e104078800c0d8a2250009070003203800c000480c0070304a40c0c2001e4448000504152040580c0f980c5c030f010402030030364216520040e450b0700100500d400c0c0e04002f14003841244520b80000e42084039a18000c1710100008001a046004410f8403008056110318140c0803540e4080c00794003040d106204101c00c0384240294954800c5c1100c0364090b01c00c0c0903101c3d0180d014024102200210f4140000c10140d82c48810102c0710203880c8a4156150b00c0c10143c040c920900f0140024280380c1040c59244c2c6100f0303240005024440041007444003444c40700304035180041d140c13086400904111802600b40461070b120380c0403040c10107801240c081080000e442491600ea4070708042280347c0414040c0000e0044d20030340301090480d002c1c84820310340784001c0130f000000d07a8505607038001c10340702941040c00940002c8196400c1c50420003c0381040860301da0032180038080000e4114403 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 555995251 1250 555994001 555994031
    0xe0607020f0d030e09010e01120b06010e060a0201023a020306150d05040203250504050405030717030103060b030c060703080a0920180601050708070624320103 70
    0x21a28181d0b4019200d4200030201030f4808410002d900d800d6501071101e98a40050702c0142c03030240034400d4200b40d441c00c450041040341c894650041c50606003aa4801030000102340f05900072041440542e40020f50a1411707449086800c020031075074032000704c000078007400c800c000c09024908291071680100100e0304540da0308000c00700da00b1040b03400316590a83e404d101001f402040b901a4440e0040d810304110f82c2144420740203000c60b0001042c1030180c244001c01004180261054840344010701c46180024450f00a0b11803103000c1058458172980341d440c2550a8030007600e00d69000303400002c0d0309075480c2c884509071880306900d0b06220344103903281254000101a1114085c6c0305080380ca034000301c0e01c0d401c40c0d101d910250059450301080c24450700b581c94051020380d03209001031400c22034030020a20080c05404241d01c600000b107810300102c100011030082d481c6401100c0c7d02d64400c1081443c00d1140b010a4a0366401074180d800e5601205000707400c89285006414951111070440980b10 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 555996501 1250 555995251 555995269
    0xf071b0617190504060e010b0d0b011a0f04030b100b040311040b0f030a0809030d2a02060f0a0f09060c1a09031209030a08011e0b0d0b0405070e040c0c02010e060702 72
    0x3242c10810840c9494100007010744821030031100d05500c0d040c290b191506181c0c07a09410300313400120136003241e46003403804100071280110012401c40d007440305079504038002004000541c01411240020309001d8681c40104e1700d41d82c0142c0c40030100300410800508800000344086200715400901e8150003404100c01680b0844d0381c0d40d150141c00c031450308008038000580390046055040760b15140c0c2514040e10342c00d0840c2c0c0c00d046440041140402d0501444402002c1c2c00d101400d40d5007880b000c0700c0380070401e402c1175203c0303804542c0c0890409495540104898018030480c50312942010880d00c0344002900071614100c003801c0c1000010f5862001001102c0800c0c111424461461801429640c0c0782d4000f84007074000104080c000103040d546404030400140600d09416180c14904504001503a00c941601c0380d107240c688040781015a11840750038400c0042c2d4590184030b0392045c0c1004100d90b1100d04501c280410b4806c0040980d901010074925011309650050360f40343c1c28000140014 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 555997751 1250 555996501 555996541
    0x70c110d1b140d051009080903030d06050f01080c0a03091e050a06140601081f12030e030601061110021308010612050105010801061202010e01030e030f071b0617 71
    0x8066403510345050030070403030384404580b00c80c10003442941c402010807411902681000c0c04a41c000c00f441d03604071210b9803000d4045417040f51254908417202d03000c203046400c0f02606c4100340365501802c11030350520401c4202900740c2480e114180e40f4150260810a0195074403150401d542c48030404108041c003180510386030482012010708095a01d411651a50404000c0300c0c6281004001c888040000200a004440503142c030600f40c0e50f02400f4803451004070701c0903541404640000203403c228202c50401c810301a6450494044045080c5450003406900040400c800c130070180258074008140c4c100c4a002c0d0310350241e501d0380000e00d0400292116040100b595203800b10014030f00700b107000100c0c031052245009000c140e98608641d400c0396410321903e034114580882d400010348c811804904290340c1414006034241065541d1443c60f008010300c81d0243c1c100003445424400103280c00f040c03444244d800351020071f040403401050014190004003400c3d000f04049660045c1c540c604035554 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 555999001 1250 555997751 555997763
    0x1f0306020301080f010b0d050309100909050412180501211d010c110a02061e070c030b100906050619110d180605090d0b19051005010806010503070c110d 67
    0x30350b11000f00507200c1e0003051004c24550b1810502c2000c9003440c80300c800145030460081c40c02d00702d600003800040840100d4503020000000d4020a001d130705031140500540c0590300c62110041c941c0005403002800c045441c0c0c0808c01c201041010ba81d00a9030300300b440700700c40c0500b608a0710021007075014000125007144152000314219000010542c03050f0a650850b60321310900100c600c039425250310541e80040d4001c0300401c8440c030307000848081c120043d03500c0c0e500b180c5401116124110f200290b608203d4464080c0d0040c0850901d8a0303003014003a02551000300501464540003e0240c400c4085244000c441c2000d5901c08601803918048120412001c0c0c82076203036030000040c82c298034080750314145001c000001c118684034038180d80f84803e021308103000d80c00003500c4240810000a1019461400100d03003420300211b80d001d501e005c0c101417803900c441c40c1e00300000944140f40c02001d50f81002418410021b0443d881214420820382082c0d002c0e030301446d0754001c42c9107d01c0128003d841 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 556000251 1250 555999001 555999007
    0x50906120906041e12031a120a03030b0604050604031202010e0a080406090e0705031f05220c020303061e040b0a080a0302010506150909130c0803120604050f1f030602 73
    0x103902010070001c0c03190788125507890038013034144202d0841e404a02d8000d409942c41c08a6040200d000b54050107000c4000420058810925000a40242d00c9484080b6841e000082c0c3d8008060701750180480001048a0306410142010045005401144030140014119101c440032180c000e6000e000c2c0c031010ba00030b032149419182000443c0d988540304500016501d9680041c00c544003182c414010903040d070740c15140d901c541d126440034020301070740600b60812040d00000c0d6651600881106d5940e200841c00c08030f022213038400c04071040008200305540080040000590300d4190303001081400c240b0a0340030510844c0442d0080420304000d40c1c018030b17100d0f40490450800600c03061709074400c3d80203100a5546405120b05200400341500784a8401d0244150f2842c01d8001158003288a4542003011172945e11200241807441d4880c0e505031b080000c8a610300c035458468158171500583d801d00032410308400031b2045a4009001600c10800c0700d41441c1070102c00641040156003092043d52 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 556001501 1250 556000251 556000261
    0x2040519180506010c0f051c02010c09090209010207180b03060a02071e020a12080f0f07050607210902010c020315091b090a11070609030302071101050310030305090612 74
    0x21264050141c03088400c81c01411801c20380d41401201d100354010380d01c45c1940c03003c81da1384240840c5620800c440703030b008401c0c0ca80351451800303189181c41c059542c00403d9031044080d016103038820940040709141c0c010000341000da60001081421a801d00b0582c0f603480186440d540001c10304080c83d180c0c1406590b00307201038005150054454a17024140c0841c03403c0400c0d401c0c06210303509600094126881c510b0422110b0440204803000601a4212600c0d2410012801d036881d4003165410f00541c002180c414103004003084090b0380901c1504021040c41d1041061700c0c00003101c161016113003900c4036014021a4030690f0101c010f554007400322003515030701070550303030030a141101c0849092065441d020610442416030100c0114050001140f90300d0f00d0000b41d001d00000700800c00e241c80c08000f80b5001407030758070802c428075000b42d0f00140c03202010302d00640d034800954a80e5040050a0090002c20207031b810105007280d030b05007800380c0d8480180010409a000f41946412400b0040741081 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 556002751 1250 556001501 556001539
    0x506010303090e0f060306010b03181204030605100803040302100302042312070608040209040302072d0f03081206011b0c170a150504031803080903060a230a020405 72
    0x140607035907103020b940c81c03582c2e4002c13008440580480d00260f1540c0f1020040000380170b100300941d000101000540c645174442d03100340e4500150074145081c6220006010024881144923260300f11607400000f0a907140b400c851142d40e40aa0701001c0d1245d481c4044105c00203000342c1c1114010a5000c0a0380d55960403000100b4000c0e2081e12058001c041c0c0c1e41030804088002326101007951b00c10b07254580303a03494a400f403216280b40184120b00b035210b400e5022854040443c82071011602c0500b8000008040b0710340d003a864402640f04111800d00c466041c00019100d20a84002d1100851180b03140e50740c8500403910b2041c01c0c240c5d5148111500082001d11500c089014141c4034018210b01d0450842c0040325a10403505a02914203502054009500c0f80281c00440c2c006000c0c1ca007036000d600c01034010449408650303004070750105c4001103924080c10305022151b84010f05090400441c0c541c56401603003880f07a0005603041e4401c040c0010b410006590544001d000040c0422070020f070030750200 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 556004001 1250 556002751 556002767
    0x60102060609070809100f021903060815151203071b0302011209033e0303060a1e0503010c0924050f090319050c03060c07080a0e180a15090e1e03070506010303 70
    0x700c40b1027007500340f01d90701406030082408403004000201003418001d8609400c0d840c0107008004015801c1d1102c0130145e40351100141c04058600155070707140786510b0001d140f1f000d003201c608002503401000b000076030b8005264601203e59044003142c1002d961508549400c0240301900148158411420300c9801c15020080c9905a145580c80d610b1401c050b032a03581d0000301c0383d640d8010031758038090002c0c502d001d10390034040ba1f02031005102c5c1521840064296000c010310034000940d124410803200a000b440b10500c0c1d0a03802014151800b40e140082845c4030b41007000c1582e24002803050309a41f410404521203503044007030f00803520794616000c6d44803101031aa1a102e48101d00c04552003001c80300c129240103901c01c1c8000d20b0004015402d540c3d4045100310250b00070100c03c00c0058000d010400c02c0e128468020b40065101c5802c6800450850745400903c0c11603e018074003406140c001880450000c1031809032a100c140c100404ca00d140700f03144005015004000002041540024003 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 556005251 1250 556004001 556004017
    0x10060303020d030f060b0901110313030609021804030e2404120302010606020304240909020309011407030e03041e080a0614010501170f1f0617060102060609070809100f02 75
    0x1407000513045100c03007059603010b004840ba03112040048421a40c06540f0107992928a00d055a041c0380e0140c0e5100c008014035131080e90034031b480700d510b04214580103031000700c070480007444940c00381843e8900a10300c001da03010031805464420500603074000d801011a0b103600500400640c0e4680340e0701014081814241c0880141d800e0031b00200380c0e54000b0050340c0c140d402c1002c1c0c00004800001d401c03420311200380001001e10041e01d80c0400d070b505040c00158458084e403000495000d041c00002e0b013070350710010050070815180021034010400e000c01103804990000741c41d600f010582c1d50982c0d543d42c010760f10025007445410310704010050160003401c494240c0d00803038555aa0f0718401503803040803011214100b01c4548001456059500600d80e13003210210700640d090240d08040c0c4a400c1d92550856800f1850220305c1c901c89007041a800ca0744201f0038030113028a420450082007040b5800f41c220000c1c45450000107254020411004a2046d4884000e1040510740428100250300c4545 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 556006501 1250 556005251 556005257
    0x9041a040c021605101e03020d05010902180f010c02090a06081f200301171002040b250209130303091505061008091b0607020406030321060e0106080910060303020d 72
    0x30300c920302002460040500360701c0f0102c0394010031b03c11100014803005d600d0f0903d5807c2c00480105000c0784140c50103840559001641d0341e81c2e1080c62582c140c3c80707040151180f0744400261034203980c0010140355445d81a1400082504c1d2484007030043c3c56242c005110902c11203c40c0040c5e90380343c0804001a16200c0ca04009800030608403000c0243c00b0b4100128840d010401004020b14201040300c082c07006078152445465910415130599019900100b17940ba4040f0f040104020052542440c2400344100c200c00c040c4a80e000c640c5203500182044c1111944c020060185030180e0825404103512a280340e0300030714030510240050038107031341d007900403d0603040c5284020300580409001d00b503298001c08000e03002c00f030204c581c2400706240a4000900340030810050310f441c09250f0180d813181e110420381402c0032011035510810f0344140400a400d00300200100c02d12400f1840c1911528a007030380d22070f82da40c146d451600e003600325901c642030f1401c0b400105266000c10100d9400b00969 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 556007751 1250 556006501 556006543
    0x181909021528021504030c031e031d0102030907030201050703021015031a0609061c080708030604113603190510090302070e180f0601080d0801060509041a040c02 71
    0x10101c0e130f50502911071683c000d0300c1c0004100464007400a000c0c01502c245003c44516070418226103844042ca81218042900c07407a5141424040400009010b2400b4008504620344031144c927590324201d10019051200024640301498428099080c606060140034012007041e40042042c2c60382503c0261654083d503041c145001c03028119103800f07034000510184c3c482d00c41c0e03002c0040d40b16050b0b0241c44a0b00b140800c2d000003842580180402c24094603e640d128a407030303001d11044c5c841c50088401d640c5010071030301007411031040d01c4003c00003100d040400350306502c0c0c01402c8000b012003030641e4948500111038078601d207079599440354030b88034001380e44540301594103104c10f45404800042c0982c000c01c5051180348501c0400551000084446d000d28540034001c05007803070f4100e92070b0310030343e041100140000c4204100d060b401002c207191100703140d0f1404200034074a00480b145d0b5480f46840b59001080d0320300c10034181c001c071000103004110340001e84001030741c0d5010016200c0704d80d000803 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 556009001 1250 556007751 556007827
    0x13060c020f0607031e0e0d0506040c060503010302032104030c08010911041e020903010b121e03040b030a1802031209010e091e130605151819090215 65
    0xe18241d400303c5034036031207001100503071910020700c2d414a200a041004030055101400384d50360044600342d1805000030b0011403e050509444454040d0000418800c04000410058600148081c100015484040000e40c088a0f104119100360b50000c1c1006850f0ba001241188040d071040c011b80303106408a81841032400c00b0305c42a01c40b01440c0d2008050b2144840660b19105e40003000c00200040c00001c00c0c1c03c0c01d800080c0000b032079070a512210340c0501d1040c03080e070110000d00403504043c48011814649030890b50881b5200041c9000501c50f201c2d44200d82190240d05502c604e01d600405071400c0411540c410307003d940000e80340b03d000901c02d400541e1141000e500c2e00d03000340034010241141000c0c03608020f4202c800503001c0c0741c0044021000e400402e5080c4180713801440304000c910317800d40b4000104420700c401c29020b501002140014410705103a4160400030038801c1803070220740302a0307034000101c101100c0c1c1000c44501c040000c20b64582c658400410024103054041682c41c0441 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 556010251 1250 556009001 556009009
    0xa0606020c03010e070b2a0d020d1d0f03100507020c1011070b130f0e060f06130509060414011707080303010b34030f02061303020a1713060c020f 64
    0x401000e840d8540041e081448000b000c00001c0c000c84840c440005805040d16687c1c084030014400d00c108650440e0702d42c80c000d66414040104811954509443c1c5886100902029160100d000c9840b94502140014890300c042c00107900408000d2000c12071480c1c441d10203515192003070040c80c411b003c540340784940e250144203501005401c80008044103070074010f191405500c0000e02c101c520580320000034003503100c048072502409a8100020304da0400e1418418500c514049003841903809001c1401503005140340d00003103500403540b8602c1c1d61511400300e00148032407461440e2255400001291003540c800303045c0c00d940d601c1400c5440b119903800605d5182e0100703004145007500d04104007440c002e2076248000d031270801c114245091f000d54103d481051b0b8134000c0100d0101d400b4614103151710b07405100465002d4044101d440520f10a075038003c2d140e0400b211300070141601c90035000071204400c0b040c0c0e820b005451681d1030071551166005001d5000a0784200d1003a0b41d01a052002410 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 556011501 1250 556010251 556010261
    0xa0c06090f180207080a0c120c0f06050421080114060408031204030203040b1c0621030302160c18050c090105040b07110a0f08070503030a1b1a0a0606020c0301 70
    0x420712040c1d07000c5034204910b60111050558080c51440e80034080103021492840042c07542e8a2582c8991442c40000c4c509080c5211500d14000706011503020b00380045000403901c00b5205600041c0014595114030f08030075280145a009e0045400700d01c000003102da0840d00b414183c0c1c1381d03000c051182c280c8520410a00380304501922000b90000c2c08802c9420300c19050240d0050b10900542e400c068803084041d03c2c07504840080181404c01b02e41410304d0110500c41d12010f41500d12060b150300e07501c0c0200605a190b203070001420994002000c02c444d5001200307140095a00c1452640d10b00d503180040d910000c182da41d0003c805e4949408106603068910440e510100107844403410280303000100046500540000d03200c42030342c62440340c290b039218000640508000100c5039402030600120324940141341d002980607038010813a01c0d025039000000150000c0b0741400207000c005031445c0c1030562081c5828410701c500302101c284450200d0a40141042c1c80b01c2d40c1c201c0b41803d01410415080c0c0b4 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 556012751 1250 556011501 556011509
    0x908010b03150414030d020415030c020304150903061406030609010c0804020108070507052a0906030304090207020607060e0318041e050c0915073528020a0c0609 71
    0x703031107000d540c000c01036080c80d40b070303400382c0103890503c80000c4034040303c0d04660203404200c1c101039001030148510f00c1a42c0c401070592505241c08c100d100400e00380a940d0348114043c5034030f00741250000c61960307881047d10b040a507030300c03810074412490400d5154803a00c8003602c4061190150030300245104905100360441c108483d41c485880751a00e400550b038105000e00280c04202040082c440420020400001c2000403030300c0e05070222181c40e180c181d8964034524003c1c400c8020380140003c0b40d03000010b272400c3c1e5440c28401a90707100c591000500c03a104511004007454282954000c40780008800b0b0300721046070106100e6607030100003c000131030f10160000c074116a80c00c0c0209440200590103542d015a2040c0b059240030341502c00034021480c4ca80f03a50410340341c00100441040005865911401075032210b5203038550360500c203200702c600a41c4d10320b00944c01c046103201e1800758000c8002c116114a076202c0e41c00ea041500000e44801183c076041d1803c4c50b5200c0002826807007421810215 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 556014001 1250 556012751 556012753
    0xc0b31050c220507050d1404051204030b150301061d0703060b09130f23160305060916020705090103140606060c030a11163f02090406060e0109020a0908010b03 70
    0xd0340ca491402c002070501070618400c02000b400714040c0c100300c900c2030120382e01080c01c622119241900d481464201d00740c1c41d100202c0d006000400010340e03080342c0740703400c1030310901c21070301e40e80900010a0041c90715901c0701c0c9691002403a5603581002b1001614020102c0b607609000080c1c550030700161602c58011540d030401d0840000b6105104e450b0700000815012403400324072406842034144094100340c0c00702000b100c040f404d021208009401d0340d0342c07418131810140300d64900f1078002034020324000c154440c08911056900795086c424051180545001403041d400c6585a04007030312080e018100b0046a4403545000c0340c41c030301e0326000b80e4a02c0403941d8001d510741269664100c40c80e0102031b00c0141e0a214680141103208003442290f40904014468828194803900c010b03d4860617128041c0000c1149040940410040080c0b40c4856501980c1c21b000f962554078281000b803403a64002c4501c000c40e4070010880174150340090040345550303583c8035519500c0da494242240c08011070241d00d = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 556015251 1250 556014001 556014049
    0x110f1506130b060c0d17160f0207081605030d03150519050a060f0f0306180203091501060201020d0e0304120f03050c030705010c090806070c0b31050c 66
    0x1180c603141d110041449010071010034003007180404100c0c150803000b40c258035078101c074840c41c016642c0483c45800d0014280c60300f110038104002039481004000b1103980811002c0880411210300810041c0d008056003011160720040c01c4840800307403c42030140e54441d0181c260b8446801d4800c0c001d094010f54840748011029152200300304100000400d4075070915600c0d800062142d035036403a508002c0180b500e50114100030200c00400340b010ba4051030060510b400403d0041030b001150044002c450008010307603a0300d0341031142e454407020180c0c1e4116034071010004034000f58190007038840654076420500c078051040005a840c3e009501640182c2c80350031860202040304000e2020100d030090030301e149440091000b0608640c40200280c0313941c0e445402c0705a115612122003801401e507a00500741c0b0303044c450380041041910f18009021203031000c02141e40c0e0301701501d401d01c1020340b079000c403140411341c1c4d02c0414004640b008240c40c81e0092105c1c0144038208225003510030045c140000b00 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 556016501 1250 556015251 556015261
    0x30b07110115050f010207080106120b0c04061e0302070b040507081e1221070513060c0503091e03070e010e0903030603101104051203030406050a022508090907110f15 73
    0x104004081032545c0c11482214000205d502c82845048043c02a42c40f407018010700c10304040180440242542064030300800040081c60307441440a80c0b0b0307555100b140c1031844107400003107019000d03150014040c0c4481d101800108100013400d041117464000944205041001135800442c0310a4403061b0305410901c040500301d0104030081141c0c0590280c55079221a00c45524480500d086a110011600006a0441a80000303281d10001c214601e004410100705698042e00e0340030f040303002d60180c010b00c500940030704091034010201c07840c0502244c0400381d5032a9280c0c2201d4080c8204480034000c20081030350ba11012040302d00c80d2201070f005021b072002c05c888140042000038010f0024a009010104a40c1e540c1c00000321001c4050008540700e0806041020481c0c101501b0031045038410040c0f0880f00783c0000c244003c2e02410b0320445d451003600c1c1401440c070700c03517043c0031542715000104016449810002500720300b00d204003240c0400014064a030360300d10600c943c0328a141503440000d8 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 556017751 1250 556016501 556016509
    0x121303080306040e25320a030210030b01030b030a0f03050c1009061406030a0b0114011202030a151208030a18020d0b161e031107050601030b0711011505 67
    0x7541100010748002500509501401d003000070107140f510400d0341c010b0404c0c00c000070802c0b640015120311507000c013071343e00941c03a00f0082544044030504070802c5d00070740d03268980c0c41c05643d8000b144c001d8102c5443c8086000c00800401c0103100a50201c1d14000b0440058200054100001030303020f500c4090159183e1025210754010300c814a21a11070502100e24685c4103004540c022440b4103408518403658615a00480000a002c80e010342c2c00445050f01044140c0c5015044416012128150100720b10049550300c3e0441d0382000c010b03000000b0301ca8100590707030000181020300c030101c0d21032507150003a2603c40d1358683c60103020600c0520101d4840e0701c1a610022900d41501408078441070250b001c21800a050b4105075801c4145004000381c070203202441d0142e0310b5841c6000b401030104000c804101c800c55045000030580d85900710160a24030384201e07185150448100d510b03560f960701c0d00300c50f4203500704c600000003584022100d80c002c3e81406100d0a0040c4025000c80060070b080501c = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 556019001 1250 556017751 556017757
    0x9061a0708161511071a15060c01180f02040e0708121b0d080406050105010e06041a040e1503011a01050d0b010221030f01050a08100f020706110c12130308 68
    0x30384190540b440d800c00702c01d400313101d800f40c0415085813440c4c80341141d05086000b204c00700c0d0000b140e00d4072042044511103442c525041f9404c400c40c4c105480c0d41c046070f0010300500b100702071a085285104000001c1c4140c220b41040011300c03c403000e2009100014400c0d499040354070590070190301c924600d90b030b020f1580c4064099404555500c42091404004651604130582030001c0854036030000c0c0b106120707850007a940506820709040803403000040c04a8540d1049100d00411300c90640c080d418810221001c44004100c186000d42140c01d041800340f0418929402d280d10a620b00010100c50340c820703c0401c540030704140c4503c0c0c1058507529411020342444d000850460003040c400d100004c00e143d50b03c50034229803404280d00d07850200ca030b4100303548060308124410b1000e5441040302d01e034001200c49400c40c01c80800715087d031145030050040d001d48040149440d0802c60560311205403c03024240111280044500c0b5115812800f2620700c00c0003100b81c40000490024070101d0214001 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 556020251 1250 556019001 556019003
    0x90a0902031203010b030f09010506010f1808060c0d0e06150f0f03030d06050103150b04061b0503160b06040b031c1103030a0501051206010b030a09030201090204050109061a070816 79
    0x650b00154020500c0400310781c0240c110350103003440401403141002642000035400310030880200114105680060b000801c0100c0c800100078626031050a00c3c80204190f034000c002080c115021403d00040282c0c00c0d030008141002c540746031030182511050000741c0713140038001c51103d910400ca0240305012512160540540e0803040308010000355880420041010304001c2d1800038026080000040a42c0c1c45d030401281c01240d201c6081c0724007054a411502290014109081c00c184000300d2610381c1402428054064040032030401861040c2e020341800c000d03c140045e03081681c840003004112043c2c0741c500c0303030182c2c001a084d245005680c0940e014810703150421080815480da51a45140d00440e40da403881030f250030042096041040c1c541c45142015409081c07030350304110441d106800003c250601c402e0326100a131040c58002e41c000c0c0d550540245c8240110360316030142501406d0304d40b04004044614541c454400c68401c1c09592480b0343c014940c1d480e00003c0c203040d003c10038402c80 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 556021501 1250 556020251 556020253
    0xd0915030b0a090e1009120c030216120b091c030c050405120703060b010c03051615020c0619020406020a06020306041d0106081b1f02070f0b0910090302090a090203 72
    0x152501d956803490000801840c9010707000c0340c5010281d02036818050940e804a06140c2444181d0380050300603061540710f000701380707011801400c0034103040345000d10100310704060010829011031074a00802e40801040c2c041c5100a141d03494286800790346140118040d14400382010300d403903209210341c01110300080b06240141c180342d1680c3c002540207030000890001c030b52161404104000e20b5000d00907541909003000c2c0d51924003518050007502c56400100700d1030301d2a104800411500245074240c0c9590050110740301c01c0c048414950341c0000761b07405603150021002000c15130918ac02184d00765405030303000e060b040e030896541d00083c1d04040c01c21039003d80c42e01c90702c154070b00003240e180181c00190400864000d10700060315040c040706020b4031350a01c05c182c0a03660306443e020f81540007480200d6000e224040b1001c0102d0903d2610f40041c840151000000a200e41036103018146d002d0f0f04035007001050f40d0791041a6400344081c88002c1d0011220303000142108040d510907544c20340054 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 556022751 1250 556021501 556021511
    0x203070303111309140c030709170a1a04030e0a12150b030d121a15030432060109150b0f041508040b24060f09030f0c120d091503 57
    0x14601000d00e0f05950000550550781d84103456980d81e800321000d40000d0117030718507803440c200114028101603550181451203c8a0140241da071807041003444200d68000600034403824002050141d1400142c40a0380010018034034424a86880681c04003101c3d4444500c1074040f2403a5100c10a0030442034003180d400380d03628982621924148040030403503550759038045020601e10b0180007140c04c182d82d45183d600d48403901e001103841d941541e200002105003000e4a95030345240043c128602d01c0d001c4041803044143c824248515410200c4804c2e20344825a00e2070780c0ca60010804942401e071602d8202e80172860200105903001c401810300d603000500c042e2070691144002d40039031400d80c50510024000c00c00700001d1110340d44910341c0040e2200d00d1800f45046560940c01d030b02562803403661154600080043c0c0200d4214121100c03010044c05075030b985255401601d4841c246641c103035008049036080c0c032442420203c1c8081c0a60355503110a410740b424017200b48011040c2d058050b0600d942c43c = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 556024001 1250 556022751 556022767
    0x60d0606080a21090b07030c02030a020a090606030c02120a08070c080319180209060915031204142b03091d09010c0f0206042d080306091501020307030311 68
    0x10b110144505001e0031041450460141d0440c40003d0610b504604004c0710040a01140440307a0489001ca605442d007030b0b10454007400000d0821b002650002e50050000000155031103c40e08003104131000c0d0b0310100a5500028400d03030302c031001780f240301403000010411a040d03117001d45c520310340201441c9492006ca400903a200407130786d0300035102c91001e2121600c0d09400030800b401201e4036140219000c048468507640842c0d003031500544141e1251800a00003070700828402c40d11004a1401001c07105d24440e50391049074079510500400940b242d00108a101a0901901707150641031804020300d00c0f860703442c4850b0021149200110100f254003a80051416070303040b410300c0301c281c4403000400d071030925007992821240a41031803424041c550310320120903600444e11503481a04860304940020321440058071880e42d01c0e04d4004164030310144481440110342c065446404240e40304c040700c0c0c03034070401d8020900030848810f0050703004000303a10000f807094018189001d80c0c00720b018200502 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 556025251 1250 556024001 556024003
    0xa03060c02250f0b07050a03120b06040f0509010506030f04060f0b0406090e0d0f052a0a0c03110f0a050415150f0801090209150c0304080d03060e070f0206060d060608 73
    0x140d410408101454844188541d040e12030b0b6100081c00031000b0146001d807291b5449480760354281000d024046000074a00c1c030004a80c0101e00309080c002c081e00d40ea9912032100245c040c1c2d10303020b00d9000b81c25070300c004510343c01c0102c00ca0340210301aa1914606a5076a40c030800584036a07940f00303091546801010340d8544442c0150005000c0c058008110036501c20f000a10f0030781070140041c20414407840b400e10290308802221060361458250840300b50344c0c8105500b400300040d05207100c0703104858060b4103001c2038280c42030680740306109050b0071460001c200701005520102d2594010410300302044a4038050780700e452144400364803000720950300c800312805039901400d108085558000c0c400300b5143c0c01000d490142031303401811401c204020011940b9031f01e1941c6040d00302c6900040e4194000410000c0d1002072a6907003c03104203101e00040200a800b20348611225000000049200c06002d54003110814115500a00e419a00c1e1070412103c80145981a00c0c1070399100302c0410b000070 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 556026501 1250 556025251 556025293
    0x1e04030b040b160c02060a030b060903060106050a0f050a0509041d01140115031b0f050417070611061902090d020a0311010e030a030e01050319020a030b010f0c020a03060c02 76
    0x2004030398006451601925810020f03454900080030088402d103040010b03a110415580701420f01c0c580058044001c3d0081030702c0384600e04903650303d8400c660002502a90090052648188030381d16101c5000411070140c43e103010708014800410b50a025620740b0b0b091591180c00107001e2044a1124400700300c00c1c01c1c0c00c40761985404002214500300501039106155000c050258442c5010415400070050443d90400140071a0040221100c038078184144100b064034060040701d01c0100c0c210a03205803030b41d5551518130031000407030300611b489402c03200007007080c51007000c200d04618550060240000025400a684694410101c103090000760b00d031640700c000610310a48290102c40403880001d00001c01c41131410f0b00c26400403002c0d00019a00c4038810400a800382010741d22602c845260300050071b00c505403110300e40d101044400b04a6815042241041800e032201080c1c05182981111082804400a0740000221404000141940d84075907041e51513031043e5039a003030302c400c421000c40b5 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 556027751 1250 556026501 556026503
    0x380606071b061b0503030109090f0804170d17070f120f0f052208091c030206040303061a070f06060e01030c080f0703020f09130507080f0606040603081e04030b04 71
    0x4281c1840501c0b035140c20990014240b02d40b0703400040c8600d034a5554903560f110500480c1035142c0c54010320001c100b94840524030990b844440103807202e445400740020f014083d02e4642e0244210507040c20041e000b810300d8032455a50711250005941d44100a50744003034645201030400c80442041013140601d4400c08600c5441040d008c20300300407803210001641c4014000c5842107410040031503880c2c0000358140803082d0f0140c1d00603243d410803c0010f40100401c64030300d0301c51100d004202c0800d603021071118492880b90724200500c644a0b101042c96440342031070711242590408c540c5020901007100b1041c41442814040380c49a15005155003008082e40100d0740d8420b20401401604414000c00703440034038040040c2500c518580000342e0012101c481d003801500558049810782006806a02c1841c2d0080102d5010399951000281d0b14003040c01414071038081c800101e00c0c1d502d45405244101c903080003e1500740591740100d240300415402d414607030b080041200000184109a080d4415 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 556029001 1250 556027751 556027793
    0x20f100306092a080403140f04091a03070512031e0306150f0f070501020d0c02100b0102070f03080c0f010507090e0702150c090406051c38060607 64
    0x1507180446001c190fa05000c0312228940c410782c560041d048501803000120016840c0c0a04140c4441c1010381d02c05c0a014205c5612100c0003a900500c0c009140017030007120ba03407080800400030b903042c40d080d0070407440444543c160803100c0104003034503010b041c0d41c0b68450301805513454954074640d6030418640d0b41003034600c17034240442000300610700891501c2800d0306480d00685460152010310102c0e200d0146111490341c004245102805002d40c19a40c040c008041d04000c401d83c04c100181d5614110350340c1100140c2040d2040c1c041c0e501c00704030f482c00c0b0380760070f90700c0c1010b2415655640043d401200715074140d84540b40000d4507081090180ba2b00940d541e40b185080c9900300809501581802413901c0b0955001d5106040c2c404440d80f00e1a038060f81c00340042c1d0f1641801c2d00001c0c00385c03010358271480d40b001d40328110350f05900c500c0364031462046c40303604107a143c1c16100c861010080e002106410122803091005048802401c000c640d0084004101510300206c03941e42e9030350380301d844108110b1 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 556030251 1250 556029001 556029011
    0x1306091d0c0d0b0a080f0f15060105031506121b04080303060d050f160f0603060501050304020d11151903090b070c060b2106060406084204030909090804050d020f1003 73
    0x50382d21b00340507203807280d68002d024101c4032142d2032041400880c0a00a42d04020002000406005a850114001d5407000341050faa07050480360b140f46e141d0050312211a95036060000c064160144c20860703045450385000b940c1560b44610410079402603801040d40c90b4011100c6011001c00f0034030030403400070012001d1540c150b003032054049072800030360400d80500d8600707d414400c9a8100e02504d9000341c3c1160b1649680e03180c0d00d80300c081c208040c0003150700b003240d070b00303606582007150000340030b41240c410940301b00784038880c00440075106010405400d403201900804c4009215296002c03070a4090503000c1703210301e01c80e0080380710030000740c00c8001510140c44140c50f020409101003608424226070500c001410a940305468400d00344400d400441c1c03491a5002c911140c2444030104a0380100706120099801c0d2030a01c0c5c44070449040300002e5000d10045103c5186100c1e0700300d40368024440d0b070305150030107091000d10b000103101607a20141103c1c0003400396540800c840c132803504d65078002c1131b = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 556031501 1250 556030251 556030273
    0x4060b06041203020105130b0621031b0c04050115111606050702090a0e1f1508010b030d08011a0c15040302101104030f170705031306091d0c0d0b0a08 66
    0x100f110b0007e0503500c0180c00c46888440450500c001c5039800c141c04441481e4601c403068854621780780003c0200159001c0030401d0f2141024a81a205600302e101c41542d20f40450041000205d500074010250b1741c10f582881025428802d11207401c1418102084a40c0002c003902d240150200503805000050700001d00c0c101103003170aa2840e0742010300d00c0e600340103012500f5001e44e01c583c02c001e4407507480c992040b01d54801000c1034001d03880342c800000c1c42c2c3c01460303158100e060203410302003210b6004c0c0c03252003681c040c29803044120300c0c12101d0f119598424180140c0c0314606650011040808601c101090030903c3d9505d00d42c0d160140c0d01c82d4000f030007080c00a24044042d14844090701c84c0c25907081c030042003c901c00c5005031028942c40290030048445240000d14030b4010000094101d200108080c0301303400014803c2815a0308580f01d680461399a050b00d4804009545121580101a03801041c00741e0701c0c1001038031400e1482c40c008103c0b1020758000c101340c403007242c0c00b609942e444a20148 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 556032751 1250 556031501 556031503
    0x6090a06061d070e030c190303031113140612130b01150815040905101e09020f012a060605150a0c030e0303210a0b010e010c02060304060b0604120302 66
    0x50003001a50340c003040064040e000815280d80040010041c00800d40d0007000e10ba4040c404000c003604000d208801c1f6140070b8414010f0300155020840c0400e2030500300700300e282600c0302500e520601000e4030085a9041403c1e10710a8242034140c0350300040d00344080d0b20102050103880c1d11501901d683c0303001d080c0003410000c254180607844450fa0342d43e040700b1074501c83e521020b01ca0388151726880c0000010400ea0120780203010903d80a8110b006501c0d0f41c000292864000c125002180c0b6021f54a898180e9050802c850b00b0044c000d504c01c00c0e2440c10b100e19405134859264240e0740c0c07c3c4030042c1403c402240c0350f06425151040700e03140c0d6240300522491400d0701201c6400150b0007c414240020110080c0012400c904040c090001841d4008103a640810031130300c0604085203440000c1102041b4968031010545d07038181a6801d180380300d616544541400d5100e0350301603642c0307200300b00190203204c9154409001900c1003034070f4400b41381c4c50b074441200500040200818410384030203142802 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 556034001 1250 556032751 556032761
    0x8091207020109170a1a010503030d1104030c03051510180c030e030d0b280b07080d0c0c1101110631050706180f0b0c010e0d090f0603020309061b0c06090a06 69
    0x40312042c86e02d2070040c0201c0c1c40000035030b00e1003030000e1300c0094000c41100c41501940201da000810401c1e010101008008000c5034480c0c00c540220050042911403420552002c4d4081c0150b0005110b0b0000340ca800301c029070860510030a5500300002da0030400c4454604690003510405c40341d41d110902a41a404c141c41d50602c5003245003207044511084c480f04050841442c850861003035000724a4030f061100040031035044c0000c01c04104000098040040d00408080d10151040c00002c0300b0038625500681182d83c0d0195100050030b0f4503500c00001003000d03104c12a80440740c1c1c1020302e040051b501110881c0980e980a41d00400680e4035011009011121111010b000c0c1903118404000e041161004402581c0600c0d0b00a80c80d600719440d80350041c61002841c40c800c0c03003615192600650062210302c19030b44164802d2890f06c1d11110181d050348010b650740c0c442c1c3da0003000044c080415800151140c511500e85503071600305042a40e52030004103aa440c203a5800c0600c05000308003030341c819 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 556035251 1250 556034001 556034033
    0x20114071a092b140d052403030c120c1204031a1f09020307030f021318020f07060e0c090108010509060709121b080106080a110108091207020109170a 66
    0x512043c022480507010010454101000c040c4000810b000561028550540e00803035401c80c2c08118501d091410121170883c913200e60034580008900b140c0c1241004001c540e04c1507140e030700a000700e00800c0b280c1da120342d104801c00d20150003481c405150300041fa00007000254061104510040c458036081960020090440803802d200c407200320b00421a00100301040780d0034030341d00507101e54071040298090301c041d20082c980e007440001c242000044040012003952220901c4c0d40c041420360180300d04034812650700050300b00050103024000360041d08000400c0c0c50101c15584001c1a94001c180780c0303242a000b070043c9944810410414110820130709505c94502d20301014201c0c41c00d4424036003441c18050143c6400c0c010401002c000c001014400700801044000700301640d0740741c80154540d04c41c00803c4480719500000011550322912000f406401808003030704064409554013912980030060882c103010514400041b0b00940c403c1128880c00030342c010303000c6580706d490184541141164 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 556036501 1250 556035251 556035283
    0xd020f0903011b1b060b0a090f0b10050d05090a02060a050c300310051306060305010b1305090702100203070c0317040b01170f030f0703140412020114071a09 69
    0x4070580c20340c00074030300710004d002568410402c101400c0c490060410701210a400012402d80002d01e85042d07882102000e04e82c0c1d90070030042107450108580050007042460010b1000d00003224000300700d6003d15000a4001c00710340218101d90301207801900114004804a40085014003a006050200c130101181c42c120003c1c182c41030010040307200e14a800180b11541e0048002081002d0034590b060181100910b02001c801020303000b20f01904a070701950300068105400003c01c9013540701a10b01c454070300c6185030f103494206014009884c80040090086209e05440350403c0003052004600079142540c0d50002d003400c0d818094007803d00c50b080310001c0743c1d650040102203503004064905403031a00707070014414a500070740d440c60040100312a000c94000010090701803402d400080c80003a11903145c0030390401d10b21525112a000d01e204200c0b07104041c400446c01980304401d602400300003003080c581416a03d84417801e54506100034071741c0c8141c510301402039981d01005002c0062440d51 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 556037751 1250 556036501 556036541
    0x9100506070605041b031407170706110304030816021503040f060b031212010e01050a0308030a0c0525051e071229010501031a0d02090a020d020f090301 67
    0x1408164248251400500241e54400c0413804016803007004502e50501005a0040c00f9200c0c103002081441110006001d480392110000306590180c8540101201c103030040c02d032861a0802c141d441080e22403106d00903000400000c400184c2401c007811009a4845980411002503c1841100300c43c12402c0c154ac05070034810000025100c00b5100303d80b5031300c08801720302071102c0c10109180060030110982d45504c04682c5800c0d201c820100c95040f5141c02c1701400381030b6070321014064581d14600001c0d2005504000007000031995412010014410340351991512580b15106111080c3c2500c0c40700c1003580d200c4220080c02410040e810710074030030103c51403102c502c40c1c100554607100c0380b0950b031a0819444c003030000e00040008035150781107032084d240d1401034890401d440c81c0109004103800300c0d02d802211141c0c0380e140d4003e10300d01e10300508050f080407840e07002c000c19440010310050702c040c0c00f000b60701c1c071811850010305184250056600e845d05011401c240c00e6450440740d01000007092 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 556039001 1250 556037751 556037759
    0x1906060306060b0301030b150604090c03020705120a050703110a1e050d11070e0a020c0102030403090e0906010b0a050c0f0f070f09050903040501050315030a0c060201051f0519030f030e0910 83
    0xd00710701e82000e504036404000b23018200c04100c09000e15445458198034002e13401c04851b4058008000242c82002034401c15048019070002c6070044040c00d0000860510400c0b0001e4056000002c11100b1201110602030b010354661400796051510b18201340d076441110420000f04010b451644035144c10501c139881300f52401c00f599084030740b051041484803007000c5122040154100c928540500b03009560705e240605018005e110b05116521070f0883c0c40001a40c10702e408030310a0306032840c11a00910300342c5845c00407511a00081d840405c0c0b4001e5a5281003400020090381407840381e40e0010785416450712000a022440650192540c1e44c101000c1000c400301c003104890035200242016030700d80e200e01d00821028420044816014403407101c5110901030000d03400742c11500b084d070003809035907a40e04001d1101c0380052082920403c0c900401e0005103080158100403032400020102c28a980c0e4540e64210903100b0340035404105548004c13181c0c0d003000c080c40c0e503100e000e444403e40650b1070 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 556040251 1250 556039001 556039013
    0xd0317060301050c0d0902010905090423010b031005091905010e0705121c11030406050304200f150f0f030a0b06071a040602190e0102060a1a0607051906060306060b030103 75
    0xe03021070400e100d1b6951680310071607004130f0400e805040045c194801f14078180c609454605200c4030038a0b00404540e40e4032103041014010314078400b1000d4064600083c582c00c41d400075203000b4008285d1801040c00307c0c1d03519104c500d8240c103040d0081d80003044c0814001821030404d4140d400c214050b188401494540031400241c0361036489183c004d010417003120074400c907a0b0034000b10700c040850000182c001030031a40100910b020381e014094008030030540740000f0808102c0382036855000100d0764010441c034a4002921030290001d00110781c0b4012500d4500459640900e8144603a00d801009024544409101c2c440002e541a00c015160101c41d8442503c24038210350400034018810780092704004154050352031340d02c84d00c0c8142114a11a01f0090203000c401405540144030714800110102d240740144000d2304000e040100c0410600c0060004071340c800f46042c8c80c0c6103d031070350090b8090101400700c500c0e203001c0c1d100010b6032400c0d45403950607036545a000c00d0400b0000d00c01407002c00e07030f = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 556041501 1250 556040251 556040257
    0x406080c031e0715050702040507030e3d090c0905040507230603010b0702040b0f061e121611060c0a030c0201061a0c011131050d0317060301050c 64
    0x821003000511490010b8002460040c0ca908070889590400002d40c4d65541c1000c040c0409620840d4107108a030b54201040381114048072580b455903000e0903882c1d42e6074054559001c6044c2c40010800d051b50400e01f000828040c5480303488080d50354511141090217281d0390700760040c0a00300da05000714101074a4043e03942c03080b4001c403c5645070030b85030403989980d00c49012202e0300000c0c3c103d940b80e603515401c101494200d040c1c20f80c06942002c2a10740d0529046107844079141c0d0007403d040c24120b5404041002c020315600800c0c1030101013241c0401d0001101c03070140b01d034580c090941000201c40000800c40a194040a20b196005000340303e04180001c1c10780c1c80400444c1760001c1c1840c68000100d004d00703900e5100403850510360480061000c8201c2c000e000c011141c070000e00080030102140c1c411403140c1c1da60401c10070640658a0341a0f10088141d4100340b5200020804131354883c000246041c1c040441200031407001c52100d0302903081c3c140340c61392101044008000c0c0b8909450042032502c = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 556042751 1250 556041501 556041523
    0x50c090d03080c04082e0c021207080403051c180608060111010207060509060612030f03071110230105010305040b01030222020711091b120705070212010b0406080c03 73
    0x150200041c101ca50f0301c4060310000d240410444000c2030303143c0009058080e500100394800380b0b0f00542d11185040500400980c1c250550041c18580304501a24002d40c100c1c000c1103d69000c02c000010204001b00240c03036800d14122514018110400c802a040070181881c501e860221440e04200c1ca58104070000e600c5142801e00100e080001c821250084c0304400004001c01c4c43c0800b4850080c600003103540c45078038103503400c40703020348000d0f840c1ea42ca00541e8515031020004000043e4424400c403014003c1400c10000c0b182e5241c01c02c01544103036445101c001d0b1540031050940e0311146890081300d80102420b080802c0b0605003a11660903000c41408041e010b00e0100240e04110041d01500b1a03804141ea1802c5454541e1442c0c0100361040ea03483c107901c100f00d1040410298a0f908410354420280d49a03650f2400e0744047c120b91504200a10300c80c1404001c0c00b80a000da1150f603003001c01c0718000f2000207100c8000400f0841200c0c0650014507096025944807a90b41d10300083e840c03610 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 556044001 1250 556042751 556042757
    0x1314010908031e0706020c0a02010210020f0301090e0f030d0b0a0e06130c200a05010608010e07140a03020a09021c0b01050702010809160f060306050102030315010f0c02040608030d050c090d03 84
    0x204141c0903644130710410800529040c030004001010038130100d1101e0009100740d00380c51101c0d80340c240c02700c20790080e03400310809014200300400c03071541d4952212505501c42d4041e1640008140c00c560b0540e005903103000480e42e2100b48140e031074644000010090094004e00d11000c6c10580c0c0800c03854064140e800c0041551040d103e0f00f0305004200c540b194405040f40c410150034041c2030f65448500c4040c044071290f00b0400046180c0e1418020f1440c2150740c1c20041c884203280084440c820306040502039040302c58100003001684a1080d040c0140002c4800903a6511401c002a03c0d20700b10b8203890010f4510740014078846030380c86011a500745809291403500c5845000842d81041c1106225035042e141400d40000c20311441680740d81150410303202005855526401a070300d0b844100e40d0780080c0203c0000001d00c1e5130244040105171036003440d00d10082c900031360200d0101c0b81e4a400040980d4408510301c0a054441c3c0a03450340482c0044019007460404030108100d034060761001424 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 556045251 1250 556044001 556044037
    0x305070c050a1818023114180a051f06080102030a2702030606040504031803050c1203091804050a290c09150c010e03131401090803 58
    0x6114041000c0c9019003030040059180d5076444002c20f5541e0300c603849038040c05081241c00c0e00c80e40850240f0b14410354018000b840d440ca400504035407000000c008401207076090140c0300492121501c20204c0769030300d6a42d41100b6081081144c1d0701810000131151a5621412805000404c0450076103041c20911004a035620000003450000c2c080740e4000c6101c43d131000c003c00c03607114415000401000940d00c04c084030350100d0513120010b12042c0310301a40503071200c801302c1d02d0360400d0350200e03a10034000d29100d402034040680c09a0340ca0156441510b00e030380014441044c624240541c96034a506800017140381103503c6d0041140310280c9101e040b009901080000e0a20400313200c240d800c55445071138001c40b514541030ba005c646000c448100c3c401c450000020307822600580466030324170002045541c0015030380e00364946c10f52149541d00303010354903800c0d40281800c0820290464a46407542d1940080c01e10724068045154075030f207581080711100301084922808412100781800d00c2c609040c1c = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 556046501 1250 556045251 556045253
    0x909050a020715091e031b0f020d050c0a0602150a0b120a08030f0a0b031009061517011b050d0f091a090c0f0a0509180303100f0501170103030507 64
    0x1000340503819015003544880b41c40d00040c0c0f64254054012035110380c0c03401c1038170100c1490001d581c2c00600c00003000304841c0b50713a0b40f109240203c154400e10344154503003000c00c1050742c04180d494049070f00894065100104822140c5000e48181002e0400340c402002c45d070304602095502c0e0705000d85449030440d965844030780543c0303610346a803007800c2c032040454015540da41b5000d641a801292205040542440402c1148030140a141089080180104001420301260800921030580e040316516504c680031882000d1908004c0c0c006c1c24030303606003030032400e0442289081d2044002c1c6403050b41082002c440c400c503001030036102400010800068091054500c00000b4480310802918007004ca0100407200749060200314446e0503000c09031a84c003800d86083c03044060310f10403110703132100e00920280454205007103410742c0100102c40d03010142000380200380c1550b005484000310b0a04100e0240708140040129600402c0c0c20700e0000030b5034042c501010340c1100d044c0401400c01500050001c = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 556047751 1250 556046501 556046521
    0xb0307050111010e010204060909060b0f070b0a0e0613020102070f05060a0c05030c01050112031d150705070e0a0902010f020d021b01030e010c080a0605010801080705010818070303030501051c03090905 88
    0x130340140350002c56171a501c54134041c1050041d40329400000d42407900128204140c80141d80c1c01c10828400e050404003075a03117104e0600001082d074842c855031200c2e1980110410403089000c0c2c1140c442e00404030300700340002810304141d41c00085008984003c1088692190022500341a81d00d2034500429421450001e0541c4192800c541c105d600784400401c0314110789101140c070510070303107810f04030b4183c103c1c10748a07500300306005550004020040c1d0084100240052048030f1080c401da41d40d49440b803480b5a2030f054141d1f828000783d580c840c0d200341196040803061241c4400ca0008004a01440e10002c0d0344001078845140c584a542000c40e41d164002c1e04440198401c030002400a01c02810004000420403910781c002c1c00d040c0080022154040e0308014140c545602c0601403141c1040c0054410b00d901a211940218090100c03840d0340c9424494500130718460783c0c02150700c1d450101044011220001e00c0a2a58000c505400c00203403c0400c26007121540107003c511aa6185081 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 556049001 1250 556047751 556047761
    0xb03070302280303082508010504020a05070f06020904060b0c06071805031e06130822180b0312030618100503010921030608060f040206090d06020a080a0b030705011101 74
    0x780c80c101c9450b00e01004045d0009103a51107070401500c030030b2038145502e110200c2c40c0c803604802c4000c030b12000010721803401c00e0b4000b01010752503070510620f031103a00c0d83e03900c0c045c00c00d804050321800d074003144100051074140544002003a00d030f445607081054100b0031301e403a0a0044d03c2c503000e0000e412810304881450f0b0007220001e242c028181c031a420001d51840003402841c5034900c001d805910f0002d4940d20b00c420104400e140c010345003c1c01d100208120750a07410724402e058444103640d10000a01140010403450407d50b07600001c03c030800440180b501c0c240511802c200000824403c005881d103401c12144103021688913140c0407600c0b140386456104425400581e015404e240070700d01440080d50408119141e4a1002c0c544168401412405c682c8035010300f5a442d0040000715000d1071010031070a810500040c0030505c2c09180b800000d00c1e62032015000c07100c0302d8010401c0581c0365041550194402d060410030300151241d1400291100d10310b014080c1444102555005001d00035401 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 556050251 1250 556049001 556049059
    0x23040c0b040812031902040602012c0a2012070303031803081504060308160215120c030c090d03110c04060e010b16060501090501031e050706030c0c05060c040512010b03070302 77
    0x5c119070351500c1d184000d0181220f00c2c1034842d42c00c860904d244c0b010010050301401c906c0310002a01d0b5100c401e949072510f02200800003d0000c00c02852070302c01c0d64606009860b0405101c1c010405285549006001da5070380b1114601c0200e40c2e8400580800c1c3c000241e581d103c1100c3d02d521030102c8410002070000c01c01174001070000c110110b400c40780603070840200e0040c1d5000700e0342000300c1c00f44243d0303a12191082001da0b0b2401c0c0080008284941d203603401442e00000c51441c01e904016040c004151a6446184154001140c81c0304003029104c080c85802540d103c02d4034140452030030603852481c104010311400245000020701e800182d2030280c4043c049503070096040c821941c0d51031454000c0c020a02040c4c5070b0001c11026103680700030784501d240425910230050140145800d005800070589680d0900600182c4d080305130000d4030a0200ca4851444490119140c9003014244a10580c0300c8044445581c50326407805150341c0d0020b9032100f00c95044802814941d1500e144034012202940 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 556051501 1250 556050251 556050301
    0x1122a0c0f080418060302030a020607051c03060e090604031e030b1215010e04050613021503100806060102030a170c0f04061d040b0d03110123040c0b04081203 70
    0x1e020410001d40784002c2003107400c1e094400750544807806515040b42e440e4070000f54141d014001140050030b0100280019074012416904d03e82503096040f28281c00c056a540006956006c051242c001c10950083d00308800301c1c001d000d01e241980d0043c041941c000c5468a0070621094400c0549200b501701c41c400940140491500022105216907204465101c90840909860000c5000c1450303040b81d03441560040010078640e1202483c41c01c285141e02c030142e0304464207103014104189da0a008501a40c4170352f070070b071200cac51410300d1203410100058242411500704116440045610041c0c103c10355140f801d161050352a80d074007140407841498145002d582003c1400a48140c000c10361464914140d410524000c1c88142007004a4510300746c01980000130103e00e0002c00c2c0f248080707031000c40300b5000010700501d81c151010324002d160b40c800d0064201540c20001004034104000d002082c81c0a013103410203041c50021515040e400d4040b02c25403101000141c1c00008215114002c0c1c84411 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 556052751 1250 556051501 556051523
    0x91c0804151d07080f060402010507140109081623030a141315080c03010b070f05010f0203011203020705060310050d080909151c020609011101020c06070e01122a0c 72
    0xd01c0e10783c0c03518824494040603000c4e004e80104c40600101e0258400d0f54165919490304160395507070140000c124008130125981c440b6040006902c00c801491511004c81031200061880d00c2d100e07644100161180002d090b440600b40c40011000040d11a040c0483c24800c0e44181311400011240c050903e070440e8283c140ca100007201e035880000729100700410382d0b400100b41d48480d40003445103c280f082c5510b50b1000c0080c103002c83e4440d00d05402417032040c000403800040301e2201806a8200f1f0f00082c4039030701a50342841c10140c0403c08880100002d40c0c810f8254a004c1440c4148480b491040c18052100c126407001040038400131a5040c1000a04c4c810750350070607a22805442000e06205805240310301c0306000014204c00d840e4101940c0101200d140400740c5004641002002c0c040c034440359000e01c80c15091040a0180500c075080319625902004040d00005080d16502d05201d0806450807170461040c0c0c40001040c031200a07840047d004008402004442821201201a186803210 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 556054001 1250 556052751 556052801
    0xc1b1a0709030b24010311211501021b2404141507021315050a0b0309010c0513060c03090e0a0b01110705091b0f040608091c080415 58
    0x706181e8140d9014040310401a038500d012600e51150681031504800302e05902c196031980701b6002410340c2ea4141c0c2002e414608490003485055a80b0001c411207001000b00f08424800250f0041e814090b0034802414100c5605c11304001000c0c1031134045001e11001400d1501e03034141200100e011900141c941030766030750303a440d602031450010103050f4030131645250300c107141c070b10040306650049400508018403030600903a140010281500b800c141068204000102d955480411100400322004426501e00d42a0220707070840e83c0d40340424080c440284050005510b000b030005050716810b0404003450311351406c09803151141540401002c4a0100410007110081c2d000410402c0e000e80b2031180460314a07801c0d503100c0609001d600d40003400a4006040c0d50055100ea444140b8a40021854849280d00b50070780d650080c1c0040000c2207443e402d200501400b000001ca006c58860082d0038600d41c20b1200400c806400340000e0910182d42041c0700007422a0761091250001c202c02c004100461 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 556055251 1250 556054001 556054007
    0x1905060726090a2411010618020d0f11030106050711060a11070f06020d0e040207052a060304020a0905090705100f020106080c060703050a020c0a12110102010c1b1a07 73
    0x12491203401045001e0000074100c84100c000414514404c4d522400c0c441c070700b0b130111010b131042001015659200d900000b4603441c15074440030000c2e404000540d0724003040600d8000d40782c0c844654920145030181c40d07440440c072079054030306564051900d80d54401071350a040303c0290a8000d61039002500080c1c0303a41040d044044481346c40c15003070564454030b0341c0b0070328210030402a20030384000d600309103840c082440c441c500660152000610060401c4915181c0030301e4401001e600301c1e1031607078504600000340b40e5203c100c0308083c0b08031102d600c3c40c40d01d40d011544020712445000c0001e525200411441001885814040d0002500e401341c0540108401031031000b0103071311180554a001004245614082070b03812856001403c02c038580745082e6400c5032280d000c2941c84003180074400541b940c030703031303498010800030f00b00c6c030440341d4001c0524100846100070050105040da89482c40307a404440d04000d900754008000b818040e440b881d0750420400101a0740000ba6180c0c504804000400ba0 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 556056501 1250 556055251 556055257
    0x17240403030c0f080a0c02030c0703030e09090a0807060203040f02030f0309100305010e0705030405070305070b041a030f010303110c0a0e0a0608070602101a060c0a030e1905060726 79
    0x4029607050244400d261400d40d640c5242108800c00145a20006000405141c01828580e801841140d19104055200034189207842c2c0080300010000095200645040d40c0c1882d0400e403480e01900f0b4035007144d55407626070301c00d80f0002091503402100060600c0a424498408140c000d8240c40d05d203152040120b03100d81c052000544515218603510031024424841e0754140c0303944514555154803500000e50707503a04010400c496074881c000340480003e8042c02444003d042c101107031078580d428100748100d980f01c007014a00701584213204200c0040000706080381102d400d403c090b500c540c1c5942940d410460715182c0307540c11040c1e56000007541c02c00021082c0c401c416003141001142c0d11410410780315150b0340f1461006030f0060028400010180c0e01c2000317500f15802601c10000710312404140d8580080002119a820081003802895041000b142070564100c8840030306400522111021103414052180502c0c0049850300c10880848810807407000321b580380380301c0034070002050f00542e4 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 556057751 1250 556056501 556056503
    0x30e1603021e0901090906020f0a0e090c0c1b01050409020f0304060605060403030906050c0307020a08031209060c07060f020d140907090504030e0d0219120b0c070c172404 75
    0x5070804000620b1001d072881901c0310840010301842d92a440d2031a460007a150681c810b49003039500304020b0324104c0410f0300411800c001070b01d94440c4400401c0c01c0184004000309044000f007810410f28403c1e10380414043e800620400140705c0000c110300040752140035641000c0c61152000540280800491014500c101e205080c02d01c1340b55141c0f424021a4011403100402044840c0c0050000b0390150700a4404403142d24202c030b00b00980f81c4c000525100c00f41d806020203810000e58000403402182e0044d038006a154000c00450405070f103840007a109240029111658403800354500d5104c540403154200403808092140c0900c0c680c031007090350f8099400194500c14400002aa00158080d0030300c926010340b10b003048814400240480255000c40c02c0341c0c02114801200e4000745074140031805401018050a80206145407080d4071480181c0081d03e00c2d0b006112031070005208003160300c2550504180004c0714020b241030315140401004039000040c0380e4070389140100d0302c402da52510803 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 556059001 1250 556057751 556057759
    0x306020d0e0f0f0319050f0a0e03100509120f070501051005190e070c020d02180a060806150d0503190309120302090a0e0603070909050a02012006070f030e160302 71
    0x2440c0001440d035030f2074000300d00740d501c0d03078105001c400c59444980210000703901803400c3ca90b107440402100620158040390b400f0002c0788100405445038241042107054010700d003d000c000c01d003003209072a607803424402204104054001003080340d07400030000b03550b50243c1c814001d014a092010883c0103101d46030241d0340c0a0022141c0b80300d112440120306004a4001003040c0d40a91118a01241c48a06041c2e003607070080fa090080000580300c0c0c070030b2181c020403641e0414555003840d56000c030545400da400708203642e00600070301814040c0c6e8030384440d40c4081101c4103000b4142518041c0e003980070b81d860074100d189a01612441e065056000120001d224a9403292042e90b0b07444141c2c22030041099203600011840c00038002c002d503230031006800130802401c03600d030070755941c1c0c090090302c0e5252400c8070303180c100020450440d600440710325242d04d00c9081c0316541c0c1c85851001607807000700402c0780301003280400013001802e00030307030148610111481c10f5503414030b12a8007615118030184012402 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 556060251 1250 556059001 556059013
    0x6040506040203062406090619031a0301020c0606060c0f1c081602031602010e060a1d0d0f03050d090b010b190306260c06030117010f0b0603060d03090306020d0e 71
    0x50f510941200982c01101c94000f1092170145034240102600446001c2d03820980c01c1004114041c0d024562400200260b0780106032824038011082c481405205001c1c00f0b68014880ca03104800c01081c1c855024100ba034400b500ca00c02c05009500d0681e403106802040d0052605070300d413452002441d02000003103502d03050081c0d1140140a00c1c21070340d2409000050304207003c1220f00320041000001c00c6401490007400610503080091901e60100e17141c41d022a10300c1d90b00e0701c035403954204194618a003c80f42c02d045c0384615140d640001c07400c19001802c0090000700c524503501243d220860054210103510700c1c560f110a28410142c0c084100402280f540070100040d00744070340128800c0c4c0f0481c6180b084201c43c5032400800e9110700c02090f07000303402403004668054950f03001550080108820442c4440344a00d0320a0844119140307442070142480041000c9480300b80c2200e41089003a0b54102c4038541340d040465503400780b600010040c030b000040740c1c052200290803070400c900800042d96a = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 556061501 1250 556060251 556060261
    0xb16050f16150615020d17072007061808061b25150515010e1909020d090b010e0f04120c02040c020102040812071203020318150103060b04090b0c0a0c050604050604020306 75
    0x8021601c011f010383c41c40e04010001c0c80d80c1d4810b460f001e80441d182855a48040f6003442c038903080c031364590017840c0010010025005841c805804007001803903003c024007180c2c10182007103034411480c05000f8407510000070307454404c010f07500282e203036108540011106040c1c1a2400040348001171a0043d0802e09110114001c520102d074a412408070507100e0030303940c1d01000c0030720500c08564101c0c904804040540010309148500040016042c4410009500049032030711000646040e000b40341680401c004000700401c41304891a080f54004911070084020402c0458001c507030754900a4102c0d081030a0b0118181e015000b0f07000b554030000c29140059144c60720450359004420001c1c1440c51002801e00310325000b5401180c2110000040c8210407000104440c07a0001c5c008010185406003001001400715611880c1d100741c400300d03030511508165840d406015040a0204026100e0025103c20745034007455258003142c0c2e005054924074030b003d08182d40c40c1c40007103405a009001e0b4100080d = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 556062751 1250 556061501 556061507
    0x1020c010203191505091017071707080304120c09140405060c16060902040b0d050a20010f110c19080d0f02030a030506010504120b16050f16150615020d 67
    0x404c04086041001302c146400700f00300b0780311000703441c020111070610804541c000c580380061107104000001000480c0c45c0644401e60408240700c50b002d190802c0000b4050340c0c0303002c0101c9048403040601500c83c01100d08242039000465481443c44a28100c1e0301e8019144005046108902507015910b9568510084030018841e0f0b40b00f4201d8580125007440000d11a640140f241c54000742c8009414403071800412400810a60281c0f02503000300e43c80410007040c011104200107004035541040101d40300085c00440700100e072a400e01c07110740008201d0040030014091528030003000e400810502c1c4801d0704050910b03001c1c2c1c14080c01896000d6032007a0003145500c5220110b070b4007d6140640ac190200d005050107414141045401c110014001b099044500c0c5014040c0340564107a080c1495030749450010144040d05003d0b041c4544200c0881002c19654070300310414903101034446501e44100c1071803460040b0700c0341901d082c0000c26948441005100c201c40d8503001c581304180303144016 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 556064001 1250 556062751 556062761
    0x20062106010e0312070f1a0c0c1006140433060311070305040302190305060a0c022517030715090b0106080903070f03021606030b19030c060e01020a0501020c01020319 73
    0x1201001340100000380c00035200090050881e0302440070490071001c446940f1070500c906544c9405803120102c4c19100c003c500703200f0701c00c150320052410424203180c0140c000d581507442c600c00344030b07596402ca441c1341032850743c1e2005400c503040304560a0b114010f2090920300c44860045100003441c00d40c818041c10b000100300c4600a4043d103d4030b040134959030822200782404100c516811700c0e004000000100200800760052000d06400720703456501d50402840c00900c0c2e4a0203201e03015a400320100601014080e00687c0c41886c0742049607074450600b14610312403404000d1401e0007480b9080b030041d000760b2140d03000e0347c0f080c0fa07040c0640e40c0e2080125100e60f01501d5411207074108000e00ca00043e0801c48400f041e5101e801a50071701c15100c0b10011203a0055071100002c40e0715080541e05514090001051000740700c80c0005000303056071154a075001c3c250044109000d841001c2851580c0208440304c0c1055218000f90340d1107007103001540c041e400c06d07107010b000c80000b55209440c01d0910702a03 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 556065251 1250 556064001 556064023
    0x120309010608011509020918041a0c090904080a110313030b0c030c2b090f02120d0203040e0618091b0f010f0c02041e0504020f0d20062106010e03 64
    0x3504c542031003007840003544a0144c55034407903c0b80c444445040c41072005144207601130044600781c040e00280c2e031042c80700700521490486108004012260b0340d08070f1900e03080750304a0340c84e03900d40d1041d180c00c2d40c0010310007411041d648404640d40120b070b00344000d600c05a0348111801c03481e07134072071443d420780c180010345464185010070f224141544c0051a481c0301480c00341c0101048411303100200e102200ca5850056940f0820040e2450560074042248500307001c0b02c100130b0812140c24a0300a4803030085002e8050300d08036140200714107980e00d05045a09560040e00368410382020140e00e542c681c02c0b164038044044c2040707410075680c070340040e07080a50309045e198102200d00c1c12004456036a004e0600700e9225554540900424100c164540c081203d500300c0040c1504042c010841038507000c151140c4540000c07080b100010340380c80046200d88242c9031107198001c002d84005400f601070710705c845648140b0942c0070711040822450b283c3c000d410070707201c40c44c501d15000c041c0740e240c0c4000c1030 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 556066501 1250 556065251 556065281
    0x27050409300c0b091009120207050901212901031703010b120907030611070314091008041a1312090303050318010204150206100906080c120f12030901060801 69
    0x415001080d00c050801c1e600610030304c142c0700081c245e0000141120310b501c2064034010812088640425010800480540703011150320a45615005003900c0c0398141d0031541800d00342d1030f900d0360200500071440c2910b01103800b400c035461105180a503590300e4402d200a40ea0b01c0700000144070072048610489041ea00c24a1307129241004031001070008000103412480644203d40c0000b01203a454843d4070440400450200e903142d0302c0d410001c00d0804442e1f00c0122070302c02009104000c0e0b0301c900b880001c45956007082105690360741018041c00801383c1001440181b000c0030000720350014900d05203041d124503805980904a044110b414005500004000c41c00400100b03c100002030452a29075074404005851700e502c2e14080b20080941e072080c40050381c0200180700340307154502e40d6000548440328081041a1170803c0c0c007981d4601840a140c0181d90300e5452031a0381c401480080c1002034400112400303011107046843d496030084417601d10f15442c146c130202d003480d010f024140c405100a4 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 556067751 1250 556066501 556066517
    0xc120a0504020120010c09060801140409052802010305090a11010305060607020a090203090c011110020f04031b061214010b0307051c051e0103032705040930 69
    0x820004024100500241d0500c2004055407032500311021a0074100c81001d400414004210307880130f4071105581e0011428010090300500102ca50b0130803020f88480106d502007004c42d01401c0030744c00c3c130109502d03040a542100201200c0c02c5400d041c8034544500c01e076000c019607610b46041c1502c41e0130380030b4014000f004010813158150f100380c100c9a00010700620551901421340d0020705006081d91200030038507004020001c402c2c809100c2a64686800c0c06c0450050b01d4404426454080307071411018105d60110f452441c101d40b980a941c082d551200045016102d210106090302245100fa100090000c05d405000000e003030107100444c806000e9502030690906205440680004040c20b040105c00e0080340c004076171841441c1c100a542c084001607a04107032091040d00034115000c407203518039000040000a602c98252030400c03034460350440c004140d00c02c40c2d0026036020350205500c41c2c2440c00c0745007444111110322600c401d02044a030a0f00c0781076030300a03140320584484840490540 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 556069001 1250 556067751 556067761
    0x60604051312030b030114010e0106050f030c030a06180e121c050c120f01080d02010908030f060d05070b0a09080d1709160e071121090609031905060c12 67
    0x50034411441c0059803d0100c3d1044945020034211f0321564203418401c0c2820f40108200003607030300c400d4094841882c10904d00104c60107000c00503c030251022845550000001d07102c3c104507070184015000c90f0716040f07040c281d0325919a0180070321800c0041c3c43c0c040c5480c2c0f69103e00c0390004a400c22a4080c800031200780240030114028040240136001d0300e10108000d1511134510b00402d403041c038161a04000c194105400c00d440c1c0440d035501070056a00d00f01d00c4030045000b520035030340e00c130b11218540c02640d81c1e820042810300c0b1034140c00400382d100e161300c080b50400068001d01500c1c0925501c0d4034217155980540c40d0b8821031007000c88045a889a0f0310b034180080c1c0c0f80304551008145d42100d56420110400c1240b00209a0000607030b58a520244210982d2000030f03800504069001071800c2102240d4681400e210864180900d4000044030492078451300191250303100d008003a612541c1c0492148815041c56082c00c80c2d05024500003d4400315043c41955103903090904400d00c0c9a5903 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 556070251 1250 556069001 556069013
    0x1506080f0f0415020703020102090406030506011a030f01150e1e10180b07030c080708190503040b0f07020f01290102060403020a03050d0608031602040e070803070611040e090706020606040513 84
    0x171a140075070865408000380c030700c5c50310755001c2c4400940c82280140020b41c500312440b42d804041d907541d4001c540d410400d01030040c00302d01200341502d512944014100301c180205460201c9050011500034800404003401c92404c5040c4408415054036900440118014111203d03684272059070841c0e00514814801000b01c60090510360740300e4108040070700c1d0292204a0790390091481141c14110002d40032034002d41614119494a109041207070550403d0366564884003401040040e04140310710028168503c20403011445400040c020090f0054181001607003003003a50622100c062101d10300c518070751000440c1d0b40f00c2c0e50164041c046807011690111016484501005030040d11000007040c003800034402809448a006084080e144446c03061000f5a081c00c0d070440d4094101310010004e48101004440038164842c80c001220120092046018061030b08884d90308030300c2c039003084004103000072814141c0d907054003115510341d1460b003004241c0fa0100c40500503001c50030005000070702 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 556071501 1250 556070251 556070257
    0x204180b18030702031614040605061c1113080d0f050307080c0904050705030a24030f0204060f030b0103050714013203131b03080307121506080f0f041502 68
    0x7600c001501d140c110a074002a00d00501a002600d0160018a0400c000741d00321040700c4809005440c2401940d1812000070b4450080d9040c2c60220014800c02008001e0640e020b264181401d00410361a641a0604480b262003c3d000f1003071148a032410a0190300d02802512840c00415a0b5243c0756039614941114218405400641105014070004949130303254051988191034941e03d041d10791801c0380c4e42009840444000300100d86510b51200d588036808039245060301c1d040810301c0307082010362012030001c08030303035020742a2048880004810401100355103412280100116990561244507074070b0800d0001c00420701281451861441d0042c40d1544100350700040e40da0466400681000380e84103500445150394003182468070341041000c0c51110780007401c20384c02c055103a50300350350701c00c8007600c00036100078180055000c5851212403136405c8264192010303254845641d5440c8800342940742d041c0e80410000e1000d80000ba640300c0740c003000d03038400c0d0307001540c9010780030300141424002d40c = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 556072751 1250 556071501 556071541
    0xf0403020d08070218091903121e020304050105011707050307170a060e0c010314190908071a0708070f080402010305180102190219030914040b030a030c0204180b 71
    0x1d1420f00658025a8800f43c507003401c624140c0d008409032070601c090302d04050011007503000c140004540c1c031000c07a9000104c4180c0d0b8000d82c10008041441d01071424079100c00c040c001040034000410401005810740061703049480411915240b402c04120035074440e03283e4040c841c1c06900c0030004101e220800e24106100800040540355003103181d8640c4401d03030300170740300741c100540c000341d9040e80c99681885000b0305041d91203918112401c060450401c00c46014500d1205c00c1e444210040922030094120b480039607102c9a103405a03050301c0c4021040410456800001c90500e1000920141c050b0b205c0000c48101507858014641e00e540c010340081c080942121001c03003541c0c040108818091005081c01080b081c012520140000002071070200c04c3c1e840352940c00c00d245503000000b80c00049a0040d80c2d01d01d8001100e4654003000300b80244410b68100d82d00d0b1044d510304c5814190888031050446000350340c24412000c200e02100104414840014110b001000000341103a9060514003100e07 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 556074001 1250 556072751 556072763
    0xe1308090d080a020c090c0a0912141b01080109141303020c2e03020412120c060c03020c0f122205090106090807050405061012060504050108030a030e030f0403020d 72
    0x54001da485070602c5402859540c070241c1d001028011a916041c0121980808184056898100241300c0204009524416441e4400345801c1d403004000782800c8115000c1282c1085545c1070740d2810408091031002c0503034502040d204000454400094004c003082607180245080590300c842d00740c00c4240c0e071081000e070f08501800b600b2400e595201074640320148583d41e14030141c04502c2d0504508400f0b11040c0005041c41080204071030102020001e0106070031241128460a4064099412816005004201c3e40c6000c0b20444916015406040e5013540b000440c1c01111100394100d54031000d03903242c440350701700034820044040c17405c030429080710300d80b60200510581c0da003020641120007a0801004500c90190510001c0d0082046000424007164140f10318102003000c030301400306e100392590800490301500300410b83c80780c06ca0801481d024200300500c1d039640790815102d40184201c000002d0800b42c8a650608001055440c25901175074410700e0315103581d007005100080408200e641d = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 556075251 1250 556074001 556074019
    0x908090f041508010c080f0105030a0f0314030f04050c03070e15030c0409050a0b0702011e050c13081b0306060a0e132108010b0705060c0a020a060e0d090e130809 71
    0x504503103040e4030b030040110000101d44440f05540282c030392400149288050b0065100400c1296800102d4010b031680000240003100084c4c201100e04a41c071076103420340f13000b00205014001242e420550720490040b800c3c1c50301c07151980101925807503a403090703036040010040030a030348128883c00b40e224020000c007101c0842e4241c0d404101034450072101580c00c0d4102d17062000501c90703050440c0380d000015100802c40180007680c1c4c62400d88481d01c4142c119036540c3c0010300b200342d90904407038034007001c00280502c450341d9105056503620000d06410107034410380b01018442c02c1c000703149030082c0801040880458282540600c00c07000051204c1009140500160301249083c004184051014180f007614205540d0000d0802e0350107900c041d181c2d503c20001040410000b042040d00404003070900e80d070781c0109100803441c12010b140c001d05001d140000b00c0b5420040001c500e140d0143e251100c240340c9035510405e8400a500301c5010444010700e0141d140090003c10003060901070041c02608 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 556076501 1250 556075251 556075271
    0x6120a0b0c0901091205190201030605121f1116033b060301030203060f09011d0304090b01030b0d0303051e090d030f020c030a030e0a02032b02010908090f04 69
    0xd0014400c0d1446400880001220301c0e165a01505060140c0081100c12503c035001d0343d5445e0f0307280400403030300300314804010142c1d045a1280e04200020031004189082243c00c00d11141c1d250301d00d511590305054804d06685080400c0d5002d21001c000620001034100003542000300c09513080b80400f00c00304200ca031480c2030240c80350394100110419004550500200003800c0424031501d010b40c0c4d07446461705100400c0180e0340003e800d5444240c541c601030035074460b090034a01404a1400300d8500c043c00ba503410803e8034000020f0130440f00e005206102c8242104015030485183c4602650443f000c840b000022078029005540c0090010b042c25040c2600c3d44016201014140c032010082c0d00304002d0000c4240e458007d4008090306518114681600a0300c3c2e1690b922840c61400b06142e120800318406010500842200540203000d40d003d003074410b0b5400f00f002800b02c03d056491182c102042810510512070164110340c41101c1515210b2540c08000d66000d120103a1648540c0342c40d880c0c4 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 556077751 1250 556076501 556076513
    0x601032306062a0c040504021e0a08100f052d07091802091e061603090b121f270b03011d070501030515010305070c050601080d08070309030806120a 65
    0x801040004003004010840fa5802281400703c0c820003148101d040400b4840541d407036100c0185490159180c0350b043c1a107480c003241d01c551140e0310864136400b41100541102003260801005464008020003280d0b0381c040115140c4014071500440210b1880d02c0d600340a84150003442e0003007900c0c1006009244d43e1200d08042c5241401c2a0341c18540108034545c803810400000c104980c007050211810040c07043c0481c00354065406031040480c090450131040c18002c50304800a07141615810340e5403204641d042041000a4030740c10103042c0491440301d0031065501076002a14402204518048181095090320350509140700729600e560b101e03458280d41d000d01c10400078401140801001c06140304e8500e0410a5a6000f941070604020030486800300d81c0401d6100c000090030002031a46961400306c5841d0520701d402400d074410800045074414000070381d0702c240c9003d40e581c9500365481c440110143e03034059100901140e02500469040c0c81c3c40a145100803000c0c030110392182c40d46032906 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 556079001 1250 556077751 556077787
    0x909151512081b010e250504020d1505010807021c030b090414010b15040509220c080c010c0503030403030e030903070f140111070315110705010212060103230606 71
    0x1112240301c0014410f00081503044025030002c4040c008100e8003030849aa1501c0d00607100d001880c0d0840007000c104032401000344603000c0e1101400464031400030308680001800707844c185644d0010070006c0091158421000c0b5845094280d014140066034a482011980c128028040c140354640c100e0311480d8880c10383c8280302d18014002000181c0551080c50f08490b45075520b240100c0140d0401c0c070804440608a5045410030b86c1c5100c05030351030b41e0310807944020048500c084c0c0c80c1c0e0343d403000701032100350320140c015140e4900076a03201d12940801540d190300480d030002c000c0e0b00148001000309019602003124034000905482c5070091a10009007000c42580080060b19400b160910000d030880c1328401024400782401020500302d480300c181e40d6801403100030f048000481130703c0001412a04002004108150000c1d155406071900c00e01070b400aa20b01000b00d003405000483d507600c40c1c040c10146400e0b124001c89160b04144060140d28001890503800500404c061070028a0211031 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 556080251 1250 556079001 556079003
    0x12210c0702181e0415060b04140103060e27010c0908011b1e0201022b0c030b090c0f070203070303020c03060916090207061506020105100909151512 65
    0x6400c0d6108454410030009181d0602a007003520008002c02c02d80120030300040c6480c1d5a0801010302d00d903510710f055030030700c203034110300103075450a180c1d0014280075070750080c0c0306803550701d0074030448580d1032001181142c51903c5012000c0d1001e1000c1043c40080c00382c00c65240d98054011186084002081030035102c02921540000c3c090350400c02002d1803e100e001d880c81401d0100c4c10f114140300d40000c10f0403580c0841c4208000c0c21433a00c41c030030f5000358115017014554840310244241910f41000c100e0315043e1030041120f0610031001d16940c40781c4110044098010100c20007074880e0310100b142c503001802c005100b040708014940c0076035400c200c0c101c0103500c20341c02000e507684c00348281410624040c15203000c0303502c00c2e4040c80c034680583c000e11064500301030005803543d10034203200300034080500103840c19400c0045c005c210b036581900000d201701c80d80715008441c5661180150308a5803806800b51698542d54401050340d940e0b0782200d172501000380001100292241c40310400c034241500 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 556081501 1250 556080251 556080271
    0x60f02130e01050406090603050a030315030b0f10081c080907051201051e15010c150203040b010f0b1206060703030e0f0f120403110f010302040906090209030106080106081221 77
    0x7004010602e800d00400d406050f80120074400207180d542c4940d80c4446501c0d006042c10340f1602112000d038136640c412001190080340783c1c003040c1810000e0343c1c2e01c44e40695000000c42040c0741c0200d4807920008141c0c01d00c0713245808420010081d003800b1a0050805042d01f6458040e4400c0054680d69190000c0b80c141c2d41440001044d040c000449082030a481224007143d81c04501001a0191208820100b4850030308040c2e00183c00340c941403c2d15001039042080180c0702105101c140010044032906a5103000300301e02c121070f203034611400d15008100b107002c040c0c550000000c47d141000009010810701c07034140414101e03d00140141460820760b40640e1560010110503043c007c200030f000301c4090202d0340310740b8050640d21230740350307510811189a0289054000f02d0100364071075411940101341c5440100b08441c0ca8000a50195000e411040e08c01d60a1407404a400781041c4544000ca49422000305515039003081c0c0b00c6270f0b541005086800740b204e4143e2102c8481181c844445c0300d005a24 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 556082751 1250 556081501 556081529
    0x90d030207050414130b060a0b070308090d020619150909080c060708060907030c0e03030a02010b120102030121030e03011505011b03051b0f0a141c0c060f0213 70
    0xb400380b2040350b13524110070750328109010a11600559a11032012142d40107110600f403907482c0702c04918404601c3e440180c0d85800040c1110174140c0c0b00001c0380c0220103040a80b10290320300b0408990b1218255452403461b0b40e0551074140c108220791103180901180741d030a0303a0195440c48007008880510741c0c1079a42040004584c100d030102400f0360341d80080c0e1030070860101c2c00e00318081460400002c0002c02410303a2044c003514224001c10408102402c02000c5075968005000f00034040d2100d5a4118054040010461090034042c02668140d03644110000c0c0a8110003410f415030320002003090302803180000860129480038000c3c002a403000d010403e030902d140c04001130069240f24061481340e10103aa051000950140c126104007000603204020409040641410022500541c200501c603001e0090304008107204482ca00403552401d447d40e40203244500c10b9041c2003010300e0b00000300c41e4a0b12a001500b03a03406665542c2d1000c0005050002081850140c90001e80003082019455 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 556084001 1250 556082751 556082759
    0x10e0f0a03020d0f12020307080d050c072f0906090a0504080c062502150a2004080a0308101d0a09080c0c03011505061e070803040807030f03050c070b0c090d030207 72
    0x5d550f000c0e5610218401103260811030b0f00c5045803805001e900564840e20340f03011030341200c20b010542d24080d40220744040303850150403a003034640000b904501c48640001d18034900919107640498403498015145400d10381d201c402030001864010b00443c0c000a05025012070018204602c130f1003140000500901c0346103483c1c800d1100c255200031001194041c0401002c0c0101507115a038011000b10400f00f10001c024244070b07540407104a100c1e804c624041000140002e001500e803c80501a44413007040e500c540020f00814401d6008090020001018403034214602c541000c4c0d100409550019115515549400280c1e015446a480f2540311000d607100c1c0b0b01d000c1c4a4000c0015150115840c3c05107010045003007401018256000090398840b02040107030000c04942d0a036500c43c03262903607480c0074a04103c06800003681540011200191107403014043c0c45480e000c0d4840340100c50600c007641d6143c030384c4940c0084c00f003080c41d20180034808194648288100f8442d00c40d4010b071080c0c0d410 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 556085251 1250 556084001 556084013
    0x1009050c09160e0609060d0501180b1e032b020c1e06030406020c0304061214040201090311030a020a14120c0901062706050714010b010e0f0a03020d0f 66
    0x200d10315051044444005200c4803502c0d000c031010b50201d250a240401064040c002200c0340a12400d86030001c1d400560b031110401c2c5684550305036040030700e0724004113014003490821203001c0c00429070044600d1200040c00360310758915850103032008003141d0040043c540c1150f10600d110b4140703240b03140351413007001109805104c0c074200c00c041a0348034102e0704802c00e490062200da4071469801028000301190611401d50110390a52681c90200c9556075600e9000a003034406158160403070500e07158100a50030030700030038076000e160160b49401200d420764981062911848070201d91500c10082c03403070f00584803110064018000d15003200d44014404007813000700c4119000c80320941e04031100794806541e031110200d040d00d2191804003065550302041a40010042d85000081d028803000022001d030f00c83d00420340ba5100b4047c942800107100d46c02402e0390001040c10f40030642e20b111000080c1808418070b461580010700194400d075030794011840a02d00000d040e540c4102c0c0d000d81d00300340700c5 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 556086501 1250 556085251 556085263
    0x61407150606030507020d0f0e0f0603010608090601060c020102032506060311040b01030e12090a0e090307030f081e060d140a050c0307030c0504021c1b020c0a12120908100905 77
    0x31450020304047c050f40c21005144414250189040c0107800300244480d07140c7c424030034168040a4092a56944c44e1480a0311002c0c1c101c07008081441010004244030340315054108285034103800071400c01046400e04644803480c820f0340032406004d51021300102d00030340103001c000c3d03018241503401c5548d00030910044c0c40074024082d040c50f0170000d000c10106000250342c00744083e0340803003903165410b031400a254004140d004030540e10504003030004122001c002800782d54440e480702c030000e03a45480b0680c1c03211022510440d01040b280c00b03030311700c07681c185007019400a401806404034400ea41c1d40c04aa40d2003c02c1c260456910609268042100804c51103201e100110010b00d55203147d40d444121900d52405150700954010030b103244c8480072501c03070f00b01511684800740b2001c031400840b5100c1c01c8021240c00c006103c2c031202710070700d0f0900106c0c02c07054840c080e40d5002446032a44502884108204405081081c050400211181c0c01e004581c0c400b003019801090f00d02d5a8181540b03005 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 556087751 1250 556086501 556086511
    0xe0606040e0c090c0714010516080c09150405062703030705030a1809051609140d060207020a0308030f090105011a03070f0306051207030b010906050a0614071506060305 74
    0x191800c240701c101a1000580c074204188215001031056484d4035040c40c45025040004220030501d040c10711149206400ca01d104028142041c40c40607c4080c1c00c60380003109403180c0d14421401c01288900341400301d1003000502e40642018503280d80e03403000c1031140e0303c18403904d00c52b5441054103459540004076030719403009040b802541032569640303d158981c45200c0154050200000d10f0807940c200115810009202c8210708114a1908403541d6101050451074140012500c810124a0b1064241147c064500242c0340d400c0852090361114001d502038a81643d005100e10310000014400700001c510500141b202c0194504200c044d850a503801038001d0314252105901e41381c80510000280c0b82e0101d600d1604105900d01c8000560040010307400082e04131000d20600d84919000003410011240f0a8003503082c0c0381e1303a8000700c404840d02400b40c00d44c840c4407154200507161280b075070000300c0c04007001c2c01440c103040d560315401446640b60706c0210141c1c8406e8100800c030b40510616904c4 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 556089001 1250 556087751 556087759
    0xc11010c080610090503150118090c12023007080102090303030604050c0c120a09060c0c05010302130f060c061b17071103070b010509070c05030a050313020d060e0606 73
    0x88801180c05880c0000051416015848030ba2410f1089449419240c0081c44042d042d60220341c100c0503080c00c803800c240036800300050481511780038946a0311540480581100c0007031551400c10035444440515180181d030b100c1000e0382001503808040c0c04009035503010313040606944014440c96030a0000a42c4590034507441880b001c542030b10080f080b00d60046045400003407079542e42e042c034082401901307042c0025120f00100600a16000e070001d10390307030350b003070300c5980e40c5e00d80d80c6004a903d05414000108001590325080000e5402034000d02400781066203e00259070300ca0740900540c0e9181ea003d000082e00c00e940500038032116208059100120019081030107051010251030703e640710200c0c109540e00f86000580107031003003508030002c503510000e0b80d907100001d08110801c3e41c82801a40d10518804c004141181d0080d03a28042055210014600302503000e0402e48050704000c4c0031049030040808034100581c3c50103c1c00300d4581c0f10740c00c0050040d41c60a0690300d0300c00000c3c052401 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 556090251 1250 556089001 556089011
    0x1c0602030a09121409134206020714010c0506090709060e061011210408010b06090112022a010f11030919020409020405010f06030e01051e060d12030c1101 68
    0x20482c1c03002c01c540f0340002c00e4480001d40d414106480740188008400090001e5200131f0015900310a1840d251841906038580304035000c840b01c903e8402c022a102d442c1c056030244004000c1c2400c2d0022800001005051228564034191690350a2000840f100602500101814049a055489540060480b159881c60b16282031004502c1c284820b00180050144083d0b81030a00342c010400314103c01104045001443e540245915054102d4000c1e40100e5007405290780d40da041103015a130080c0c00581d00c1103c41c940540e10031009500c40e40c0e641217460a059000108e9250142c41106400501c100014140c468000281c0071900180820704c00c1c1030042080c40340c42e040004a1604d250f0402030b00780d80c4240c2d580300060003800d0a6000070f4003d030804000140703400288680302d0072640d0a4800b88074131030400940c50300325801203411180c04601030300b004421754030225400f07501c85405032144942054a0710b03141d07901c00c4800102c10010f0384034107860b10070b01d5004126003800d410010082c00 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 556091501 1250 556090251 556090277
    0xd02030307120213030f061104060302180d08040b0d09081b010c035103030f020a080f0a03020c0625020c060f0901020a140a170306030a021c0602030a0912 68
    0x400c4c1c582c620000d010450b0400000b01440001ea001c01c00101803813981c50365456903650050301a400904100301035203c50181304101e401c1c5049940c404d40ea01c0f400d010320381400c0c00313440001c075002500400b0a03141ea420b10180040c41c0e081c0100351071088000801c43c1c0d550a0b5180c103083d540216080000c150601c86602c0c48500d14442e10103907030011000980d142d07402c54030180300415000d4032010402907504079402c0b019151034002d03401d60b400b03545d0301001003420345006e0380d0b284010f00005240ea003007004031030203d40c0079001600b010005072602600d40600d1905080c03070400240d40c0d10514013502d00c0e00031200d050094940b02d40b0050b6002611800084100013000ea010f0900300c1849a000040e14100a07807081c806c0c902c203107078080444014054a4071919552350005407041303640e802c2e4103a020550f041090181c91103440002d00030180001c2660a01041341a044091121390405031180d0002030800d00213940308440780d00002034040300c00e05010a500d042c0c0c820324030600065425641c = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 556092751 1250 556091501 556091527
    0xa081501032a0e01030212030f0906070f05060a050a0e0d080a05040203070e010803220b0d0e01020d020d020304051e070909021305040302101d0304090b060702030d020303071202 78
    0x181141d401c5500740c816640030403010701012503414807540c42d0071005000410303000e080b000000e059078001d40d4099160305020000940ea40b0401d0340100307501c0070034000030030325192205c018403050340305600c1d0741d00c0180a9510546088020380d642301180e510b407010801501c200d44186100d5000c0b13172004014018010070b01902500c4081d1030074602548400008055403410400c59000b480d08004e00c180039030355081da040e1a0340114041000c0009000549641c0070b584500110540d01c056209514005030085085c4c018002c182c00d50707500d1354007480940d074106401d00c050806803102c05005640d902d030901c0c0890405001d0710b0454081c0d020305d080901044400280301054034a0028002881d20860001803015864140804030441c185010081015400701d08182d451110703010038007840564401241880340040714003010750b8000c0c042001401c40a40106d850110043c110368904035490f00400d0a1241036440744000d0b03440081032003000c03a80090840e034000c414020440c203000c0308000070 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 556094001 1250 556092751 556092793
    0x1a1504051302040902120d0c1101091401180e1501080604050c0319090f230d08150a05041b0f0504030807060e0313030605181633030b0a08 61
    0xb90107513546507046400c6458090340c1c00305101c0541c0c200e44014484c044c0050a10700080c0044444d0360342000400955401540100d05582e107401c58041e030200950300444005408849150310000100d40016618000f04c072942c0c0504030003014140c401e0026000940300200150105026070b15010401460b4990300c415a0303041034030141006120103001807a00090099110050002c00c0124620020401d2403003524a10384001517001280d4001c0d85661034480c07000c0d0702c034140420481000560036549408000010000c0206815141511030b0007150881d0900c0074518032040d01150170100d0903070480c00c1c50802c030285140140c90981141d4903000d650181e5540140529220f4403000041d02d0144203a9030b405036800c1800e81da095403410040c0c09030805540c0704500c030399041e00b62102c0590201d030450115041c2d1400f0409181340000030440704404105c100a0550184001540304c6000c0c62141c00c00105940e01207240c411840070008444080e601c8000d03a82e100d408043e40c0d00d4083c40324 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 556095251 1250 556094001 556094003
    0x100813030c030c060c03060e07030506010804030f03060b2706030108191e0f060c03020703021510080a0317060f0f010c02010e030a050102030a050f040327031a15040513 74
    0x2800250542c0740546610403240b0004000741c1c03c1c2441c50101e580e143e4040d004488900381001c00c03070b490320481913048580566890307001520400004010a001c0c0e00c2402c48041039260006405070f9070b1200203d5600000141081c04401200290340c028040c221500000d178101c03100c2c1d1075540740240030341d0349603a51002117011040116164050150b95080e9990191007030720b03034000a20803460180c0c40d0040480302102c1c940c0c50f148032100024802e1080d01d14407030345038008108074180701c0c40604031404010304d420030030000f415000c127400e08103000c134910040c42a20f49400500341c02c0c030ba42c071401800500241c0500107010111300b0940e1030142e01100d140081c00d1103904e44015000480d1080c40e050f20741500341c452007441c3c80c1000030560080d0710030203100b030007080640c859080d0500d90140664020300001d49604010f40850705048440c08020f542c125141106903581e034403c04800000c40071010905204410001000c0c4415110340b2111002c1303401b003002e46404050320020108130b0b40 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 556096501 1250 556095251 556095257
    0x6011205010f020412030909060f230d1a090a122106060c021e0609060f0d09061d0d120f02130e01030c090605010e0d2f10081303 57
    0x4506010300000303500c03010220b2403595065507981d4030344200c1071420070010000c8000540c180d070b0008070350b152441341d517007620300f116072031659240f0f0010401d0350384525401158000d034002480728203e0f07461551800145104446c0008030101148011000810040044c030a07a0049105000050802149502c4180c450300b0074500060418604441650f440c00345600c3da1031030180b0100d8a150000c41c1001070034400c90303044501140398000b55200794032055400b900594240004c030303140e1400324040e140310045201000e00301030704492080d0540d01c0080c419110140c4d60b03240c0300303803040c040800407810100c9030009041e004200c410061400042070204800c0681d64241c1c0d04241c40c1603011100c503000d241c0c81c0614110748031501c07428161001e1104546c5107208a9001407030110ba8003a00781161416103038007100c0d20520703091042a40b80004103c403c1301506001806812810007008040f104144c1c0000c50620100d00f4828411200b0460b007043c0a401400c00020f001c4400351700801c241d1500e = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 556097751 1250 556096501 556096529
    0x627080d020c0a050f160f03020f09060112140105010305090604020a060f110303040809040506010f0215040c0302120106050f030309090c0a1718010b150702012708030c07060e030601 80
    0x180c1e9582400840603004085006000c130803034000c3c10024091b032910103035440e60501170755144002848030b840740c4402500314040c8201c0d0059490628241580400103040901030405010b00b82000c851000400134508240e4030300502c41560316209860344012940024020360600f6000078840038018450042001810300382c0004031407094026a00e1140b0030400c590312070904e890115815003000d601030340240d15040001c3d4013580b0603003944100b1180303034000c1e10340c2c0c11a01c00d904500540080045c2c1c0c0304802c2400000040e190340401c8000001c0f48000000e200c0c0c20201080716241c60b442040348a68014458186e503981c0d030201a68002c50201c07000303661820140400e5031907070a000300c400c5008c405030381005401d02446070781100300403480d4020411310b4910020000401404c07515108140780611008006500801421300819014914020b0700f082003c1c8051501741141c000740030341e420110b08240d0b40c1d41c04214500103003d103414001c2c8490305030808659915414418483c09089403 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 556099001 1250 556097751 556097767
    0x10e100e10020a060507080709060f020a080408010506090a020c070b250b150d17030a06050910142b06060e0705040302031b06030a020c0c0405040627080d02 69
    0x3081542035651010704000300d070008030031000c1c0d101c0c904000290360b8503003428001030b8210b115210251165900781c039203034825402c014040795680e031200340140c10761188042c41c0e000304e42ca40020b400182048000403a4a240000900c508180007400200320780e030041c0481c0e000e4050104038074081c0d54200e030b4280c0d280d101380d000310081b40c100e094030aa20841c0e10300c40300c41405001c0a84600c6100880d1104201c01b201900380611240f00b5035016005035019098a60b211070704000454000d0005100880d000b612980021311115080d2109480300c0782c8007400304060040013180c0d01d043e25040722581103001c0da550b11180c1c40c00d5406540340d9052a5910003008010040e800300300039000c41d01e01e024061030681000740c00755010340400d034807900c00c07100c00c001c03200c02e0211900089100608418119110550403402030b421118541d509400380c0118100a516030b403090b984a580a2840030601048000f00900c40118004800c84000040e04005000c5000d16044600c40d0107031000c01607403807801d = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 556100251 1250 556099001 556099007
    0x3021e0c0d1127010b0306010e04092907020705060405060901030203060a03081602011e0c030e060d051005100512071803021c02031b0a170f06010b040807060e010e10 73
    0x10b41400356112038201c03d48400043d10780c4811500d0050703980d001a160342c030b030700c221016030004480c01d03030024030040400c0420303062903009440356034031808074109140c14148044c24404007041d040c0c0d44420f020b0f020401003960401a04000700350a0301d000385071900340404904684654494507060580000100c0c1d100d80303401019100542d00b05508903240d0128901e800c6640e00700c10020b90000c2e55030704032021080c0301ea0b0030640310403080e038840020052060781c05440050070500c0306e55104905102c00554140d45000d490b110380c481d81c2c004a50a4140010080301c04080d0905100304802880b400b07e902401c2d0301f10700d811200f00e041a504640d810360700100040d42d590402504030484600c1003900001010b50031104078801c07015a18451200000036680020400d142548900d414008100d08465080d00e14400d0b00c1120549207403000e94040246402e00a9000020403080000d04000129007800741a010741046d1611a038041c0c12800003e1400d040303020841d1244800003404801140 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 556101501 1250 556100251 556100273
    0x105090f010c210216080c2103160311091009030c1203120b0a17010504060f0b030706030b1c050d090602010b0901060e1f0917010504210c05061303021e0c0d 69
    0xa44102c1113a41c401a202d91f8070746554280c0700c40d40e004006210300c8c0e5642d4015000756032107a4100c0f03840020034803640500310301410948600300b480d020204100700050303c42c8501440c4500d035544604561624501d003501c40c000b015407000102d0945c942d00c0d400081d90083c007581c0c2ca991080b03004980c00f29500c001811507055a440840a0b02e030b00300d40a40b44103010f401462046d8000c1c00c04101d014904d91308071050300c651188080e4507420a030014052180658400d40d45080e001e04500c07110304801600c8003205869080c16103450740705800c40e014080d40301400a001c0d19607440240300074484a40414030380c0c0410b004d20000e1140a511249190300c9413807221003015800031840d62000c0e0004c5010b0200503503070140c031240551030108541016014025140030f00c0d88007174002040744a00364440e4a82e00261b610f401040700e85040d41003c680200301c514001c480742001b2800f130851500e40686848800c0740703400c4d181c1d00395a03d0401640e00110725050b90301ea080d41c000144802501d454103002c0 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 556102751 1250 556101501 556101503
    0x3121802062205032d03220e0901090c0b0a140a09080d030c02060c0c010231120b130f0b01060e0a06030509060f07110109080703231c0e0105090f010c210216 69
    0x160fa001c1f580040c0103040000070301203c3c9806002d5240f5190010020700740d2750b0101e000b074040c0800400c03c015041b40e000040044440510344250b4420104250b040c5692040c9641c6000bd051031009020751202481604158015030404000140d642540a5181c9130300800c0d00155403804a00c10950040c290100c80c0260194110356000084031a80c0203a903550b5203031100b0158600e0310700441c2070540030f6096401590041d908591036560009200318440c03100c0421504200c020204c180000c0c4010561406413540b030b00c4103040c141d02002845002c118135030000d8100350501050183c0c400700032800c1d68200e170b042000c103250355580007c15521003074400c0219520f5880c2081d0103092140b600d0113404014400da0350341c42499600d00c802d9417206d100603250b104203441008030340c11048202401d03008003054554003103105000403004500319001101d80440c190813043d0b499590440078400c4003444103041c24403408114040c1048a85054141c0c2a901c1c0607a000668408030026130740745076001 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 556104001 1250 556102751 556102777
    0x1180320030d0c0b130503161b0306020403020405131a18070b070b010e06060a0c06061208030603070501090b0f0306120610060f0c03121802062205032d03 68
    0x40501c0540c01400564014001c1d100202d240e00031a16840c0300c1c03d2017420040e0804015802c00600102120307000038401000c8542d030720151404058103030040043c00045005010050700c41e4554010b20082e140d000740292001d80002d905040000c104894a11840c0900c03040e4161a603589070708200800c14200030800103120703102001030b00c00904402071140c240b25507170000d126640e07560292aa01c0043c0e51180c0c3c410014420030507800e1140204590b218061072000c640301c1e54500c54102504964902680d01d09800010070000717007005c004031002400c1c01e01e46620410301e4484844000e0280d410020b00f40714001000c0340c0303140c0e24407a44144035030092b0305541003424056203c2104505511801e800710ba407211101600900035090b01d01010703095100e2081010f000b000f64001000c006c01c10041c00340c00803441101584907900517000c400c1c02445003107855080c404000e0014030440d44100d200c0e50049014554801000201c00030714a505a400d810300000f1021450850150b00101021 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 556105251 1250 556104001 556104013
    0xc040515130803042d08010615030e0a170705150c2206091701110417060f040203030313230d0912020d0b040201200309041b090b090a0503070e07030b0118032003 71
    0x384d02400003072082101070727640307040140550054200c1c0c0c0b2041044005004941280c940e252045031400051500d00e110760141c41e905240341c00048644842910311600c40c0ba40800d10265500141504018440c1c4126114141502e42500189540c040740103440c20301e0741d81c00701c2d84500d0b4002d400c87d02c000b5081025940d10740c1c0c2c42c4e50704108190806045a00e80c0d1140340046100c02d051092194002e58000d0701561941c2e68484d180c0041840b0540c003150507900010b00307962800c0300d002d04054003108007030142c04000c48a0200400001c031582110101e190074004c00d50059540202845295502840d8204240c0d124001a203103401d00480d1001e24400c03030351284060312004170090642900444041040c28010204032410f4452000c11001190004c4c40520204182c0800f074241200001c2a0041d0251200046428145594844200c2808407002e00280039014015580500001c0c604602c00846001c1c0c0d0003004580740c07101500502c0d101c00c5000c415030712000c00f1400d19074054200c1399 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 556106501 1250 556105251 556105259
    0x307090504050109030315060c06050c0403120f180b030417070c09060815060607141c03050a0c1b110d08030f06010905010e03150c040515130803042d080106 69
    0x1c041c055400c8100c000900d030030401c7d40f4685c3e28580320700540300e0310307038a013031040d02142c6d5110028040a090000100c4051100000291651043d4141000c0907902c3e01801c024003403019012120102a2107544001d80d130081c06030b49074401c02d0b6544140c1000310506807280c0441c0c0400070707100b28a00904100000c040201d02c0110075000f0404807000d070402c99a00d035007040707800c03d00c85005581403940182c040084502182c8000e03040d5a020580c0307010303110b0305e000710480d035800004040d00d4203020075220410040d40040a00c9140e0514015041015507503141080ca220305a02d0303500700070192407011201055907200c02d09403228150340710403015900d080862400c005032031b0442e44940010b81900c0045501d511410700017005440203001003a400e0102e50202201d594020000c03442c44200380030000c0d00d075480314a42401d5002c0c2c104590394919129403560ba020005070056a0964403c0104011851000c8201000b90542100e00c2d01018102e00070001104204d40c440081c541c00c0040100f = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 556107751 1250 556106501 556106503
    0x7031103210406060f06020d0e03010b1011100216150c090e1b040311121b0f0d081204140601120303020306040b041b090e0114010e1201180b0901020310050f030709050405 75
    0x8198683c0940700d02011914271001c150030380e40e02194450700080d01e0030030031043e46d004030504100303905940159030fa0340001e0721803101260004c0340c0440c52a10501460014011001580044003580d21010b1200107500600a880c0e90f03c0c500c2542615222800008c00e0380d4a00c00c2d8022044e0042030b1550356556903400d1241400782004010761080c241c2c088207590703407100018400440110048603008410449081200392402102c101e50044540c07022036001403041401803580c04440440c94070a070a041c1400003001f40b084020100e00e80c00240140452840c800345800090340c1840c000d40d0340e0f600e85e000704000d880d002c0462a0064140a10300c030301c0d1280c061038100d00303040039540c10910903500c0100c110000000e22a916603200b600c5880da103c0c0d4070900c403c04412001400c3c441608052030f058a007120007040020404c204640744417020003400769100d94004030402c000b0f50075420b00f20505240c040c10303803140c288110020110341982ea207041c040c200040503186010082c1b0700e0141042 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 556109001 1250 556107751 556107763
    0x60d0b04050705130b030705060c070f0f0905131a0711060405070614091311040b120403030c11060604090c1206020c061315091a0a0207031103210406060f0602 70
    0x1846080000381413010042c0910032580d03001c030b008008081083c908410301400383d02902441c0454011220003103a51403075045098003c0003200c2241c49942d01d003410700800c0300c00180070744070703210709040b074501c089006c800d6004c000c286083c044007525183c421080d618800c3c0140b040c031950041500b00000e2100102c2c02c3c0e4110f0f50aa144d0030081800044010054403d410b103e69000d20302194070a07000029131f010b41c1032042c2000c0d240b450f041e1a900300e20803c0d0000c0d400741d41854041c0e0308000804d0390500071740c5200a0b840c03c0c40e580030841204510303102e06004041c07078002c0e5039455054081c80300c5c20030510300034402a5141490340d00c00e418440b000c1e41c406e4405c0140c511a0380081071100c45440c030b504508940010041202c1081c000e910005010600801e803001c103044608a900c801e0104000c0340203807004400181d80d8041e07490068860980e010541440f6041804091140180e81c54281880d0b09540c1c510b00269a40b490b2031002450249c114040d0303a000a00041075854000803e = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 556110251 1250 556109001 556109009
    0x303031128020c1903290408131d0f1905091b15120709150905030c04090203060a1d160503101505010c021c08030604062c060d0b040507 60
    0x988000c0743d44074090052080d40303400c610074000f004403420000b10340403441c034241c610341c811034140c01c88040701440e10825000362000d90f581030340095541018210310000c000100704507408002c0458902d10081007802008080007055121007000070488000318409400c0d400c07c4c0032040000e424039040e003e5a918048022821034802c48220030307024a403001d60003844800118580d4a0482011020701030b0b2036010348904280108040f0100b084172103d00110742078106550b500c840c2925200401d4a090302c44245103000c0d6150800041c056280481c00303075884030704204040340da2888020980c0e01da4041078004002e0f4000c060500ac03201c41c107040700360101e400071400c82d1500c00b546680b400c02c440d2259200e14a40030700040130002940108111280d09000400a40941244011800800000400844908600008004d203c0c905403062502030801030800440c00015104254803505551160b005014440740028489e940d401c005400020350003240c0c04028280713841c0880c0d03a0851802 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 556111501 1250 556110251 556110253
    0x150f050a06020105010b07080a18030b0406060608040f02270c0c0106060f0e0d031b06050603120a021515031b0f09061810150c02130204030b01030303112802 69
    0x10014007036105000310741c1070764002c0010303918000300c2d80d661500b00e0340201c0783c000030702031004030f030041420404685600039401b4140880e179625142c40d02800300c0e509a08210103012206c1c09004c04510024811000280d040d03441d500f2851124441c415441d004106428054031030030708003d00c1107448005050031070f02a9000f40840c507100c960640d00d405542c5401e10000d00380207080d582c00c0c03406059a0351424064100422029410100510b000c07180f6501941c00d10744075402e01c00581400c01c003540c85528480790441c104200301d076000317440e20844290411041d11000c041022640c41d81c0d8254107590004044414821061030300400d02804403007030328403624040d00c0700411030402e02d0440d841604014080410f2001c0304298070b00c400340c06090700d402031446070004106098082403003400f00000f600c8508401004d88100120314022081d4041403034010b100030000070302aa0456070540e03605003004262828088446400c0b8020f11441690022a030400700b8038810454455408030103990b4 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 556112751 1250 556111501 556111519
    0x807120f02210a05040f080a030f02030406050402010207060513090e07050607050d0801061403060d06090b1f0807060806011202090a0605180f01050307031a04110c0f070f12020301150f05 82
    0x3d0920084940848000d411442407061040001c1c2030b04e030003400341f284c25081c006001d590301c0f8000000ca0300304940848000b0303990b0080c001550380400140f4000e1940e4a003084c9060034803c0030305040c1309188541115940c50314030b0002c00079001c0c484200075007005070440b41c880e01c6604209586200080204002c80c43c0f080010400130b114400c03002c0e90701c0c185400c2924580b6504248505041402c0d0300740c8540e9922500500004c0350295914003d0000144241c001040f210001d9405211a4040c998550205808025641d0050081e80c1c1c001c41c04d00b4070314004c1c02d4210342c00000e4800d00c1c084541c8804c40e0792002c0f9203d50004064181c1c480d0700d0802d10341346080b2009221346418901c0c10341c0c0c0441c80030300019501600c43e40003403102d1003600c0a00a860144e1034003181c1a40c044129018034807070f010902540e425401c102c600c082e0701a66001380310640c9400d40d142c1e10103466000707810344103800001d088250740b001d4118542c103810707100b5440d030150b07a10449104005501e002c1d030383c4109070003 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 556114001 1250 556112751 556112761
    0x150a03061a0a020c0909151032091902030907090c030e150a0204030614010806250509010c150906060603150902091f021018030807120f0221 62
    0x440c0640d00150034035001011903104040030024890002800491203201c4c00d01414800c0c8503501d6242d002d151542d0420b54923904004440e400c1e121000c0f051382050310402d00706600050504003018020800f540c50b80f002d9140c1d50300c601032040100d0207002180c1e00010078040c205000141100c01c9407450f4404014101c0800740c00c405591980180c40344551010b6070540040c0c015000072a0131011150005260945d03950b170301000c0d42c0c2c0d4040d901060494803001040352002c01d20100307911280708064041340b0810540b803d03090f0140914030004000e004519080d40ea40034510351107030399800510502c081161205070001038107a20750115a821708001000a00c10b0013400f83c00c010780c2c5d403081303030000310b504203140e440094010101440d80054060420650140440491095031180d580a802400700710324149040c4d031b0422103031382461040390400d02c0200342d02007441a0401032515100d0907841d140700420b006060f00c0401440024170000e80b0942e0040407040100d602c90600503000706d03955030 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 556115107 1106 556114001 556114049
    0x1504030f1b0f080c03060a0b09070c03020313030f1703100b0c070905040803010e16050a080702010e07120b09210a051e030a1a0f0609150a0306 63
    0x200f084c044c070705040c000b55034403000a000601456038a0300c04107031b00c1c9500400340000c2000d00604c07442050706c00c4c01110040c40c510140100030649904200e4000441154111581003120041b0f215241ca80401d45c5d1007101c40c66500802c01e440c1c00d4140303225521441070500035002d645008a00c422082c85400c1c0154007038130489489605114200250110107058203800302180541340201d20340c008100c81c902c00c3e9514015803591503c000690140403c544100c100d805080408290301e0000e070001c0160500a03c50013031300e5156400c843e42c881950049010018281d441000c005a60500007030500c00c1041c03400310310b4010449d0050064014544500040701400402d102040303459000c0d030340c0c007540c00c00d03040d412215292000845c000c0e001510319000381c0012810b10702c549e450700c41e580a0704120450560b070f29184188001c0040545004145040310230001104d001e80d4 = true := by decide +kernel

theorem cover : BRFrame.Cov 555935251 556115107 := by
  have h0 := BRFrame.cov_init 555935251
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 555935251 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 555935251 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 555935251 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 555935251 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 555935251 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 555935251 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 555935251 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 555935251 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 555935251 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 555935251 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 555935251 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 555935251 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 555935251 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 555935251 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 555935251 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 555935251 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 555935251 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 555935251 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 555935251 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 555935251 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 555935251 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 555935251 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 555935251 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 555935251 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 555935251 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 555935251 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 555935251 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 555935251 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 555935251 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 555935251 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 555935251 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 555935251 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 555935251 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 555935251 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 555935251 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 555935251 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 555935251 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 555935251 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 555935251 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 555935251 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 555935251 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 555935251 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 555935251 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 555935251 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 555935251 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 555935251 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 555935251 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 555935251 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 555935251 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 555935251 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 555935251 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 555935251 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 555935251 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 555935251 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 555935251 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 555935251 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 555935251 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 555935251 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 555935251 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 555935251 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 555935251 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 555935251 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 555935251 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 555935251 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 555935251 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 555935251 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 555935251 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 555935251 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 555935251 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 555935251 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 555935251 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 555935251 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 555935251 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 555935251 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 555935251 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 555935251 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 555935251 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 555935251 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 555935251 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 555935251 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 555935251 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 555935251 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 555935251 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 555935251 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 555935251 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 555935251 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 555935251 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 555935251 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 555935251 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 555935251 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 555935251 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 555935251 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 555935251 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 555935251 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 555935251 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 555935251 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 555935251 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 555935251 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 555935251 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 555935251 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 555935251 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 555935251 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 555935251 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 555935251 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 555935251 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 555935251 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 555935251 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 555935251 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 555935251 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 555935251 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 555935251 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 555935251 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 555935251 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 555935251 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 555935251 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 555935251 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 555935251 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 555935251 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 555935251 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 555935251 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 555935251 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 555935251 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 555935251 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 555935251 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 555935251 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 555935251 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 555935251 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 555935251 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 555935251 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 555935251 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 555935251 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 555935251 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 555935251 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 555935251 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 555935251 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 555935251 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 555935251 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 555935251 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 555935251 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 555935251 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 555935251 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 555935251 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 555935251 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 555935251 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 555935251 ≤ n) (h2 : n < 556115107) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
