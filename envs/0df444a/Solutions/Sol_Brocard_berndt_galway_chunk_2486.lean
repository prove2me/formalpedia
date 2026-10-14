-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_2486
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T06:51:27.729718+00:00
-- url     : https://prove2.me/submissions/5b7256a2-7e46-46d4-99f5-bb773270d4d9

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 446942446 ≤ n < 447122302 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 446943696 1250 446942446 446942471
    0xe0f01171002031801200a03021806070f020102120a0207060c020d0b09100c08060a1721121602070b0c100612120f0c0b060609040c080f0606040503030f090103 70
    0x2d0300304a6840341c402c9640413452684600038400c110071480c403d10a03482c3d041060325070030140d002d000d80d800245940024003080c4504440d009040e28003001784115558201440c3c40d1211200c5141c0c124003610600d901042803422480c2507840c000d40981c020800c20b45420001c9524414803201a070300006190215008900c03018052403048040c4001000900c00d503001c09000c45404070914001c00c08840c007440029981c01d41c0140031581e2100144d06145000c29000d418100d140802d00070780040600d00c03503c2e1014000252546500e42a02c1d191140c0d07819024501c826900500d04005801c0b084c41807011382004009010b420703090b401100d410261030311203402110481e41142c2603110b0366000e004100310b02b90000d0102503800340342c007034101c0d070009902038034100d08481c006100080c400000742072a21050141c96030004020030901040051031405885c80703906954440054000c00d0008a0b181000000c480c101ca40240c0150328200f02c4c0c5090701840d4103e120018101900c8120841c4c0a = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 446944946 1250 446943696 446943701
    0x607051c050f033418052205100b0a0e010306092310090903020c03160b0a0c0f020a031a0c0a020d1101060503031306020c040c050f090406050603100608010e0f011710 73
    0x1402a01d50041120100c2617469090036181e019030b210300c00d16000e00380c040000030b2103c141190729080c0030843d1380394840e03000f0b14500c158220610000c40440e4040c22035520040c034180000c82078a0030000d05480390740c0c0c403040e622119201c601e1090000d01030a4402e080b20400c035480740100d8100000c840d11141c140007a5510a00150010383c0884c200c1b05040c6420300c00142d505541852038100e2520302003800e01d0901855003107609000c070403031801050240c1298407182803540240400c0c2031545924040400507240c458000e1502c03907207400a9a0900b00d03100b2501400041e40003404590761814049503149450b03500a1000c1d500c03004001a107440800c050581d401c074003c21001d400342000b00080c5400c540440e69032045050450801325285c0000890b0b400306a5000807641c4c1c4c8075003001013400303000c2c9544030315000240042000002d1022005d61000d0b00c0c0c96940340061660383d101024803014040d40c07510520702102d40100160340c0888100d00104194030151928202000c041004 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 446946196 1250 446944946 446945041
    0x7031b020a18050f04170703030204030b0a050115140306060702041503030206040209090705012c0d0c060905040b060d0e070e1003020f0306090a12020a020607051c050f03 75
    0x10421469921640c010300c2d14051141c0c0043c50411204151a040e19500d00300d00c0091458641c12800049400605101e40c0494004d140c00411103c110b0400042510007860300f44102c00c54081c407000c3e0b404506100c1c410010340c010851001d5411520385904115407a44950000c0764420350f20303000d2486118600d200200154002d8028042614003801031100c4090010200900da802150040c0150303a0000c50048400d400b401ca802a1071583e80d441c964101141c201959016110602d84020003444d103002c141640d019a41e20116159288284800d035901030308150f5119405001e45103201c112540132940c2d0302514000c4a03507036a0f550031480312000c2c00740d454100c0035800200034815030501984202c00f411040c0e00900c028a4080c4100361110500e0070000c2200449410ba040420300c00c0043c2c1e904542c00074100350b625500c52402c1da41d584841c004000c0424082d01219203001c1c01542a5102908208085891503582c43c1d444240003803100408000f1071040c1070505020003c4445480b03 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 446947446 1250 446946196 446946209
    0x9060f09090c020c180114090f0109090305071b03061b1b0f0c060e041b08060d141e0c030d05040608040503040e090a05010b043c020a082a07031b020a 66
    0x16071719418580e04c0301c0b41e6003460700c41d070740500002810310515400c440c0381c850444d07018460000d80781c0d43c03a150407036851054034005052484104050301d01142c00400c0001103c0c410700c0200880c90100d5a5003400c2c1c0490030304240403640703444400128a1445d003511801c684a05800c22080d0350540e944200c440442e08504001170b0168440403540c1841e00c68070340398550601ca070b40140c1d920000700904218006003201d014035100240501000504052003440041050075a10107003480c40301030b1508582503041451a218150100140d400c001c01c0200c0101c03082d0760751614142c102082583c001c44050800c946030700c010000024034031284c0301d101d0b000f40a5007002d441c00424a04102c0e003507545101c005407260b0b140072607545008060ba511a01c030288220640b490905152030344800307503001032130311160303d6000207646000c440d446928680328610802d0420441242101c1240000410240c002e88071007080180078042801000048143c00d0448964084440c00b0750109030b50000075400304 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 446948696 1250 446947446 446947489
    0xa03090f20041b05031f0e0a0e120708090d0204020a120b1903200d061d070f09110c060a0c1404060801090f0e0d02061506120a020a0507050a1209060f09090c020c 71
    0x201581200c9d00500591055a40042c0000140e80c1e40d103110503c12240000c00c00c0000042200f21600c03080d00b4098030310740040c021511400c6006c00500400100b110781000e15181410008461900c80c3c40c0b00345410700c4085a900041c21552681400314031036141100c110b2081542d041c860ba9030289401c2032714428200450078078882e1400c802251003d4410220903005040c0034442200e09455200844040708000705913510010703001000c074801d1703024140303280c0208000c0006806081c6c0210301420210b580b0b01c5034612804003d66120f0085004120010302214010011411240c01c20392a0904d0341100243c0704180c001c5080c90558542c44a40140e0003100800072401c10320244034080040640b070942c5440803002003822604c400600c8492229408034540c480c0078401c00c2034400c1c059010f4211035448800781402401503c0140d032080000701c20170f401160345403040e090701445424644800b00401d007040c8502015081d1a51080c085204520958141d40d8520302640b40f125111000d1 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 446949946 1250 446948696 446948701
    0x307050a05160f0c150e1c0203010614102318060307030606020f0c2101090b180d050c0c10050903030a080109060b0405030706050a03090f20041b05031f0e 68
    0x6a400103e6403103125042e51040316250602d801c050280c0713103e06c0c116444003001401e042008070398071031010040d42640c0703000000300301c410703c0404260700c2d404100d41d162000f41d250b81c800c80d000100350310109402c032942c0718030345a07070b20441c4090840503c41950000e0a0b0310403002043e026042168004000394440204201c1c0d250107000144040502d040941070041051001c035610060260000110603d505a60500400c00b907024007411944941200201d040142c1c0715841701030302501564a0f0b003d042e40d285a03c900400c121100403940c1005805155491410030000700b1485c02000c0c14001c0411400d8a1554140010034400c0710b140ca41700d080e94100022a0200d9613690003220320202d04004c00d100c1c0381c0e00054000201c5201e031411136078079903980c00c0440181020440040c65032038820707011340401011400e440740324040221900d032451140001c020580c0c07808040d04100c11910b03034051121a101d24002c40c1e00540408900a04841544500111120513032002a207042107500707 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 446951196 1250 446949946 446949953
    0x30f071506051c02130612050d0206070c020d0f0f02060307030f27081b0318040506151602030312010303020a120302071101030207210909150b0307050a05160f 70
    0x386406000c080d07803000d00305950343d0003049016051600103441540418a10b5000385d03000d400c4000a04003114a8034000341c610702c2c10b560b45d41420120b1201500a0100003034031305114203400030f40e50b9001810380c0002042038680340c500300c22103441560500e001e90b0f404805601d5107030085010b544551340c0011350b03080042c1000110365440100f0711412103100c6030307030f48120341c220005242150040290f036692400c05010031020300074581418424040806c1a9024908010720382c0101e40c030596042c02190b079620100180c1d01221030030701810312010b00400300302d6a200042c1006961002e02200e10303000f4030785200c0000c035209a20031801a40881d042c801006508d40c045944585903080c154280200c5544140b80010110390290406a001c50810f09103c010809460311001c04182c3c1c01ca400d18141005292050314020143c2082c20600c41c10306281c040c0d500c03e011902ea46034440e0070364445180031226540124984010010b0910445807580501c841c40c003c0d8600c12201450043c18914 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 446952446 1250 446951196 446951201
    0x13030c08100920010c0b09070e0105030d0906110109060f200c0733030501061103040803071b0509070504030201030f0b1c06110a090f0902030402060a0809030f0715 72
    0x80e050418900b080003501c0000c00f04034859070290080a49a00b07802e004400403a48681142c001400720381c01c0105100d448500810f01d802a00d00d003003080c0d50640e0701d078400e266030741c504007103803400084011500b00002841a04140e003044480000440d44103d00d803034800688085031469071480707642c2d10340414003e042c0c103889103807411010b00c0300382402c03131030303403003980c070356032a4070075454041e000e03c0b4507090540c041080024100781c40303424007860034528031004000b45802d00030500814010855034a40d035000009072000c80348444011403070051075070f980c001a501d108581c4000a41c6418000c242aa20910040e10510750f50792841d40f02c070310790f00004081e0780e2420890300c0418a40421501b1580700c04000c00c8180308690300c0c0c40c092407072915003000248074008034240081d0022840c003c01c150b100341c500b02101d03169255804038a4440200720220f10090710b0081d0300450400c4071006080c000c2440c81d90002c0c0700000c0d2030511851040344241903000003400c483c407047e01c1d81b02c140000c6036407 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 446953696 1250 446952446 446952463
    0x501050a0b030f07030f0e01021201050f06040b16060603030c0b06010c110103180b090106050a080d200f0a12080a0902150f0c071401120506030d1413030c08 69
    0x11a490000039250448001940c4009040741d001a00c200c4002011303076000341c0082c0ca41418000080044c0c000d0701c0d1004c0d000f504900b8502000c0c81036000001104d180c8141c0c00362070b07107400602d01c1d45890b1408103500d1850780100300c445841c03403881124901141441c03240400841c0203803105105004145080d80c207c4800910035414020140f00c04d078080344001c490b91400c10020b0900081186443e0918110f10083c2040101800401e00800c201804103411038001c54030300790344050700ea40c2c0318600552034000444e0b40000040c90300180100c42c0440c000310b480b52440d031205542155040c40e00302c03030070584610782c02c1e0352450b1640843c280081d0301101007580100d8132030b030800000700164005018500c4500c08254824030103c0e42c0851540110b04a54800031002c0454464075510300f20150f40007000c51081d800710702020b40b01d488200c001c0c01010b02c9080002d01400d10005200410395028145042c8114251018441242030401c0008071001440c014440060b200340350000c072603e0100030 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 446954946 1250 446953696 446953699
    0xe01060804120503070c0605280219030b01110a060b0901150806040b1c0f020f0612010303080709090f090c120b0c09121c03150b03070315121104050105 67
    0x4100802010840c6590070b0561452203180c069900c5d1903c1c48216421280e03040090082840d1100703004040000b807048181c4520b00c00e14100c01031030352001444c124000c02a0081002081c87c0440421600c640d1101c04002d8050510341501031001000a1601a0704801111f6141c1d80318500e417400d00d052000140146120300e0101c0e203000d800b100003050301201401d650702490302c1c0c49d803160150fa00c800100721042d80001a623541c84100b800d02407005200000140c0c0104200c1d500f444940c10030000301d964403403000098581e2a441d540d03049910b048020151410880003150100e04803010b0702883e0302c600b02d58030001c51007180360304140800c220594840750854607115038042c00100300c0c01503030ba8403040e052002500c1701e8410001c240456401000c000803402204140c0b02c44c01c50407080c0602d1403480340d03000c01c05940c0014442201c600303140a940c0d0894014000500840e10a4101044541905840000403503441502c01c050482d0070b03500301c901d81510203015041c9e090500c20907004040 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 446956196 1250 446954946 446954957
    0xc0a060614090103050d08070201020f07050a0218010302150306040212010e040b010e240f03030406120e1506120c03011b022b1128150e0303180c030a05070e0106 71
    0x51039175480e03031382c541c5c5074289403d0061000016800301d00079816903840000c0c4451003503a5020318640341e03423964140081244039504420300e888a0500784004203040c5ca41c0507041604c0c9074000c0d040c410240d00001c1207140d00540030040321f0f040d41c40a00c00580200f040404055aa0802d45402c084809050f0409030b1040341000400c20a51a406d00d18400c0c41000d404090078401c2402c085102000e00e802180e07050f1000040001e00948e0003858608411200c00c01084059a550703103841c2c070b52003601c0e50314424492282c0070032600d00d084801c001290002c403040b40e1650301c1a03c042820345506140c0d14800850080d80340710300f1794044c011300c03100407002007406c90901002010f0007a1524500c0c00442042035000131aa03020004201807111101050320600c0329900e04040c440c5542c0911104440560415540000004580c040c10100d24004405581503985990000d0072103640800d060f40075208165490340191401c5c000300030940d000e900901645030a020120b041000e047c0d000204000 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 446957446 1250 446956196 446956199
    0x80a020d0c021e0d08030403110d03090807032a03050a0e04050603060c072f0a06080603150606070b09010b04060f06020303161719150f14060c0a0606140901 69
    0x94500000c1c00b03403000344203081c0700f283d81980041000601c030100014400e041c00002d05c030903da0440880400444c0140884800c260141c208030213840c3c2d1781000506201301448801c1c0024010702c20002c0c107599160313811070800710940c4042c201205490b416404624005500c90841d94404042140700906460034001d0303080800102e81d5440008080c03201010380070416004110381c5003c0d151700c580650210382c024140c20880003c100c14102c0010b8031880c4901c20018400d80102060b070f10a000c000c000e0114041035040398003010308000d01d07075a0321080800900b8000750411b4145801103e888000141040c019401d0108582194001c881004901a010800141d000007243d074482140000c5041c64a18580180d0b05000401000000d0b0005402040064040c3c080a40d10b003200a0394180a040c022240e140c940c0d22040c00340300341d5030790400003c0c401c425180009000c800b2001d0304480c900b90a000010341010001001102c001e40c60740c0342080034029580040c82c4588045803c6075055 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 446958696 1250 446957446 446957449
    0xb280617040b0411060a020f071502061b19080f0901090203070902180d0803090d0f020d0c020303090612100803090609090703060f091d0102070f080c07050a03080a020d0c02 76
    0xa4401000140180302c1d501c00102040781c01e1200c00c02d03940300641403a0310752240700000307500c51a4144025045100f08000000e880111404039142610190041c001d184c6496035800520001c14500681c3c1c0142001440250520745500c2d01140000780d030b0380d03100c2d070804240107210014003801c484101e07818056a8009a9800700d03010040b80daa8080059548980182c03490003c07d8002038554030030445150001400003190003103201c0d40781c44049c0c61810000d0f102c26103007a4039000080c001a030082c503182811901600c0c203504840c0c00142140d0404818000041c0103620882d154065030210101f4006c0c0d42d0b000460450181c201500a9800c00e20700c0400700e5102e00520a5080c8281241d0010691a070300036400907000c0c150300071545080ba42c440035540c004d04201107828000c6010301844001e1030074103100f90b0302c02940c0041c0e00603541f251034440a000d508042d004920a00501e07100081a580d0b484180006506c90308400c2d84503101c072240a0b003170a480740d0340ba2062082241444005 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 446959946 1250 446958696 446958737
    0xc0305060a030c120f0807031e0908071e0b2d0906030a18140318010305040b0610090e09070306050916031403090607080c0106170a030806040b2806 65
    0x5651a405184c1610101428038000381000030501914004c0002548810315034007101d500500303801da00c0790000400d10003504564400d01032140c102d00703401c200000e00c10004884508200c90820070303510150f543e01d508079200c0755480700304010141c1c07104602103500000c140d002e00c8610420440d400c0d0400c4c041c040803543c58400242041036041e40c81c0ca19417440440c00d10700103013260300414030290065207280c0c0c0942c3d95005108100302c058450240c0d0802e980f00303000342031040360300c021a03481c1d030b031194001c1c4400d0f500644206824081039000120716050700d8082d15200d207030010018404079145080c240c003140d00c050705081107038224500e40840044111000300071031b60300c080d48542e0641a6203805040d406040340203948124000ba50f41d00b444a07402c0070b403086926850003040a240c2c1c8040f4080d8441a03144c608625801505080000c01d0044183c1139110070050000701d50b641a180000710359900341300b1004600c0d0340c05d400c8072480042c0c441008000d00703080d00705104a50348810140c0750 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 446961196 1250 446959946 446959949
    0x11b0801060903110f0612070c0b0c09030c062d0a090b0f19090b0409060e070306051c03090302090103051609110423090c0316020303101403070e0108010c0305060a030c 74
    0x24428130045c0c1240d684840f02160b441d000851340c03000d500d003085c400082102c500c0c00301c10b85003c5507140200381c11000250455100102c010700070000b0100c13103800c0c4045034002070401100303481c101400d00c084e0b00740c8a40d10045600c41c0440c495a03022480c0c0f001c1c003140e106c0e800280c019a4280149840a44041d040791106070300c0b0005003c1c1568511012075084038a41c001071002c01c0c005c2000568079895410040c1500c132041e48540ea03d40d1600e004904450b124420540d02091900980002504903114564041e020345402c4085c25200e8021881c610000c0e0710442d01d0703521800b90852804107034214030002d040700d004d0501c0600c840007a4500e039030045000e070b4107409041c08030f040880b80702115120f0140034040c101481ca0710b000040d071103080c1c0003100c40c0741c40102124940d5800341c1c40031040364400c3c1794400345044143d04103140c030501042200000ca0301807051010200e08000310354000e5000700000000440e03a449102c50003425104041e203114010124489e09000244c034a402480 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 446962446 1250 446961196 446961199
    0x70311060d0e010c090303170702060c030406060b0403030807110c03060714090a0f0501270b0c0c0d060506030f0a12031806230f060a03080c0f011b080106090311 71
    0x1929005601a01d400800040c04000000c0d032a05400005040d0400c07188001c4078020385600201d8000954403403034a0108640000058220b80c00280085880c08055500207010304400201140c071044041c0c0b150b4440c1d0019004250403034108100140e101c413000b410300e010700000d40490b40b44500425a542000781481c814041c00082d600300181040d025640526802000c0120441e030300e20a40680042500a403030000340c0313054609020307c402100390781130304007800c18010004c0c0c034105c01d10500c0e40006076920003d010721200c910040d940c900c942e484041c001d88001800342005410540b800b0100c6003003901c0f60304182c000d540412800200d0202482103401c008c1801180328141c10f0405040c18001000c0524001211840401c1800003c0d0481e8012600102176110100c0c0a00c809008a8039540d001030742d60018800221140d0240006c8a500360444441c0d00383c162540f0b080d82c00203002c80c05140b00d0051008075a0f980006154010007880c00d003244007030305507190706880c030310003000c2076 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 446963696 1250 446962446 446962459
    0x417150105061c2a051c020d0e060a0f060501030603050303060d1424060108011202040b0105130e061302070f14030708030a0c02010509120d0504020d020306070f030509070311 77
    0x99503002d240710180c80d43c441c90001c003000316001c800e400207110b0000806149060301226407228010b8040c00807108484c80e04c0b41510761401007485804082e5210712074a110039030b02c1d0083d207180507030308001c224019240d07040040b60740808140500304484441d8011410941014405c101080c1c001c01100d41016041c0c0d102145644c3c0c6040120a8044461154417680320340f4801b222106101e000c1044c0811a0803030840b0b285d19032500441e030b80d110a002c0d00c81c40301100c440b05001460309504c840401c1006040060800c05903560401180e119a800b0140c0d4520160030030034285030008a84610004090046040104540350310002d08003041c401410301da01441e139506000c00c10003d9440007540140015541e00c0c02c0004400a4026144201701541c01d01020030100000810300c4112a040d044a031b0f4207000904a400d405800003900690308038130002d8050015842c144541d0344280340303c0e101c55080301d001d075800400300c820042c01007025030132811003440000e003d21103484200f0b0040342e24 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 446964946 1250 446963696 446963707
    0x22050105120c13081c08160507151805190305071401060308030a0b041d0607141c0603020a0f0311010509031504140c0405010e0c130306020c03041715010506 69
    0x8031054410030003d80e0300f051001000140c100d000040100805071001c101440a0b01403900540da4405e05803000d190000d1070800302da0b0070070310400c0541a118001d0710744000d03080c1d82c50510001c8895900c0800c0400502c801c0e03031000d1060030403039040384442111000c201c0007241d403001040d600900400038801508142c03000c203103c60075000207014681080905a0740d0a100f168400100404402c0c50701880c1818002d400342d00091211015001810b8060041070340d64032412240a4140703080812500018081d00420b900414071000803802041d50004095040d0300421844400a502c11064403101c14001d1001400380300b10311500500a0925a4a6280610009042034202910070303447c03480c41420417041c400130b038070340c03112800640c1c080d607034010011014801941c009008012661940030301007101c01341074034000c1048105440c4109a010303200d5544c08103982c80150000903940c4041420b104c40d1011018440140e02403000070701c1c5465848211b090903c00c144200e03482803001046 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 446966196 1250 446964946 446964961
    0x1030c050d050c120a020712030b030a0c0306020705160b040b07020d0f0b060a140607020904170a18062a02060903100e0c0118030b0406020d112205010512 68
    0x203880300000714100502039460030b50040c40c9550010baa49158418605000c01d00c40c200520890b05256085521104a440c890609802130b20710198000d400d4420010783c4000314200014043c0510322644e00544d5820443c141103280611030040e00280b801079040811610b0781c08011182200d01a02070b00361144034500000740030300c401c0c00003d00070400c1c50500f1810402500745051081c2d0b012503980801b540c85080480c0305a0f60b00d2030795a00020100120005858500d024a03803051048900f90801220741704144d210303800400c4e004000c1900e50019000f410b81c140d00d1600600300f00d29104480e0b882c859404690304400340f1050080505032511305040d51560000c40e0000354000d01190014400c006080340103100c40441d1605500840c0c103591b107590b108401480002c2280c41d2822101802e60f111103081c200c024008441c0d40381d0030008031003912000d000d03d00c05508290705007034035000341090482005074090245c1c0c90070320f00e044042c0202da8028060350850710000c03452441942c0e4450 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 446967446 1250 446966196 446966207
    0x40b0f28090c020c0a060302041d0429090d05030403091419291e0c030706291002030307141b0309120601030f060c230c0f0c090601030c 60
    0xc0220401600702200b94040540014914145070b500340c0365450803554039078048049014902480c4100c0b00307045130714060800301e400100d820600603188207607a001d003140e100d40f0b0111080442d00e491580f4102b0461f140106000341c089686507070615525526040d5030080064006001d20303108244068060030540e110107811101c0c881007069030707594007501c1d10302a50141c00e44542d0000c400c00c26801c1d07001d09a0307194081c1c6105103c1c2d036035200c804aa00c0400708080e5000440658190b01c410f00110f404a00507015002c0072003442400c4803103034520407031400300751150190440c2c040e4108408201d0740f130394000b00b00d0398042e4244c85d02070040c0b81d010b84110a03521400b9000340840c050200302192490300800203014194003110346404540028001c69100c1c0c50902c0044c00d00310351401081c010880c00d4120306080600c615040d03020311400d5014030110301c100c1018100c07403900800c001c803e040d010085d01400181180c002c0850000641c0028800d600007005181007584030401d2603d42c90161 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 446968696 1250 446967446 446967449
    0x20060114060d140a052202060d02090d1a010303260f0601020c181f081f020423150c1e03040b16030e0d080313050f030708030402040b0f28 61
    0x500c000d400f01d003428040d032009000c0548412224100e000402c4c10700351040c0c5104804513901030005800e00d03000041031070094003c403400540040f000c0c802000040c0c0780203500b4103c1d4003a60b02c240165411828010142150600021004021200c00300c02603400840300e107510400b5180b1002c07a0780c0d20200100d0500b200741c0c0b01e4039004108c448008400c01d020185103441402c802c3c449205c17440d0844c0da120941c480c24818a6501d400c5060b00305a40264071a034040703000c030300000162801d0b50b9001300f0302d18000504d001d5803282e810010340b241d0902d040610000c0c0c4416100c2107034100680341c19100d490fa400007004c003071191412001044100014002d6070024090019101d854041210310344030461819001280020f12001c0031071018540801100b01c4290002545411503584501c082110905040161020300c1a000882c0224404000900c54103201e0065a6201d041510622041c1d40401c6100c48c0b05004080203541191101800382d141351a40072450317491100f2480e03030001180c00307a = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 446969946 1250 446968696 446968721
    0x80112230705180a05070216150915020102030a060b04050a090504020415240f0503010e1b03070e01080604020c03090904030e04050c030612070f18180320060114060d 73
    0x8985a041c40141c82150051083c4c628034002c0c80607940345e410491b25a5161428003098849400040c8500c0360716800400d61980c05051880509460f03420f01d00c4285642803005005030b4001007001000f010038050b0700028500c5401060405041070006690902c2c01d006031640d40d503541c00010107655070b50700640a00c1d00f00303d040180c0c8548a908038448140b140c0381c0000651006100300030018400d1410f58800c48040d1b85090641e428000b0346515010042c03c06241c080d50182c078149414200c1d8021800b448098541918840e04c100014000c0d00c40100080c0c41184140300c04940618088229003000c1310485500e00103946514040e076001c842442401e0304186007904000c0c5000c0c12100542c060002150f03006510400044982c0c0d4640301c50080c0880d9100c401c800b00800100109011000306200c03034080b664501303a26102c41c0c0d01c0840942900001c8480340c0201c100c1c0325904190b8510320018002e46019810301c20a5071402d801d07040c0890080308005410b4201020306c0d0301c06550340300d0 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 446971196 1250 446969946 446969959
    0x80c0405063402150a05190c2001030c03060e1513050a020a032f160614060f06070506010b130b0c0c0a050d170a05040807030f03080112230705 63
    0x40d0040d8004a0010b2480e0881c065142c0604400d07418501900b910f10180303095881c6450464078000c90786440c80710103400300500603a90a500d00250050140764400c9210091020003c0c10301d00005040d81d101c14402400d05150500c180310403c000d0000c02c0d07201d0b2004141801c000082404140b400e111050803ca405140c02d0500c84c4851081c1c0081160451950341480703000ea60150046200005800050300c524041c01c105001a581c40c0c06848014200c0e8508214481591101e90613210b0340c41604002c2d000b4007003045031038900425903041c0d421003034827000e00700341c20365030b5441d954070060141c1209003101240300c41e82058582210006402151550f03910f86c1e0140c440341c0c0e03032480c10030740e9248100f00011000c00d040c108620172212041d00409000b802503111b1008003110341c841c05c00ba00c2004003c01c400706440030b08000c0c40000f1403003003e011464581c10b04006020000603049100c91500500d5071001080141107504802c1c2190402e41000da490f40300142e14200e0302d903105540090 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 446972446 1250 446971196 446971267
    0x6040b070f02030706081311010203090301020a0804050610180506040b0a060807030e01020c0d0c020a1203020f1c0c021201060f090f0b0303040e0f0a1113060f080c040506 75
    0x2204002200764910907011103016580f52041502e0070310003280c0c55000110f11480010220311100040f000034030042c01505c3c982115038000c6426680041d03510b501007407113070080c00704009040002e1a4401446091054000e0a245a01e141100180c90b580d40003511400802d0f80341e81c50707600004501800401d47d14101399580c10140804104580d40d40102e482d0000f6100000410300031948100f4004000c2c1ca4500d540480680307043d00145002d0303070000c2c42604046540202c0421614025009070014aa06184c000c2c1c20392a20751690154002c039100c0c1410320701a190002c0c20086a03644c11620151440781c201e030510b004003866030041100c03007401000002d07161119408803545d4481060188025030304442455540e11462040c80300c00a01c5400291909101500103600b16405841c00300d00c140c0140440d1141d50848085412800f040a6082100e290003590540a6003924100500c8514001c01100e040d40100d100d10b6001d200c0c0002c07454000c410040360841103021050f40c4000b580c = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 446973696 1250 446972446 446972453
    0x30203090405012318010620060f040b0c040806040b190c050408070501020303060306041707063813020a0207050303190e1e0f010e060307030c090621020906040b07 72
    0x2c810049140f000c021103451030540c0c100a802c5d520310315540c500d80560359207003c000700c40c0d040c3c007000444015507010042400341d64041c8400d80c00f074960000c4c002014106800c121520f520060080690148d00300000c2140410200310503a103d508002141c009030360b142041040d210071001e2803000c2a18142010882a40190251003641e020301d040300c0c10551184016a9244410b03240607605902010002e4000b45840f0540c03001d0749558801181001b10720340d612015511300c443c54000300303003094209440e95125184210040da485c140321411140d000310100c4e008021003071071307100013940002c1e21070903050080254000400b809000c8980d100c0009141140511a00680c1400103171103404c00c110798a046010450075512442c0d414003107219200401040c9070840345400d05120603071115103200d60b81d50029601c070300c80343d403001b060480c40c8100003231400107075820000a1000c4012a0b8510204070540c0c1c01543c842040010b079100d98190000b0b102d23001e01e50203603a40d10b10000f40e58040 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 446974946 1250 446973696 446973719
    0xa020d020c06070908010e06010e040302072c0a090201200304121103100b0a060c030e061606050603010e030d090f020a0b07120206011d07030906020f0418020a0e0d03020309040501 79
    0x43d8880c3d94840c11096240c0d04030314241d9080701d40c00c020691040005000d10010081400e810510030300444002e01c1e512503041c036010b0346000c80c0d0348641800c00780207014405046101903000305060310030010b1854560018156000f09040e076100c40700c4030b40c1011101107080044602400071000c440d065103216207060403080c4c062061040c0280580c403000d41c12003115000c0d03a029010300400c0c1c0d42110341007110407070b8544488041a420411030622440e070035110382c07004140b840b000100940302c003661400c22000750f0740e014141e01d000360314203810100c800d1004000d840900c400481d011402004c0b9040000c0252072030180a5403111402100180c8195014000c03e407480c03054441400200c400c100590722842d00b4070500b9116605002040000200030300d03c40c0d4080711300e0400103901d24180e103c0c54200e07002580490703642400040c0511181000158070070218042c0320041d403801070220f100400781840a016030b4001d040c100340200416009005413250010094010041507a43e90815200b = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 446976196 1250 446974946 446974951
    0x305030313140c0d030f2a03030b01020a020306071409040606171b09060a050c0109060f0609061409180d0305061f140f0706090c0501032f030a020d020c06 68
    0x2621442d50702c54480100c0d0200344882e22480040c040340c1c0440082d1003d0314105035425404041243c00e40c40d8039507050150000d0201503a030b0801e5010600b20b14a006421100505400c0c0e06560000c10540d0050350f001803e2070380020a80b421038050030010b03040354468000c86840d298451709000c4040bc200b50f00803040051114080c03c55500780d1540f10050500c11002503149159403000c02c01940c542c20094002c0c40f0410140c03510a10b0500c002c55100e0071130700302e903504649040c1c032682c42602c006900d000d0000a0600d458081102918141d0090b00814106400700c0c002c0180500088060690190009003801c1800c1900c0c0110800c60b0300800174441154034502c580b0024070518006403412224014021441d16203161001c020001d40b80b550300550408150640104010400900d42e8010319260500c12260308000d40c2c104000542030f03401c031024844000c0d2150b01060090804946804610b401c0550015500d0300e039038000101910801041c3c440d0700d800041d28000e0040001a000d2 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 446977446 1250 446976196 446976203
    0x50301140f060603040302030d02030411190303091e090b0d0209010e0a0f060e070c061e0f060504050606040b1303080301081e011e0b0307030218070e0118120c0305030313 75
    0x1081d602c0c0030400c2004e02050f03a0180042e80b040c07120200c80b1800b6401150014003480074501b88448010000c1c00c010000c2040309022003d41004004054102401d9000f4080070454905e1800440012181c1c410340361041c0305c08562101c54510701511149942982c2c1c0390064540c203803568513200000401d030421f0b500458914035080d40c0105c8000984591000c0e90850605008141c03184002190582403442040d41c50319541d03010342c076a84610809140705105240d00104540750402c4c0c109080740c256a001501803410041000866628001141c065880a21a050b252500c001d510410040170340c01c0208080300c0000003060b801f80c0042d206400b40c000483c40301c618400414550b080c0c41441040c1c4d2440400000c00c040fa000c240d42040940300000f408030350340142c0e03d8000404005412160031b50039116841845092940000030b92074440003030a00004d44402144800880d50b00f510824005190040842c0e04000403008130400841d085003c42e900ca0420f102e00d03940c142308404089 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 446978696 1250 446977446 446977471
    0xf12010807050a060903061d010e010b030f150403110c06030703021207032702010e060703050301080601080a02010f0f020118050c01180b09280938011805030114 71
    0x3020300d451090682070390b907541d450101441ca596103001c05860162320020900211010800d1606001d100310310300360111000200d0104450300a05041040d00f0021000c20381000380106650600c110a40780c0044e410710b803800d4409081da55280c1030580c141c010640c80036000050251070382d855000740c00080004421520552600c1c0401c0e8102c44404ca6044040c44d2134040d0769140408c9066249091801810446894462240003400039800134074100c010880102c014000550100815405019044002e005034030b1150000703088000d190b404036041251070208824203d2007904441007030b940c1d4205070b401c8002c8500c1c10380c1d199155900f0307007800562030500c03014114840c4601482100d01010030705103400c030120107002010025810401e08200c4007450001b07141e40818101000300004040040d030880e10071415142c5410440c0381c1410199800240301ea406041c50540b014580309003071138014440d42d2140356022200e19401030f6815447c0c140c02c42d81e41180340480c1842000d041460 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 446979946 1250 446978696 446978699
    0xc0604060b0a050303090a0e090316031e0305090a02040b010225090e190803040c050904200a1d04050118050d021c0f03050912040f090507140f03060f0a08010e010b04020306240f12010807 82
    0xec8080318001c903901080c662000c1035140c05801c26500046e1001700c18410389003000d8040c0b00340c801a83c0554100c0c070061460010411001005208003104803000c040508683c00045040301c1c2c0300c5203d00c0015041c4500003001c01c003004120700d408e500421010385040700e1846d01c1d0501d4800c003c803403000a0300040c41e00c00307020018a000742405059030100e103078201d801140d40c980e0610010005200300d40c00d644e0303007480c420015207910022925921a8008020035004e402c0002d0401220606103e02b01c2006540b030b011841c1c0140c00c4070340c41380c814540000e0581d40c4040c00743c035200b12610b1100d542c0c0700004021842c080d500140809a824844007030220b40c6071060101c07140c0036003040d401e0440600340010294030007008001c6800c050014803184080d40d440001440700071681d030010707980b60741d180c0085000b06400c0c0600c210102048401710b0442c6055070200e00742005c07030014192181d030521810f0400300d8414058030450808080c055071110000000c40002207000c1c060000301d403042000 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 446981196 1250 446979946 446980007
    0x111303030c142d0312010b0d0b0f060702060c0703200f1915020a1e03020606013212090109031814010509060c0604060b0a050303090a0e09031603 64
    0x401c1010b0b110b042e000000c40000b0002444220400b007038402c0d0f55800304201e103005801401010ba0302904021101540d41c0000110b04800c444044902a01841c0d405282c0500e41d500c05058400c45501518810b41d20b1160010040c10002d50380c0004010221510070040004545021094420b0003039a160400640f22410802e541d0b982d00810f02000240520a00040c500611911070601181c0110b5406181c55a1800341860740040c1c4030780d1003c0788142d02d20501d6070412105400440038200f80f80c505080070903030305034134001d5401104c40c0440c00040c9220348204c41c0840d10400d080c4000d1008500302442e0060282a00c2e4030b069001a50b00000d248402e41c00d4840300c070447d000b880700780382103c41110065855402c01c801c8517070b1001c170921070800c42c4c041c00d2182611540c811203000603051001d40801600150700e401503070080d44280008981d0383c964075181e6043d51203240004081b655490304981c40c0d84a240840303550744922008a0040540022400594030100740342e82d20b58900000 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 446982446 1250 446981196 446981203
    0x50c0c210702040b0a0f120605070c03021506010c17070506091209010f0e12070e1f05090c19020309040f0b0d11010201061706090c01021906111303030c14 68
    0x400000d400c0800c9103400516040d0f005801d41a0003400491090740d07110041006035030360754050100d2907012001d04040003120b01c0348550107a41070900807405011a00c00079500c1c0700d100c20005841340743c1d50100d91141e0080e48904003140d80240901503c201c2800b0080b629006030320100c0c0c641c03040f80c000c1288072401068091700c0345560300d20a402e10070004011204104110b03468818440c0318030122100380c0f0b07400858500344036014001c2140c0c919140300ca480b448001071094401780300c20154000c2d4001d8030010781341128012030310905940c0b41c02c00000703003034418070201400309443d10844005c00c80d00031001e420224001c440c01c03c00e104a0780014030944001641865010b111603403d40b000480050050005480c117100024110784c84905c00102e40e1025400c848042c0c0c007071420840207010030040b24141c45000c0c8041d0500c030006000c000b012520b14600240032030789800410b03904005000980f41c420811540c140c0806c0d07030b24100900000b14032401514424983c01c0500400d55001 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 446983696 1250 446982446 446982493
    0x703050d0b011b11061c0c140a021b0f0409030f090519060f020f0106140906101707140a050a0305060306040b0703111e09030708070609060f12050c0c 66
    0xb218031050410183c0d0703540c0b10820500031850745c0300d00280300820040c0e5100f45d01e800050850703403001901850070030000c1c004201002c070030b003004103041081a069540c0442d40c0d0030b460b0b4040350079001000c5501c0008482030891085590001d107080151000d040e8881040c84802200743c440e0b080c10b0391284144058104051401a003401e82e0200401800b4071070750030a040541d05205072003422480462950039079040e039001c500c40498918495096150924815400101c12505460300408018029203d82c01307070108440d0402208000810080c040c6400b555000c4840300300c151355514001019000d50000d00c0d40c0400203142100292039400d000070740c2400345401156221042d541c9a204401070b200c40840312141d01e0301401010520007148004910504003000f07116220f0f030540042c0341c41e000740707984501c0250b8071a0b10200806500a04001c007541e0756031500b1305000846400035180040c0200710780b0741c070300d203407504202c625814440941030016000c02a198103425421100c50b202910 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 446984946 1250 446983696 446983727
    0x1e05031801020c0a02100c0c030b150102061e090313080d08011706040209070302040b03150f010f0c0f0309031208010f080106030302101d150603010c0908030904050405010f020703050d0b01 83
    0x1e00000503280c961b22250b90701c10540360000070829103a49840f458031040c1e000316901006002440f051700300b115080d0661050a10081a1924014080c0c110300f034140b16880c0d000303941e94408249211020b0040351045285100c1c1210030981e541c10055903101400c0301040007508020001c1b41c0c07180a4102e11004144003002000c003525541c080219204d40900010145036080000203102542c81000c6c41c490020104e101c040d03030729543c040c0719010400c4c803912410083d050301d00c0c07120307507801c4104101403d81000103154a50380c24a415106d00c0c46d0780c1c201604031078a51010320441c0d90b000e0200c505a42c543e40c01401007070380d980103580c2650210b0000601603000201c8180c202406a0f004c503200352031483d010780480502c00348143c01c0403822b4140d2031040c071900e401c2010b43d090074010016420400c5c034202030a0b5152548040d128041c030403400b403099450b0404202841800d40000301c03045c8404004658851041c50068a1584070805000d840c60404000e00101e6002d440c15518010a = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 446986196 1250 446984946 446984953
    0x60212030c0d110412050a0209070e0303070609051009060b030d02160501050906040e0106050a080f0c03150102011401171005010e06120709020414040e07241e05031801020c 76
    0x221460380b14060f02c202c00c140040e001d41440000394a1900d88030421049009802500343d144284c0180880d824008042e1f80c203005000070a0710f038a8400100302c079107035500500001054406407074003c0c14642d0070b64400f840d45003029019014010564404020001c2c00c8040711509120f0000c140c0c1c80e0650103010107000304070004100055406200207001c280c03030080c80795207069110180b040c141e190a0700450002031002c1401d51200e0307000a0051b8000000c02e43c41d800c9031421280031030040c4401440300c0c0f082651805240d13940d034001d40000450000032601248a50703122001d02c41d851040c008a80ea0320320401c0c2d1031403128082482100c1c1070310f41c110a0644566a030405200702c2c04100e807004190307480395170f0780083c10010304e201910103844802511090414840200300507600c12900701c160607004180300300010080c0c0c51108000701c2d488018040b01d484081c0b402e50b101000e507030740e005000b812004512009644100150312514030112600114464000d58078200d0003401c401e282d160340f = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 446987446 1250 446986196 446986207
    0xc06090b090c0f101b05160806280b06070c030b0601020d0806030715050c100c030f0e0a031107050904080a03140f0a02071e03030c11010908090f030106051504060212030c 75
    0x52003005c007056100f80300c850a00c0c41410558401d03192100d00f040503009404000020300c400c29040c40500e400c00005100011070040e006e8140507403000d004254101e995880343d140103507443e010141e401c0710342c00100c1e441c43d456a9082c4108401400c5940f0360040c02120200c401d080d003e50402800744030050020b202190901d03000d840302e00d20301038040e0305002041c05600c9840d90104085503a84400701400b00d201220150042c0544032003100c041d0542c0c0c1040369a0301c90460003d403040c1c0346501454180c0403400d19154980c2024141d400950b00002d0044c02c00c41480300850090240b4000c580d800c010401e200d0721002c2c0c800707005131204c8654024800204600945a402038410705000b000005151400c5070001c00340460034070000c030003007034484240340300340703074202c0c106a107030700e00c1d020082c4820031031640c1d00d2030144609204640301d140334828604454800f5801507001e8100900102040c0d4007041d0300d80c000360894840c2e100140b181d902601030781240300055070b0040100c1640181440b = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 446988696 1250 446987446 446987479
    0x50105011b050714040b030609010902011b1115090d030305041a0f0117010f06031109070302031b0c01020c0114011401030207030c0201050a031515080c0708070b070c06090b090c0f 79
    0x984c480700c10740d40142c80700140c0c0160b540c144105406050180000601c0c4401840050400c0c04203c0c00b41a589219102090200b9601341004204010460b0b021407902da000c0e40481ea18099201019088140c1a040300c0030541c06502c03030790140f4000c1942003e030480c2c1c68030910084008031494008086218010004c09101e03410100300c1c410b121001049201d1444030000c11180c5581c03080e0740b5210ba8520070229800e02264203a007000c05450194038600d010f41c001c3d9a45048244d00c15000b0308000f900c0011000294103031000c02c8608802400742e111220f01890701e4180c203024009038140003902100e002c3d030280c0700306e0b4945985521454203400c115001991160031540d04c1c02c05140c0c4a817903400c55280d200c6505000750030b50b1401c030b1881d40d80307000c0c005080f910001d040500c8a0710400c25240881e0905d020b560003168096182c4100d0303030310090200c404000c5500300420305070410141c003040203000720b106442000450304442c1605001d000300a01041000d042c1504079a40c0e00504001 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 446989946 1250 446988696 446988719
    0xc030613171b150414070f1a0d050c0c0d08040209040f05150403051c060b12091501060e130902012f06040b04020a05060705030a030f1e050105011b0507 67
    0x21000b03030104081804607034903080f800c0007008611401aa494841000304110400f900300360030a505000820000b810094201c21401c0c584c007405546144a140480c9071501003004c5a004420200060006d030a202c0d12540c2c440e08140d882c2c8603d800303180c00c048050751155150503c03450300144011501d46460f02c501441110211058401d8020050700760020711000c1c1109004038441d513900c0ea03481d00c003840c6108003051228060781001e03060007000c000605882050707400c1c2400b0700c2c0883c41c0c1500c82c007100380d1910107101184565a03040000008007039800140720b20304500d05031092203084403551528022200316040090105102c00f03400ca160380d0094403c3c01d6200181d8000d0711123241d030080c6892401c003084034204c440c480f028081000714140f90303121800a004c1550294106001d5a903410313100d0040b07402d1a41095903516104441c03020a410260780c1c0c505441c0c00314030020b5a98103001c0507210900402c1c0c04a03180f0b2260006d0016896400d0f42e01642250203407443e20304040c2001c06 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 446991196 1250 446989946 446989957
    0xd1115061513170316060b030c0d08120106050a0f0f0306120c030203070e13080705120f0a02070503070803041e0902130303081f030308041401020c0c03061317 70
    0x100501401c090380000e001c4600200038941c1c0c510381590003185000341c01d20300c040c1a0300c0034180307130340081c0082001015940394031960142c1c400c001113421821b840200f403a0200760144a54008410040203042c04541801091400074141d07105109a80301e110540310391040030300201c0051080e00d400803005100f0070204034686220328022858070b035544941c43d046d000201d02a030301004250000c008601d0100180c9005085408880850b85001d82c030748007100565040151036000700048039020000107100ca041c0c0c02c2d17448a20180c0b0340941014144403a0012841c0d13501512484c007010903c0d143c0040c0030001c850b90700004500d0a4140080c030348284e03010441030b0503048108500880c01d51132030b0028010240502c400380d85090303e03508004103050000f401000c0d8540d8048020092100b400d2504800d80c1e4060810f070105450b01d1074140644001800c00c80e44a51001ca03086a00d0740d4086802c1117503107022802c6035455101d011241c018014040c1c0010007491342c4403510001140c1c0c4034064070 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 446992446 1250 446991196 446991199
    0x2306011112030711010e0105040804180920120619110418241d07110d050406020714030a06150b0403060c032f090d1505090d111506 58
    0x2850600072800c40c1103150002e03204040410394404981001200910401850303014100c028840b50600343c56120891040b03004002e081f00799206010031440c030a4120803481076100403c5960000c190401c081046815490780d44640740e00c56000b910b120000034491700aa0080c00e1100000a49001e914028060306200c070348042c800f4400010240c1c4a01a12101060510703000b1070048105590030040010384903142015028016003806140500080100f01c0e00c4944643c8034031341c50700b14040d0b40d138030202071000c1c6052159440c0038044552103805041286c0700da400715048a41c5032006d511020707544d909095007692194030820086601508881603003034000c002e24254540312140b008499000740c2090703604540700c0d00031010f0b9552521448180081c0240381c0c8d80942d50034400f43c1d00307404021501070300440011410076103650303904002e800d5032940700c07440380ba40396001200c2402800342120400da44d070060b12110800940640e92647e003c50848000d064032008120840c4241040502801e = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 446993696 1250 446992446 446992453
    0x91806011107080f0111030f060f010c050d03090b010602120d02071e0501020a14181e0d050106091a0604030b07050403171306021207060203060d051501030623060111 73
    0xc002181c2402184003800c0c15030003400c115140d03428514255404040a8000c0040c00c03c10024001140a4000e8100313804450409140c03a980004a80542d000a406002e900404014031035240c0c040d480052400c0c8203551800e41c0d603030780e0300341030381c4030501108605145042000050300c400050350007082d200d0700c039101d445c0d820040ca0352502c40b0008405400c42d80d0360b50014052441c0c94016101400b80c00c501c1c940d142c07500c60644081300c1c106280c8200395008200702c1050000c00b4040e25050000200302901e08250401c00d0300302a03020b011240301d8600064541003e14403006050505042e81d040040c0c0742c186050701c0c41e982c0c20030038400248813400f0080140700c0800040d0030441c0b40c1c40d00000074041e03140ca6440713a070400001c0c07030704945c03041d0b066600c84840251010450015900c02c1d0341c0108005891360b80d000c001c90403010660000410360b001d15603c03007071080010300103a41030728025801003007645105042d40006491442d0641d011a00380800240d41e984920f42c110885402c44059 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 446994946 1250 446993696 446993717
    0xd0b060408072706050f09100801020a050a090b030609040803040305040b0d0b010201150f06050901090b07050109051510050607242013050621010801020702090c09180601 75
    0x20350030074200781c010b40c07881007403e0000c0701c0492058022100700385468004200301d51400b000245248000b180d45030103444598009852182136024110003024400d00a43d540e83c1318140c004c0099111059440c04500d006201280d03c0a00c40b0550344243c070b01520a80c0c20b601d55071a11405500010007c400b0040108001304284c01e104018080b00c030034074a4082040d9901d1400a4203560181604503400e510100080058150310381524048600c1030601680d220f0b0014012a4042d9098000c50703a0008002044020880c05502c40c0e845140114141c540601240d030a07000741c2182594480a480101201030001c2d1030808010f12149109001c0d400704c6c03040058000c240d03040060740c0c00001e142d50b0302e0520a46030354804d030300868440280710949000c0750751443c5009940180122409041c0204598400481580c11341200741602000c14138550303950a03850b03020398000f54080740100c02003001704d025000d0a4058030141e80d0b00405031100014081c404401e02c4400030401070401150604 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 446996196 1250 446994946 446994959
    0x1809020703180e04030f050c0c0a17061303171e0a09051b030307120e030f030903011b082415041a1e030a1514130606050d0b0604 57
    0x80c100c891203511641e900c00b0304554402441d007240c0d880ba400c1000301c0010003001a500404600030340e081070a1694449801300966450a940c41c918160422000d0034041180100d0320065440b94080104484590f62035400f0f5a949005100700240818003195840c4001c1102c80e080540c042601c2d48100e9405e06d42195080380300c04150713240c6500c42d80c0d038407000041c40b10a01c46004844080c024a40d101404040420b40d244120030303018117862110364409020501c00c118030148400c0007821078400100080c0b00d10f403694091240d543c40396113004281c01141e1411043c14cd4040880e40354800c030342c2d5411040e81300e100c0b00c80014401240b041440c142c026035605202c0c01c0d41d248280500c5483e43d04180704803120702c001d0f508400900740c05021300001c0c08070000701c004840c1101c3c4c46880d101d0304d40c8c00801018000d444484061482d0725140410318113680186d4210b05441225401040048250403030308880c4a4010100001c1040040e0f40000400ba003003148503c0e006050f491509031340e0807 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 446997446 1250 446996196 446996201
    0x28060c02161403060c0901120b18040804090501120803070e0102100c05070c090603080403030c14060f070824010c1a0a05010e01090c0206180118050d020d110606011809 74
    0x8212803000d100072100380703000f41000c000c00c0d0303801081541001e1610822400190140100c4a02c000440b030710b40242c01042e44994004030361440411203106880d04044c078090440b50824028001510318100000680c04021041064440c1e004102c05103140c99800048403d0724444000c541544121012291001490700c19280a0562a594280c8600300c0d494072a074420b299600602c8005d081207010700110b2000ba086804981d41800d000021446c90b04c1c00c0d04040510030140344090154008104468503648002481000b46603039a40c2a0303620ba00000310f41c41d0b00c03000606e0100c03419000c6041c9039402001d024401c18019842000491900814543c00361422281801c040d6180d000401007a038200c0032603030142c00000028046604850f40007076407440010a8200c105641c0c011107101481c081d40040c5a0035174856090307152800c80e050855559440101c0d43c801071203820020b400c02849007040d800d9643e0200003030000c5880d224011200681c3c080084d00b905104a41c00041c90700c02403 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 446998696 1250 446997446 446997449
    0x61d100302090703020c0c18180f030d09260d0b040203040b0711030c060901060504051308090d06060306021b0f01060617091204080601060207050f0609011404080a1428060c0216 78
    0xb0111180145040280309d1003140c2ca001c0c0d804025480620411200c480c04415a2240001ca0b4000203a064035400c090030400f51000e9070ba010b030428510030b4000103402d40d00802c2401d516410900820540b10180f10480c0310840c0c001d04911104030100304294414031040d040205c00d901203904180d03a070710040d03082c02c0d001c0d00d100c810740c2c1d0350714010006820b00d4010b55034003c01111400c1480c29440e190410f2034401c250303045115000010894040140b994443d40207190488011502c61403207242600007441008a07200c5284075482d2400b5400038140524000d5404542c0d40b8650a032071101084061180078280d05007900482403800d5950a00c800070b00300410300a4010181c1d0351501002a0411290750040740c044c240c6c070910300080e40c44050880390260030030311781140341466021440072103000c1d54102400e03034002e8041c48010f22041101e12a202c9810ba0140e88004426010035001420819181c15035403107074140c02070101d64243d011003203500c40c0d40152145000c20300c001046260302c5 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 446999946 1250 446998696 446998729
    0x31d040f020a080612070302060a030506150a08100b0c0c040504050307020405040c150305101202030a06020307050d14071e03090605160f030608031603090306061d100302090703020c0c 81
    0x100d60402c0720902c5c01d00d8410034003a0203100036008182c00c68010520398401c0e0200002030545400100d030054031407550342d10f6200d415001203616400c826000a0080d60150742e9070320b0140c900c030300124002d0a500f0449009609540c024900701c9410341c14080a003100400c103841a000a200d2030015840d01d000e42032189104440101209080c1111500545980703d6030301c003003600c2d00c0d08201640200e0101c243c01c2e40c03105002540812241d20009190100400008103058008400d01025071342000c05800f15046000d41402000075442c82001010710484100c3d00285103407243d111314019000010035100e1403484c01144078461521410240c40003641d141e10445000c40c5510380c1103510000c1925215001c2c64103202c418a00321074240e03240103c1070040000038241f4201000c241c01101e0b0040155030002050001070b5031a031712105d9234088800354031035054810340058090384007505840266a40241452400e45441104070003d4000004482440c4110058054155500740038010320380ca4 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 447001196 1250 446999946 446999957
    0xf02060f040303080f060a0905040503160501050601030b06072d1b0315091a09031b01050a0b01080c2203151d1203010e09070e1f12031d040f020a 64
    0x20b0740c03400510519004010900c601540c1c01480b800c0e0745c0b580f9180003221203101c8085416100c60401e03a08510501e4030240d841601111000100030f01074006030312580c0309032800c02c100c24403c41031020794800c500009100300940501e00e01d1012490341c410780c413466801012443e070b4295540d03260142031200038488452030401030401c10007810856511816811200c20b0110190940c0e9800e5108680a45050b015020341e0014461103010419500b01e5150541e03007490550304230748414001c0005803800d40545e420f25030010600e50250801902036081001c0c5e4500d0205c0c0c4000c8460303090f144d400300904507080c0d41800408101200e20259019004400010b840c0d81001d207103d035400e20000c21201207410290454214071024003c1d0b90454882040c5620603030754109100d070a1043c0380d0011807031240e050007070120541e9100e508903420a240c810f8907140f15295190720100d002c8450b0300400088401104000350070f4144907000c040040544042008825401c150f010f907042464080000740 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 447002446 1250 447001196 447001199
    0x30c0f070506090d0f0524100e04050303070e0402040b1c051012060e21120703111c0e010c050903070b0909160c02030d09150f0207050d0f02060f04 65
    0x4400c0c00100000c00080380c0e0186440c1c950b502049104014400143c000c0d081c054500040c46018025114040c20078095414106080b21502c0d083c15010790f107070040149005008900d20440c5403155000b1500440114290740e603400085034001200b80e005504a5000d01c0001001100d040141000708407110481ca886c2413250100001c846009045400d040f004810070801c4100c240360b0410080c1c1c00c00703008201d0340390308102c482c605642c0314801e05110143e1852610ba29041002814200070850821261034403004c030200d00f81c0d49011498407240381d00308000c01042c0c805e11454400d0f40c94401e03022904c14000b844e0703142181c2141110f640801c100091720030251a0901050019041c002d61150424a8040c041a000e0b00010709004881d0f458011001041d4064003da1024a5006003183c1403030b1a2100c00501c4840584689041680e02442001c1c400d4001d070702c0c0880003440360303005003045403800c0304105820f0a0031000751100c0d42526012009602c41000030030414100b091a2079869 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 447003696 1250 447002446 447002473
    0x306110c0d02120406030b0105040305060903040501021b100c0201110607020f01060e010b04050d080c030406050a08130f200307080f19150b06090310090c05061e0307050903030c 78
    0x140d50380c40c0d410443d04068201034000308010207840964815190004804e0111001601c242c41990009050380c80f52008200000c00e0020080090341ca00f039007595410850341c9000d100d4002e24000a035800002411081c1d8010703c01c0812100d601e005141c40444680c40e4101d0500340b01e4251085401600a05101502d641007401204000e281c1d03201c0e4240c2c0c962501c00d400d44076000c1c900400d80300354102c0c1110383c00c0c801810180c0d5440032103441580c1c1c0d510b94654010304554051803242d4041148a00080c41d08620441185803991704a00250081c0722983e507104407415410080210702908100c0c0040c06803010045c050150a4a030006d01c030b2101c140074450701d0000050705900a6405d004070420002d0401c1035000654407407a0404034180c90400001412401084221a00361003580c1c3e6680740c0340241d400040c102d5002c2c10000740410303101d1042c0092481201400c8050904080b075501001e4928001142c4c40181307454410305050303503030001a056920402c5800c440c1d500c0030081d817600303 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 447004946 1250 447003696 447003703
    0x105010e01050d08090402031005030706030902040506150a031e06081608072102060906030406051801050c09010c0609020621010801050115030b010c020a0f0608130317040c0306110c 80
    0x2d05000c8a10000b181442ea64400c650300c0784101a90085402002081000440d840c030f2801030b000080513615940e8503103100800604000d502a4412403c0101068450808114420b0020307000d0f0517241c6004007503082503010300311000c20250311102c01e01545025040512a00014200c16400b0300204a0f402400e40384a030150341001d0155001040100a80500c1141302c0102840341f8040c0d42d0500000c1c0001141405280304040d08041d000041104200303c590110f40306030b048403840d00e14070030340c280d049080320011030b4910484001041604850740c0117148100c0d40c203100b441c020862a2076603011441a800c00307080c040d01c1d482c44110030450385080c0070141d805040c1c00002040151b25064009201009510b40d410903d962441440319991054844110303040d0081c00c21030003a03036500884c00c018941880380600141c886400324071108292403d03001959055541c101072042d014441c031003240d40151089840070038508002000070305a0044012408040314481d1700d9800c4204410704 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 447006196 1250 447004946 447004949
    0x8011107060e0f0d080c1e0c0f0a02130f0207051b010f14040501050a0509040c050c0c0d020f090c040305060903090108010b03090709050603010906150915150813140105010e01 77
    0x700b640001c149040c01d844001681c41506283d842c100c1305545413071000d14a07912800030b4005e80302401c04242d40700510508000c0c40c441d410300301108e1641ca8181021900c400d07051030000d40c0058280c40c074a0300000326401c0343e10415003110700189080c1c6982d842d00d240200a00d442c001c00807030985204429038102c0e001c03030b0404003d81440718011006110742e821520690003003905010000c50075003110b074030074000d071005210050320030483d5070038900003e41550044410142e0034480e1b4088410181000495860065805040100500c41d140c0070407200c180c0041801040303000034003000010910070001a4003400b0004040e50f51641c4140c0014480c42e0140c002c401002c0d030400500540d2200080d0400440340382d850000780c15182c100019024118051010f060141400c50301c0010000e40b684440071900002010801c00c041c89a80040e10340080c4078080c0313a00d0000e13003c03c10050250310403e61042801038110782421203903440f0840302c0007150200169a40d07403070050141503602c0d100d460 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 447007446 1250 447006196 447006221
    0x106061403010608060402181009031506051f030e07061e030501050f040f1d03031005010306060c03030902150d0506090c09210a02040c02060f060406030c05190801110706 75
    0x924640c10f150700a0200c0602070425805254006640c41e41c00102c2c0e83c0d20440c40ca001041405d47d280121801001d210031408203440b03226140080008144584c40340a0840714040c00d580a05102d1030106040e0078070004406090689500700d2192245041c00104003406254aa0400d502160b0f081c10011640540039103091604e0f010050000c0e0741c0314000000500740860700407400303120b4101010060010710103001514410340c0c40e40d40d801e44010002d14800c03150800041d0381d0954400044040d15810b00c64500810700381c00007800441c0c803d0308540c00c03450000d00ec58188206040c0400010760200c1c00d07604004d641d64060005526224a149030402c0d8505002410846030500040c10405907600a041641605450702307a48102405261100341d0020001c0100d0528045c0194840c1d0049a058464024a0002130f0f55454180324110a4039042207400c2800380c10041407000d00c130b03480c058840c0d82d004100c200207081e11090040015a030708041c01252192074502d0501e007564080154103 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 447008696 1250 447007446 447007487
    0x5010b01091208221202040f1407080a140c04031214090609011205090106240207090216051b0102011a06030402061b0709090c06020604030806060306061b010606 71
    0x104280661404502003070741e004400a5070b00c1c00c40920914010004d0000e03038500d030390b030442d0020340010f01c1c004944880703000342e80503c0b180d441c200350314080b1843c2011401e00c0c44000e2000c02c040c10b10500c16507501480c19080043c60401092202c102d98408941070308103003c0c005418810001c1c00041da040b5134815080031308514006c0341e1200d0141c00f65007000c0e40100c0d170110f015141c5e0781c440d003444040603240c1401086a4104200c4007800b0704001d000b5050324034030032012a00000d84007480d4568644241d409010864145542d2034065881000c40251440b075640551002c180b040c440d690896101401d6403205001c003000290135220312031541030050000700040401905c40c001102e038000d5040702e24075038a00d840664040304e019140c20b9028188100c1c1c8020604415503400809000d000e03110041c1c00e50741ea40e2080b030340c9080481c4c0003030024400314049103080c1006400b41d034116138010314050521902810017189100c41e4107505c0613a0717450b2803080007080d80010f041e400480058490 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 447009946 1250 447008696 447008699
    0x506040827090c0f040b030a0e16030308220209090619090f08030c04030b1f050405040503070f02242808040b07030906020d02120901061214012705010b0109 69
    0x140300c42001040f202c2d001500003621114501c80034210340103403416100598480c148070030808003d00c01107203402050b110f02010303509061764406c1c002c03086a41c55542c464a079078410500f0b075165602c0010201003c1c800203103160050392100800c6201d510702000a122901d402445504003903200c01281e4400c3d440c248091011a540380c03a05241950810013055417030b120271585130494420340d80b000d814140390606200c031507038025011041034002c500c420022191200c04220445900b80c5004140e54402c0001030b00089010216942d0f0500081607008010300c0f94034401d14a425214056003040800030744039019107801c200c5043c6200d5603141100c8001d40100015022660180011307100b1251100040d00c81403003500300e2035405500c280295203800b081c00811020703402800148046d10b0240c2c000800049c01445031108440100e0700040341080d403a1903410031981c0232441178075103540b10b4900d10b614140d1000700006000aa00504801e400141442400c41f00503c5403a030420440150 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 447011196 1250 447009946 447009949
    0x1030c0c03180f0303051909060804060b0301062408010f0501020a140a170408060f1009110909070801081203090601060f020f06070905040f0e0a0305090d0506040827 73
    0x124140304039810708040394100d49200c48404404140d50040344400c003034010101c1055400b0b8083c18030703020351032000c28104966038401c2d282c03024140a880b00149041000130041451038000d03207402103025000082554a503c9074404503d07040c04a042c0401c088103c00c154540d00440e580e0050041400106d100750030800003c0d210170690102500c004401000307403400c21340c14846da44141d80d0011641c49030800850910b05280c006105108150107440b002135000c4081821241c07040034005218650903003004900b40050201038000303844000c040c4102ca0780d6482d0901d180c1d000e0400d580f1590210f62600d8841488d015410b080145100000d0080c043c25100004002e419900c150070103050413518584d040b0b2070210f1003400c0d443c03203104a10910030540c3d0020011400da0724192010b011901040c160101034902e50040301d015688204108800309100d07801030090036900404940b200d2040c4d8403a6883c0c0340c0706032010f0f21480c50004012500d044186205040d081d08450b004000e04050ba0 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 447012446 1250 447011196 447011207
    0x510080c0f06310f03030305071b1509022101060519270c270b090915060a0f03230412020f0f1b030114010b1617090103050601030c 58
    0x40da8144040300c0f040b50f007072074804000340300011020383c3c3c460031659a8202c1000c50702014030040d80440d1410340801c81580c032030009052500d10154000c13003218081c2c1d44840380c001c0074030610203070b4580c0d41c0319200c0141e030340c0078a000f0000340800300c807a140400120b05a00319900b0381d0269100720f25424465404805001c00c0d0412a004483c00e0b500ca91400c034244003100c070070103290b00c003014540800710031001e401c044040d0029619070040c9200f20300340c43d00c80040340068010040e4805040c4100b4917075240c0203606031303404000300850301d02450f1000082002c80d000300900001041c0e42d0940c6d10f02c043d915100702000c41551159030082400c3e01c41c0c0a840462000e800075000c9400d034000d10f44007500801a071020b000801c002c0303d568580c00b01501d9118030311044c0810a001e00e4042114003441c1c140284021100d129004842c5640781c0780083c00f156200c2c0c0e518020110b50840c099010410107940010a40c104007611035032030804000041c126140100198141840d10350009041a48030 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 447013696 1250 447012446 447012457
    0xf020c010f06062a170c0c0303161538040b1c0609021e0a0503010203071b0611030f04110a06020d050c0a0b0709030b090c0306160509040510080c0f06 66
    0x803081c240390b07203812040d100581301e86201d02074180007080d0115000d1807040310080280703030107031000d0711940145134041503224802c24001600e0513200402000114038054811170101c8400c00000030419080c07110341483c030012100782006100c60360000c0c2407450006007046501d110454041040341c079103000244e41e80220f802019400c401130341003c010001c855218903403043d00188190045110707000da19184420381c02025009422010000456007014025207005540307030780f241c4100b421400701450b017902d00440151682526009901c800c5e0102000850041d081c08000381040d141900301001400f66042c00d0501a8035120300030445598085000705501a03e40382440d41c1e10303000311135245440c4911002500d507104000a100c911904110680c00f100c1c0300c0c1001003416910090615116440c407481545c25410040010380d00300c9014450641d501070b181070060900c1c052902040448030100d903000c101070317441207080c07145000030048811396403000c55100703130208441c1c0f0101d04640101c = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 447014946 1250 447013696 447013727
    0x8010504080d0b040f0f0506030706020109150b011803030518030a02181302060408031209030a0c0213020c030d09140f12090f030619060e012402030d0f020c010f0606 73
    0x220f100c0c50b48203540e41d401500040c800d22074140709803a203012045000f4482640c841340700e44104200018024018024102855044811030a1004030041481d01070031540daa030f02d04114460f01030704914800044540023850282c0c0d0341c070762078400103104004103a8500c0e40d060311036400300c5410801641c40e503130742810040100b00018065119070b0900400c20703602d080c0c003d40c0100b010034046405507000020f01849030303500c584070007692120300300b940d04c0303106003003410001950544002c40075051801d680d444054601c0c10040c5017508184041381190005840c2e0700416807204012010f01c800c6100444803003015001074284040c2021074240c0c0e0317519100a00c0400040411950116a01c00d600341c0c400000c0076007034650528100c0364039042c40b002007403542d049a14144c0007042d0031501118290507540050900312041c1c4214040c045a001c100c141201107110400c040e0780c90b2016805901c40c191074202c0c000d42c6a02c02708a049096640c1102440415072400c2e5003003100641c40302d0071300004d101 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 447016196 1250 447014946 447014951
    0x90b1603110c0d03020606040605090402030715050d1b14030c0406140405122406060702010c050a200117090307020d0512070b01081902130b120a0c06020708010504080d 74
    0x1052907035203041c4030605040325807104000380c2c21800d140e00481c21600c110001c0350304000b0191243c0c10440c0542050b180a501a808801c084c040078170801755003003034030759242085802d11005d20b4188007626017a00d140d00c0001c04030307194002d0a41d0000b442c1250400d0450059080d86010455010f02c0e0140e4440d00040085001011401040001c00c44010b804040c0c8203044191020241d19907900420700190800d2046070007a00303804440061031801400010882d51030132400d600111086110100d05950b240208400080007883c5514144940100c0309591110f50a8600000d800164000c41ca140184003072810012440750100031142501c1d17040f2000e4103081240e08181c1c1c03408040b41342d1282c4500d000900b14081c0b00000908904a031030240440d0b6005101040c4101c50110807a4001d40050401010700b9540c40190028019800054100300052009008052a10800750010350740358013a0482848415814400000a491640003d000740d0400c1e90b0f66444a04c200c0425045c1a503 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 447017446 1250 447016196 447016217
    0x10b150a0f090801021206190f0e041406040302010c110a0b0402091b0c1c03140604230112020a050a0312030908040e0907060305060d0305030c0705071701020703090b1603 75
    0x14090300b804006880c000c4003c549035203003100c1e040c0c00b241e4141e030810303c51826010004400202d508281050714824042880380300e2900c10700010218002c2d1040b05d040341e102c000c00344800b400300100d0340324070b0090f80082079008c00752001401c1d80c9003015800c000d5800181c02440400c5d503106440340c000f58162204106581e80c03107084107070f100906407001071400000840390701004001a440312200001c1500510008030354070194101c81215542c52100001100041c40c0380c54180e01840156107a0850807680e4060209805d031790303036001d0700080c00b0445201c0705001503040c4960b45001a120940c0c00d080c1050030750300e03041c910b0303424aa440c004054a80b40d030300040000314070681d0010044410b050301c2500340f101c02103440380300c1801120b0029150400281d11403808503c0f0f40e070b0440e0151112450f60302da881082c206688810010744561003100c00004211200050b00058038120400058640e801454020000c00c490b6011202080060280910a01c90300c690011074a5040c100303d01c591 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 447018696 1250 447017446 447017477
    0xe06270a0f03082203060507080a14070804140f062a0724110c1209010c030509041b050408070906050f0909070b0f0c070f21081c0b03010b150a 63
    0x1002c4038130100120880030800002000580d40200e8051840d68488422641d00c603d0b221044603030004180a02da0130030404160700c24028500c00d50498000c44e541035140b08083d603400d1802034400d030f805006078010020010303111a04c500c0c1000c8201e0070484040c50b40040da00701100d9000c0c0203c050292040c002c00d1081100ca81c20240c6800810400244421155400e00d40300300e4100c002c0c00031103030050000c040e01c80040c0074121070b00d080d0b0507184d5009000540c0c5040341d00e034200100040d00b16684402c2854155802c004561950446946640c0d03214100325001d410030313505902080429061440601040c0e4908500001018060301c12900942d0766641c414944030711540302ca41d440b140080d1440b0a802014010b124104059084502071035490700c4040090710b5034801c0202c5040c3c0800c06440d0000322089075810345000713051007800d00b801890805500c07181680000c4840380d48605440142c01c0a0103950302074181110a80142e011100c00d00c01244211495842009001402c66108 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 447019946 1250 447018696 447018727
    0x120a030516050709091a060a15020f0f0d180503060f06041d01020a09050307050d1b150e0907030b09182803020c030601030f080a0e06270a0f0308 64
    0x1030b00201100d03500b942d12034075040100030076007083e2401102d010101c2500001c91400d40d002e520080c00306502e07145002600085100e40c042c0020443c0031350346201303500c0441084000d91580c1000c014154500d0109400342c9200780c0d400705105141c1c1c1e5098200219500410400d6006804003160411ba51360180003d0040409a06010b00e050a80400344030751001503014108211003a126094107076154010565901c0251040715800b1441ca140b50001a11a00355410145c0e2012030000c8915202d5001051031550440c2c001c0029413860400512494640c46081c1c01c1011418100000040751020802d4440c00030013480c1024000f600186a072802000280c48482c00b05d540d1420290903c2c41c4160581703003d0505500510072103480802c1450049a0b084c100c82e80142518a442a42e81e20007a250700901c0c01c0000b800f010034000801c0d0f8541da002015001218007000c002d2101c0c040038541103130b6005480d00c0c0110f010700d42c10320042c82c0e40300c2d000c000d0b030350070030062903e800003036250080 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 447021196 1250 447019946 447019987
    0x60f070506042d24020910020c130209010c0f24021306030204120b060a0f080a030f1115040f0609050f15071b05070305010e1605120a0305 61
    0x2501c680020441032104105201d40111000c8850003005550580300d12a0300003629400740100d12400012000c50907003c07034850300c11824100143c20f026041000540c0300c00c1e404184c00168004859024040c600a214894081e100d40c00440c100352810700002d01c1580070b054002c1803011400250303030612991f0070040504111000c180880354400141d101c010350440c415102048006c00408130303d141c00707402030354180c0754102210701c0d20040a40340c2c900d2000c0003130030507900680707030360000b03e010303582e44800001a080d440000d00da19441ca1a0090071800301c8504103041000d00ca4040403455030129004040642c640c3c8080003136140c46c10408080d00881200400b4103292a200c541009004500c03035218807807c1051301c0c90140d0f01030740030075811002c95038040002d03819410b886071702d05011301400383d00b409201100d5241d9141d990300d90841d20708140c0c2520a038130030082010760400c1c524241c0d0140000360340828000e008104c049985410305030000f41401004101d00701d980d04480040407 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 447022446 1250 447021196 447021203
    0x6050a02070e1f0b03040210050f0c0105012c06010e100e0303071a100b0f16050a060f110408030f16060c080f0105190314030c150603071e05060f07 65
    0x2550034000303043d89981001c144040c41030100800c00044c2c2c580e0780300541e80310390b40141c42c0305d10035414501d0448082d448a100420311801c01d101324000800e0034402d19018201690f2515100c01d640815003105d80022040c40d410010308000308225642e004008109610041d07030812554a4003400c15034516881c450603d03014030020a1404c24044900d0a142c89181c8143e4500481c1c2c58034032a220324040180940410a5010004400700250050003800c11090700c8806500d031001c00c2d40c0301810406000070981d5801d4480d44540b452051501c980d40204248034003c500c0e0030720b00f101c101e480380078200691804410203e001e210185c2c0041d600d6520ba030313010004003c01030382000040c0803880262040013a82c0800d40001c07400d0b05201000440c14826002264906450340e540c0144108020f0b50380c0303039035010511004103e007404014104881c050706075116103078a40401410724000d115401070b0141c0b2441c00c403c10011528203520340c152541540c0c569955415015084401d100c0c280f00107 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 447023696 1250 447022446 447022469
    0xc0105040b011d0c0412020d02040507081602030a02100504060e1009060c030905030711060f0f0403120212070b0402030309100e030706110c040b0409020901060816031506050a0207 79
    0x401c00c1680c5040a0503504022031100003200d0b0300342c441590140c129215591590100030901041e5034038103000d1440c40c070062001c9403000555002c20305984003a0380420108000c00c0600c002c104050405021000440c80250b00303010261800a542c0c071503240400352983e070f440700070505010158001e2095038003900201c2d80540d020800c208020400301c0301c20b0325035514185401850b0740c40b9029205940c0c0d040401035090002c6602c990580a1000310103075480310041204480c0203046c07001510309200c050550a0300c50f440d50074290410b40755031102c2c2e800c54003c040e0021408442c8020746001540200e0307503e8103940e41e0300c0820710310702c20706d040d00d98040304e861071400200d41e102800d904401c80513400e54080307a0361400d05484000c0546140d01941e0010000074a0034206035110709046100184042901c0a258003c00d0252000303070440f03800035840e0810804900c00e10746089121099034901048410303008008504525843d00a40c803c125001403040701440c402c000d004040c3c41c0c0411074 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 447024946 1250 447023696 447023701
    0x1e0209040c14040504050934090c0c12170a0609050606160b0c0702040203151e0619090504060e0402100c0b040b061216050f1f0305090708030712120b15030a020c0105 73
    0x1544400e0340c2340301e588020040342e01008202c20b1198000c4040100b000d480d4010b020a0f599250390a00741c00302ca40804010091401e0b0700e540d40384a250034010382c4c01e54400034074541041000003d41ea030080c1420b009000820294900c50324814a180e05503070001d83d0030240d5250190349580500ca0400040d61042c0040203010114005c10b000011100c41142c010051144106103401c1400d0480c0c2010391045c408d00500841d2260383c11040d160000c1460411403280d102c6000404840c102d400000c0486807002c1000110b080140c045400f070007042c01c0c25031004006507250034403444001e2006140441d48408914903444242d6001c020341c80c150180c40008440003000445400342c6e00c201481520664012401d50411600d0740d8030120140b40c044600c0c252030a406d5001c3d26001e46408017901c24034600280201060016041d80c40c0304405020783c1c402c03010705c02040400241b8040500c149415511403030703951500144019103040c01d8209440ba5a801040340081c002c0c050040010350800d400c = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 447026196 1250 447024946 447025003
    0xb0a0503060a2102040b310c0203040f060e060909131e020a050f0d0218070e0406150f0908010c0e0907050405010815041e0209040c140405040509 64
    0x15500c41d28055800788030543d543c2000f2080341e5400b07810301088108214060026003403e400c00200403030040c10340126000ca8001e002c0500c0c0301d1290b02800780b07888003000104040036010742000400d440c8011401c19091500d2940340301c00c24031521051150780da884a4150329610152131003c10014201422840c1440380540c1c8452003c1003259243c0441c010382001d050b05000c1400740c0380e0003409130b00030b0505100c1844001c2c0b00408259a014800f0300301c0c0070050b51803490b0540d1024401d134a2001c41c0c14050005000c50200402052046080500900a1174600c0000c650680c055103040e0240c40e07040c450070703180d5031000c0d0000c0d249542011030583c40c49410044a011600b810340300a03410f540c0d00d01048400e80190f000c0c031070001c1c003c10080350502c2c0452041c2c00d610100100002810311030610440d212824005040c20381e00e40201e4441c3c0345251602c14007440b00402c0c24443d520704a181c0118006105500a40d44103640d503101103214000c08003c0002d00c0c2e00e118818403414250000d = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 447027446 1250 447026196 447026207
    0x11010b04020412051002030112020d020a0b16061109060a030f0e0d0c03081503060609070302090d03030605010806030726010b03010614210a06020c03131403070b12150a0b0a 76
    0x300594040c417505014001040162084a040313882c0d02d490b481c1e40814940c20011113a007001c005070703400300c44044c0110310001e80c42d00030500ca5410310924207840021380740c842c0c15100307078490801d41d00c0000c1c82482c40544800c02200c000c1800d0349000a1207142d82d07150500104040309036840103103e49520310141c1500024070842490103030310b41140715521004200007246000040e580c01d90454008500785091594030315400c44d0280c100541020350758004202c058030300300c1050b00000e4507424104099604883d100d900960285c1c050016542062034520b003490075889200d0007040d21144442d03403000294044810118010b000703000740b035503401503000d034103080800c650722903205c1c2e515405c00c0e035500140c0900309042c80303000b4000340f0f52a0341700c110003504100f0203400e640c00b04010190850b614145e140001d002082c041c42000f807048420b1501c1c0000750340004c40b036020300708030480541a10800455101a541501c00c192081c4034022465450301381d417001e41001e0300852039400d42038100 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 447028696 1250 447027446 447027479
    0x402070f0c03151d0703030e13020c03120106032c0304090e0f010516140703031418011107051b210c03012007020d020402130303050c07060e06030711010b040204 71
    0x50005010383e0a444568103c2c0c5000a115503446074032a405c10000680240003000f001380000707046500f0703400c03c20040d60990b4400c90b0380755902e4200184c0e6645100b00040e24a02410413841c00704451200305820303030b408201c80c0301680c0500044a01c00e802c1c10300d04004650141610803000e01076a400b8212a580d190040480c265095080100090f9481448445d401e04201c4c1341d82c5c2d10200aa04181a100c1607110f401b0a2701095100c4c80d40041c481b11101d40103009032101601e4502d501100c42149003140c0d0074840ca00c5000c0c01c104801008240700080d011940c00b410564907040d1054900055024048010321140300040e0701d0180307840b0100441c008504150a82c000c0c450003c0008240c2c00c2071001d9150101d05920074000180581040c04040c075555201400040c5042c1c004020310300c00c508590f1048002440009042c0150b500600566008000314181414900c8042d000074a486c000103015a0412200c4d50400391080004d42110000100c054411540c0300d8881d00d0801d60f079800c1 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 447029946 1250 447028696 447028733
    0x504021c06140f0408040306020313080415021236031c11061e0442110301063204030b180c0f0d0218010512030304020303090402070f0c03 61
    0x20440012428001007100500c03c4d0303413203240c0303034078141c11681c0e400025003003c0d1010b07840110110b600e400040f0044001c00117404c0d08a1031440b416285103001b85131900c1c4040c1c07440010014014001070304903030362914503044d160900310000c3c005121a140102c0300e03000d51160f41446141b88800710070b00010301d101c50300c401540e108204916011140c65036aa003d48940c0c030b134807050580c0c01c58091a032014203900306c2d12030101c00c0b000c4091112040002450b080e64904a141c52118540100c0e0010042c4501c0c0420200305200d810528114182d907400144105c2c428094903404481005803030030b0306180f40d40b4520a10754001d4a41e8814160a034000340412100c01c07100101003010790451b200c5020303549000300001c1400c464442c09200c17120540d05030242e000083e8aa00000503a20194003041041308030145521640c9004208901c1c46290320380410513400c100240400740e1004021128450b81c190380c0542c0d2000c05123000c1038229042c1ca170280801020300c1d8007004001c1004100c940b9240c4 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 447031196 1250 447029946 447029981
    0xe06030f011a0c3703020705040e0114130206040b070606060e03060603062a040e070306150210050606190804020103060f0803070213060e04060c08280504021c06 71
    0x603900802e0144242ca0449010f1350003961040c02c01c0b1028034020f400900303a91944507440881c105001c0c030703a5100900450158203d842c050016045c60301c143d4244001441c001c1c0524418a20705250510014094154800080e1402800c0d1b49070701d01160002c19041d00d00503030381c030503500340b8130014001406a000050040c0b080b150031841d00140107409040018050000c58451511030021240d295608000303542038400b03500d50f40d54252014000a2100c00d424803501e143c2448020201d43c115004110f1a000129900000035070010304e035910003901d010700090035150346001903640c3c000d640252a40d02c442c0540f01035415030020300940160300c01e80302401380940320454600f1205e010b004070103542c0e00c144220350143c40c0048262480c2c08519400240c940d07114860301540030000c503000d5810546641d01251600c3c0d000d0303502c0f90b009540b481048801c00176880200303032481022410140c15030301e5001013419942c0d40c07402200001e8400d4140050003081e890300c18081c00c10f03540f64503103040 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 447032446 1250 447031196 447031229
    0x63c0b270108100e15061909050f010f030c150c060501080102070b1b180a0f06080f0c0405060702060a09051012060b0301030206070803070c0c06120f15050d030e06030f01 75
    0x950fa020301200c101059000d040f910035046101107021800400482e07000c54101d01000203040c40180e0b940107000b4103a0041850320b000582c041c05d480041c0d00003c00c18480c00d40810104154a5628083d00e842001128800044c0312003102d00350041100504201d00d007000004014034154000c040103441411060081e5807020315a00f180245aa85c80080150030441c05051096a0300a08100c3c01c00401c0e1140ca40e44036010b0444040054001d00041202c0d1418044080c80450541e030b40040701e04000c83c41d0038101000f14246000d5180000d026890104801e00000d0040921401402000d490144189000b20004214052044505076002c0c503200c008070311a40c1d04411a8140e03900a8443d5151503180c4c0d0350700c00c09a200900c0c41080019401e6140c0005007102d00c0000100070690301c3c80141384580c0ea04004a595048141c0301d101c0ca061201d0301c0c40d6281301c11001c11900c00721204141c400450130180c80f84001c8008041d8400800000c01a29641c8270303001506942d541641c00c0f0052 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 447033696 1250 447032446 447032473
    0xd020f041401021501060c0303020c06040b07080a180b0601051c1d0307080717120a0c0e09070e040c02010b03120406030b030d09051c0f063c0b270108 66
    0x860340c2071031903900741142c580188842d90040030241f00a0344a4a0010300e48601070071003505103d001c3d28221541c16000b01446401a0f01c460010f800005400d030030048103501b5526086100d5030004014070692034140003c03000c3e0300442c107840c0c075955019180002200001c03403e80091000408010001a503480005d0b1700040000540341c6455003d00131515110543d104c640350600050369004180000300003a11845107420841401002c6601c00400d1741d08000601500881d545015180203100742c1c2c2c00c0011447d84004200c1a000c0d003a14005200040c6071f804a01410085441607010f100303050a000007200010000c1c0120341403668104805002c8504050b100c0030301c45030110000b00d410000f40102e291404036603458410f072403001017214155a42d030340c10100803030300c096a540d6540c40b040b080c40007100400d1869180c600344484100400c80c0501ca1100c18203010806059a0324652508583c4a503045170f02a9a030119140c1c1044140c1000700302c40301824000d11015028803a80010907 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 447034946 1250 447033696 447033703
    0x2803031b122d14030c0c0a060f0b0603091f0608010603031205071715030a0b1504150503100905010e2a100905010e0d06050a0e06010803180d03050d020f04140102 71
    0x201c10142d5074003180000f114030303144071a4001130a200d1003c1410000300c0d0b80340000700140d81100d23118100c0420700c203500620303c40c216540b40706654000c0404008004141c1030100b500510148074010040013184070342c48500041c0300d87d400400040d841d0910210525802020305551034a25907828412540e4882007101c00c50211404a0b074841450008584020000e0f0441600e02e00f001d4200c0340305503001d482c1e11420450030754071800c2e100d80d0303480d40b0742183c14180102e100c80311038032404448071450301012903640c1c42c4440e40f80340000d0340d52203900c00f00078080d0494020340c04060100c495240380e002c504540301060004100119204180050381800c000c060448250016103405200925000054590300d20707684401d640541007404100014000e03114070b90281c4560f5100041c0d0311b07241f03400203190180c107030050301d9549d000340580d02d14000207490920503500140c40004024103e4941595640150642100c4540c0081410181f814038400604221011119072025602c1a40300581c0ca = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 447036196 1250 447034946 447035027
    0x15030302060105120f010f020316030c0509060904020d1a01080702011b03020c010e010c0207080c0f1e03120d1b0f09170712112803031b12 61
    0x358000034010070052400d42c07803103e01c580e6501c1c00c3d200c6105140d5400d42c00c603030200104181e90b42e07000c000d00540380201103403141078044034102004103944102c005800e5015611141d8400d1100107054a03054649030143c8074500b054420901244091465a003091050558041c0c00540807100184505205014129910300d0b01103444c500440c0701d03030007103001e03600062030010075640ba8000c6500c180c00902c207003150120f10303a02800c481d90078004503038141510680304501c21382001c80360b1036940d9039580662414820500040d498925050302107402c101d81c002c08580301c500040b034200782040103500101c0400f101140c0c05126400080010f1307480764400c0b140e80d8001485c841d41841004a80b8074141e0007400324600301d50702c455440c1403d07840307100601c4085540702280450b400940c24030356100c80d1200700c1c8032500e682030f040700005c61400d03140500c0050704110078906180541c83c140c1c9810300300c2e1034025402800090719060080c0c85074550001000e03425018442c548103107020490f00c0d41 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 447037446 1250 447036196 447036203
    0x120a1505060a120f032a140f0316020a1214010c030207030503070e0f060a180e091c030204050d050c0117090a060b1302030708070207050d0b0f13061505041503 70
    0x101010169213890b010a004c0e00d404409000c41c101e05210030f074400809080c9254005101543c055507203240800794503881d59454007a03035000d81840480444040103a0300d070b00600391700c0d03402e080746039000240319480250701500413219081c0071141800f65500010201c031111800901281c0c0ca22030084040307205030b50000d000242c0c180045501b942c4034480c2d2031030302d0b14001c01c8005030701580b40001d01c042d800111404007040016074a851002c514490340c00040a601301c03010080d161024565840341d100e080d0105800314030504800c0ca940c002c0c1d043e10007820014021800409480c41c00a81d40d101e500c2d00c85011070741e5428150803441c40c0d500c4a911071000b900140052640940e00c90019001790542c099201241c0c942c003040c2000f003840594405c0945d5907840d0305504207110060b003851410b030005c5019202001090000c00c0c2e0362240b0507009818001c1c030860175a21803100031a805d07481d000c000c0140f030034807500d090f140e000c0c001200152031040b1020840740650304060701d00c40e2854407004 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 447038696 1250 447037446 447037469
    0xb1b0c0f120133090501030b010b0714030409020d0e070521101104050108070806010c170c0109060c0f1106061c0605131106130e06120a1505060a 64
    0x9114a0400c0510000080965400402e550014030620740c00c102101da0a6110154021040703c90a03c0007403149008280c242010012541941c80702000b4282c14001c1030a400000a0000200209558003039947d90148050f02d0300ca075226a0001d010b54400d0400100050a04281e008840c002080c00001c60b8001090b02041c01c224004c4941d1a0f004402010320350300a03648034840004a80c01600129102000e07205d68582c103190000d01640005081101001144003c001041e41c018802d40304031600445085005c2e02000c5a8002d50b20034840112469424403d81c1c400308451030700580c0400c051a02c8070718086c56901e00445020300c400e242d0b1800c645c07100c00402e005007010010f5044681c08044c0c800c400c01c485460f842c050b41c03000d40b20a039162110b10480b000b40f0001c20440031130b404044070011f140c41020440041d20390403502910078216042c1021440d0380c0e036107907110b56549441e0020b032942c0c050981407004100146900e15401c440c00d001c0010400c0c50042000d601317880c1d4010a5 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 447039946 1250 447038696 447038719
    0xe131416080a0c140f040b031618050c0c030a03050402221a030a022103040509010b190f05030402010305060a08100b0a06090503060c0a05070807080705010f060f030206090301150b1b0c 81
    0x420000c2c7c0141c540c0d80d605801462040301d940a50380c61810b0281c500595a0310410602d01000822200010f1a41403404000e0004501683c004421a0036440d03491401103082d40302c60001604500361100341c60358015140c0145c000401c401d400c01c001c0340e440e0100c1d01000889250900d6201c0c01c10f903c00035400f520032181c801c2202501100c50302400c0c80201140d007441e407035001243c90003200381c12080e5144d82c0070400b0f040e02c241e6034010340c0014020346400e241c5c174244c03080098028003000d04003c2c141902d0b40c0c00a504c9460b071800602c006d0000500715100c3c0c2030350b401c0d00700060883c0c0b10141d01410b800e4401081c01c2d4010f160020813a000540180a281d0b1101d4032042c00c4d802942c03100040000401c00940420b1400380a89040d80c09100c2c946d503240c0441c81c181d800c40d41c070303c0d03940e08085003409401c1007454403000041e0222a01070703480036139801c00701000a004209040c02041406114040071440c12090406040d0001d0162500381c00221840129592142c0340d02407540c3c4600100b44 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 447041196 1250 447039946 447039949
    0x1e060e0d020d11060c030408251401030b060a0302071716200303041403060a05040b070518040606090609090614060d0b040f02130e131416080a0c140f 66
    0x5041030598000e400303c8191003c40310000b04540d00ca00c49540c1e49901c04601440082c4041c4a01c445941a0660840e22080e01d0300441c400e0f6407591003500000110400c5000859029030845042214001d2986595a81d803483c090700075008040c0030f403402d1361340318180400b0200c00001c40e0f820041c1c103020b8140b03142c600c3c5c1d9450035006540000407050b41441c100c200942d1020009000a82040480541c1da141c414040c10b1500800804880481d42003106100c0410350046101d9040161403510f565074103c00b03048080da42c0000c2d01c2490b0007a140120020329694815001d400b607811030780d01d4198450f41c902905096580d01e0203035500c6a0b401941c3c211076450304600a1044a140c5440420400c959a00013001c80c0c030301041e803d400503000207181c40480040e413025006030541700c424070002d080400c0f51021b820442d044c020142030350341301d401c040d1000c2044598100d10380c2882616441c0d48402005490300e9040070121500c541440c40819440343c2c04c015000070f16400707410f03507a20100010 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 447042446 1250 447041196 447041209
    0x3060c03041703040515160c03230403200d030e090601120905010e0f0102120a0f06230906010518010f0504080f011a031c03150e011e060e0d02 63
    0x51048a040c1140040b00c88200b0440c40954070840c0202c002d40581c040c4040480a094402009201000e100300050224150000550140250503181200c5e02015846a90300603070413510304861060ba010600004109003c280c0307451303840c0000705d01030701104000140586c3c90202d2800070081901540800e06ca800c00451142d400941450320000a00c00645100111000307000c4c1035415035151a1070306048181003211309031a483e100000c40c0b0703021484000781620301d800f070040003032541c80d80c085a2640000d40c21060140259480b14030000c059910304603000e005036000c003806035511000064141d03000e1000e83c1c0c0392542c1c00c40a0030080c2820801144c022540782e0302c600c1841418440418502e10404c44207105803080070000030300c3c2c110611403011051802d94540d00ca80d1142d005441d80700010038000020081c03a060216220340d1000c10049503042c02d03040f084c038200205000140f02c0d1220440c1c41d850300b82107541001040d45800007100d086900c0c00241c0e0300a102035a46800506054 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 447043696 1250 447042446 447042451
    0x250302010909020a03200c0106050a0501050d180812010303180b0f0306010c050d03060806061009050105032a0403233c0303011e060207050d020102030c150a06060504030203060c03 79
    0xf8a4009100c3c208101e10003804090540c0c2075554400104241f180a4024030441c80900b404842607081d2510f4a8002040c611030902d0741510030f03032504960700515842001d50500e1030351220301c1035110514a80070303040c0b082c400d12041d80060a0644000c0480010710f0791072041e03c00c6d110b0200d2030201d49000c0381103168000f820240c1080f04202c4244040380c0d0a012140050001e0764012840d54a0300e07058618010026103400c1c440d28a08210640a0760000c4415084941c01c2c00d007191250350ba406902c400b4141c100c0080054041207110940c03003401080204141c0b84140e400184200012440504041ca141070307603112030384484407110310420783d03034085a040c420400080031203440e1020852841c07090042440d11350b5201000622000304424100603020b40e80d11a002e14492401e8802562010503114050181c141072410b48250391081c011038401160341e804807039041c43d249500600080040310b8a8a401c1c0ca0b201c13002c0713000c6100b20700300c41c1140c2e0028000c20303503911645000101039101 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 447044946 1250 447043696 447043717
    0x5030c1c0c0c03061e05010f141801050d030203120709182d0b1509011e080f0403141b0f010c08040b1003050601320d0b0711070825030201090902 64
    0xd00002d00108045c1d02415001c2c100782e2441d2a041440c0ca0042030140f05084040d510410064202c01c000d0f4003008401d5044a90440b503040c140300160030141c0c214424000000f00d94001a41004032450f085400b20003201d103400c1c981c800c0701000720a02002c0b200074204618921100d00c00c004020f0764139640c2a078110400003400140f0503100c0d400a2864619045501c01480000c98110050360300240101c2400c0b021840c6d00031034062141c0010208680141803101c1d225145000c5030505218040d811001c0d00d002005950b2200c0d4032500c586081405480c6050621078809100b000146c1801484c1007004c09448075109a1180d60b200f00785600c0040c1070710001c183c0e0b00360010102b4420400345d4004c01305d03044c101070000c071004c0e40550300022044480c1b0003070981401c00421a15884481c4444d290000c40e070805036220b10b60210f4501500c5c100c2079980c1d00c1841408200a00b0225400c00001e22580342008403510180c12000c02440d03622000e808600100c80801c0074014680040061591 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 447046196 1250 447044946 447044981
    0x31e0906181c03060504060603050405122101030516080d09170c06030c0319140a15030b090d0908070e06060a03020c030a0c050c01021b040e0a05030c1c0c0c0306 71
    0x40e0080c1409404860442c600290f00e4050030410750401d403196030003418881c5414026444c107500c41c5941c89000004617a014100082c1354070303400c2d040d08018012100c4059020b0302550303503803c1c21661a20034040a40c81e00014a42c000780407000003075403603564141c603140c0c5489140b6000c2e03201c00c1504040c0640c8118090380701c98454907520300d401103108803052141c580d200c0c03c2c906921600300d08084003501010745031804140a108038140c0d41e65004502d01f40210701d410103081d00109096107540003c004070311080500411041c0403800c24003230040360b950030710010390309c0100f80c0d0703141da40e03103c1c0b00c05e43c043c40c0700864024204000208010300040c1805460702100c54845441d50384600140340000306002c016604101091008600c000381c01d200500351201c040c00703010000419442c1c1d507845240e0360360000203c20020700048c0403854102d07047c1c80e2a04030a080701619004010041c0c002d00d15408800d5626601807607030442200d82081071200c9a41c190ba40e224001c0c40c420410005210703 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 447047446 1250 447046196 447046213
    0x916050120030d1d28230105061320090a0807080a06060b0337111206010c030804020409110607030906030c03020406170705160305031e090618 63
    0x1d408100900480040300f01c0040d18495520050314030440384070354510b080d04415100c803510480c64000940031201c0703c0c485008103101e41380c90320540e040356580303002500d010565180c00040c191702c450300c0f07550240e8580034000032903044a0215a19085414000a4074240c052030b41c80002019154250001c0c00307030440142c58604140c0380ca1030a81c00180c40d0341c03001d80128104821ba018803002011744401c4581542000007900b440d0303441d4000c2d03041e0300c1004a0601d180a905200c0c000c07000d01c40c4482d0030040018001e080303007520f9000d82d8801150700c114102055103544189982c00500340c060b96402c2081c1c07550b0b42004040c00d017400c015902d20100c0d0009151a80d03400e00140600d52080e102c80784a64509040502541c2d0103080c00b03000e151061108204041c0c0010f902000500642482c0c019035444180a84950184149403041800c0700d5400904064111005500400141e40050120b112101c3d80512441086400407c140c100b03801007241c1e1015000f4010041405005031011003 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 447048696 1250 447047446 447047507
    0x5030903031206010e010c05060714090414010905010806010b07031b020913020306092802030f060c1b060601050711031f20030402180a0605210609160501 68
    0x60b08801840160410071900340880d9613040405d8114007030081c04e0035034170b11500b40c03200380d00c8410060000043c0002c80004440354840501281c04200c4010002c000768996090401405042401a0b85500d46480000b0480c024000350f058103c81c2d04008075460008140d03012945040c680300094031415070040594016518030000314407400c0d0b40ca07c0200c00030498010146011009440c06d001500440b01001d6207012503540302e0708400001401040082e01440403078540300007881150703610301034042881480b04605001b80440b20342da042e00c1783d10416021000d511650103883c0c040c0400d00c200b05c0c180005045031749c01101460300800380c84044c2d1065601424107404079070f00b00c129580c1c8000c00d03203004c0c005078024164514003200982c01c42c6015804224106603048440203d45100d000140041015411000c05480040c10401c00c0012045400301b00810205620106003c1e210008942060020702d040240f085402034050b400e25100041d298000b03107021102e1480305c01e508000c0300 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 447049946 1250 447048696 447048703
    0xa0f03020d050109090b15031903050d020d0203061e03030406110a1203020306030f011b08040c0b0a030c1d0d02060d060905090a021c08040e0c16110a05010c051905030903 75
    0x244461341c404112110540703850340350044010008103440945141034415a02c00003035007060341c04141420064800d09080a4603240070b4194411601030000812900030344481d0007540c003c1000f6210485103048400075408418071030200d03540c040d41b007413004224440c41002400c02d98681113050f581c08a0507a100d2241c41c0c0d590b20f214030b01080d0008140207285c1801c00c0003410115508000f0000742c5407103c1c2c081e01c51f001c0c100550b07080202100100341800100d02d1103000416034241c1c8680e4506207040050040c056451600d000f0842240c4040e20a0b444154a8181c03982d006052000c0280541e08014054204140024040703a8a410100700c03001184169400303014940c00401404c3c102e8410010641040480b18000721000c9202e103000800c04025203003540da0580702120b040d07841c3c03142c0050398050024105503c4104000040030700001c07544e030117a0fa07142901e0040005d900c0d42300546982c10a488020095480290b42070590054212a5886030744a45c2c29070f03251101c1003000a14 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 447051196 1250 447049946 447049949
    0x8071d0f1339050a0509090127030201050708070206040f0311010f020c01180b040b090109150203160f0c03030506030a0606081f0b010f0e0310051014060c030a0f03020d0501 76
    0x42060705901c0030303120020307415200400c1c9001280c5020b003107003010003090a40c201841414060540c80e0040390740b0120179000850b4056010081c0c095040c1207001203c40d1846812095015519040210765242e201d40e03045403244407e1b070000c2585880383d40e05d204406691160540c20001c64509180240720280100d00ac9000c00880158070b800d41c5100441c2120940a491080809401c1407800041c2c0283c644641c800d030020041a04c0781d41e0180403a003d407860b04801400e5a40c0340e2020300c12002154040c41c0294658462100342c41600740f000d0714010f940006c03d4010030b1a841d010400640309801103903104002a00f542c0780344c0020341e5a03070150f450f1500082200c1d0401004216001d9040c1044619640d48c0c050a00c071140614002800d921100c0201c10300b0441d02c031441c82c0300360300c2c02c010702e94565410880801c01890290b0300a50441150b002c0c140406400a5400380d040c500082510311903500c0c10040c0d0726002d01c2241c2546d25210112040050580a0102609900380f41c401c030f50 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 447052446 1250 447051196 447051233
    0x3020f030c0d0306050a0303140d090c2301030c08280204120b070203090607020f0409200f030a0803070e010c051906110319020c0c1908071d0f13 64
    0xd00300441078043c0a84000b500304034010192444100040303580100130300010721203800481d503505036201c0080003500d02417a019140c8102d88000055581c4064503402c01c10321041004d1907089490001101035901e04c040c01070018842c01c0c0410f4401d1101008000c02007890111511200c1d080d9100d10160782199008001c42d501c1c1c0240a0280f201c104001a800403442c4007445c81c0c003041000040350380c02070480181c000d00f419040707103010313440d10384c080b0306040d4002e1000760114440e04103235030000052003185406040d1001c0206d005003400258010320b250300450300e6041da0354a1604581801a5a4103581040102c00484001c10b00c1032080c0108408003501c52044e0f805642050002d5401103c1c03003220b40c2e5820010044441c1c1e4078400c0f440c41108040c00036a59080d0104040c0c5000340c84284560300c03801c0c0d206003101603a00c80340710104840d0602c00783c840321a920400000254113054a940001e01074038001000c091000c1d0350326a100649070001d080641003070701e800450fa41c0d80407614 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 447053696 1250 447052446 447052453
    0xa050f060d0603050a05160b0409020f04030f06090c0f0302150903120c03031b0405060d09080f0c0c1c020105160f0f0501020a0315060c0609080903061603181a0403020f030c 76
    0x8a052003400d00c1451f41440840c04d81c001e005140000136a1141302d94440c1c03118056020628022001d07000044070006e540010360590b481e070903820f094000302500181100c10800c281d10014044483c4e0352009d00b241e400400000a100c0c0b46084d2648550201d504240d0500403188070082014401002c0d0800300d440c01d00a40d12490b244024186a00000c03131401100441400204100d0b503c81d0105c0f1642d0781e01810209080115262144c03040c0191448505040d202045001c0894000541030b22070003001c40d8040181041e6190320309003581e10a102030b00040b01000420039100c00f400001a40501c16180d0201c1c005043e02c030700541c2814203c003160b280e50002126103105030b25000d4008d8041110320032400701490201d02070181815640f000300b6841d105c907440030501404c5020740322440c00c0641070f1185031400302c442800c000040495280400d2800c00012a4140241c0107100b100341d10001e407404054980101c0098464001c00480861140b20003000c44404180041c049102c5032000a = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 447054946 1250 447053696 447053713
    0x70f080f010509120304060e010e0d030e12090a0302060309100203070801090506010906021e0f030a030504331e0603050d090b0c102301080a02130b0a050f060d060305 73
    0x6080d02d40180201841e9030180040a50100600d0100c80d00968000000181e20307601c1c00003507000d003a86103101c0d910360043c86000e00060790150003082d01d0f01400d10030740d004048040d021580d280550410075400c581000d1092005040c40700095400c40703400400c5580810b000f00d840703811399204079414000110f69200401c030303c3c07905010321500042c0909002020504115001350703103e0030f103c2001c010b101d00418510318600240081783c2491010000e8940e144524200980641020b0314101c4180c60a24546040ba60b502e8600350400840d1604070030321200c104405401410511100d110f802c14114101098042d09214610081d4464405040807005001001c1d00100541e0b105048103901004046174241020407110201d444002000410300c16000e8402003d078141554122114032080020540c0f1000003020f54075148203d8041c901005010b41d881e0603520040c40750750700014911003d214501e025103405080c0701e0064801070911643e2070800c4103a5004e5030056480da004441e2 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 447056196 1250 447054946 447054973
    0x11161104060518060915091003170705120a0923040c02010216120c1202070816060503070c032c03010e0609190c0b0c030a0314010b040308030405070f08 67
    0x50740020503040300e5040d01c80505003101105a08010a110b1042190000066040040b48880c11412202514422981c07a00b070125403003010407400140c0317103d00750016804a1500000c1220100c03980700c405003401e0b8201d0340c414000340d00403104080a01c2008403011450141c0600c480c1d020403a0440780003040002c050070b101c02c84512480d600c0840e401003004000c8151400e464001d0075070700000c000c8500d0003103003080b11610f2035048028603000c40d4004818410b507000075a8029070340380740184d4194201c0c81ca600000c6c403036103100b000e01145042c8001004a0b02605c1580b0555019040c51660b5403907059800e04004d8003c000c0c288009000d401c944d400741001d00c141845080140020240340c01c00c9200b8681d105222040001c41d600e00c21041c9041004e0050f2140027081458022501d0b140b220004944a40100201c400003e10700f040c006100000e5401081c121490340028a19140c10358903405210380c00188149e071103224229000404510b0709820000810f14403002d000101034441 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 447057446 1250 447056196 447056201
    0x30412080d1b050906030a24060206010506120a0203130c060207030525030b04050c09040c1e0f0b0703020309100203040614070203150a0e120901030f0501080303060411161104 77
    0x4142d007003001c14000540c4a4024080301d001c80011201c494480d82c51144800180c000c5055036807010300000c1080c440781d00b144203e00107580c11a000e0b100d45030380701d409014080c001d070f030100a9000303407400209803040c000d940255040b103101000c8144a082e542c4503040755070803913484030006074800181041407203c00d0281d00c4140c0c034270180760540400d01c05a0803422803ca4003018000394104008202008820002e0819a401c0986410000e00c0c081c10000749445552107983c115071000d500241044080c0c0d01e4500c01d8a80440032814040c2c02c0c01100200b9801240f412030039071004200c1047d80e503589580907a40c10303015600450350b41341800170041541004980e4108282011312820740144e4022645541c101102c0458070600d0b603a1040040c06010044050501402041400b01c40840400024070500000303032020300590a40c0c0c141041181c034240315a4495400a20100d1803500c0e2681107116040408024036090480300c56084101c01507802089504940600c0c83c01a6804c1a0 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 447058696 1250 447057446 447057461
    0x7150c18180c0809120a090e01030f060b030307050a1b03020406090617030a0219020114030a050106020f0c1c0f0507060c020102150609132d1506060909050702030412080d 75
    0x2032800c8407260400c004c0180d40e40300c10401040b0288004900c2c102d505215028441c020440d940d9411030959490a04600c90071001d48103449040c00e040302c40301e039418000101e4200380d5100d402421400401e807a80028020b01ca078440d07034240b01504c000805130f030700d5000b03407000780c140c2e4100015801e25100301c04450a8070800080200c2d0000e2015210164000c40e45407c00e0202c4400c00d480c400c454070040700c035500d500b41881910a008418028945465800309050710169000c503128000c90203002e540d940024248d0f60703881007071720849241c015400e440541d807251203000c6100140c195503231003a0500186402460002e00703004500c0d815176130704000d900410001e6402d902c00e03c0c2065004640c010400030042524850200c164608100c4c45a0345c80070310154011082103410b040940001d000820340d4804da44080d556500031130903030b0a512518003240e4080d1100410f00780345c44012000381c0801005041540010b000c000b030001101c040c0f0a00143c810306000760356042c1c160250045400d00c = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 447059946 1250 447058696 447058721
    0x5091207080f031216090902090105040b070b1e010b0a050d020c03040608040b0601080415090c090e101b05040510030921020607030c080a110409140103050f0307150c1818 75
    0x2d524803085d40d04c0e040f410801c1a20f010031805030342c41c2c02420041e202442150b1180384003140000e098001d2050071603100380640381000c0a07c0b027100302654038100c0d040080c0104058000c04000000320700e0b014000414003945040c10240c14060013460860940e04a94040c4010481c9001080100041c0f54001e80d4040401d007480341c000d0507d81c84030300510301c540c01c003605001d44d1403444e20244110200610002c140c01c410074096104440b071195211110414a03131451401c0644408802c81082413211b890362055883c83c0c2440d10348401c10920b03281c4a400081450707502c02d00080400c0c01c2080074110388098560842407580002c1000340740c8000100140300701480c00c054003801940c050b01d00c0e03402c12211040851011641100618a807141d984084100b41c5002d03200c0030906d0400f607040c2d0481c1d0282d0159408410700c10318060b00c0c0d1042d55802071400641d03036000e00d00341d0600e50107401c6282180c40c15251422580514404001080c0c000e40316003400414108808612400b444070744620 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 447061196 1250 447059946 447059971
    0x16080715020a0507050909030c0a050304060210110a140d0c022107030905090c0c0610050307120503070308181b10030b030c0909011b03060f0b0a05091207080f0312 72
    0x500c1d1600f5803111440c0c003480b403040d028503001c16103401080058916000103441074403030071946842d000b50749070b01510512015020358101e0040340d025501c100d40200381659441c501d4152803480c121040c1079005c80420420100b800000e68092980c8116036940312660024552100c4c40c40d80b0350315940d0303180302e0483c034200c0c00c2050341c00080d409801e20080b68002d407002d400c281ca82c90343c1c24160380903820f0030a095201e04404c01c031044040300e940200b2950250140c40c81141c861a0301d21041c0604031700175141c0c1c0e000304400070000c0d00c180d08469201342803c010010220220342d07843d003800c402448015020000354107102c00e501d00402c5080c050801b906081000544100121b503c46180c42d0142d88200d400c000090001a82900300320414000a00680c03540d46019070090000d101c503015509000c1d030200000314012070b02d581107030304070342032601c5648c00c0040b0b010800c5001c144d003c540080f039000352600040ca1640c2006501051200d05000d540ca07202c28034041d2600c00001020f0b0000100d = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 447062446 1250 447061196 447061213
    0x2121809250c020f100314010f1a070c1706040b06120a2301110301060306080706090311220609111810021507030519060b0a0f021608071502 62
    0x10240603054801886414508880e4002d40000307000c0c0c01242c91001d4011640026172079590780d00d40e0040040c90300c0c0c2541100d503640c071844501da2025240c010310a06a40410383d01c4c602581c04005894000d114014a6984644552003145940c03620b1036154a550300c00c00c144010082100803c6611044c2a034424a107102c9482c8d50542d140c0421502908441d4045110b90021120402c0c254004240a000740201203615981800c154424460300001074a010f0b0302248102011400808403180c2da543c002c03d190854403088041c0e9a0042d002d03500003121041c02c8100d000409845e02c01c95142e90700015042c0c9440964426500c550515041e100703401c0040b4140c601181c00b00c10100c0c0e5003030b1218009201400e806038a000c0e14507405800c13558603d000c01c06002d074160000c5104c2c400c600d55030b00001041140d450180d5036207010361003c4c10000c1c009042442c2c030031005040707030741101e104440302c081c80c00400411a004a800c60345281e00031000502503c010804c045500e000303544014540305 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 447063696 1250 447062446 447062491
    0x11803080d0605031c081f080a03022407090b09130c02030301080d080105060f071a09060717130206030a020409060308090a05060a0903080f09210c060a17060102121809 74
    0xc410047c0700042c040500680100c451a589540390058000542240c0d0020240c0c24080d41e40c1d2900300c16020301d6000079a119952180c036015440c02070b40b498507940340590400502540ca6000f21041c01d4004950858001000b082c80c0101c8650700c2440d005990780b54140b100b900d04190210203481c0600c40c0c2407004100e180c031070408484d04003901c5008240c840030949490307102c271b10a0011075850a0003100c14000325940100707100b40200d120751103440610411448071070821904a0310151030000900b003500142c2042c10080d5803003004c290f0300525164130382c9070f4001110215041510918004141c05025042148064024107401c490701d80c14645440801011141c0f640002480d000e800701343c191102402405507140110000c10003124a41c011041c0d1050201b2200861002e2140e001804030904118007111080c88180d40e07904403880290021000a04000e0940c0b0304501c038050b6426512146180030b0a484200521015038a00b0f20707004004100801400401070403442c1a41407514 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 447064946 1250 447063696 447063707
    0x2060a0c1104061818080f0d0f0c0210111308030c010c0201060807140f06030f0a1a060d15120302030711040c0905010e0a0f09090b0a1109011803080d0605031c 70
    0x40f5888400081101c41016682003103605d2038040040c9094400f02d14a8211135040700544288180490100f01d0450310101101c00d4409810002000da04105810f81002e0701907048100e00d180501c0544e8074000d1501e0714021004150340c49071440c2e80010520400244080c001c1d01c800349030920080c00054107200380c2c161150118400c0301d4401d20402034030050fa0301ca0b900201015480100706a4407860800d240700c8010300d04841c0d1544c2d50785084003c0101440010740d808140c2405070002d41000c0415080000a02201c0000c3c20307800c080300c800003502801c04215140c0c441c13090703025680700d245501c0c01c42c0d02c0464009105204a050462a0711190b90101c00344040724402d29061500212140200b00300f64041d030409403040c181d680380410715102c107401c0056000e00c1841c580140f0f035644440081103800c6003403c0c05a40d5400c001c500d0141d03114120300c50f030a00c0d95442c3c4070f015595036916200c1640c0f100d65000c60854aa1204000516080c403440854094058000d060803c009200808 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 447066196 1250 447064946 447064979
    0x5100c030e0628110a0c060c020a0c140a03020303040305030a021b18041406010f15020102070c120510090615290a090b0c03190507050c011b02060a0c110406 69
    0x5142c5103901c00707a1144080d83c00900244c007840d82a81d6075442111401801e02d98441019207829080007101c004813840010300b90001908204d20b2003256003003201b0815a039200f4225940d22901046010015036018030003400114450307001165520f0180c04043c0c104000c0c0034105104190165560440d61143d85040301c00030009040300c0c82c10b81d45d82c47c08903041d40000c240d210440c031400f40040381040c0d035080040e01391840b2860034002c41910384400c900342e108054005044c084824800c00100c1c0340c40c3d4503588400d02c180241d40c0e8081d4244004000c9449451003940c40a80710039841c003c540c803d181040142c80f0035002d100341c000145214650380001444017128500f00010200300042c0f04007542e401412816010a56441340307201526500e81001c1c5062085100c003a258002d50381c090011980349039030020103004480745100044d40e462011801394801c040d1440c45c1c90b00140da03a18000c003a1a4141e880d0f130381a529507070410003000d805100045010b1440c2c00f00c10f014584e03158803501c0 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 447067446 1250 447066196 447066241
    0x1050d03050403030806211e010b06070f0317040803060f0f030a0b06191e080102090a18150803030f240418050304261504060b0a0305100c030e06 64
    0x214a1b0312041d0205811440d89009800000b0042c00464842500070581c00100c0d882026a101742c80f00502e1500e08803460030360704503072090781007007220001061a000418424020b040c0070007042005020103002c11003c60302200d02d04000810015180b40960481000900c280c0c0c40f0906040800003103540c0751052079020f0034220105000540c0380c3c1d1003010340c141d400021461206010390318950101440c14003034288207040740001011803410014800d4550014000303100103c0c0500c1c01c03211551504681034800102d9403210300a0f0a48020f40514000800410009594910b0480c7c900200c501d0007801801d004201c0b116000783c4030398140c451503196101184c00080c0c030f20a61020126006c1c0c003441c0104030f4040031a000070b640112500c4a2084208451031281c1812003580c020780300c25800c100403c09a01306804503003c200305502001c108c0c0c80c0580202c41942d148d40300c0071f2038040112880140f8540700d00c01000f000d6814010150200b1a600003000c0d01d0170940f004000200c060765820 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 447068696 1250 447067446 447067457
    0x40515070501200901020f010b0f01050a02031e18010201111e04090509010e120705070e270105010f050402040315020906281b03020c1c240501050d0305040303 70
    0x10800d0007020f500842284a00c54000c5140e10800000c080164016901d241e015000b0700340e115042c0031040c0502a000000204010f840d0500c02006503a55004400c28a0452009002c4802c8484994a20031001d00361000140d8544130380402224190180680303440c11079040a840f20000c5207104103843c81040e61203151045000000c1c08020396001c2d691010924505001c00e0005202c810f52014403414501c0381602d840302c0201c02c0c0c2c6503240c0318207540100264089002001502e01052090380c05c140543d20501c4440c030f28242071400c1d55024005040203035903a8004000116503071004200030001a1815805c2901d0f6803a511007040c14034020f000046c0e0002600d5826550303071b40807150202d020003ea0601418280800400c07012a03041400205110350720750045520350070340c50f81c5401c0c0d041d401442a50900401e000c1c50b0441c22120910200c41b10107680e0014240c5500140480403903105164080003852140c03050ba041030b405240645600801d48011a40c0003041341c0c1601d8150070030 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 447069946 1250 447068696 447068707
    0x80d090302040b0f030303010e011706070c03080403090530071a0a0207030c0311040c030209090a0c09080703060510170714060405060a170606180d0213020f07060c05040515 76
    0x101d54070035144072059170326000020001c00c02214410845060780d204065214501d0013407100141c2d144d0041d45d0950106100041284c0003a1155250940c440c2c80703031604208183da40da01055800142d8040b0b804100d80b072945e0300b1214182c8030507070b100d81000c02e401402d030685020710321200700c04d402d40040d4914400040e0720100c00e00030040c40c07000b140c1c403600020b540c03640ca007400203039801e060b2000c0388a18184038284034920302ca8020390b88512001400c40c14030307444141350580241101c0b2048800e004001b41c001454110034800c0c107000310702580c03005c102c51500307441001140c140340c3c00c603c03070004a052120314858000119003003628404001002c6009003c3e00058050103180e0081e603020000003040c44140d40d000e1158002c00c80305001e54121921004104002401000440a6001414888081240b07462420380c070400e07002800f0f40c030b8200c120032020300580c1c5c40001d14140c1010006108020885a8802e4100780ca0103841d000d800c0504210004001400d2601c054620b184d01240 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 447071196 1250 447069946 447069949
    0x1c0c0c05031213050402120c0c0709150915030804030b07020c040617060a050105031c0e130507021207080a0309081908100b030606030423060916080d090302040b 71
    0x1540040c0500a08641c8012a0300707039882d49551044148039078001503100006010b05081c000d031904651240711690722607844114200c50f5400040c0200d1503449880d000040c4200035106103024003080c1e05012501c18140115101982c40e440c0300300004e0fa5811008201041020301a281031360f60004000d107003a01d41150407844c0004e01c0d1003c03644180f50070f40c009400c454801c03410000340045000e0b582d0a9440a510a04a4801740304894254000c004404d1800c2c0421400d5180c44c080c505090032100103107000300300d241d220151910306403030f41c0f68140100b00c0c0d0100490003403410420015840e001d038075a242040350049424050901d620f6103500c00811945100380d5800b00c50309000c00b201e00c1da62000080004c20107840c2e2940c038414940001c109403d11400322403180c3d03005065103142d91565560050460044024040c40c1c412040c8480114242409894000d2048800500340b00803172000030010105540d00c0051264000c10500214503044400002144c3d0112800961401c1040 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 447072446 1250 447071196 447071213
    0x30f120207170102070308070219030302030601031104140127051c1a061003061a0a0504170601090f02030108060712110c010207050c1503150d06090506060f031c0c 72
    0x4104407250a0488402d51200c0300543c043c04c0b11600130380d19050a40c803040401e0f40c5070014100040340c600320303441d6900302082c080c1d001150402018500010032101d079028100040d0001d41101d0055402804180c503290b0b80b180756850b05100d0306a840c48180d0204096401c02d82051017454002c0e1600c0300480c4c482010605201c010f1500540f10240d050343d2100c014030f518030708540e9030f446015004000703448203100b0320421041c0c3d48600300125441007034640324945038201100100c03c12070f0030080841c00042c540101405140d010000b40040d5040004440030348007080c1191056510600040015030030000f40c5039048219800c04840c00003884ca0300c0c01c0030702060184000e440c1030001d448141e4010550091448c00e0080080e00c2590060004118111a07140340e001e21180b07040c000300c0c52000007031582c640c495000500320f1511000690360981074601e0000296040d4020b41e040040c2d0341030401c00301694a9081303019140c8070010b0041d0880a0741455004020410344071000d49c00c1200c00c2 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 447073696 1250 447072446 447072449
    0x20f121504091b0f150e040b2106010b070f03080a0e0105070903030909090c05130608060106050a0810050105031902070209040c050a06051306050c16030327030f120207 74
    0x6407003400300d0074990808107041c0038480550002110443c00c0084c9030221800120159100101064000000b05004499511841c6201580300d41e440518410716541c26080c01142c91003e00c00e150481781008500742041016030155a0040c0e04100c00340014030a2452402102d900d824000c8840d100e840404000304011015058258a0b020501c103641d500503602c841101d1180c2c0e10f803565141c49000140c00e48214600c000d081d80e462001c180900e00d801f01302004c204001030710014180c0d0ba02d082441c5042c1d0280d0184011400c002203080e8542d43c8a4521544030541d10340684001c0d1070b00c00000c0c428030008010201d00c1c21744400e24620700c1155011945695002446903155042905000003ea038051040c0d074800c4101510003d03d60b0701032810341e00c00d000d2503256501c02c18600402554640c3c420300340d00c50030b802081184030310210701e01c0300d141c05540a0755864611000b031180e510b40c9401c030001c0465801c400f0031810000119940d125200303413907001300c030250010030840040e494030015 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 447074946 1250 447073696 447073699
    0x10b1801270807080c01020f0604020f06070f060204050f0d05061f0302031b010201050f0906040807030c21024308030408010f0b0f0303030a05040309080a0f05010e01020f1215 77
    0xa200e40020700c0b510010b942419260044180c3c0c10701c0c00b21200590351143c4c40702400149800000008000d454031001d0400c188501030302840c54050203990303a49050200c03e100300c40550f401314081c0441c0c01d00c42254000c241c0b06035007500d91450b15448081c0e0315040102600340d840e003040390045038014240d4034080116400703011186120807800120740d40c4601c1c4001310f03005610b440c001850829682000340d01541e8170801a2039503413159240e4000719800200194144200600c8480018540400540d0394502440001014250014009003490704020100302d0030700503042c0c07500801350f05201d0812000000071613490408103060010004241750361050b2030740d002c041030004965006412042036240d440c5802c201c0d24524204111061800f0880315070103034014800a03411203281d03807001b41c1081c001c0c1406c614041c0d907082c0c100d00c3d0810401e001c4840000310688402004424003410b000c081240000b5070500c007184003845510b00400c41c1c0010044075010110304070569581e840ba044000 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 447076196 1250 447074946 447075017
    0x30d0b040b1009081020030903091804120206070f030e120408070e06040603030503010603020c1e071a030112030f0c020409080702030c091605210907030506010b1801 73
    0x103888409032100583d4441c0c91994011071720b5000071a0b4880c825044d00000341c103034104003904448111550340d0402000004584410800304009907207520b0310820010480200d40464070307151400081764161b1005031001e56101c0f0701486601b035040414105100450700c4c2c005560044910070300e207410803403141c45213880c9002501161f0701001180c51070035a0017080702c14070743c0e898007000d000440d0b02c07a10020b8002082440140146c5202c1d80040c540506480d045500c20803d00b14804c00425110000038001d034005181000300380d29210068200c681c0b080d041d14215803405840342c1184800d4400202000000d0503500f4405020380703d18610160094401c01100582d403270000125030200c0c609074400d1140010351050751511141d41486500401c2035001c0c050304039030054030307a0303000296021001000600024841d0a07941e0781c1d644101c9001008044141c13450074564206241a00042d28081c001c100100d641c40d0000005480c01100b86001290040c4491241680040c4c0b140f01c02003110 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 447077446 1250 447076196 447076219
    0x5070b0705030711031204080703031401080102040510110a110a0801240509060d1509050f0a060b09010e160905120d020f0102040524070b09010e060f0405030d0b040b 73
    0x1a80040914459001a282c0b0303504443d00d113150507900d02640c1309602c4080d400300e0004000401c120f0140002e948a41404504a000c0506002003010240c000070f0a03170f903000c5000c210520300304114015403226801d01009040b48000c400d6112001110017401007040600c0d121203a0300c3e03030180c20380204104002040780d07403c409a1050413600211502d0001c1d005a0070100301c9141205801d40640c05c01030500c941c004480e030317506e4941419000081122640c410312840410407c0c451559594904c102610042c060751500c0740485001416160155202c1e60044c010006a210380d66008541d00401e10070b40f0025035011580070650b50000c542046094919110554000031040200c400301c0c1c00340c61140900d2640c3c03900302d000b203103b0564080c201585140b0040a102c04404030352102086041c40d04005032507c0034800c009407850402c523956405580c1203550b05100c0690400c018181410550403d500c030075035280a040702a003040360b0344115841087e48ca070780c0800e9201c0e0340500b952100300c = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 447078696 1250 447077446 447077461
    0x30b0c070f0c0e070924050d1a091b0421020d05060402040f0c1d0604050d03120f1815060e0109150803030928020d06050106030b0d050c1005070b 64
    0x1072140c45448542c0703e107800454841801242c0f20001d4568240d141450045020000702c1c000180120b4030080c80030800094130800c005003d6040e00292180c06c10031012000014000d04000091030790402c00141000b155039851038a040750100c8190303c0f07952090702415080710f5440d02980c44001d42c44081c030500c4104002001c40c0c1d41e8440d42c0212002c00c00d11006900410940b41441391050000c0c240000d6013543c0202c54410381c21036103001d41524142a202c0001c15404410712400354040369001c0c000da0200c2040d4000c134145c00700c541c281409089412410070884421410000781a100781c031200c080c9030800d0754807241c0101604ad00d0100d40d542d403040c14800402d00786c02050009800544042800a0001308880c040d44004004184c00301c60001d0b040c0001644c1d0000483c28154003114401581c1e8141d444400103001d00e6001805501d801d00c0034040b1402c3c003101501402441104402203580030684100301030003660b03540c8001c0714003070044805100c0c4841c010803529007102401a503 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 447079946 1250 447078696 447078713
    0x6040e131e0609060c0810060f0c05010203250903200402091807031505130e030c07030302011d0123100803180a050105070f060b0604031e0201120204030c030b0c070f 73
    0x20f82d0f0003010104440c40c41d8242c11103010b40c00720b80a4059482c0c1c00000c01c03500744201c840440982e0340d480e2090a03031600d0b41e100350980e80b00761703819540d00c0c2000380b0300c0150745015046044181801d040405203585550b60300d0441140c6410f4a480d50004500c80c08915115070f0100c1b1070751540103000b01d841040d200100c68800d241900d0010019240c401d4a00301316425182c850141c0d04000c242101c0d21000824400140280600d01c0308a80001e0080a0024200b00302a0001e58820740010405000d00e6054443c13880c50640b08020681c1440001e100d48a142a046016803c3c0032078054015a02c002204444c1c02031907010880d60721001881c5c0c1c030081c2d602d2141021030042121241c100a0342c40b801100d00e07006582010703101d81242a91400001c1d02c90f80400e0300b4141c05080c00b0300742a5a81c584144030081c00c12443da140b1043e040f0f603002c56a1001c950922840c42490440c03c2c1811620765403d140c038076002c0288031209540100315401100340c01d44079801d42c000c01100506001340780c02c618 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 447081196 1250 447079946 447079961
    0x10b0711090a06210302060105150705070803040305060708060d060c020c062b020a141305090705030708010905010f030204090206120c0403060501080c1309020a090518060606040e131e06 82
    0xc4a120840c4e5008180c070b1405004031204d400d41e009114690800301000054030140d42076903481001006000b000070f07030a01c0010000c0604c0c8025540396807a41c01d00d0b60601600400701010401b00b54101b0500395102681481e455400c040000b506446008003a0702d03081d01861410f03800180447c03800d0040d100d04218015030b5a1040e4003680150042d0304c3e004c242e02071411341201186400e4240188440030002409058a8003600c5000460b030360070100307844040c207552035000030702c0c00010010115002450f8600400c601d4408202c0c940c5060b081140418003400028492901d0707070103500030f5540b0301d4295806e1b40604400000c1da03040410f00c0401580c0302d440120b40d0305060500001d103102e40420b1265001c1006480c407035481d880e1900e420000c0c090260b040764401d10059011540c203174036110307251254044038501115040d20840c0c62341351200040c6498410b10007007009000c03a01074401020f82005003c4214010721a10386020304030707a8900c43d0381c400c20b440d1601c081410b00049410814 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 447082446 1250 447081196 447081209
    0x2e081204060210020f07030819020406050702011815051c060b071223030612300f071b030503070507090c05070c0b03060f030f0109110102060708010b0711090a06 71
    0x100000342022420f4142e0203240300070ba1034803205005140c0403a005a1203258002a40001d01c40d130251298489002c0780c00c2500300702d000450200310034085507000710350f1010358a4030401d81e002585c50000344d003c0003028201807400b00603001c1400d42c80c44807c1c030081a2a4960030310188007888e29010080501e412030082950900018818059428042d601000b242c4003c040080320020080041c4019640060511030300401c005078a85200d0505000309200c0388c3c0c00d8058803d032094140c0a07041090076100500e111a00d00b0401505402c03003120846100581c013488885200292034400b5242610a41c0090700c503000001d80c9104000c004030701c213000d4039030201c03003044544001d1a08032210b00600e64010610480c0c58400c1c000b03120301c140590f81c04074005000444401028020900308840340c49810030326910341440c441085011489601c0307010082c4001c0581d481c1003500181144010700c1400303c0a8800124001408200c08010a25040140105049081000d02100104130318401c1c403 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 447083696 1250 447082446 447082453
    0x402070b0112031e02030313030509130e010506031b0f01020a120c0c14030d03090c0909050312070c0c03121b08030f0105040c170c1e0301080c04052e0812040602 71
    0x3082c160a4a4216130146401580154195502c1d424003402d4210120070aa00b804428801c90f0016170310300d103240c46000c000c0b004c00329510607400b000c1800e60b60301904440c404c2d00301c00c041d2040194660400c095050782151000c0e600001c100040c7d0904080e50b1000d03080c4400c7d481e048154503041001040c1c503a00c2404078040f680e60b04e8410510340c800042e030b110b13819000000d0700c1155601ca40c10404002d401070f0080803442e43d407000c0d5101200c1100708100c2d2207030030101c5c2010307104034202101e690040490500fa4152051a40d82c050f40c0e000601000744415900403061450503c1030006200040f190000088082640d092a82c240d8200f02c82854860099800108160519020724801250a03071280c0c5002101040509a0824002c0184e80c00d190280510000c00103035003004d03607501d03074003a5007a41d80c1c3d414102004e0034041d48002417405982000241706044900f100804010700c0350700b00f4811048800e2009150228156100303243c03d21401c90342018a1005500910454200741c089 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 447084946 1250 447083696 447083717
    0x3080106090b0d05070e090112030314011a131d06030d0905060d020906090301230f060f04020c151006020705030610170f030d09021e0a0308090402070b011203 70
    0x1251030001c0c0c1d00070781c82c0b0450240a20480801c49800240d00080b8909202241c000c2890208030f403c03209038130038078840490211040505030075100300840c048024909416a40c1040344814100782201c0c10074000c8440013031200718030000200e0303241c0540722007800c0381d000c101d415180c03900024080c0c407103500c24040d00c502c4200740b6020323125502c1141c2015044030704007003038022814029001648540e8200e2010041420300d0f41d004e22031400c07084070b190110030103407840321481c0b8581103004203000e50350345c1c11405201040c0d892200b01007800b58125000360f554a80020418141a00003501d41e500c40783c00310521109094900d0f00809464070390b821103031640c1c2c0d59070030940e80b420300f0f6036590341d01c11400e0f600b4009030040e00c400d00d03444e44031603040740c518081e500941813850380f100f60100340c666681d10b81082180352001d19034008800b40c0d404e1034201040080026a01d100c01d110060020704005503c01c4d554459405881c001d5401c08104c920540e980d54002807841e2000c2012000a08071006 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 447086196 1250 447084946 447084959
    0x60b180603090a030e01020f100501090c02030c03070206130506030907030213021305090603070f1d0a0b0310090309120302031e0a0c0f030201060b0c0309010207080d05090603040c0b040b07030801 86
    0x16680301d40344900080c1203010a9450a6174204200b9000340d04502603048034074070b0840104140c03103044290356000905507141c69004d03021585480d0103c0d045400400c0501c031946400400d440456404039803040c0d803881e08a020310848945170b4455600504044200004460302040d14421a802a43e2400c1c106094401c01c0c0e080b4031030f08059403030305041e21500780810305001400070380c0202c0280c1112007075601e403008610340910503448590040d02200c00340281221164403190888250303801800649081000203841d801000b0040344040d039120318100a262081801d40024440a0004101003a080c10000d4403036000306060600c055800d060400010184030407207040100560b5114409001a81e4180c1d100c010b5000c00e90443d034030740c400401c164140e880201aa0b42005005542d0b402040001900b041c0080d03001c2e051030f0f0094202500d045400000f243c482010480d20b40f03549a0b903d203071840003401c044d0402001034902203030101d0798190800003082d90030700940b80c2103080c0e079a901 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 447087446 1250 447086196 447086209
    0xe0a0906060605160602090607060e0f010c020610060f020a1b0e0609130206070f05030a0e0906040905100b1903050c01140a020d030b1f05040518011a0906070501060b18 74
    0xc4d80444441080380d026001c41e4440e8081d01c42c0b1070006104520341207454480005460010165402c00c1d042003550040f200c0091040404401990014100c3c0345007410310303039006501900c180f000b84940080c12100d010710a2084c0a032590b4031072405500384c810448001d007400342a000d44481484d0340d0300030031340074500005114031905541d82d01d500080300030350a200b0141c00070802140c0e20b06500080e0000604144054228941c4503590441d14103406c0007000341200c000341280b07006625202c0804003040c2e000c100c0c0b5445484101001c01c8e001d03041408524200e41280a00c1d0150b14040c40c007200300413011a40600d0040240d840811441c01d0010400b964803540b507510300035a2040380720a442d94065000341e140280001c210b08108140080c00003580c00c0c40180080c0001c0c00001c09000d2132074201001050300100d0041c044d100e606019000404512074400355501c005d02240d42112903560808491049902a000780540f41ea599540c03001504002981c03840c50400c181c58090608246 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 447088696 1250 447087446 447087457
    0x1050703060b030610050a1403010b0310120b0a150929010f0f0f0c08070507081e12030402040213080601090c030c02030a0e0301061d041101090509011e0e0a0906060605 74
    0x80c00c011700d25540d032400f50754030740c40344001400380300c42105420441d00c0310501650003441020106542c170315048102034800c0a990700311010000c0074a54090110390f14030082031780400d903c0302c0003d40142075005001c001980341c0c0325440c42e901740900180b001c04550612555000c8101618020780000c00042d20f0452480c882c9100081120325a00186071048400745004602414540c056200c1d41d121444680d201c008142d50070381c442c003801c118044040040c014605000203070407000644005590751145080c07400401c0c0000701102140941d541e07541250b0095030040102c0f0002591281c145884100910400c3c2109240070004009540039028403c0d00c005954041d600d0819000b006179500340340d5680045d007565030b600d4042180c1641102030309050840d01850a8a4a014545003405020380c8103860704012008508000540354510004d0546a100303919240b0307181c0741000015844140d601c580c1c92503451b101800f0090003181d00c8240d000b40600414812661516030551b80c80c030a0 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 447089946 1250 447088696 447088699
    0x3181f080a0b0a0b04060c030f031b08041109010305150603120d0e100507120f0605090c0307050c010603030c03020d08010506030703020705030c10020c0d08090a030f0309050d0201050703060b0306 86
    0x2460000d01e4100e101c0c2d01c115100c1000420304014291103010f40c801540150b0050390219404113140d00605800681c4409a500240344c00d0040510b0700311804805108841090107000410020408100c46d4607034140400ca4090000e05441d80d503070030000e0381e562850440701c51000100c80410490b09010170603003041e500018a10f0314281d02c0c0f844143c000c08211501504600690010300c11600c038a0080d0b03400b44902c0d40e10498600c00f0000380e00100c9806848614000d441c01108000c684c40c0d218289034016a4088215102e640307912050b2000c0c4075540200c141546003800101c201504101c00803d494001d0342152b401c400078105c1650584001c2c080c3c3c69100e0010300000c1c28a611a4000348880d1744100d003624100320088024620381500d9025024600b900803c00d1030240780d0070084410060002d03e0b0032483c0e41040c1840a8568222010240400c03404101d2207041c54000c2d0030140c6415440f00890b101d107810000000d0080a0076146200001d040c124000751b590504030640380620350 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 447091196 1250 447089946 447089957
    0x61d040c06020102210402030a060903050c07090e060402010804020a0306090f060b1002062a040905011d240604030b040b0604182a0806070c3c05010b0303181f 70
    0x4842c0510030814030040040f41d061007182717844000a141030248208007403198450700c4c3c0f505440c01c0464103001c1c10f50401d04070b103447c1440070502c08200080403508260282006031031610743d4008210f01c104035030800717803d59007000002e90800082e180c0c00241c1c140900e10030400d50204000300a01d181c5030401d40b1005038013040100312845078901e20141080041143d611441108940001541e080755000c040f800d6900d84c01003140904440d0440844400442e040303038907240c401c42d402c2a001c64102c0208401e1403000310a22039484142c1220701640c1c001001081500d0145045030b08114211684c9000c1c82c1000c2c03020701c003001d00d80c00b03e6030b90680c0000360f00d51550a4072000134642614680410b0040350481000034603450602080c0c0c0203411699480c4644075440c1420680103402c412a296580b40da000300704121603501260341b02c182e60800d40e080c1007208500b841c50150206012256041c0400a0a498510b00c3c111200041101c2030714444144800400d480d584218203a412801148 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 447092446 1250 447091196 447091237
    0x80304260a060b3601090c17060a18050a060801060617060607440913140717090102030c03160315030b01090e0607091503061d040c06020102 62
    0x10340640001942031005000401e118a101c4030208801300304200148001e4000c4089440c01c2c3c0e0440d130002e001d018908010300032000080801000140e44540e01900c168121002c11038961b00c40304c6404c0240842c15201001d4000410303208000d00054442000d60f0303107440c3c00000c03d8034040c05810100e41464640c00c51810440b83c618140d140300400040d4008000c1210700c000581c40c0034161030403100590103841001c403c038a0104103003841040c111010740213901030b9003100240d104079000e108080d15550f0f81c001e06031a08001034280f00c00500c6680d01cad01c0080040c0c550740a01040c81d0a04001e0001505482d1005c000b8201d1106407001d44c91001c0400000b46401c06046100142c40550310f000031708030100d407024030002860341c1c0044a603030b2000d1004101d50380480c080d240d1a10303d01c50181c0000e0405040207003140441c3d225944d0065010500c0000711406944880001c0074045035600c4440348840280d07119410846045550038500313032001c216a0320500c251104244004a08210310 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 447093696 1250 447092446 447092453
    0x815010905010f030f150611070509010605160501060612060617010303080402060c010c020604020112381f03060b34122d0503010b0a1404080304260a 66
    0xf64805032456060503200c40010451404a21410fa00000c00c03d4002008a00b4098010070500308070b8507080f016440460103109503134030448054111485800d02c0c90340c4940c1c01440310080101060702520310b502c0c0c4480025a141c0148205201c1c1008078410031106445404c15a021b168031a45000850424001400040d008144864000d80000c0c03016080071a514442825100d034111003c0041c1c2100044c0011560031400940c0c1e611440034083c4450f4007006180050b20320800082e4003030586014031401c00c00300d1069080304560703001d002c0c0000d00035081c0e540e003200b10001685000003850f00000064101c1c803c821742d0f002d1004001481e00d111032415140060011444043c0014080b030301c0ca00d80052104400c0d190700c410070351603115615480c030409181030355608507002c0a842203c3ca450b900300b0b92010442c3c1c15120251244d0b9142c0000100c03c580d19440d9202c02e00c1c90000014001c690180000090001c0f501010b034030b051050a50071580110760b404090600441d400746401c1c0001 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 447094946 1250 447093696 447093707
    0xf0c0b0c06060402130f060f030501090203060906100e0d080c070906081c020106051e030607020d0f0822140118020a120201020c130905070b070f170408100606081501090501 76
    0x40c6117946070216040c80c2c0301c071030049604259600641c003194068401c400c81c0750b0036005042c0104100481182145040400328001e044010300462003490350100c400c3c0d84900550016160410280400c805442145401030803a801032103030516512589100241d0000340e4002d46040c1c1d0044d5010300324046690070601d40c0e1113880b107449000e554a0780c0020440b51203190303400c54240400a182440c0c4440a0203050034401d001e41241c04540010f00d103a0303465600700707009040070b007241e1070100041c1d60b0303103000d6030303c844420031180f1002c1c00c1d07a04d0388405000b40000402c4181c02c040c0300130808050011400c140010320250002d4008110320700030005404d030307803107440455401801610079013032554000031300e085121080c10311a1a0b46aa0710741c28040100300c00780240100f04565440d10f03a030754541c00b090000c1072400a214040900384054120021420381c0d0050400704111001c0426040c230384070142c505405070100150514001910350b034a045040b4a40309010b031120600c0f86c1c103202c01100e0 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 447096196 1250 447094946 447094957
    0x1060302240708030705071109040c1a0c060703020c06071d130f0504061a090417160f2f090c030705090303070804081e030307121103040f0c0b0c06060402 68
    0x640700303010440100f840b00009611490140c1d407116501d0010380f0f043c0c00e407030b4102c24445000b0f0400d101004001007410b2550300c1540c3d1250990701e294807044005020a12403502c80c2c08580c0103d101f4010840c0d011313009065000b00900030b982455503401c03011144c00156412589034641c00c0e08451845041c4040342c030007115405d0102003143c03031820407403100f83c071000e5038115855071707a0b90078006405110070030b1818040400c5402c4046801d25440e200c0003003080c40f240300140440006e569240401d8410600010b0758040c18208000c00c0505202c2007640794103c0c001c3d013001c820041d42141000c40c42902c1d058490060211240b03440d0325540d05040c0e00010030207020310100700b24070055560100064003500744940c010b20303656414034001c02d04182c0c281c1521070ba604611340310030f08400404015a9806101403410151141d03813500008043d00b10094030b04005040082440140001c0b24105603032640550301c000b1040360b41d9610b10000d4400c402c00100c1d5034104e440403e03080d1519400804 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 447097446 1250 447096196 447096259
    0x30109110a051c06080a030c05010501140901090c0c0b011d010e130b1005150711030601061209150603050a060b09090a26040806160c020f10030e01020406020304061101060302 77
    0x26810745440c00079141041b0740c841035020840000c803003010801c00b4000c0300d024003050100b500240001201051106006020b441c0003191141001c01115110b80f51030050150811411007003540d55884102c01c0d00600442c003030703148c1403076070000c100d0f00c0807501d120b8014001d014000b140c6100035240d8920310310002d0240380e031003010303040006403e40e50700042e1140384032017105103540c811103480c00c000014640b09105000e5080b11004116040e00107403100700202c400c074030104a01c555440e000d0b10340302251690309641440c040c800300500c5000900b4819080c41441c0c10000c4001c8441002078821003103072070007841c1d032001c0442e41c000351641d01c0242c0e102c660006251400c0207028031442464106410240e5580e0141041107929544266085603890090401400a2075a0303008103002401101502d4040c02c540c503030b0384450a01c43e41c40645000741c454000c64841d52941d000070749950103403003590f000680840410904400610070107085aa0042003481615854294105004a050b1400303 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 447098696 1250 447097446 447097451
    0xf061407030804020607020a05042306040c0801030818100908010b010309080d0b0109030f060c090b0903120c031605160e06240f030906011a070b010915090204030602030109110a051c 80
    0x1445403254003070f601c078000e252f115564000d04440744003e8034243c024031a900c02e07410070489002040c0c12420b140e05698001e8a000d507502d04100c069120700502d2810650800c0810140d10f008980c806c40b04000d880042c0000d02680f40702c04011019a51b4802000e00004820800f101421100342d01681c004c40060403d2803020343e607604d40e042c030046001c80a40f982c03505c0d04034510030b19900c24505005010702200e203d062403402e5005c82d6035100b18800340d007086840090315400190b01081a20100110000c1e1008448103c2c644982c40c0c420714283d003020402c146802042c42c0041e480450f10484010304000c0c0c200c0d0054a0b03000c0751100801440c003104070100545266100c40200551103808008010440c0f035150034200e030f807100450344804040704c200b8010000015442e0716914110350a500300454180000080b0f492981081c0d4808501c103803000400004000c1160051412250013080800401c015404d1008181c880c4c1c9842030001002000026440540c15490382b24401491400 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 447099946 1250 447098696 447098699
    0x180a060207080301050906090103110402090411030403120506011b1509140724200c06040e06030708010c05070605130b151005090a0b0309030c06010f061407030804020607020a 77
    0x8100880e84079200c20741e6100c0c8000014802d90800302e103001d40024050752460b00319031554880303800c4410b04428080c0704540000d5950100d54950b0001140c48102d4000b41d0b699042905d00500000900109004c003142030000140b41980101e819a6044490140d03d520300c0d090380e60760342c0c070015011181c41259a5110300034000b042c0141070750740a40c00a18000c080e00e506140c4000031011016034103c2240702500e0001c050254881e924081501c00d0012500308088401c448a00b8041886925500480301027800201c8420280d581d0740100010b03020740d5080354a07440e60754281c0761a50080d0003c40c00800c42d43c0000307a603e0b403120380c0c400f16801c4514622a03240ea950301c9404c000f51f40700b40007443c603207405402a00c0d00c040d418050351000d0038928545522000840e800700c101d803286c0c2c001c5507004000030390780e81d2052080740d0340303a251041545c406617107030380c08901c0c890481c0c041d26000842e5138440314400081003084901c0301da00760300c2c0c00079070307076111703800c1245550141c0c1049030401e104420 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 447101196 1250 447099946 447099953
    0x20d060b03040804140a120204020327010f06050a15110102070f080a030b31020c070f0312020303010e0606070302151501030e01051302010311040e01081005011d180a 73
    0x341d4050380c812201c0d66580e5251540d040500d40c4828401449907100f0801004010b88042c0d0171b1907131030360507100075807a0b0b51030841c1c0560002a08420704101c254400000c06010010740c06040c00c803400d0b0604010607a200c07000e001070348209005401030032407002d01e8442c00c140101c07584a004032112001510340080d6643c3c0d10902d4445520845203030b040800c54070911034150150340d0504100303541100441400d13400150f91020071a10182e00c0070740903140001034000b170350116013162040d60200c40705d03941e940c8503441c420762140c40207440e481c41c000111125113201000302d9048941040c051070440e2100420000c459020240440941c420141d4184040b61020030b40c61141414244442c4141c054a0000d010b5420260090030242d1410f420840d003806e5055011000980a10380040d5650100ca800f2010b0310864002040c148451000054040300001d014485041808001d00440c3d9940a44c1721180c5001c0a800b4130b400340e440001200b00802d00e400070421082d00040f5940451184c4 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 447102446 1250 447101196 447101219
    0x4081912082509090b04090203120c030919050a150203031b091021020a021906180b060319110d0320011505010e01020706050304022706030d03110409020d06 69
    0x10842d001045082008100040e2940300c2c0620007601039a0138082000c071a40065200c1000d020382100c0d006000c15642403000041050710f84281014000d40040c594040f2031031004200c91044511410705544003249002e88221007000360b1406400960a60301c070504007042d2a070b00d10942d04400c8000340401c45203035443c0780305840b2007481503d940754401d44030f03a032094400108400c8500b00500401041003042c3e8005542c0d03020398081954070f03954242e9407800e84064005c84212614101d401d1034080f0502c00704590007800b40c4802c4045031510785080c5040004031614803005000c00f11600b030401240d0a1200c110800d0324801d140901c4544480071440600a0115100100350781d96040b8165410358512214005410b0034200302d01c0c6105103200003540e84020b0302400c9c0c00c00c6800310105045495144c8860040c3c4c0003401d0102a08591140c814543d000403a0840d1285c468075078803850150007480f824030b645081c1c841c2c2034030380750514060f1406580480020400c46688a00008184e030450 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 447103696 1250 447102446 447102511
    0xc0315021c050a18061a220b04110f1305011e080916080c0a05090906130c181413080f0a02151509090303060d060908090301110408191208 61
    0x3c541c0011300e80c85040301c1c40a1081d4003921366002c2e80b8850041e902c000592101d8146100c0c071f43c4004900c00000c0c0020030003a01c1100d00413074a1050101c0c0d2030750300c0900781c2d0240010340e07d5002c40b032102c16551001100c181403034400481c609100307400401c00103032050115580c01001d82084504014525207087c141048960199166803ca0400c0c03152078075001d6041da00400048407040198146881400d84070000a000c5070440c100c1ca90302502040801562800180038180407110508070103180b450117040c0d0000503045039609480003500c80400d000e1807032505a00100114242055003004824a80c08a1a000700f54410a09180c0d03650001d421040d105041450b0f02201c1c07017070500148005240098030040c220741041c808c10050781c4980014024540c0c00840206207004c00303081910443c490354290942550a0411203a480101d00c1c00a00440300309104403990480261141d1800303611050000f08030048015a11082900c15549070b0740140010754203a82d0000007403101019001344 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 447104946 1250 447103696 447103703
    0x9010b100c020d240b180109091e0606090b040903020d030c051b01020c0c0a0e0c0a030207080a02010b010210092402090d03020d030510030b041403160c0315021c050a18 74
    0x400b05000c00e1801c0c40c01032400304442600d20310381d2580c80c2c2900e098042414088c03101080d6840c500c4000380000910b00e01c2c10a000f64400b41e40401d101e0910102a00d01800340000c16414090103c1282c1024403034484800d4040d40075112500c1c00d20000c402401c01d66400c02c0421a00f803003070305078240c0b00040d062106281c03000010794903500307c0303010790900480f8405588100e050306810001740980a81c6d00341e20003801e90f10f10750750b103011210a80c02806a0580908441408507075000c449805511549082100340c080b0354501843e08101410b844483c03c00400020003000e00d54414070165242013030a40030514058144002d00000c02c2501855990607401a400f411417602001c0d01441016000001100040c130124119114480500f101410051003805241024602c1c0302c404d0050342c604e82030074030180c81c401815041001c00701c60b0a010a0300e100302e100f5800c00407251203108550074102d40f4041950902c0300c0340645002040014406c1d2401c90300c600304040c41c003007840e0f18044500d11 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 447106196 1250 447104946 447104993
    0x9050312030108010f020903060a0c031d1506060f3f0a06080c0f120a020918060c28050910030203041203091e0f1b080609010b100c020d 60
    0x5081c482d81e00b505c8010141a0302e00784100b0110b101500c1c00b04940d0340c4210119404a410300e02c03508200c0042c070041700c4a815840102200b80741c45040480c0120800c00068141245070b1500d03410400c0b14440d00d0750b008070f8800304004654a400280f0015201c2c080181e05000d07070108070000c8007031303e48045020727203c0c00d20310070382003000c440040c1c811140502160002480d480403c2c0000c40d00c4403078513002d900d100301003a2040150014041040c1807401c0d0f40a403004000303061641d4084603140f08140105c82d9800b5110000307240c41e2480090310700700001807002c1075507880c40060100c01940303460841d5040010400c00c0c10303000c0d1202c080d00c40c1ca1040a40c1c0069503032a01d810146100180404c10804050a01405201148404070081103044c1078041480c1e444000f40b400149215a00e10002c1186074181030b0030341e01070307502680c8074200c3c2e02600580b00a41c2d03600f40c0c01402c07214005906a030103032195800300d0b0264030940c4100300e458400350565100700304c2c1e80c5030310304d045a4080d070000d46d824 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 447107446 1250 447106196 447106199
    0x609081603050a02010503040813032f0d08092b031e02100e0f060c0c0c090702100507141801021c0e06030604180f02040c0e13050601090503120301 65
    0x104854880c030400c12840e01251800c581d940340d100c194200c00641000b501001080c28003080008a030740041e4039142c0c1e4030703500d0764030325101081800062509240240307001c04400e46c030003506104002c40b000104002629001540d40c1c0b41241c202c8203046802c02440e0080c00c00600200d06040c0c0c5240e07445002e83c070700c00c440307140c018804210b500e85050724090410022640315000125000f454105407008600059401c20242c0b910307044403441c41103846030310140401c40c581c010003800d1003014101581e80c201e0701a007d01c0600c400686080c0700680c07000101241f900e146070322a0750029030341c0c944080303045030000f038040c000d0b04101e800024883d69141241c0e515078042002025030900811994201c0420810141006016000303c9000c2d020000000300540d507154015440c0181c4064415289480c2d400d00f07500f00040c0400480c0039618280801c40503c0c087c80f002c3d0268840140040d0781000740d81d80321405403c0180003030303050100c407072000700d071036642170207600040c12078400181e0300c03136 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 447108696 1250 447107446 447107459
    0x5060112150e0d12110d091103011103010905040201091505090109081c0c1b0e040c0503070e07050a0e03030c0a06140403051b0705040929160c14070609 67
    0x103594400301c00c0d41103890801c000d031508001150b071848882c0c150800c0c03681c081513074034140c02600341d900c070f00f14146200140c01d1207811900e50200401d1802104040c94490340d40c0e0034142250a1040c00c00181041880104000c02051300103e510500c1890000d0340301e81c0c0c9000c0100140e0f031803079030100400c0001c01c40d0f83c0c1d5541e100c91102c00814022004049401c0c85080c9000156820082001007092140124042c089140340b0300401138400c08410b501180d0700e0b0ba270000360000580302203481c5001c04100107054a80003407480240c0d40f0440460285899115003500c00383c1c07081c0315120070312940c071281e4201660103002401449200e8800b500b114034052902d07208980c600c80e44080c2c0081c07400c00744000300c0d50010a9480c50040d110000e041910100c41152410902d03500c11a407081c00c24036500c041080200c031036064042000004041400011000c08071309000b00c7c3e140c2d00c40141e03070301810b41403880340c0c028a2086004040740f01c400c011100015041403072a800a8010803041c02e41000751 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 447109946 1250 447108696 447108713
    0x40e06030d08040b0c0708070b1005010f030915050a0e07030b06040b03010e060609091501081b030a020d061a03030d15051804062a0309060c0306050f0d0f05060112 72
    0x1803611500d0814000d140c02d68600e0051013010b40004280c043c042030440800025108071910f864105e90b0f0441c0c80d2610402468002029000da07500007241c40c2c01a000940c0a4080c65407001e500100b01354801c1102c8440070010080103000841c0d158442c0d92008140707409001903005103000f480407030b0340d5181c0a03052100743c44a07c02424046d070701d05440329040d0403021030035a4000f581203c0901c1c2d2515030219080c0f4243c0b040000109880001d000003602c2c2c080055031403041500702c20710240c224441400c050321554194806500458520030400004580e6880141c28001c40c0c1c6070740d4a1070b01e078900401d185130007140f51041c6c090b03680c0001680213003c11558100038101158406030003d41071206100720500600005e08a90316080d40107203060b81d101c512101256040d03036040f83c450341c181008000d00045207060b58928030f841d0011203864403901604090315009058008403000740d600340b06030b09000190030ba9030f4a4214030201c0c0001d4003800582d0003401000000000c0545900300f5680 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 447111196 1250 447109946 447109963
    0x307050f0d0f110f04050d050703021c03020607090513090804150917010b21011805060f061f120f090f050d080609010e0403020705030303012d0305070b0d0b0402040e0603 75
    0x2040c003800e000d00030702411300c00203c50aa40e415140c40c0d09009503444c000e8582038960700000e6004511415810fa50110b400c0e0b4113070032a0007503084580c10748a070317801590325800a001d01a00000c0480c6c03003140c119030707503084602550300c148a8a40740c65501c6104e015950012600000060300f5136004101c440c4246007050b1482441c04020450390342c104000960800080010400c21401003601c4070311185c2c02c1d403016511150b8000707910030070fa0051604640b650b0084808800a2209001040725403c1400c0441c5c0303030705900701210f910f0074040d003000c3d20081052282040429118030400414000d10300981045034403412044092045501d010b500706180442520200f00b0b10f581080b006075100f0105904481c1c1e5003c04070541d449030b05080b81070490791b400440c1c251000000014507800d8050340c0c0d050b81d20001001d0459030030010300c20014021684006012544185014080310b544c0304001c0036094116600010b07100c080c1d00208042c0e0700140d00c00001403000300c04025680c10140461003 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 447112446 1250 447111196 447111221
    0xc0106091515081f120201180509240a03110114030717070201090b07050d0b01020703050d05031009060603050103020913050d0f02010f020409052215020307050f0d0f 73
    0xe010a0520307810002024242d10101d080041000129a020011180d5807400d1110014201e007096110311540307401c0c102e266022400036120044200c2c1050180b501141500c0c4000c100da02d154540d00711903d102800080394810558510505407a5581d401c01c22078020340c45200c5060802d01c1c124000f41403c483c51841c01103c2c101002044070382903000c2c200c9159444c0340c40580000c0c0c0c546a070304034010070448100070041e1904d8402d0083c0c01c2d030010302030807055240d040180082d002c130030012621981d861000400301c1d440307a200c2e03040c0b039401000916402109450003001041e90361880c041580d03c0c40d800f0402183c0c1d00d40051055050024080c4e41c8801008800070000c0050340d1500d54640c07030080c0900410551072074003c602c0d80b003900b012000012328102551582d4032003500100511007940c0130780c2050356a1381d101d003d203022003402402e0b09421a40103009010150028006940014612000c001b41002818001075004002d0301c125800c82c180012114078031100401110505200003 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 447113696 1250 447112446 447112481
    0x1060f0f0e130201051803060f040b010b0901050319140406090c0b280201020d0207110315060319020a0e040501150512030405040f022503080606091c0f080c010609 72
    0xc0407810040b84402e1000390f081c601141d4036080044c40118010501c0817069040c0128005c1c40554514900c807030340100c0c09900c500780140d9a8441e1140c09124140030316010410610000e0b41c1c051101018800070480310401150903c0a0740000b002e4950450b022105141d49501200520040c403c4100c041d1503c4103180d845d00130307041c048000b4401c145086001c82ca4071681c0e0441428400e40513030340c146800c620295218a01c600c1d05601c0f4045402c0518000c0c804c4012003503500b1840d06c40b1900407000503018022000e1103d010708240ba16108041e0f8204000306800140070042855091146004100005101032084c4107007041c00400d83c0094881c103914003401c0c98081010007181c0c00c0f030b1004c880000b80c0018841444019015848903107102c0c2c5a04020b03980b802c110000d0803403115100703940340051540d40d802049981d00942a1150b0001c1e07a840d44202250200c43c20440500d0040500c800e0380301322035950034130640c0304011203183c50351a2072080000011318050880c1c01003208210 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 447114946 1250 447113696 447113701
    0x51501060801030f05100e0708060603030301140d030c2907080402030d1211120f0709080721200f03010e0d03020901110d0903150203041511040801060f0f0e 69
    0xc010741c00c10f01000d002c014001009204100c0100080b4501242c44d100520001d054210002e031198214410344400e40a140b0020310320b4030f03003c01124180c034800c03640012500d000304140700159940003000c80174445490300f0480816100d0142140d40e1060002d120b102166076490001419005001003041c0074200b401d010040c0d9011450258030b04191a254140e100020800000b4292002c1340480404000410644480001440902c01d0715071882c50840c0f5100c0250445881016100354046a04034180030701070b512240d1170615019485104046000701e89840b0030099240c10407002c804822001e4500c5905d0415142419440004600800c500421003402c0c584405240807a2002c050780003c10154903800303480c4c480400041388049600d075046400307015010004a0200341c403001e07841000321030310109034021a071090b80d02029089060440e0201c120207400aa801242c8140040c00082031010b0240710b0040204962282e90036980d00d0540c00300804000d40d0014003c15159404 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 447116196 1250 447114946 447114959
    0x90c05011b020f03010617010c11030c0d050d060e1e07020115150915030506010e1c020f0a050324071b0807020102120d050a140105030a02040504050f010e0a051501 72
    0x3001c0710094040d00c2c5400001c141c000028010400c80e00700d8980d41010005034212544d0541c010415a8000e84604207030780d1180c50095030364043c61401c008194040c600390702d80280700d00094140c40850120104450b03481d0010142d03010701c1115440b50700c46101c085240d56103c2c4400c1c058003c05580002c2158078035002e8a02a049600c0c066001b4482814080d40b414a00c1404400c3c02440444100c100c00d0024403802030242400b0b0306c4c6ea5000540d19080f107002813400d00007403141190403401c20803c1c00404c1d403e100d42781100c8201c0c2030f808001c854001495440030300c05d110345242e001200c007007800640320350388202c4440070340003078100801c0c400c0510709410002c10102c403440d0481000c43c0c03600d1007840100c1c5840d550080d8002c90b11070100e114941a442c6812940c016034480100f404580c220000307079040b600c424814154135074429208440036040580c05290031900810550b104101150401c2d8251224141522004d522240c200c0c4103000082c06650301c055440e09500c49507515020 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 447117446 1250 447116196 447116237
    0xa1a0a050114091f180b0310063009051605092406040909150c02030301170a0503121909080915070218070f1110020705070315090c0501 60
    0x2144181c11680014600143c1e544540081002d40d16400d00642551a0608018040e00409600e001507256407070010921350f1144042e41d20440c0300001c2640c3c0c09103002c204840480c00d40011b640300c840c0569a000708415800307a120703101d900801000c5400700e00c5191007858100c100305400c0d0711841405d41072080b03980e1500490742100301074804180f4442d1007172074581e05000100b08503500442c0050300261541c05500700c0c020650040c005003d40d4180c2109020550300c081c846540140c100f04010f12021a41c5042002038012180441d24400c1560b5a41c80c603590180c0200500c090890081109001e045190701c50a01980d5100f409003072070b5952011a91302814a655108405039a60f8400740c031100c1013036800f070b00e030000c188803020074010180b110170860a0b6107640001e040041140c400320b0003450848000c070340000003403200c0010856028025040b901049a20380106d0000001195003410a80c0c40301a000c04001a1107503030740703850384100d4585d501140c18402080c4000480d1180756 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 447118696 1250 447117446 447117467
    0x6021504020a0302090712020c150a0b090a110d1a040b10050d02070f0210030905010f1a191503020306010f111506060d11220b04030602071a0a1a0a0501 67
    0x40d10001003545501b0803e8405107041014201500d00c0400c030300300300040005100c094862104600c81003605c546054400b6901034a110903040309a00000c01c540521b41d9102c4003003010a01d5907c1e0414201c4542c4c074003960450300c5c40c103e11485082c41301c00700d841d0501c900d10140c102100c3c129040c0d00d80e10006849800b070035400c0c05101c1c0e40441d6410901c030310080092801d40d03004181c0c5000c4205044054028100308005940c030398a8980e40d41d401d5034a91282095289d80044045080c00701a0100310070071140300306e004014132140750f001807100b10220030f040c04c0014644015031a881c00c5000100400d1000c265030003008030860f403020103c80045105506901464040545036a0f20008a9261321400c007130001e030a0300d00240b04411003651800b60600300b494410340388100311000002c2c0e00620190060403e6080100400c100180213075005100042c40741034101200c410001c210034000300129a040900c41e01c400e00307200000346074245000c40c00c031308650310310300c0c2030a000c0001c01402c2c51 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 447119946 1250 447118696 447118699
    0x3030a1107030f0f05070804060309050c060315041a04020c15060402040e01060809070b0c070e0612121b06010f15020d020c04090c05030a030504081002030c122d0106021504020a0302 80
    0x5120070780f4160352080080300c0c1c40076040320a6940d88d40d41c502d4018002e0040c81c0b002d07101d5000381c91410a080c07a1a104480c011a642c0310f410220008030803c12009060038101c0b05c2d4036041d8044485e039503460f24000703010350b052500050803c4460040c00411014002491240f08d644100720a20103842280340c0e450540d0070614180c04540c3d0b070000100d1504419801441c081e00c80030840114a91000800b903040d41d41c0424516101d848a00600441117200026020b49030450294000000744107006401c001940346200d1402d81d00c60de4009003002400e030000a0303110780ca10011300056001c000b8400502c6102d00c020710714240b50a80094451103030200340740c8900c1e01c0f18980824016641d0b2443d010b0403004056426008461602074001c1d1300c117209641c054040ea0500c00340c100e88510030342e4890701d440a25149070010410030007812940040028909070034020200a12110450448a469442e07003856011941003e002a00e8005900c000d2500140b24104000041e11403440c0401281e50 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 447121196 1250 447119946 447119957
    0x309080a0b0f040302031605010e070f0f0b160b010b09010318030f2102030c07020a05010207080601030204020d0e06040303052a04051e03030a02070e060a050108061201110c03030a1107030f 83
    0x40304e00e412825031007060020103101c0a111f240c08184801948280c5081c2405411501072960312400307002d4905c490701c18092104e03461036003005110400401000901112280d46603850044e6860240400003a008140f0700c190208120805503014400d090308440c00350030504034041183d400330900b40445141c103003001402030b200090318841100040d0132419546003035440345011202202c1c0e58020f178400341d2140307150f9040001c2c0d550011422005991085014100c1c0d607003540c0071f00c4007035800740c010b02c10101e942d0050b01981500a0044900442c8207540100e110308100700c4580303503c0c1404041d00080c041056012a9a1842d0003c031004c45030113441400102c0c6014014074840c69002e01120340601001410304806070303010400c40c05483c90528001002d490702d038140f0101400a00502d4042102600400e403645130000000140c0c00c0800b0020a07581140740011803540c01000c0e40301c070954004014040c42c100d040c0204803a072840100c0e52401c0200755200180751003002d2040406104 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 447122302 1106 447121196 447121201
    0x6040623033c0106080a0f060f0501141603020a0b011e030f11041d0f011a01050c01060b03010e07021b01050a03020a18030b040309080a0b0f 62
    0x1c80884019281c01a01002e41803604003002d540d089010299000361071000050000d03030283c50305a80d0140b8500303100039114141c076111541d040b40241000c00070b00c0445194800001199802d18041c1c4514a0120f0400142c2c8112100103074100c01141018092580001e002c1170003d114260302c400790380e41e070441030034030b100e00d54480c0700a00071004081012521410301c1c1e0803d580640c0340c4140c41d291090014007129003206040341120059480c9260160050100030f0600307000c800240041c0b9802510140c01007c0b1300c1105041c003d0104102403030101c01d40c0f11a0180654110342c540d256100c148441041100311228401031040c810050342c101452114002c0c907074410b0b12082e09052100c03900ba006034000f070101504110410b420624603d098642c09002140100c005200f80e08280c1001420030b4400d030408190fa9001d00000c6001801d203050441e4001000d084038030094 = true := by decide +kernel

theorem cover : BRFrame.Cov 446942446 447122302 := by
  have h0 := BRFrame.cov_init 446942446
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 446942446 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 446942446 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 446942446 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 446942446 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 446942446 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 446942446 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 446942446 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 446942446 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 446942446 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 446942446 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 446942446 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 446942446 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 446942446 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 446942446 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 446942446 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 446942446 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 446942446 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 446942446 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 446942446 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 446942446 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 446942446 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 446942446 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 446942446 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 446942446 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 446942446 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 446942446 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 446942446 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 446942446 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 446942446 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 446942446 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 446942446 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 446942446 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 446942446 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 446942446 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 446942446 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 446942446 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 446942446 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 446942446 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 446942446 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 446942446 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 446942446 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 446942446 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 446942446 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 446942446 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 446942446 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 446942446 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 446942446 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 446942446 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 446942446 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 446942446 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 446942446 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 446942446 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 446942446 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 446942446 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 446942446 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 446942446 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 446942446 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 446942446 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 446942446 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 446942446 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 446942446 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 446942446 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 446942446 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 446942446 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 446942446 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 446942446 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 446942446 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 446942446 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 446942446 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 446942446 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 446942446 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 446942446 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 446942446 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 446942446 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 446942446 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 446942446 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 446942446 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 446942446 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 446942446 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 446942446 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 446942446 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 446942446 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 446942446 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 446942446 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 446942446 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 446942446 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 446942446 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 446942446 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 446942446 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 446942446 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 446942446 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 446942446 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 446942446 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 446942446 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 446942446 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 446942446 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 446942446 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 446942446 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 446942446 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 446942446 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 446942446 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 446942446 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 446942446 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 446942446 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 446942446 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 446942446 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 446942446 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 446942446 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 446942446 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 446942446 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 446942446 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 446942446 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 446942446 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 446942446 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 446942446 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 446942446 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 446942446 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 446942446 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 446942446 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 446942446 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 446942446 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 446942446 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 446942446 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 446942446 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 446942446 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 446942446 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 446942446 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 446942446 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 446942446 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 446942446 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 446942446 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 446942446 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 446942446 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 446942446 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 446942446 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 446942446 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 446942446 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 446942446 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 446942446 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 446942446 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 446942446 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 446942446 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 446942446 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 446942446 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 446942446 ≤ n) (h2 : n < 447122302) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
