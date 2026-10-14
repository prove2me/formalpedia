-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_3059
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T08:32:22.23738+00:00
-- url     : https://prove2.me/submissions/46e4d78b-9c15-44f3-adec-9c2e548403b2

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 550000000 ≤ n < 550179856 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 550001250 1250 550000000 550000007
    0x20a0f0f020a021e010206010b04080a1211010e0c041503052812031505010e101112040608060a08060408030727141306050616020a051c03032307 64
    0x80e11000020751052100d00b10050380e40b0049600c800001040c82544503107180c0019107005c00680041c40b030210180414483c22800003070500c60140c000c40c800c09042c0c242c0301c05458501c00241240113079401e00c6074220319840001840d500b04001600c040007403088881001400c4007076408001c00c0307508011001c0d01c12600165004014969009400e5005405a0b03201c0c041098490141000720341c8131090240200000300c102001001c085c20030040340140000040c01c012a10181036080c00020300d481d9807100c200f00200c101e9030f862007030480e94460315280003030302061040f80c1803481001c6806003c900020f01040b2240110303030007074401e800c0d902c0c0d0f40802c1c0c038a01c07203000030343d00c030720079650090107aa004c520240340c010701811412801210b5850b081c421441540100c03881800d0a1100400580d1590000c0300d41103044580d6000c05030b038040c40007524030300f0140c4c4032503400282e000306500194140030041c2c0c07244d84031f03490402c858001025541d590841c81d0007901e0403103040750005402c5500 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 550002500 1250 550001250 550001267
    0x81f0f0314010e03030108070e251d040c020a020406090c0507020108040807021504150305010b2b06030c0e071d01080a1e02040f05030a02030c040b150c010b04060504020a0f 76
    0x12507000108010264009083c074580090740148195400200c041240348103108807d07030040d903206520051500c08807050602c020794900f444080205204030000052080604014443e2000f0420301104508000096452140078001c0c0c2c0b0071071500c417000404022038400c1f80320340009901c40c907040808580043d6041d8030014015205c8442c10000c01e4010303612003a010510a0040003501e81b620705202c070400082c0700038030f080401e052400c4018000040080250f49000e45406000d40c02c009140040450050082e1032840e4450708100000c410403180b0f02204003502d0341301002c01c805a0341c24108a13a00714010040c070048100d01c004504040d40b140c00801d500034a00c1a000c02e000030401b24814140d01c0540310030083d5a4041818001003200080c00b200815040300104510f00d4640c0001c1d0300d03180441d100358407495a818080f1440c0e241c02820070140c512000d501919800c1515481d8041d080e00b0f10620b1280346025000314491500d0710940d2400c0c451a41c03403000c80c44122005540341030 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 550003750 1250 550002500 550002533
    0x90a15090b030a0207060b01051810170a0902030c0315070c0206040803190809070b1c0b0a0801090303061211040504061107080405150c030f030a061203081f0f03 71
    0x94000c002003421040503000750b018602025006070f03a07444a00700301048842d4000c100341009400c20038540350064203035080014402c120792203e15540c2001c030654440108400180311172240d102048000c91155100028182c02076041c0e9003100e50403410591554224a030002c0b5003440c0310081030049100e22a0824803d00c0540f044c0d1416450300c840924640001d481602c1650015080f070450640c000c1c166900080c03c2001403041074104601c0f401c4501802e01415604016804d180203c6646d41e0007800b50030001800c1c2c401e14030b80700c100b268007900803a64107801090a100c000255141030804128a464100c0310301704650f851441000080c0c1070161054503d6601d4454400c4d0582c3d011008001103442000001d90300c5251000340400050b6141c240c081041c024041c00000031740210407141e070b01c912910050344d00c2d500c09401100500040c0c00960075840d410260804054200440902038041108140c0f0415001e103403c42004010780904002403204100800014800e2143d409114 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 550005000 1250 550003750 550003757
    0xd0801030c140a030b13060605101b050c3015010b090109150e090a050c1614030304030302040914010501020d0f05040b030f061003020313032105011e0605090a15 71
    0x1150fa944802d02445c1068600c02c1070301801c540e001003085650700c15880103000503a8010003090303040d4409130640c940343d44101c000e1200c400d4040104201440025104000200701e05a003040d182490010b0000446040d06158003a81e0042042c10780040c1380c02800030554941403a0341c0c28800780103816044010340e079060020420303003c100504480c0c40c0c6031150311a6520a8550310f80b44040000102e03020b401014903607c5d04c002d100c2d56200901c100c40c105070840e4890020300301c039882c1180382c4110400580e03000e40004000d000c00c050f4075800800803542d913039a007030000c40ea641070420309903242840b4480c0580d0020403000405400f03040c28030155190b5061183c14035941d03d142e40340ca81d00444142c80e800c260401003044a240c8540061441101440e04604503d0409484800d9a080d11006001c1c000c85429003480401503090304d80c10005049403d024950751070358a0030005a08007140c0303001c05ca5403800840d02501c03c80586110620041942e250b082ca0000759402c2040151000000c1 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 550006250 1250 550005000 550005019
    0x317061e131b02071d060603180f030d0f0b1018081605191a16140106090c050a0c0809060403021203070203161d19090303050103050d0801030c14 64
    0x240c008901c81c1240b41509241c501005420400c0d00038184031444d0886202d00e004007041c4014814142d24142d80a041030300c910b03a07a51603d00114106d5024804001921310801199411051012026260701020b080c0d040c00340404a0140701c0550300161203080e007100030440042002c1e440351144c0c20b501040100240c07082c603194007126040c5000f079051800761071700f0250304200906018065640c40480301c51040c1c0f00fa81803031960003940c5010310110710b0352000401c01540210800d255180b030164094081030328020b0b036407030075400b90003103214450000703107000345526440e800f4000f00c1c0d040c06290f40e9019081499a503940020f508006106600101c040c071001c001a11040c0d80800d48071412401036481c0d01c180c1c410540386c10040795270b4464a9044000400c802040f0b440d5075046180503044034605591003600d12103d01c080100c02e40902801c04500c0024550160301590680780140e0549421544000003a942d140080c40024910802c1d030b0780400101d0f0014070b40080000d4000c003600503 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 550007500 1250 550006250 550006279
    0x209030109081b03090a060f02011127030c030d23070f0606080a0206070204360308010512061b090604090516020111042108030f01030317061e 63
    0x312004100d04403070315440000c0c84228415001c820081410f0a030008500c0d08450130081142e5080600c244014441c1e42285441241d0003904100640c801c41288192104444030603492100002030044485e014090407846580c00d011411045408000d4000c1180c124264811100c1c600c104098058200282c040c60b56849a1540205074060282010045955081c200303501160030f80d51000002350f120800d0342005843d908240c0d0303100c540466001921182440740076041c18403400124100311082c00742164120f17544a40100424040e41d220003c9a80b500c1c00d03c00014510351499440d80d02c1640060b4641aa004e42d011030380c85c01c40885418030380014003040c680d401c981c0009401d03035102c80802018a25008406079900b010384000d0140c80d0b16008042031500c594080e0b158000e1860344408500d104020344244003aa028165580d00c0c40c0204000c03681ca0300a020860015010345904c504d0f505204a01c14014080103002186e8a100c80c801010710120b1003260a4011000150094 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 550008750 1250 550007500 550007503
    0x8010b090a2309090a03021009110316140603060a03110a0803030f0f090a2a081203090706051c090317070908102003150d120306090627020903 63
    0x240071950450903550002e101100300321400c24002c0000c046540310600c0c8001082e800244046043d4900d24001090384103802c1540b01483c200c0061742e01417080c18182c2c94070801c003a5503d804c54800100d450107000018041020f5480140c9650ba8001003480c010300c007085480848100b0001c0c018015a6056a1140a00e0441d04200c40b070358a118031900400982d030301e00c10351130344d84a640d407c00351249011690701e840c1400c6411194180e81c1c1c0002004900b40703101e12100340d02820009080703c5102d038400c051074410340e10403184040741e400350020000e02e090080741075504982d801c0d50154443e541610110004000c018030030b8040104000e0031520880c03091042d03a0250308240d6a010309242403000407460303c4035001001c0081c42c61314140b04d07540381d018a01004a07050b0052403964a4542d890391002c0c114005180e81ea1120307240c1d54100801003134803a002e15405054905105940d41c0e24203c804a441c07034869085182114281084d4101d4407500310125078015070b40c011300b08007182000c05d = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 550010000 1250 550008750 550008779
    0xe101e0801030506070c02010507060b0a1e081c021f0209040501030506100e16030b0f031515150706020a090314030a0305130201020703142505040b0307050108010b090a 74
    0x1004168203030014014402d00740f2561358000c4003800d08500511899000a00380d2082120140c40b207a52404c90010a5540c10400002040d480300751042ca6040dc05e203081c021800b070b1192000e1780c421214880b401d8020711a01e41411032564010300442c90780c02070148488200b81070034643c11a403c00002c003a0b0754682c03013540d020b54010300c002c100c5460503030250044000190420400b40c1030321800c02820700035142b12411420350900c1d000c40c40c0c40100c0c020038031941d95030384035035418021044200810341500781c20500c070304059031404ca0f408454406000002c0040f0f1503650450b181003201c0e4001c110150004c200e040f015190203019260389403a28086002400c0941c940d03900006005a0800d9040c06115003000780c01c411008801259030002c0d50390900c603c80145002c507408500d0b000c10009001e070b0264841c00301001c03100400d246030325640d641c080780101d920583c5010509a1241000608001030390010b0b1036509040c0d0a044c0044541d40100302c22640c4801c032050003090006103c1c80380c = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 550011250 1250 550010000 550010057
    0xf0c01020a0c05060f04020f1e12010c090f030f11060c0706210203010e070804081210050a080318040b03161203111c05161a010501080106050a0e10 65
    0x5814520758203141c014202540503000341e0410211005200c051798480015034146030044840d1270f030724122054041004039445054650186907600555404d82040d0003a0f0518901c9a0350308100f17030385600340785d59544181d0101402d907041e4100100c00090600350700c1c12083c1030040c1014149800c10189600d449856081080002d503101207610051204030080d81e20440580400e50440d0705102d01d84864120081130042000740200100e030900c1071b040c01701c1c0c1c40c0340e01201e1a4103c0b8940404d00b8a18501c007403080a00480403040001080d007404410f441002d40307040d040030800e80000080001526002e04056454040c541d40810b9112040000700e0041036080380b5108044031300d04002d0a600d1640401000d03680000d01d4000d030714400d80070300042a03501400c1c11901d5800046c2028440605000300410b070540314101c4c001c680d10700c8000d0f981294000d0b0381d0614160b807103000491382801007a00c1c09003c07401c195240340c594500349444001c006075a00d01800d40760880c3d02c6030150300300d05550 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 550012500 1250 550011250 550011257
    0x110118051c0c08010e10150e0a0b0f1807031517061515030c07030c0f11040e010b010e06030603013b030a0504140d0b01062d140f0c01020a 61
    0x6201e0200001040040001c25109000700f107689007070140540c131103200c0108202e4244da1303081d01c100200081d00d01180a0641d03124800450f282220042c070040c040250850312a10b030941b6901000d16100d843c4005c1d01c3c1c000300720304101e0345a00105901505020303410070100e205c501c0000c140013100c1c0e402d14407480d0389100249140c0c1007400749a0151401e141485020b1080100c2400303e21042104498110354413580241d40c4586a05044810143c507400c001d041216144541090000345c00c0c6200411104840c100800c640b1218041d003240c40c1c1d10801404615456142c3d0320030700e403c801465110310f01038008540500c0e80d241012281c101ca03844402008484600c6240d025007025040b100e1412540080d07260446011018080340528881d040200c3e044150090040d213419807020b101c15409540c00009584464004d080720407505000c4241c49482c1c0640d2600450715008240703101c0d40b030307221403443d0108c009048a950780420b0505840f010f04000c09401c10703c00748000c0403160010355 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 550013750 1250 550012500 550012549
    0x30b07030c0e150a0f0c05010f0504050124090e1504050d0906020d02120c1e1011090d0809031c0c14030c06011521060e0f0411011805 59
    0xa070094910481c03500014010b64042800390310400038502140d9001004e8104103a200c0445a011103640360145801052075007408101d00e80f50b1900c4d004580142e00c40e500074407032400d0006244001d0740800c009081004c80c140c0742002001e0700382c0c1c0a00c190200c800300780c440d80f10300c000c541001400184c1d02191a9801711010304449a80030700100080c022505c0549001d01c0003410003503842941043c1582c40000004202d980b01d401000742260500d101000e01011406041c004c0351a0a0400300c0074a0351410a01d0f0b1354110101601120b0902c08003c005042c410310700e4542e014980c101031001e60301403260a503440306084d103042451415000d5543c45403901a014603140141103600712071161154020301c0f0000400b00d0100300d060550b980602c41224202ca61b050448102c02d038220b983c0554040c3c0b854070f0302c4c5d190a641021058580419070144180c13202084051907080c11540603003010051403411440c0e601c110101b001d2115810200c8405a448a00003081001c556900300040100c02d03 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 550015000 1250 550013750 550013771
    0x40b15070c080d0503070215180a050d0807050a02060f0a09050a08030103030f05090d02010c020a17070306060e0712090501060b1602010f0306080304030b0910020f0d052a03060406030b0703 83
    0x2084a1501184246481c50860a006001035623445041c0c0c003040000809800080603000140030b0501c20206010880e001b03c411424010748030f01d84401c00ba0f00061b00c0000003202c550140b01107a50100302c5600605d803a640b00c3ca060f040041c17000d0b01c0442099102c40446010850802032a042107005850b420754a500d107240180000880c01d000787c007440b2090004810507034525031428009602820502018a8070b4400a600507150307800c13800c1e1403580c0b2440c45196003000203c03081a07905c5420304020141c3c440b42010f411400444002000540d00403489080141c2a004003040920400c0040743d540d4480550200582111500301c81c80305801e85100700303560307101005c00b6503503400341030411207a800d100000e500d900c50b40c00081e000f034030007201103010702800b00f025010202264204540750300090070704441c0c1c0e038045154498154204400b0516007003400501415200c00c03056021114100158180059000244500d51040d920240000480e4421a60510401c0190750020781c10242 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 550016250 1250 550015000 550015003
    0x303140903070303022503020907030b030c090108010614123403080913090203100c050904090b0f0a0b0f041a030106062102030c030403050c070f0e1e04050c040b15070c08 75
    0x410300d131082d00c2d0b40041c6e041001d07842d09020a50080b005180101d820080103011a141864041440d0782001d045400028070070300640c0000d0036912260014021102c81c401000300b01c86c1d581e10a0714050b000542c0c4c012205421307403d140404002201346444003d0b40e40144901c404403075200fa5100c180c009041411450801000907007404409410080e40c4a00d4020a940da04606540c01a40c0c0d0794204240c0580c0c05242902d1031088020014007000c4a20310744400f01030701c16100f03101c0d6044681c4c0070600080e90b034040d88003c00000707400ca034403c13003e100410015040c51040b0110b4135071545401d0031781e91028040c10000d0182a2907030628020b0403410030200e4888500c41ca0301e028414018040c0d008082d40849070801d80500d03185444850000407241400b409501214013036802141c0000c0c103d4900901d00c0c0300710401c500051110705441c103082600001154014065080300100021600d49a44a07100d401c00103031200408404030200c0b0121a07014007415600c92801100030001040b0 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 550017500 1250 550016250 550016293
    0x1171e0d030c0513060302030a020c0604060b042901080414031201050109171b04020c0303090c0307060804030210051b0a2a0f0f0303090614060301050705040f030314090307030302 79
    0x240c51401c3c902d001075001d4489454103180c0204010184c0000100b2907130501501511518607903103003a01d8450501d482c1c00c400810b034100e00c40d8021404d01c2d010701030b070002a1114407070300b02e0881d0440c40300503180760044503030f648001c000711400c139200d00b00d0039400c1e60100043d010200001c0ca100002d0b5041c6000900b2110995101900709109814182c1c42c15a0210342a166075199007040c1aa035481a000100a0f028042a41c0d030b052101008011004100150801c4c0380e5000341e00b030702d82c410344540c400c907090300b021900900540d02c646400b81100d50543d000c207921004091500301c1c030065400401e0180e910440640e0300040d540441091044c0c10031120091000302c460040c509001d40341c1c0d400346203443c11000600b0752a407180b1140249406500420003c0c1c1c0c1c002000c00042040b841c0540047c142a103819001c1d61034000040c2c8003500440440e800d4031008607d00310020701d180c0c0c04688052603802a081c00180500209919032010040d10300598829005400c0d08211600c0c43c407002c51 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 550018750 1250 550017500 550017521
    0x6030e0604030f2d2003091c0b0403020304142e020f06010b09040608070e060d0507050603040602071e0b060f0a08030d062301091520010c02010c0e060301171e0d03 72
    0x155154403d045d40b840000c101d03031a0000a0b02e00702d009034070700310341703880c6208014901510341c1030410100000c0503804401032044da03c514092080741ca88010074050459210900680d00380140d40790b202040e00c1a06120f81300842ca8411510510032104041e401c2040030780c04130310264404940d000d11442d0a0196001600090f401403640910744442e5415200c40034100900070a482d00b14181840004d04c4900c002d01400b5184540c1c07070500740b03402d40080d0f00055064842c5804070b82c0ca100d0390340307000d40d96488154004180d401651140010452007803180b0350b00715400415100c0002e40c11005101410b4068000800025580d260443c2800c03504110001041c50504030513500320301f607800001d41410355400070050300d00044004415a5071060f881c0d602d9a00160301d110500143c1030540240301c015920394000d218010500d5000d07100e40d4048480d05601c000188014005550b8001c8404d011403e2841201c200743c4c0d40391982c5c0009107002c0f40e240f84075080030004042e1140c0501800c03019a = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 550020000 1250 550018750 550018787
    0x1a010e0d0b06010c0305041a0304060c0c05071404090f060b010206130819210e070f050a0b03072102032d0a1508070611010606030e0604030f2d 63
    0x58455a6107030014070010a0700d0305011500030108141440303881070f28080c2ca5800f00c80403c20700d114900000d143c00856003128134a091508106001d407168445c050790b070740c5c02030080c8002410a0745401008810384c1101e40c20a43e1019040d0114410810902019020701c000142c3c40403008002424243d00610408500c0d2400c9102c0d80000c41c610300b21444824005134402c01e617071000304110b50041d0303101d9002038844101c2122218604c01d07a44082c0e13990720014120b40020b0354600035000b019281d440f0351940000028020031603e19003000441d403241213450310181c10804401c01681101c3c41c548412045540441007280c440081c80c5401c50910315608200d03056080113a1088007841c0040000013442d031268504418003502c0030307507038001e0254881034801882c1c44440040a008540403002019800d01200107001400392240c01503843da1040075040aa442d40c8042d95000040626841040395a0303082011507241c0b505000c10f9048010303c005c204074644079005108008028680d804e0 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 550021250 1250 550020000 550020019
    0x13090203010b1b0c040509030910030b010207060c080f040e1b0306131a0a0603150f15080705040504060905090d020d0206012108030709080f0a08090607060f1a010e 72
    0x3840075079000e488a036a04a12071801c4400c83e9000a400c1402540c445a082410042840350f4500003002a11442909a5501e04510105982242030307810b030a1015004d0303000601c003442158401d0010191003030240001900e0001c2c25041107042c0d5020f584012041035900c02444248558100240409001c1c50700807400d40c204100051180410f2220840280b60358440100b80755000c0149101590801401d480344244d507600054058403101d01d141c035403202080c4002c00c60142d11401740080d1303054911200701c0342c0325400080d900314002601c044c0030306c281440000b602d0b680300e000d11000381100d08004115030902c40011441e00220b043d10321700750341000b900480b80c664001580d9046030300c24a5099001c5a03030060aa81441c50444080c0c28004000704104555800101110448120b0b108944400710490000343d00c07581c000100a206c0a8100490384807480c0100140607031034050382001a04414030394900c400ca494015640040094180c2040382035030300542091081041521900034 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 550022500 1250 550021250 550021259
    0x60504030c060c0f12020c0117090604061e02030a021306081e0c090915210a110f120604030e0a0302030319050c0f060f101401080405211309020301 65
    0x40848060082d18104903102c00303c4018800356009900c1059000501503101d0340305114000d481c0c542480145000c50041b0088004010640c22a540304607001c1029008548440c1d90380c4000c0d01c03040c5024100c0150003400084c8802c03030f038802580520f820410050751901c1d8124200c00d2052140d00410a00041c2000c000b803a0b45170509108102d032158402c6000d03a07a0312004140140185450380743c1040c1c103002042101039481c0c3c0101c50751202202c030304640c0d5003501c0042402d009100e5208100e50409004d42d000180301c00b400d40807a070001000b011800070100c0214400940281500e40c3c41da21000600043c540c01003410140342c101501e5000081d03042d500400d0345c0c1e128580c00103014048408820562610070300c296a610701c4c0d40c0c010780300e20f5104042d10690b01e042c140c0f601c1440c0403005003c61080e110300111081252010f060047e840d80b40500191600302004109581d80d0080c814202c0c0400e4150746d200c00d024034035240040d202d4080d110303400300820040d001050010300c100014403 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 550023750 1250 550022500 550022513
    0xb04050f19081203010305121c2d020a11060c04060e030c12030310080a0309030605100b0d0212060a05090f0408130f0302041a1012020f0a02010c020706050403 70
    0x35009a09031460701801e803000d1544140e0868540c04211507005145249014040d4800154100ca00410403107040300b22207802084540300340f81c20100354040b4900f0400800041e40c10211440c80740b8905034510340c0d441d021090726840d60011842d04580d001130200c60b69034202c890140d079805504002c007044c0c03400100c05075a91003640201d005010801206200950b8200321024155030050126154503624044090f80c03030304191903503507251542c00c40201c1c3c40c0800080c0d80600c9a0075039280c001d085e2940e02c07010000e00340545030303154500d40d1440124241182500421455440c107400503502d045448130608018000740c04544103501030402005a5610440e8003a04000560300c03200b040c3e2034924041c007103442a40d001284014190030001100c0c24070f108114103e0707000791030a21510000502444601d45903d17441c0e07610801e4040d202044504c15031156013955810280107181928901e40307001e040c1c01c00703038841d401070303440e9820008000d6040c00420000d04190900c0d5003098219904c10 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 550025000 1250 550023750 550023769
    0x82502061b160804061d0f090a021612020f030c15060102190f020a120203070b1b030d1d0703030905012a0f141609090f050706090801060b0405 63
    0x12144850101c08000400440c6003241ca18000c0d0002180394590140f9000c015600306100301d0020400301035900b03000030401446048502801000075613440042c1080110307401c1e010303018803103065081c000000c1c17141e85240007002c018050000600d031040c0101000f8503110034004000101d400604c847d07072908800043d20300d4260004011921280d858400403841c1858030062020040c02d116a0f2001744140010780c1c154942c002d844041c003c640720303080d01514042140700250903600ca03c00420130024100040d100003c516600304501018200c212861034104070300c07042c4000d50302c490b580030218000c103600c1c000151000c094061145542c4004c1c0500c890342c40b07264180b04440217a0140c0c0300c810410b403042d0f00350307400e181501200242002c000511804101700c0c3e500240e651450440b01c030015541004c010b5044202c541e1600b80703101440900001c100031038203560900384040c00188140426000f0f0715150780c4482c506031030040c1090940d449a0f00a88107045c04010a001a46516100 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 550026250 1250 550025000 550025011
    0xe160b0d0203060114040b0c060c07050c12010b1206090105060f0109030b15090108010b0112020415031e090506070f0f0c020108042a030201140c06072d08250206 71
    0x42e00c0799a07480040c0c440003d24102d400304c2040009010841c1440c4070b01405821010b5003c461647c2d642c1400340202d4401c02c0000340050b409100344044614202c2108200c0e080c0c1840046a40c411510103e8140781070103055032401d0300154100711120800340b0820f0362020046842e610b0005241c40003a1040500b8040078086da0450000074003862b840040b1400c0d860006000c3c402c256a60741c1030340303008140b0359100c0c1d07000600f030702c5400304074440c14001d45007940d80c043c04280111680040580007000380c2c3c2c1c0d0034000c41c440b00d5000003880016215500c221805100582a2440c0c50038000b0b040c0450b11107494180054061024142036002410461082d420700b4002c6003034840e42402e40080303c04060024070341c54500e080720300d40480300300c4800469100303803210842c4c0e6440091020060051400e80321181d4030002c001440d00380318180508c03c07044503c0d4150045d0b80c01206000012115070340400100342e0910070700c082074020342500c14682518074050f1060481103080292101c002078030 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 550027500 1250 550026250 550026277
    0xc07031709030c150702060f06011e111204030b01061e0804050a020a06030c110a1e1514040b0c18040213080a14060907080c0103111207030e160b 64
    0x316181c0d020812514040d400c0e008880380c4407501203120b074404908850420040c016140031410b10a11420018011501615100c00c1070300d1403110b410254592202c00010001a4051030b040104103011000f90b404c2d01003a2656603904500b800790103640c0c10303440350041000e60510342006045461008980000f1840c0461594856040c1725180030251440a5803040d0043d0700041d54a030140e00400c0c049245845140406160100c0c09845500b080b8000d0000d14041030040b0480c00c1c4c640b44100801d11503a9101c0e404200524440304850646082030001b00e048810b0009009940c40c0d4142e0241e1a20b074181c0c60451581480d0ba0090142003119010303540100e05010044904640f550250480e0801c4a019103202d050500c048041194010414000e150125050000110f045000c0d0b40c00703900200000d2a02c0c00044000f0407203030700b1820703010801b80140644a640d001d001e5000d00c40caa5004510201c8a5081d541012a046a0005107408054080012048490944442c0302c0b5040 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 550028750 1250 550027500 550027547
    0x3051501060c1511070812010e07050a020712020a030f12030515030a1b270e01020a09140301021b0f0f0d020d0e0612040b0a050a0b0105040e0403030f02130503060c0703 74
    0x64100c603c038020a01c5c0104408030105560100c2c2c081c03188003504a498108180300541c9070f440003a03681d413141103072280c010b8001c0c2ca030901041c8803c6800141c840e101800044842d0390b079440e0100c9860040d042242c490302e8190507990031030ba1502602d0f07044858400d08010020300400020780d5010001001041401c405003000b60600413014514010f080055024040c1050003c0302d00a0340409182d49500301d283c00226090b40805101b650201485600c5008005090540504100740e4814055034190340800070f85568003503d54000d105400781000420110414085403410410030324008a01503004040c81c818042d400200024180480c0c140300140d8048000410058410307500f1514490760ba00060000300700310f090b035461080803d04401c001c1d03a03c4501c05401500da403562454002241170000340200d80c1817050b4a600a4824140002c2841c185e030245004e0341c02512103002076000e52481003049090501c180c0e0f500103031211a9510300707034403940e000e0548a4000c03080d01d5241c7c0d00c103 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 550030000 1250 550028750 550028771
    0x40902072108071707111915020f0f0f0906180913051e0a1205032203050403020f061908070f030509030409090f170405150702010f0e0103140103051501060c15 70
    0x202943e280380540342e001d40740c07c0d03d24007800140704e1409000441c0c0540a004011011502d50300c25500c03500e008400240ca0030705154440045500300c2e064003400c0201c100030b002065540c00d0010310b00f00d004441951011003c8908104502c00000c00c60300f15081c8440e4200001030020034134007421040348078590075200a840c603003442c049841c04002d040c80d01c590074000e1110b0708030000d544281428403200c032042e9034062181280d406052002804102d003408107200618040001b400786d848007900440c01c280501e4042407564840324000c1d008a01c00900340805a0b51120700104010b90300d080a020038100000700503034034403891042419066413080d0038420402121801440d503500402d505410795403c00c0303c0011940316103c4c840c4903c00585000080c0841030f000e5460807a01611420359054003c6010b0b15103c1c004402141015600c0440d0762181507004001c5010710f0155004102c000950f40400180b08010b820200a10008210040000d2a07445840c01d02d4100141e0204426911 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 550031250 1250 550030000 550030007
    0x40c120c090c02102306060a0c0f060b1003090203160f030f061b0206070e0109080d180807090506040c03141815010b09010207051005090f06040902072108071707 71
    0x5600d402c01c082d030500b012445c08400c0801030344005054008448010f4454204001b01032080c984014080f0341c1c3e403080000841e549890901815002d0760000c81d01d07401d81d000240701c402c241d04100c1d002c00e0741c03100c401d001c1d800d0401c084103004041d44400c1140d24240130084110802074440102101c0303006044004000300f9403c000040c0d0b840010450443c403030030402075120b810460b422030000e04441d0300307103180d5841000f03e1002c492907000a00228000d48104560201907210001c01c0c0010b03041000509440402402d07005010806000645040004c100000d450030300e1419820503090000307056000005248a0350003c00d400420100600060a00b5041140c80c130281c640b5602440300005000542000400500b40c0076400d031980e4940340c07000c001c0c0003002038040e00c1c0016028800700142d82041800d04400540040005007400e0741c0301202c00503a401080300f2903801205903080d07104407081d80700102c404049030805e1415450145401403410303002c5048600c040c150b090126482502 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 550032500 1250 550031250 550031263
    0x60906020909240102060403120216080f1312030e010f12090c05032e020a050c0703060b130b090705160b04051b04200a021f05040c120c090c02 63
    0xc050050b02035407800c0401201d02d03010040001c0c694a200c3d54210312036610125a05110b40d07855115480b840740039400510003034112200c5002c2100f414800d00c0c1c0030039468000ba200080341e980c000c2d90b896104c03844d0301c095129540e001c900c0e0b010904034281c00094010821030201ca4083c60010480c50745800c046401e41285403d50100914043c0f54500f400008810081590303825070461310040603160036100c002d6410304074070b4601c1d00e0214a010040c10250000c001c0d000c070300d2178828184440a1a01801c091669104458035640e03a44407425600b090b030065040c414559100300039680c1800301090010400411b03610400500148c810700312201640300740b00301074008080c1142403502e450300a5032030360103c1e81001c99010450f41c0d00070f01d2420340904034110124101022842c4440f040c9440b041c0c03c82410002035001c0d5840032841c09400002d40c03111108a9500800c035400c050910341c00c881025008074401c0d000c1e01c130b04000407440130410007007111029200002c0020140d09c00b2030a106 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 550033750 1250 550032500 550032517
    0xe0606070609050d2c0f061e0309010c08071403040c180c021b030c090907080a0303020904060f060e10030f09050a02040b01050702010210020c1e0f0106050405011206090602 76
    0x80c81c0110b40010321a000440504904480c1c40b07000b0040d02c080000d0f00801348485950090002c00c0407040345904105000c0110084013074000c6060150221a00440d10440032030070745098000300c200035004800f4000e580310810582800c2d4140d04007208001c083c103051180540d90030500002007001c110088201c400242600c110111024203000400006001c020080c1c90052241030385441600c5880294500c0552000b030041110800d03590501400c41b50061031085e1328001c500c80022071040c14440e01603920309c41d03031340141d5840c520000c200403100d5a400c42c1d088402e00d88814448c044e00580820022a030898032810495188a0120302a000340d81070301065505040103401000700c00919000160700c03c481c14040b49444000440f83da001c3da4a020740142d11a8100c400140350383c0c2c0c0200282401801912100380120341e1010512a9580f46000326900001007502c11010078441d000c0a088100e03000d21165140c4030803040584038166010700700c1076440301d001e000c215403a030480d054403 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 550035000 1250 550033750 550033763
    0xb07050c090a02071502181201021603080106110706080103020402220f05030c0405040b060105030a1b090602010b03011a10170907170102070b131e110f010c0c0e060607 74
    0x92034101000b01c042c0d009100201c079107030300507404070321506118000d94241401207650014030b0081c0c0d00405c01e61044015070420341d03540c2081442d0280c0d407040142e915582c0291200040c41d494868000c144050501c602c600d940c000450030b020f003a610a207402c0c1101c0d011140542caa800ca5500244442c2030340c0041c40080302e200c0400104103022108140c00c40f0303022803d89604844010502090b1007044030010144000c842c0050711540c007a40c007031500036512000004000c000c1d540c04d80c082a0b10408071038007188100c40100203940d4240595903600c00c0940090044a000c00031f11a282e1006580007446074a403100021003c40c802d0010520411581e101a1030a0402900741d130780b5292076025903810402d5620303003004e00c44814000c0b00d00840d480002c9010b1035840002184428081d0310040b540090901502e00d10300a041c894403000b180200004c98180c801c0904003c1075664000005050080d10307d000c101107500140303600d0488502d0700385604565104000581c40340318041c03004160 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 550036250 1250 550035000 550035019
    0xc0318061d04060308030417130e0609060f0a061d06160b0f070c110406030605190b0a0513050901021309090c0905190e01020c190209011706010b07050c 67
    0x419400307001c00300d400a61030820452441000c1c1400107841241c00b01038141801080440c00281b0303954031840032050f58224060400309030f140781185102066006400c030840e18018400c1e17a01c0e16641e85604500100c034801c00b624000c8002c1821921940320310340510000b0b41d802e441000c00c03a404450300b1000100219650f000c0340d00c540c10b44a180c040240d642e24410000a1401021042c40c50300501c03458440001c072000c259648010280c1d09105a504a525510004001007050041900925031000c800c0c0d58840d00000030401ca80c802d4116522039034040c41c08100540b5002342811411409a0010038203a5031094030314060f100703003866981001d080e50000504107403503900c02d10101b4400c10420307000a60381c80312a03043d01d0f41a11860724441102051001d24011a440605c850885100140c102410101444d00300040d94070219043c0142285d40003c42c0382c4503e80328050701c10710441c46686820101582e96501d01401400c0c0185000200102441401c00050b07082940040c80e03c2c2c83e = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 550037500 1250 550036250 550036259
    0x405011805070312050903060c0901030207060f093e0a05090420011e270b090108010b1305091b0414010206100501120b06040302090709170f0d0c0318 66
    0x180c6040622042d5a1a400d02e40135942c003611034021140f200200900404150f241e000041120794032030701200d03060640c01c01903500040c041e0b009070303e0540f0803508000352280715800c092030304c103020f80080c50802c040d00514050204501c0e0a42f921482442c48404c04060480082181040390303800581d40014090200410810b000c40700c0f40d642c05100d41c075034180200001c01510030b4041103424032035184030048218040e911450b4205030744103407854403038242e4540c080d01450742e2030150848980c008000418010030358000e4400d9006005040301c0314501a00308440400041c4136000e8240f049185802049035410b2440d42c40d01411103120f82e050756140e84000320701504112050b014090700412001844411107440e0f81c038102c1d08180c40c0c11500c46410800c0e1030051218000304ca5000b54107010200140c1c031181a81807140e442a10b90310a00c03410900c0035902c8559a5800c6550b0b644140802245400003040d1822000f809003040610b030241e034903041d50404141c2040b0705000089210000b03 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 550038750 1250 550037500 550037503
    0x10909080c1005100801050f0a0203070e0901090e15042012061303031d0a24110703080619030f0206071b0302090109020705030f090d0b01030b06010e06070f0b0405011805 75
    0x2401003030130f00301070000d4940c3c6041860a07124122050030410190000041010449800842d409001c80c644091240050310005002c0c410070780106100568a10810300d11000c1000b003040b010504502d0000c030351602e940e40c504070301c003044d13220f20300418120310214031522001030180d040741c0b80d001580c03010700e007441840d0310781c220501c0141e000a04108180c41140f4910612003000100705002e0005003142d0b0301d90f012003220111850058283c0e0102400443e40284207580f00c5188039041266240924140101050340140c5014420340110100280c00001030000d101100c2c1c0c03052801d1404078245c000070b65180a0404058694000c000000c00034202c41b02c107038401d07248200d4040005988414801c4124001c04500904540c000c004840c2c500d00310308042c00203510010010007145c2c505d80c0e120028908280c4c021940103038032206000b415038021508021410050b91400d00b80402a1980d6000143ca001c01402000c00400810180042900803483d42c00c2460031040042c070051a03c00d = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 550040000 1250 550038750 550038761
    0xa1a0c0106330e0d08031b0405130f0f0513060c0f020709090c050406080f0606040b01050306010c020a0302061b10050f01172503050114010509010909080c10 69
    0x40294a0301c140894040010700702d40440c280788484000c1c00c0c00d618200c078400e000c40c580b5444203104902500d50040d90781c00905140951003a1016612410242148404803100a603025442213041c4810300c0603880c0d4100741001c0050821020688000190070240201900482e4028050404040000081c20390001c0c48540b84110010000303410f1030706d81120f154214013110f20050b0412041001015200e40dc100105400303000d01d100c2090303884000600301d44182e0701a00c62074200c801d00b0311110b40c1c14840070354090000e440a02c90300d2001070008000c2d02c0001c09960612281d040c0000545d220285650301655010b00461b607254010340c4280854804003c001025200701c0040f008c540c507950240602600700d50b0320002c00e590800070823110a048050781c081c142d00c0703000041ea0300d0807115410840030380e51059014110794110305210b8292030b510962070511504004c01042a43c544c06140c604640001c40c00041218140ca81402c40c0d10440803200c00504c556031607482c3c1508a03070f00c072 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 550041250 1250 550040000 550040017
    0xc1b030c0311040507050306121c031b050a0507030318060608030c072709050a06140f0a1518111207030501080604052d1b0108010b12040f020a1a 64
    0x2e03450510030141000180c030b00440e44500042c1c4148041a0380c2c0c00c1a08141c1c00c00c0103c42c095480554209854000141521043c0c0b03000130340b5900b20300b2076034180c0d42001d043d0b00a607140c0145001c500301400b80551040400050416581c0c02c0703003103021081c2d40d0308500290342c03101c814811a540d0300300055507500460100d5646005145001448038459400328501045c40031090240c41030301064a0020f02d004441920103014011184c0000f43c0c0c18032550203180c203002c98044250401030740242d00404000c041ca080307075182222504000121100180444040d59148014041043c80d004082d02985003084121900450180c3c00003079a86d55480c4904045c1c0c2d0100480d0ba600e401da180e81d0b000584001e00545c0206220345982c420008070302c04000c0c0f0b603820010300c040c500f0420b2480c01c102c49941519000801900044540e40711940d1030045c0803004000741004601003080c111410040c03c0140440c040415041c03c540b03601d010742d0018803110241e10007506d0140c0e8411001e9105296 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 550042500 1250 550041250 550041263
    0x61b2306131b050310020702010921110103050601051206060f0406050c0d1e0e0402090a03060f0c050903070e1b1b011401030809090a06081c030506030601150c1b030c03 74
    0x1e6140c2d0102d01028500102d62006004240600091a00000950004009034104004444041001001401c400c41195889104a52840c03902e083c211403041440b408241011308040901441faa804000d9030107101104802c0038140c4c0303c65000503800c0c0301d1030200c0900c1c8040480c00054550b0020060200340c030101d0b080d1010034482440c00c6403005500090401c20f0500c160b890201203105070300c9417240c4000640014513050745000020301c51a0380d5401140c1c070303940369114440b10004a0089140c036100505000d0304009507179000907100d0341e241c084d085641d1031060000e40c004400c4800e08030502d0700480340079564a404951008403400000e0203403134960030a6084c01d09030303001606460403260001043d0b03080141d12400c114000303002030209410f00b52142c00c01300c1d1210f020b20085a011081c1444100c000d500b000014041e142c000746050700c83d80084004100c010012003e00502691a24080f0f00124280c60309c0340040303204c0425801e0281e814000402004080150f0000360781c028030 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 550043750 1250 550042500 550042523
    0xb091e040e0627030c0a2402120106020118080f07060207060e0f070b040605030c07060207060501090b1203040503030f1c06060207030c0902090d02010e030c030613020901061b230613 80
    0x542d43d00c0c40b580507070311002da04c4144202c01040080c0d01c0a0a0b003014002910302070241c01007c0d0302660010210341c0f945040c550f00410003260244959242c0202071494070081048584803649070740154500d070054142c0c0042d00c0300030881d0707d078102d40c3c031203504c14401c01c1121082490503070b4138501e82c407041481d80700b440d0002c50803030740c00b009941c100e0305166030302481e517a501038007049290010303d0115000d03a000c0c00480c00103841d80c02070340d003e41008140056080c54840801c901e8207420f800e03a140d15042000188195140403003214040240202e54503038070b0860ad0302488c04002c88480307442c89240b40c001c010030074590124070b07142160b00030103217100c107a80c031032070020f04921400711119845240d1588032001940180032902c1d1074400142580c5203a141400424102042100c080a9940c0d8101c0407070214034054140b00c1c05018189000008041c3c0c1001041d054000200d0181c1040d4108031141c0098140040c2c1500740c0700e0343e03001e5542d070303080160303042104a204040889e03014900c00c = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 550045000 1250 550043750 550043821
    0x20d08030403022401090c0c122106230d020a06050309060601031812050d0c0905130902130b0d061103040c14030a0303021c0e030c01060b091e040e06 66
    0x180c01044260071078085132241d10b0300000000805030070701140d0921484a803100f0104114048604941c0e0164944924210740c030200c41c13424580520304650424a0202c1c14040503101c15524943c4484030001c80711744101840019036100340c0500700030b50002103590b001c1450b56101024502400e960022500310303440703920042d804c0e900e0032840003103400603541e0341d0804110030725038640310207900c1d080140c03500e0340544440050710400346140340419600c41003000141820003074240324500d122410010080143d0014081000c0c0c10005069151506032010156480200c40c5042541c09481048051900006541203410440b07080d00c401741180400030740890070100715516004001e020b030080b11035a96090f002908002040b180d1140e1410621003986d071036101d45011040c0c0301e0000d507103850100742500e00f500c0301d940005120020502506400380c071120301c100341c1c044224000c1040300140502181c0101b04071142110540b1801040c040e01c00004555040b00201c03500c1c2684000300740c0b = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 550046250 1250 550045000 550045033
    0x9120708010c2c01030f0c0f02071706071103090d060506120d0509042304111e030309040b04020d0606090f0f080a060b0114191d0a05040c020a020d0803040302 70
    0x5082201c110b0010704883c482e161024410300007882c8141000a030f0f540011000d10100ca46010116020400105581c4d05c5c2540420040c002082c40c00c1082e54001d1107048410b071100750107005901403001070b05541407003003030a00a54000d040f01500301418010706080000181c0030956009011741c00e4034101980110011545003002c83c443d03111949004800c03c02e01c0010108514082c1c032101041c98a020382003404440c00f40a18003910030030507550325142c100441c91541c0c01043c03109180b91100002551400b00589030010401c6034005542c0a0751000305019101d1001c107500308503e450070209495401221440070b070350182c3c0d0407125158450217003001d03490940c0580b030380940c4402c9548002403c9500301002102061612440c280903562003c14079420002c500b0000e261000e0307107000e13203580c4810302858010601d800360031000010004240e0007a01406914012520780802c0c04041e4020088580d130300da8042e002501e40c8030b40b4208048035420170758040340107005030104290318004 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 550047500 1250 550046250 550046267
    0x4030f05010501170a03020d051303060e011a0d11190305060a0c0905040902060d180206030c18040c0804030c03031104180b1008010915030215030a060503060c040e090309120708010c 80
    0x1e15400402c8c0750500b1074425603040e0029410007183c800525400b000140d0310b4000e58070859405000401d000000c4e496051485401c0002c0c94003d400c6100d10382c0104480d0510340d03481d51007c1e141c4100f208440391128030b0b41d00e51031300040c109100d031205000c0c0780f02c030365800040016042ea44074204c45482d041040151038608034040d510003000d0002603403420b45a401111081041a03e400030050346034007049164004640003050358802265110380d50300034401825900000b140d0401c44904081c001138484840607001508002440c03804504040c0254000500d004005550f9600d665035651050301c10495440740344235540c1450503441c4075041c8030000c1444202140c65900c1580e080254804c0140020705a5109100c4405070000141e180c4903201064010300c100716950300e141003512039054804030b600440c00303903201000304800052020192015203c90034600c80c800d84031495018034600401645507440700c0e0702c003140d0300c0503180020800e040310307801c40003070050803a0200156440013 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 550048750 1250 550047500 550047503
    0xc21060603050d1116180216031215061403071107171605010917070b1209011a0906120f030f04030b070f0c0b061809060a06120f110604030f05010501170a 68
    0xd6040c030705010300e46c64104620482d000d41c0e0801400d211801518400499180c070064000ca44105406a00358626000761000062101143e440301d51400300000c0c400458030442c0314200601102041c072583c400c1c0088412442d0400403500c4980d00e03003030f003c00051401160005540f04070350f030074915584c1c0c078002c240403204145c5488142c1481c29030082c50810303030f031071072804207000341000400d09203680005060b00004d10701100200d803911740800e5007110305400c1c201144100c107040e41c0d02c20b603a034480032941c000829940b6010944185801920b45000c1182c1c5661500010901a9544401002600880340120480070b11a21020801c1c0d405040101c4410005464041c540700131482c1c15010701e4000c080580744807070b1354940401508441805880c0314030303a84c1141302441681d0140380200800340c4140001d02010414030713618a0110807204070000c12541b50056034144a68420066400075500b180403060032403002d01c3c100e80202024020382032004460151161001c50001d00e01110310f = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 550050000 1250 550048750 550048783
    0xe07020c0405240d050607210e0d180503010504152412030908060a0926120604200d1d0d1809090305070c0605070c21060603050d11 58
    0x16003075820b6150481802083c5180c04c01c00c08128100040c9082062a1088840da5240c040071510b141174051009503149400700910b08100c0250f003100e0001c1003250103009103081410b00141c01c0c1501181003c002e602803907055103050108402e10034684840d580040740500c2c06c114000040c11031454140d10341d00c1e00b0080703044180b002e1100d00390480d00c40e407a071406414042030359130717503500264a004411109465104d440b524000f00304412131841101da81d202c0f0384400300c0030b2803100c0f13104414062400740c911840301c0c000c04100291031b164000b1070000081c0506400004a4410b580069070042240f001c0c020f20341304400700e41c100c048507504d04011444010301010360101c48110b50718507107000c10070700580b01c41100281c81202440352030103903403090b10344039101c070032031304040c0b640c100141d00c40c40600104102e40c0000400400320f6400781d81c040040001c2d1400c50304480c0401003003114005161518050022003404000940c81441005a9484c0d954441e0368488094949209040340c01d00c9 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 550051250 1250 550050000 550050031
    0x3090f0603010e15041409030a08090d21090803010b1321020f1912030e040b01020d05160f0809101e26270a02060901030b010512010e07020c0405 64
    0x1036848004131444194000f080403a14629080d49644480d50a595a4546a200051405400390400d0b2165802036501000d80445112500c01078400301c0940b4000a0500c07007440081406465a0320011455801002c4281c6a60310b400c03104a443c2d105450710b5118a480c4140001c5030000c086e0103260302810301000001c140c0d60b507820f012004250b9200c0d0340c1c2c003034a1103403403040c10170152100e0401410a450078680484c11800d004c0c082818810055004500b4190007007101c0c0d800050802c0603120740e1414654503080c9141d9258400700c0c81e1401440088004a43c00034040100080c00007a01c00321140c122240c4502d10544918913921a0030a00501c8010340842c0c071801a03501960b0910032200e907d04840c032407000005c44c0c41c812114890301c006840e01c004200e40809140b0402d0b40038060080c10f0304462a00041c401d402101d01c580c0c1019181c00c54104264814000d84081054003011403080e541c481409008002c03045805400512407500b820303c01d4030700360007903034003c10042605c00794 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 550052500 1250 550051250 550051261
    0x1a0c1504050d1b060c0f1716050319020403050a11041a040e0c12010207050c010203030408270d05010e010c050f0409050601020f0f0706121a0f0a1703090f0603010e 72
    0x81d4042c55a100d40d62000304407880f42c001c94003501840c1229246542d84c9413100c607070110007401005044421042d81185d0504002c3e4910401c0292004d0200e1414048c0e00c0c0d5654210000313040840100344a4207a0010400200300800042d820000754440d07465404442c285000780401c03502544e005440c00580a021840c05040541c00031b04070701541e10941e900500407401081001554040400450f90700103004400d02c0028042807a040c103003480079502c1d60929850b101224010134045c21541105c0e0800c2d808203000803101c107207004001510f0507030310802e54200300d4024603041540d00b81c030f5420601040c0d2114415001c44041d42c44002c10f03a400c0c1420b00c0042802440700034a130381d041d44101d80d370300d104e03801040003e04a031819001c003c2031081c0c24500d006084c0344141c050103645900b07110032800c10300800e507503886c02c0810031b5591902c009010b0000488000c80b90b4050029a038461015407030004010006003031340e0205403842038035140c00c9418401a4442441a03650701070b10000440c5 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 550053750 1250 550052500 550052507
    0x5011502031b03132301090303050d050604090f080a030c0519080a06030b04120905030d1e141902061303090b0a090806010b0403050c010320131a0c1504050d 69
    0x254001c1018103c0b800c090500701001c880002d250003051104050229482c3c07954840c3c00c0c540c900550a01c2c104003114510398002d0958054016000071441d01c131030010b40c054036181c0c400b900460f0000e401140581c5241000c0b0200d50000d00c40a002034240300310740100381c3c0170b10103c0b00b282c9030100000c2000c5a0b40d0b178086030007140282c00c251030641c072060000046090918481d000314040d006011742001d81d081d001c0e1150311683d20850098204e400801d008039041029090300d41a091551002d91820340011100342001410081000c036000c24400070f000784c03c900701d5101a2041c0c00302d821946900c0206003160000c0000200081c1c105001803082d0203401000d400c401010f41807035000181caa603881810240c090b00880c01402010508109100082150200d42c10080c00c08004207600e14480c1e41109040e15181c21070000c0010300d60010300c9a04d25014020300c00d099103840c07001290030481d150b5500482107140584030b101d803005030b6a41d44030362040c0200d5004c001003400c0000a203054 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 550055000 1250 550053750 550053787
    0x30c050607060f02030411030601060c02010e1507020907091d0621071d0403030f02030609270115060e09070215040c03020d11011103070f0b04050106050a0e01090501150203 76
    0x210b500740c2d121040c0542000c0b40c1c1c00a54040d0388200c0039105140051824035140c010141e000000700601440304402603600700c000417480300c42c103071149881545600114089481003010003034101c0303114410001e10399401405142607880010302c610320309480c407440c2c0714401815030b01180c3c008600003d0314202c6612000c1c000c0034021106c01c1e00c25180d81d1718410700341c0c071f824040900024801c0e0780400040503494811540040c214800441c11414031001240a6400050032a4051180c06d14403001400d030085418510072454002801182c06404540c2101d040b01d04c1203502040741c080076400a8a820058140719078132a500a1602c000d07960045c2e058084054025242030030840b4021000d0b80743e0313558100c8091b00840342c03512611a10000145802d09000070071150350010b00c80c40002400241ea1508070359040154001070341c4036820094010084c40c0e00407903000841c408005464102500401d049501402c002c1045d40ea032030310013144020005078040c0050304204002083c1d2031109504 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 550056250 1250 550055000 550055003
    0x3060a090314071106030a020d0b0a06021911150c0606150706090309180236040504020a0e041a0a0c0927062603040324020f041403060f01030c050607 66
    0xb040c031304503102022400d50350040e01d03191882500044e503840c4002042c050704100c05001d483d907402c3d41d458514000e4645040181c000210421140000148113020302c605a041000030200901e924a00007584010750000403501c8040c0a49070016886140c100304811440340128000c3d898141c02c0d55402c0018640300d40210103105c400d020202d29414160401d00d240c0906010040c6c2d200e41d410062105c420440d0fa00c07404c02004030151920405508020b418042000d81d4003203042d80f140d200040c54400b440d0080c118000300c0904000a0182d00c43d000340f4884540d8411070300303c4d140c0b2648a81511600901c03007000c41c241d4801080f184440009400c00400c01801c1800138000050944040da4030a90000c000c0d0041a034088082000c07030207a10000300b0120009501d4185150390303071200b002c003a580c2c0324644440c000c07030741407620324030f4040f14110901c004540781d039903032207a2040310001c0751140080d01910803040000c20110480e10f242d4183c0303410004003a0410300d44820000140e001000 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 550057500 1250 550056250 550056263
    0x60a02161b03080706051f0609380a0f0908071203030f050403110c0603010311121029041e0c0e0d050f06091f230f0603060a09031407 59
    0x1000000f00c2c07603040141c83c13050301c507030008295401c0581100c06601c0c1b141403110000802c40e5002c00026411101c858110345040800064042180b5240ca40ea12010f2140003035607012003120b00d95404502c402450808181c0d194000314102030701c002c6a010b1402e004415640e400798000384202ca0582c00080c01103403013460b0108140b8600300c10f24090382c2c0107490490128088c0384c02888104828401003040d00e00643e00340e81950300d1a2511426040e03030750301c041d0142c1c4026031200c7e4072031001d0051480304000341d11706010f40701210032020300705290700303c02d865490842500d482180c90607000d195188034072451014040600d14400070300070151204003200340000d058010140c1d844088103806c1260050700507041c070044600c9068181280100b000c07030950089030880c00c0440580540c1124030046040006924064451400a0084107101c00d00b0141d4800f00b005039003003100081070300c220340507401c0d24890740710b4486403000d0391403c80c00180860b29000c8a039800844000207864014003520 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 550058750 1250 550057500 550057553
    0x12080a0207060212040b13020108010314070b0f0301090501060306080604030315180209120106061706030709061203020723060304060b04091407081b04050a0b10020c03060a0216 78
    0xd0b141800c82e07008280001030590000200402d0140404485611003042e40c58628600b400b80c1c0001c041348030500004003040340580c440c000c504401c1202ca4054030b8206071040d40c4401059141400f82c000340300e0110484d00b41400030a606101b400381d44111103020380200030684940d5800c0d801703403906406910805902d62400105509228042c3c20514000c5100590798000c600600c0101c0c9441c52000d14541e0500008001080d0f00440c800c800661890380444580c0b02c5800082c181030682d44031b842100d0400d8004140d21400001e01c10182d48250202c60301c407a51401030020440c1e1101c41c1125021301503205002c03e0404000840c0d010f4800d81e0b000880d16002d0001500707c43c034844054903001e0074000c18452800007086460040c1c8800801440741c40041c00b110f1110020b0b031180c40380a00e40744c4021510710a460b8100c10b140000061501c0c014100802c40299600350044205100384581000b10316010240c0c801c603820003900c02d45265400d131a03600c0e01c0d08120803e6032251079802040 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 550060000 1250 550058750 550058753
    0x13140316080c0127050c1903151407030b09070c0302100e0307050105090a031b11040b12120a02150f060d030507050d0c0218070c021e0d0510150312080a0207 69
    0x181a20640c10340d82c13115003000b0300320f0342c1011490100300700c0c1114000e0803d510a0504603584500010440754020398040c0032420a0040300d0242c92410180180ca40d481c0043c0051031307801d6048200810310076201d01c0070681d01c00da400c580d1148a1718024016030080b803144290b40340f41e031700303d0300901c5030f080c003101e281020315a1500c0c21514221480c0d003658000403e072604043c0e00c00240b003a500443c19050005800588642c542d10382c180304014071030744d43c0d2448620a07480350f8024800403261031050310044810002601c020f94080c900040c0140103054400c0501d450360803000d0f010300080c545850450366010280040b100001905800340b043c00d000100014008019203850644a56500340c1200060f105120600320445559040d6010480800c80c000303910000c010545501140e01c0c0090070100c0c0501d601c1040d40c1e100c1280c01101d01045a814040005010100c4824104041000e038a40c510001c0000300a8040140410102c0d5041c4030541d2184196a4004d0303108500180350983c01d = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 550061250 1250 550060000 550060031
    0x309090609070e0a03080d110a12180807050105070f050a02060c0c1501080a0c0906081015050d0809030606010306121203060b04060e010305010e01050105070b1b0313140316080c01 79
    0x5540111030507540041c8201040b1487c8c094250341102c640000c81c1411403852025140b23603200304000d800c2c940d85140c200d11401000048080302600012203550342d80701030420a0180c902140c1c110003045231f9203440542e051241040fa00d480700194090400d41e25940800d960070382c007041c2c013880c552081c0380000c11100d10f508075460003070a8520040022101c54a0302d4103800c12160f2015500070704e004000c1108400100c1c5003001c49040040c0024140d005215940f9006c0c1e0703a410145d08030440078491410003c0010023011485011030494400d640c6503c0114292041ea01030010148550090b450010f410740e0314142e1501502e0602180303417606c0340702d90b6085da002a445400010312032001500556014450b0501420410052208960500740080c0041c894a64014100d503041c500140c00c504088034404d0401c28068a015582d050100c000020705e01451010f407480710307203150740e41c2031905c00004079820f65800180c8100344480c0340c1c803200c6081d007141c90b0202e142d54032150780d103403c2c210 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 550062500 1250 550061250 550061269
    0x90209130b010b070b0a0209041113051201050103080f03070909090b1920071a07180602030a1e03090c090e01110f040e1b0408100e0309090609070e 65
    0x5056003003400161207070414a01654040c0e016402040c81007104601060001108951284410001503a03450303521000c80c00030413525440d1001c100340400c1c49004000d01c07038008400c40d4030841e00480c81e00c600c1c59555089031420f200082c114181000140e44000e2280c1c082c40c0d00154501b0715461281d41e541801080d42d40a131402c9400c0310900c03080016401081503a0400030807c0902080301004003020b220aaa2000c8001050030201003001001c211544110001d80694100000f01600b0070b40f501400c104111040540d20f0012000d002c01ca55200100f503641c4158559240d545c50600f410284a00c0d0950b55083e0041684035a02880800c17904c0300c8200040a050800092060004102c1402c56003280024103105008006002408000805840903208050800c01c5c1030740307030f02c444001c1c0c2c1e2940c1150354400c1c0f04049000500000041410f020644802805200303202c8544132007516032107041140b0768820407039800318410781000c440301c40c0e019407181042800e590540740020700025 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 550063750 1250 550062500 550062511
    0xc0b030702010b120a020904020f030f070b031005010f020d0507061418010b030d0e0402250503041d07051e0f0c030405100c0305180d0606081507090b07080d090209 72
    0x707450350b90801c46810010141565404c0100103058039085903400101c0903000038201900c507154005c52518296004d03c1500004440c6204940c03805a48648240294004440c5d400c481c444010001480d03500640d0100d401030000d901030042164184e800b80c40c140c21240d070640d030b80d594032805520145640c0030582d0040d4103070352260b203c000404514a0940c0c43d0b0752071180c007a4008803034015242d6048424042c400800b15000b40c1ca490f0055509281b035415070b04084174001608400c5418441c0200090060300c101c80301c00d010b00400c0d0b2404483c014401d440950000d801000342e000c080d001c0c03004496100e90301c018a6450408001d106c54071941003075010034403030742001508005600d0305040c20f82403480182060703081041551800341550280e10fa010f500009162802641c5955070348085691641c041020800c80d901c405c01a9030b140c17a12541c100c0d15400070004038032100c1c00350000d0002c031048101c400d490190b407a0350307003001034101000e0403403040d8070380c08a0b200503070304d0303075212032040 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 550065000 1250 550063750 550063753
    0xa090512030913020a05040e040807061103010602100507081501090506040902040f05121f0b06031305010c091809081b0606032401060c020616110301111201060c0c0b030702 76
    0x2580c2000402032100c1c5032003850007803d803041110110f600d030808207913401c4070720074003442410341d8803414281c81074400c00301e009007810f141c00601b10b0b540d10000c001e98141d601580c21200700e40130801c0c0300f0048071b100f9110b0034049400c200010304100043d06501d0441101854080700042d40c480100d2a00c0d04542c218060305c9401103000e0240001400030000280b4080f109500c1031203621001301c2d10307901402c0b401030403000006048a0f0245058100448001d00035004036500c1c81c0249a400e1095500304c1c048070b1b50350074059921082885002c0b000d0917600540d140d606480000b62041d0010f001108007100c03958410301809924242e4568007010001e5604003400e440e280c998105810051041c6003615030300710303010360305248991070a5414150b4005052140560045000055141c000c803d0840041c8124400c00d100704544ca034003014040b0b030194001e00c00c0008070644500c0030f0060711200c00c2034400b2000100b01d81849003005100d1a4040c3d04118641e544841074480240e1080307400b940507 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 550066250 1250 550065000 550065007
    0x30c070e041b0902030a181505090312041203050612150a0e24010806150613050607030c201e01030b0d1a0f06060a11100603050f0d020102040602120a09051203 70
    0x26034141f800b40c11280100217000b07a01011103540e41001170803000c594a16140d58032400512140410421246240200002c0840701d140506d0031109503941a408000001d0a07c00460480c1c01c04052070004420a0000b40808901441c4040d0380b130302d0001c0225440c00d454411400e0400b0b404d10480e502006403e040302169150150040c01010060340581c000c2e511000800c80780010076494805140800c441c0c1c95039034001405d04411510071a003066500800004071081016000030110746c0c01c51083c0c075440c4c4100604a240c3c0c03c0c030700b140141039401102e4401005c0302e8250300718400b081c2d141c0506000410300a00b402090302110004412038034808600022401c51400c0008154400c2412511140c20329000011544601441c01e40354140f100b844448800340340140080109824201030822440b556420040c1d90303808034601e000b40d14080c0035940900c0e540306000701c40c03d481658000340407201c1107000b007142c10b9001002c40300421584040204155480401c0902c5a01250005544 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 550067500 1250 550066250 550066261
    0x1d0a0204050d08090406081609020d0204031e020a05010302030c0706090c030c0e04030e06040b070f0c27050105090f01271406133612050318030c070e041b090203 71
    0x80b1a16500042c6290b030110308c01c1c5038042080c04000c0103998a0000150710751840c4501c0c14040c2c0501c2d0801801011121410b141480c41c1c000c1c0c4450580c000c56030607485072740d200e0040d412884203a68214054100300000c00100b030302a084006c10314440c1031103003030301d81e660b4840d05031010590b0060494140d00b07405100a05030b00c40200303083d403074003280c011349800e02d040080595445a954000d0420349210545024803401c891a07070020001c108084c606400402184000320320200620b00c403662903d8000329883c20501c6c0b10510485410300000c0301a402c00111208a0180d181459864140d051100401043c8e40c011760380d02d00d081140c0007445060400400040e030600d000c40b1aa6913161071540c41401e02c05540c80c0000c520b420091050400e030301c00402c030240315010809012014140d03030a0703200c5980500214800e603074009096211030320300001d40d0380740d200f945e0307256403190f10411003844200d03540c212690f0000d2042441d415618094004850203940079880141d582d80c0c00b204020 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 550068750 1250 550067500 550067509
    0x30720030708091f05090d24061a040e01050405180a030807080f0702060f060a0314030d05060603010f030809120d020115050315310b01030c0b03011d0a0204050d0809 73
    0x804500c0c4c3e00074150781407941da0000614038003075080304602c02c0741400b103000184101281810107021080c01c05004824000b003c010240c1101e1041c0040d01e20020103052990505405072400d98201080001441e4600000c000c06044090000318070600002c0c80090036203030402000311514460303261242c107407821100181c1810760080900401e14004020071210590110301140d200b5002d10a800e002e0b03e406021a242d04110741004101e40a0807191040141c0d000010300300000a102c801c0c442035840a0511500b03020070721070450fa54020090520018070604040d100011000e0142204600307109440c40c500019400301e40c0260750744a50103012070204042020203404141d00514030074150940c8900c06040081034440802c801103241581100c01d56001e0f808540710806202c0480c1c19418070101c40070080c1301c12161481000400505060040166812101d21280c00104000211280b1003103540003003140c484294200300200b0075a50300003400305028014000291128801c04c10300 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 550070000 1250 550068750 550068769
    0x18031f0f0f0e06131e0c1403070f09110d021204030305071b020913050a030810050f09070e04060306020d0b03010b0405090c060705010603060c26090303072003070809 73
    0xc00c40c581850000c480716000050f8960704204c90742d84c1c224642c1c605040200010003440c002c12040d40505104000f4400491b0303100d0166481108214040c100b03410815030745900e98031819034569070204c020084601c20381d1158a103411b0080441d4a800001c045036400c0382d01004401b4105003504e01404140359052003565841440b070304002c1050444c000386000031a4595800920a1112000240049560b0070070158800c4d4000c2c101c3d61402c03c145002f500000b001c89219104214282000800e8540304000d00c90410340900340c02d00c40d44502d5412521032a8010b81903030065150b04001001502510040840380812140001c0809146080600703451010038020310441c10300b400c3c031984440c041100541c004045604a030340d8403003450140d001d040b45620290015160208004000b504440100480f03500c001c548440c490f0080122044050b06955000307040c0c3c01800042c0c02c290080c1c0002c15680d454811030081450052001031541c6c1c0100c1d000c075000000810a4100ca04016460 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 550071250 1250 550070000 550070021
    0xa020d0c0201060f0506090d060509030405031b01080a0b1c060f0b0d021003180606061809020a0e01030c02010605030a06020a0e120c010309080d0e070509090d0518031f0f 75
    0x20f1200602c2c044428007003448038062140700304000281c1c5005951104101200c081d03002038140280c9c41c041c556076440307400370f00c01c441c0a80a10160071f00001e041c4046508818016141e0081a8032801d41000050861660841c0c000302c68100040403129042e20703010f07420f8031514011072448859200342082c0d6148030840d9000d078004481c0c420040c4d59410710018008064a00015025489400c04401400060380a0011032030803801054881d8000403220b1240c00d2a0141611995654100d0040f803280303640b810300081504800304c00a604ca500400101d614620010070415200c5000a041107140302d0201d034590b90001d8a0000c643d00302e049901a4801152416103140f00916015225280180b80d01d04042d51280c1041c1045190007e03a030341804140c4c8200444280c6005141d0358050758041d052003506a140018079001000556103913006840d582c8a0400c24103906441e08101500b040c00d525000c0d00c02c1041c0c42c151040726100e0102e018140124040740546614001c8032200d800 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 550072500 1250 550071250 550071253
    0x601081209030c2b12022806090201050408030a090f050a0302090714041505030402211f110c0604060c05090a060c0507051f03050105030c03061902040e0a020d0c02 72
    0x1c90011607402044900d02c1d02001d5443e002c240d40c40a440a04004951100002401c407454a00c0c06121180d1074001003c07000b9001c07200b8100c40c04079000c02801d00b9107480408038001030361890000d5141c1c1c01032000380744103040440c2095103400c1c0c81400d50304002000b100040707540c0d0013040321610700030302200101401d40d0800055425074001c0764000000800b130005100f11020100c013400880400c960060007103121407043e0a012210040103a0b1041d0b50691081103040c0b0502454220310341201c0816071260014401020030384182804110b82000c0e51944550720075985041d0090740c4000e0a040e125131001d0007081c5400d20f461b030300f250540c152400030044180542000f9403140b24520050303c015003840303450800c040ca0010703d030507074640009030069801811000c442810220181c01e004450310103000c01c0c0c1e00c0324241551002598034442e4154401c0303004c02d00144001c0400c5007100b1501c80c0241c0f40a031503903044841c0e00b00680d0341c0c05802c0c0d40005c405034101361900c030700c0100c00810720 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 550073750 1250 550072500 550072507
    0xc09011401090e070516061a01090f121401060e070f05030705271315080c0307060f0c0b090303040b0109050f010b0a09030f0b04021f02100b2106010812 67
    0x100003851020b640c0a03121580010802058050b80900103690070b1034401100c40c242002d0502e0010090314640e54030042840c60750149150940c001c04140c41500c4030100c082c2c540a103059a4459841d844c10000e4451842d4660100201c0d80e082c06160050030341004140a00c0c00d20b070710010301e002911201d40040007018428400103581c00f60031100e84003421b070f00000181480000500d1855500c00c45075601c4060b007030001c152034005802240c0071021b42c000b0005426a00c0340080d490364030800c0c805905801428007440130314001c9140b00600310045c81e00019100003a070340c0d13024040f010340e1403240650002c010041002060324403a800b5044116080c0500d040000506924000c18041d60301d04040c003080c1100c51920401820000f907030800c04442035000c440c1020285c0040c103540503070140d40030051543d0411110700300340c2d207814039070384c010500114002c140f50000d0076503242d215880f011b80c0004444090240c03201240142d204005002a545403018052034414008c0c0c4450f59a1002e0 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 550075000 1250 550073750 550073789
    0x13080d0203070c0e04020f060c070503010507020304031505040614010303230405011e05130e0a06080111040603020309070f0b19030513020402071502030709090b030a0c170a050607020c0901 83
    0x80f0030340701154060407181c803558660340300043e02004ca1030443c40d00201e002c524031512480001da0081290402d600801c03083c1c03680102240c41b845940006080284580f0f0740340c081c0b07205a40700c0c9178040d0080c0e01c002840c1c2c6c50b09141a1070481c0a0b803003500051444484070405401414031070042280b4809100e2509140600103030100140307420401075000b450f003c04114034002c030103d840350f0f41c3c9810100c03211511a8a64203034200f003500c0c1c0545d40e07882c0402c0441da482052007441d0410840450781030625203442da04601a500c01801c0b01590301419000045d03480c030b0204510f000e400341a03001c039210801418100146513103248070354200b50134401400707401d00d21103196400305501aa0301580e200f410b0706058024911801400301c001c0e20000c1004841a4041c3e814001e03511016828001844a4010541d813504400000762264001c0c0e201000600c004004070aa9248100d056800d0308003580c5525040c4007040b2452009030700103c050504501d8085c509038090503500000300d03c43c140c0c2 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 550076250 1250 550075000 550075013
    0xb010902040e0c18041d242406040b0d0b1008130c0302100905030f070b040b0a020c04110c0c030a05190f0b0103060f06150c15090813080d020307 64
    0x1038185007040380c00241218010300d6820720051071305030140091048003d10074105d0b01c076203002c035030040c0c4500a50308022082a10300407501951b808202d132407421510341810b03501ca01e012420084c9800d0703d94034241d00c044d444820246c8014604030f600b085e215106101c6080a9608080906101d165403110200249401c20083c40d00803801004030210f2107402c0c500180300d00640d400103035100d001e0a80090300c1d9a80031b2280e2050b1802030b010b0b56030503450f244051b5516006030003000c19040003840f040c0305008091010b051143c0c030500c111061500c0d404007080441e68481c4111121880000d440032101408005026502e2007c0c7c0040811640380e488007612901e06518540c81d1035807002855091046c500c0007050041e8011040301c10b03559581c509480142440e0718030448107401c10b207002030060740070400d403600c8003115100c09103108410358807003080080003e4440e000c0c075a61006d07803010a2640c1e01030b2442c00c030048500d1403a10b003440b40d403d151000d49501401190700410904000405 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 550077500 1250 550076250 550076279
    0x909121d010804060b0111030706091e0321020706021201030302070501170f10051003290105220b0a091a0a0c060507090b07050c0a06020c0130090f0b01090204 70
    0x4c0085000802e07404d181d0040712590000001c8881900c000718500c8103100740c03940400c9031140b00e100312905440c1800f04000c01e00c10b40c3e44014022a41d0201c0e184501064100c0d84c80032010307a407e0052400802d5130715882241c0108000294850f1808014810590104190350140c0400d003001104000321044000c44810010402801d05e03104401003940c0c2080900103401800004110400c01003000030f004009080003500d82d01c4840503141000c18900803180d0140f01071130180e481c0c0386402c03e440003181000800300141803042090b04400200030050300040d0004134650b136100e40040f45070480035054519081c1903090740070f001704900588143c00008440405900140205a940d10100c00781c030205100e80c04401c2400c0c0000c0c03070100f0000045a40c0360341c8102250009101c5480d0f8404903075070f00183c3d80c0c1c40e01142c3c4800c004000c12001c1e842c1c603a8140680401e40c18610700202824058594010b41120182224910b0004020a0031845409425880421810207140881510300c102 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 550078750 1250 550077500 550077503
    0x100e071b0204020712080c03190905010e01110d060f060e090403090e07050903060a060803090d030207050306180d0e01050d09050109020a060207180509070e0603030d0923060408190203040909121d010804 89
    0x703554040c00ad0801c2029041080d104803540001c03c0310a1603032000c0c1c18150302006400e44014501400071412565103109501500d54aa8a0030701810101c424040b406401410580a000c15040000748040c40641315900c00e60305a502d0f01c3d00c031103841c81450300d42a009480b040405080c44001d110341034000064501c05002240c2c0f481115586041c140c0c2402596040103425000c0c00c0c0411406501e030086a09e07103040441c00303d9011000c082c4080b24400c840219a5002030703003c10100c0d5216100303170445080a80100000910648180d00140c07400006070300840141e00b00c410704101d0011105030300301c0b6035020400700313109a182c00c00d0b8045d20f0700711600600458580200110700161420010707900503404a03402040300c0495070404840e5a9010241e044901e108140014034800002c140c15000d190701241007400c100b030403070b10701002d403d4040d02413045100900002034125100d00030040303510b00500041c2c0b07442007003020092400b020921202804070b01e04650748043e07680458400d5005 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 550080000 1250 550078750 550078801
    0x9010e0408070206131e060519081f03060c09081b2b05010f110702010e060906120c03070e060703080a0507180f050306100e071b0204020712080c03 65
    0x2010b0a20018495014035400d1050b400350380d50b004100448000200240c508980e150f800705c140d0b0740c600441d0284250003c0d01040d0012108043c0454006c0d0905c0b0b03003200c103032030b20740c9901904034000714402e04036644199903880d180e9a034000389940003a440c0010b81441005041e8141548400c00d0049480d480c245008040214a4040d4003564034039002c0e442c480300c83d0036808103e041c00c0c058044d02441c80d042d0000703441e060741c0480f6440410700f2213540d1039060f11401d103201d1841080103c00e400400d540c5800400c1042210201c210502e5154410085d04160315280d0614a20080030001c80d4416075020300c108001a80c042034100425680c000440400800c43e40d554510454110540020346031184004d15004210781243c03161250565105408a4459595014004031500094455070b0b0b960084e21001c0b46015100d4480070030702594190010008071a241e011804030303880100141d94580354100c00303040d00da60002e18190402102d103079190031410804032009134001224080f2558 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 550081250 1250 550080000 550080007
    0xa0506030a0f140709060b07060c020d021b1f0c0501062903061f120513170a0c020a0902090f0f330a091502010c0c0803061c110f09010e0408 62
    0xc80f2041000d04041c040081d801d020055441c1001103964100c10303001c40d8850304007404440c50b54030018166061103200d030700510740803240807030059202500010243d0455000d40381150342405034600e0042d0105160ba680310104140d00b030181c2111020380001e10240c243d12046125414060103540c60103820108140d525110000010061001c202c25240a2058120030141d015005141400e0103c1c544209001ca5525a400341c49000c10f000802007040410804690500b900080680b101c1c1c0641c2c100718080000580005410302c159900004030550009071842d00340c00e009440704240c200555066080c01320040000b020008160200000f0700141000e02031341c0d1141d40103103440d10282c2112550b66401e5040002e00600c8640a0b240040f100d400008451030700c14410001d20114559445983d81c91940e65254558405003031560710100c1d906034a503140f185e400d41826000d00c50f4008c6242c04003082d0a111110001141c0d1510840c40f05004028121624047d2039029500805440d034 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 550082500 1250 550081250 550081283
    0x15020c061b09030f031c110304031413080d09091a040b0103060504020d0207060518030708030601050d0e070305061503100506010c05060106030b1c0503090411040510080a0506030a0f 80
    0x400b0701503048031039414450f0055042a0b0390b000720041400413801884100035002c1003221805a0786034032940f03190800f04000080120f07214030002145e0016441076545040744c96080c03182c46c001c050308020101e4005401c04100e80e5049000c4000619810794180f00710204106040460b401c0703580414000c40e150300255105a20a80c083ca015020080086407603142420740b10f4005d4210f08411140e41c1d107010041810300005103071103645070003031000075481e0030701070356440d10140c0014007028148003080c0071002c2c40c45102e00440595404400082548074514105549032403400f41010400300c2a00c440702d20b00307031004101c0b04003c2200f140003040540311030300120341f0440144030103880f81c004e503000851140d81c15041400f440408070391000c03180d00b148440d030300490880d0320014180d600c204205005418070b03801c0075071310950507080309003000da682d030102d007400c003003c8501c0e000a007150080104000240c818550410029001003040c43d40e070759604462402e1085020f000e410441c0d40c0c1c540c = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 550083750 1250 550082500 550082551
    0x1120b190b1b01050603030a0302090f06160605160f0c0206120c1323010c0f080417060108010204050a0b18100c150c0813050f0601060c15020c06 64
    0x8221014040510303000d550310698821290400c81c0c01008581081e2411030b5481014040d9501a1074010301640c94071900c500c0c1600250321020509812001d02c0010540964600002e820040d029210a5030100c04a24040086a10090502c00c1e94100c020711040d9895100309049000711f603600f480303400c684603400014414045c0e454510300c0c01d080101041030304c44c1d181010302078480c2050700801449496884041c07084140c035054860b603041240b800c8009610461050141d1402404c040c1a020869242c1c252030340d000d170300814103003c440f842503500c661040001d5401044484000c40c02c190505c000a5507080ca50f00c6482c03044140818940345a03016100000c80c440001070a00d01c44801d4820302030f0251800140940e040c49500c00031111440c56801800110a41d50b500c00e000d954810000d2100708050140503181072084142500c4c4099080003228040c00c16600c505007101500c0c5403035940000c0c0c0c80e505000940c0107000d0b01c100c0420000348550464012032264202d4620700c207845 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 550085000 1250 550083750 550083769
    0xc0e01140d270c0e010e0705090907170c0a020708070f0b0c16080105010617130602030c07020a030c0f1d010b161b03031d03030403020409061b0801051e01120b 70
    0x1000501c41401c480c030300300010f40c034601086611000a03241c003a07a0340c46200010307a100304c5202000c80d204202c0319031340d0314000d0381d919840703c02804c04c40100c80d010080704210a10880320201e646000003030102e60f0940410045009000010003404401e0a04003804a850b8582c81007295091b0040380342c152000080c0402c680c400f40d0102c44103203d41e554181e59001e08405c1c80380502080c100c0c941400c007801201100e0340b14180c8104812071400f890350f180002940000e00c0c20001182c14003483c801651400c4001c0000e6002d8500740c0e191f182008030b401a2520140d122410700003a103600f40c01058204422203044a0000380050b480e05109a5104003404506000400c030302c040c814448007040110300d50000342e80c00b84d0b03964098508260100b140844400391043e50582c810f210400c01454980c0156802c18441c68001c0f88440318580440c400014161221010910070742c0180980d041203141180540b0b138116980744180c0540c0d001808080c1140b104011103500c418003400e5507141e15a0381c = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 550086250 1250 550085000 550085051
    0x20703080c070906050f010c030c020103150f090c0201050f15030a0b0a021305010212040e1504140103050d020105010f0e0907030510020c0f03040e01360c0e01140d 72
    0x41507803000303009030464590301e02d806542c085a1038004003040c141420721800d1480d060607113a07500c0403031131900c013035500c5429500101d04054944045100b4500c0780c11602000b00f8103e502ca205030fa0610560384150782c0800c80f5041160301d4441008059521180d8554000501c981e84104080d01400803c3c00c10721407243c0900102c8001e41807201d194020350060180c61380780c0031b00c801e880703440c2c0004986608030050203409020061200740328400b42041e105800c030501c00040b8030041c1052010a042d200c06c00c0c0700c0e240641c0450010000d001c0140070510340c941c007510081000d50b0400300e070150550080d004013641b4894520000b494114104071b2180516080b80444010074400c1840364040d500c0a40140000d0240d5602a14406000015507050b28040201d100e01d40e820400f0ba04a03868040c1031840104840d05c14000c00c201149010469041009102080d0001c8208007d09005407840f052410001c00b90013041810482c0340c2503402c171040c8040f02180034076503c100c0380c01e0005c40494 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 550087500 1250 550086250 550086263
    0x10509120a0f150c0207080d20010f0e070609050d0602070203030c0f01060f0603020c060c03040812090c0117070804122006040204050f010602060406090309030b150f0604031e03020703 81
    0x107107501800f02000b4241d0304414405000d1044150300801241c440710301e842101d250f5800741d11403103951070081e0140c1041a45180d9140c20101e15140300d2030031f403a2128407110009070703a48036020f80b0310310602001d03010745128184080940e15000100300e0310391600c0c001410303090f804500f00c0110f40e0305008980760088208102c40c0ea03400b00c483d029000717084501c03500f00030008045001400a00a00a82d503107000c0c000c01500c841c0e601c41d0b5409903543c1c00100100d0f4000010044048a04500307000c0d07071f004103405c9006016100c43d1400262200c1103000456200305500d00c204100f00e0740c094401d580c000c0d07000700c100414407030038601a00c2504d1000d80320071031443c14041076071f90302030001291846070b402143d080c046a110281c000240d61028041e0200603004040000c000c01c480c0e41103100e2445c403914018402c103035607450b8110002c0086c0d0b04064001c0900b031f40c800b02ca141c131800e00ca002440403500d1514051456076009040c0c5694000c42e01c0c6040c9a441c1e040c103060003446890b000315040718 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 550088750 1250 550087500 550087523
    0x130803090c0102210301050f0a030503210105010507120e01090902040905040209150102210f0f180901050109030f140114040605071416210f0201110702010509120a 72
    0x10300194403110300010050040c0b055100f40001d80041d2484040801a4808141e2659017020180070003c504101e581c1d800c902000e0000000500030001000307040c100c000c003106402d40c0c40319081c0000c201030b880b0b0750410070140b2031403012400d0828200300da4081810507284c0d1110580060341c0c0b004107039110348040751010070700107103039815600664070aa200b100c4504903517030b07054241c41c0c035840a040d109005034003404490650f00b2561019551102141c081c00d82000c055058161181d4021100c001c0205004524207410017155a48103085400c00c503103601079581403c00090414503d44805000c1280f80c1e0044024004072070051603688141c20700138080118100b544c0e6400007030035502112407528240018100c03902c5030500c1078120401da5042403034900300c0c152034002440211003e031000840380f5003c07480d50840d040c814500c925180c48641c0c00504c000d030080e0864181049112400204120000050b80c0c450100e0700099821a4113480c0d0015031400380740340c2404000010b040c9110a0f = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 550090000 1250 550088750 550088761
    0xe0c090a09060b070201120e1c1b030e091311011b0503070b01050108130c1502030d14091204050f190b030c07060b060c06040b0a0b030a060603060c0503070512130803 73
    0x303800034104d42d4000c1e2104007181c500300d0b0030b16040b14104402aa4540c109440748908010030008481a500d418a03110704031454402c10702e41100c05130403044001c0303007000b5404403160070301c00885a8000f034140c0903801c0303400860300d030701d180782c00112401810450840c5c0411518007035142a0f0380075903005001c030b0b5103c0f18107241258205070280101030115070691b0000f240c0065442078040c54070f0313101103a0640b10b403422445800418604609805501050040d86c404254038411150001422032190b502c03810008038450034182401c107454445a02084140103d03107440542c003c0c03007a401d0300c0d4001c2c4004880c0d0080c28501a5030002c0c1114980001445081c440741c0e0060449540244000c00108030384908000640c4603442c40c08000d900018001400304010302201544045e903000c011a4100842c2d0000c0c0c181088120100c4045030340303040a0060004510844032054003e0510f185541414540501580200c2c84891030607034001c0c0c00101030b00c4844503c05001940b06248540381d0910 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 550091250 1250 550090000 550090019
    0x3131413110c011107082719140301020405030a0b0606120a1e0b18180a03020105040605060a030201020a060504030e060d0e01290609030f030f0a0314010e0c090a0906 73
    0x1c1a12002d00751300f00364916280000440c100c0d031009600006483c03405002e031100300c1039403011111444c500d00701e2007800f800b15140d107404404060041804480e0701410800001d4100140940e414003030780c410b00c41445240c80010700d8140140c3c201c0c90006050f5034440001c2c400341315804c20070074513808600500c1401e451a800400c100050616200946450304400030f0850b240031120319032001140c1e160b00c1da4a04100021134000e81800c5c0d001c01e1411a208903030b85800d02c01117003240140e5550781004240034182c810540c01c8a802c0702c1b203034101491500000d40d0b5005042000e40216a24000b04040502803030b56000c440c44040c0103d074a5000c0a0080d40040c03009414040b03255007008841c11807100e802a0419510440224203c800c0010703000703000c0750350011290315406d889007010180325030344100090b0550110012003107a4030648581c005003600d0f5506000d0000004100052000603050003da030b0340b02c0698031a80340c81d240c07681c00003081508190f1081a006241c0003001c00c12134803 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 550092500 1250 550091250 550091257
    0x20c0f1606080108010c090605030414250801090206121503010903080a140c040b0c07091113080309030c0126010603050106090f030809010e03070f12020109080313141311 75
    0x440d0300c520290380c1c3d840800c0390071b071001030b80002c0029030304200901045000310003443d00580120310369648014071458082ca0100307030003d4a28131244604180514480c1c0203c00d60250261600900100d415030740481c02c14000c2e035040d0b400728440c0703c0004609082d141c02c074007096000200248910741250801810014054a0441c035150410000c0e684001d13000c410103020b0b182d0380c4c0b1018079180c580802c0d5002074110929401040c0500c1100284101403806020394144102403916034409010030345081640c0c20390300c0004903400501c12100240d0b030224010b01c0050b402e081c4265801c84c0e540040382c0048002400c0c2507000c1d2401c0c00425a0342e40b650000d410380e40140c136450b05240e242c080d400c3d1440124030005002c0c0381c003001500030a5104255001e56402c014040710b1502d0b0711980300d0248141d1030b4020f080c1c040820300181c0103642c0c2c0009264002c0940310040c40c0b50811048010114642500401070002083c4d01c01d04440c1e1112540d4110318000300008001e002207208841e5003d50 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 550093750 1250 550092500 550092509
    0xe06120304033c080a0306090510170f030901080a0b0405090a110a05060d020c010b0303040311041103010605070609020f041d01240612020723070b0301050a0306020c0f16 75
    0x8000d01c64040e90101c245a090f0142c806070f01c11418401650b0310014280d01280700c03242095200c400001d0301800e0303400b8060241c00070f18101d014881c02c011a005daa0070104150407259808200c0403906580003108581403a1020329101c140c41ea203602c59440581591414160004d1515080110407900440c00343d1400b440f400c5131000f90701103042042410581030254950064041000d89641c160341c0c0e00070300800c05c900e00003103400c1d41c0d020002411a00705d6030040c0d480d88900010307150701f880d0038421901620030100342e060955060500050282c041c40c40b00400041e960720f4501e0666580c4005900b00c084004e0081c00442c2642a4005214003510340066041d0700b0a0364105901e01102400140d949113228100801c0385880340803288500401519500c0d82e60800140001c190b004040c0c82070603010100715540f91680c80c41480c6860741d40d0307121900c541014401449559201c0e844402200d410502c00358580c1c841071a11810701c3c5c280c04c860500b41c403030f80800340a840c0d031340c007000001c95 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 550095000 1250 550093750 550093793
    0x22140a031101020a0f050705100903020a140105010b0405010c02041e06050f04020702010807050a1103030423120904110904150302031c020a17130306020408010c0512010e0612030403 80
    0x11a40d01e54003030300740d004281300d08020854500d03880a20700d101e0030140540b640034400f102c0c8110b000d00f42060484800720001d0b40140c01211207a818030100064000036100003200810240d80760024030b00143c0114040c140c100030f00070481905542c2c0c0da0b0800c411041c45031801089100515a040000304024882c25028000c0c56905035000c2c60a4400d5441c22501030715800402d6860b188110b03450703440301003c0020310044080c8030310b81441c1000135501c01c40c03160314400c0354507040454119000f00b04488001155200600b4031b07a202c00c520044d51680e10b415500800c040021451410701400b130780c2c1c001d41c2c003e450200d459009035100300882c000c0301c0c000ea0560f040c40130600740161400c3c0484071440090b038003a0030000f0004100458409005690f80d201070300300181d580400d0b007035418560099076481e070003140c24018200e084c841c8070310703011103401c4c142d1801100718015284600144680c48006110000150aa0701d8001c044000000303580309a07603031240c4074502030944034008450b03030088 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 550096250 1250 550095000 550095017
    0x1006120b030a03110a06051504050a0b01090b0f0c0f15010b070f231b03060c0a1706030127170c0c0d060f06030303050f16050322140a03 60
    0x520694480c00540d21006000b4241c1440152001d90b02d12002c0b1075122418032808039903001052583c072641d801b0f5020341c40d5500c0034605400c1003101343c410145c44ca440e0f0b10310b40303803900e00e080ea00041c0d170000b12412100360544a0a072415010918000c04034084030a004007070906400329408180d550143c2900a0001001e90f00c0781e00d040041d029010004200c14200040742d40810800346910040d42c071a0312410603482c54264005003011105481510140d1500310791414038a814002164442c980713840403414641004001400b9000486051083c0e6105801240c0261003e4201c3d107240e41c0401e42c03c261200d20081181d10058002e0026140c504081d0260010794281600300c40740f17410182c00420500f2186c90402c0b0310342c01c01540031540150f440000300c5c0101500c1c080ca500550203a1000501840c0031001d410003050014548184448540880480b1a41100580b50450b105000c1c9030440308001d040e01a20360040030004d444050035261503110900300260f2114030a1095030b68184 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 550097500 1250 550096250 550096277
    0x1b0e120102090a0b0702151c050603120708070c03050616020c03010c05040e090a060e030703091502031911010203010b0a031b02030405131b09170601030f030c0503070b1006 76
    0x202d0141c010240d52010f02c1c11402c01070290060b015150790fa000402e0341624051900b041d042541c000807950310b0204000400c840780a040d48161907200710240c0150150070022051401e0780d11a40c18020400600401c2000c10302900c155003401456028084400c03908007001d207408080b507460070306001441014003620440c2018014054100c4030750710303503508141c00c5c120b02c0a226000102402d040784901c80090f808075000c1d00440f0040308940025503070f03a010a042c01000410326070004403800c4007107900c00d045154008100c5192042c282080e501906010350119000900725002e5900756001000108000c10020001d101c1d02840351410061130100d6440c040091200b25005805600248030400460420f040040310140e20802c002404490120400c1c6100d80411039040025240c1380b428013000900e09003104002c464000104403d62469940e40b89032010b40b40c0050412807441100d104100c820415102c080c1c0d4042d031f40c80024640500e454411003100e1186800080c445002c10301c = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 550098750 1250 550097500 550097503
    0x3030209130b1f02030c0a061505030105011a0703051209011d0f1e1f0f0605010903050604080d02070b070f080612070519050306090105190c0e010e03011b0e12 70
    0x180844070291004141d256401c440010120f804492242540000c002c440e2407204240044419148603440c0020024602c52100442d01d5207038020078003a0b85003200504c64070040b00031001182202040465441005140c01ca41c9070062450304580200c0000c2031010200040d0018100c56080c40d81803600b01c0b000740f10451b502c2d44c55007400c943d5a040ba40381031003404d0b155042c052981c00e00c58100c03186440c42c4c00c181c03048402100703404e41c2c3d62943d44004140d08030580c002c42c2c001b8882442c1c58a803440c00c54032641d0311030a001d84001c000c81d900141d030a54214007901900c4080350000d05005480c503020b0740150102c40010314200c00500c4c0c040005543d4038000000321580307030001000340300175810141030100100350075620610240301000006071503613003084654842c2d1110700001c500c5040c0314040030546040d90085004a80c18006455483d65000681c411a91800d2816110010300400428010004012103103010410200b9446042d5041886d139440b21205551080c40e00c03040e2000e49 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 550100000 1250 550098750 550098761
    0x3030c030d09110a060c0609020f100809010b0d080d0c0306050a080c03121c051503070f080f0a150513050106120b0604091a090f06010e1f0f0506070f0c030303020913 73
    0x1d1002c43c0c0300200139000304000781d000d0785035540301034102c0b02200440f000048690300451401cbc000103450904218031041c0a005061401d1022780d20000003c0140d44c034900b26020780c034240b91a40e540c4d2010b40801510030f030081002002c5c0a00040f0409171600c85080d150194002051300134420028024626102c200031900c201004014400c40d0500c0d0b080098003808000d08290b03000c4a021030280f9071aa410300142000b00a400c200412084c5000e080d00d00340300003041040202d4100c1c07101c120104101c2894880c0806c038007e40082e081d44c5a0042c1d4140451501d03002c1c000b90b207000f801240380ca0b500105511801e0150b11301f22010341d034100c100402c0c1c451400c40200a401608000035100007201461030700480d051050b511440c0400c09190300c2d1407402d0b403085001284400c02d100d10b40e002d00306030104100044400400c0141428440036091a1500c211070283c0b100080280900c85070000b0040c1e101d0f402a000300c2c04682e00d040007030181d0030031002d56115540703041e520085009180701c0d2 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 550101250 1250 550100000 550100009
    0x140d09030c1512020a0905031209090c0307030906090302060603010605040203220825020a06260903090607050d031d0a12090816030c0801020c0a0f0203030c030d09110a 74
    0x103094103039042200c8030500040c0c90302000180021025500f001050b58009041c900c0500d50320407144074a400704051030030402c1407504192060800075880e10303444d518139655200407611031150b541e4484a40c1240201004140030300b03040d282100ca0820154082500c81c0203a07002c40c003d10a40c0d441744100422880141c0349132142000001903d1040c2010316418452140504066070a0240d104000001c42501e1503c030000050000405400c40c50301e0041d15020340141d26182094004c4404901d5502d80080150706440711803a0000b560030717504000f11103404d42d010348282d46400342443c1090351b03008010b0420010a04140b1065400d5184c0711600e00444c003210f006080d4842251641403072203407003180741d81c20421281c20104e41c1c40810403441d0503074820ba40c1403d651354507502f0301703442c40051034014110a90041203083c2c8000400103a1513401c5404c899580c44102c00c61000900d58410001c100c04ca0b03000201d110004008280d0000c11014000c03e403d11201c4000000c010041d5102d008 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 550102500 1250 550101250 550101263
    0xc061d0a060c080601320f03040803010303090b07020907030518120c06090109030807050f1303120206060603070f050d021b03070c080304030f2405180c09150d0302150103140d0903 79
    0x20590124040d0918034200c6c0c0349500980e51070310000702e1005a00d43e00c00c81d4151030001001004004041c3c1c88a00c58000740105801c0318204461540000da11100c05031260003003540b9480420001e02262001502c2c9080c8441151180f40602d0000e0b0844d40104850103994080d81c0c0001e50130200600804014a034540c0e0345499556803964155400c0d007003030780792500d10f14040c03200c86401081c03000325101035800303010403034010501220028a058001003202e0300504003481070005064100503203440f03c00751400d0040e2166410107000b00280608081010003042c0000424008980400100300032402030340300d5100f0130340391111607603039104503c40180126040d58201d404640b07126040780902810107208104201201d4030384066030f00503560350501d030742c2603580450080410414845100410b80741c0010301d161507400420140c4d03000040d90702406075240c80340308140c400d0000c604c0c0040002c7d200b40095840b418200070440e83d407000c4840d94803404001c805034a008079404000c81e50b00a4 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 550103750 1250 550102500 550102547
    0xc0f03031f14060307050a090306020a1e031b0e040b03150403020d11030306060a05090301050703020a030e070b07172514030309060105040e0a02040203010b0c060c0a0c061d0a060c080601 82
    0xc040306c1076800559100300b0083c031200084005982e40c001058829070503940d6a03030414100c3c1c0412562940000500145464840c1c0b00307150b55030721000d5003408811400c164000707500300030106025040400950340d060007092084906540b40100d074030f000f00d011390b00321451418824070a80303100c403401400348055401031001079268070703045004003143d902505e440e50805032110f000c242503a100f5500000800d402045d0341048503414401c0d10300e50b02e020070003083c44924007143c11121703203d0202c000e02820365607550b180e00c80103400304845000600210040084c070001c03c00c03881110300c0301011190704a1359944514488000030070790f40900403c00107400c00782d18000420000340408481d01c08a40513841700b840144e1b0750340c8007039802440b407401000d0751000c804280074100304004043c0001c0030800d00402e0451a4040118801d199200100003601d43c030614001044130703149200c0206a1150880c40b1080011729084581c880d002c0c1d840d146215111880151121a118407400342c0300980d28 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 550105000 1250 550103750 550103761
    0x8071a04050405060a0801090b011809020d1214030c0c010c05030f060f04061d060f0315150d0209070c051506060a050f090a062a020904080c0f03031f140603 69
    0x903800f50f500500c00402140701141d45480c114291105641c040e074030b41107050010004449042c0c0d00c00c6012204550401000c05160b00081443d218032102902d80c4090003002075849002d0940640703500e48618005440385440d2003141450340c002000842c41d94207001c3c04041540c011000d0b2030103043d08903c0300f885541d640041c400c4d414460381700c41c3d6000380c80c1d0200040328241030007034081c0f0b45211078030344460f494940c0038060395410300d45182e4000ea100e10700401042900d03480745c07074001c0310017100003808402500c00540480416400658013540090502c01c10342d4100700c00081d401d20840554041442800c1e003040450070407115030f90015020455a0210382c801c00007480103031079084140341401d98503070109a9084150f0030034001b1a07000c07505011f0344c20400b0408078000c0800f02c0106030564150780429410b082c05040100b51038004903603c80c41c500280301042203800110100ca40700e141c00d05000001ca070814050030005d40c083c48010030002c0c8020314401c2e40c800054031b4a861a201d0 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 550106250 1250 550105000 550105009
    0x1030c1e030b1b0d1a0a03030e010c050a02060a0f030b0904120f1107030507081203010602070308090105120a1d06011406091f03140903070c140105071b08071a0405 72
    0x400f90074060254414412002402c08050800444101400500a05004011003c085101003203500c604513071102000003d038468032001c4845020301e4502d4106a1a01e8010710341b441e40d000082d8800d101182009a4503030150842d0a2910199402d10080020b0001e01c2504001a1b401408078106070650103440e60042034003140b0000e40345404a07800107003c8078182401060b80080b150b94101000c1000318940403c2910481959070440610f5545082000f954030000c5200c000d00c0d403c004144810146e000d001919040751090451108c20314045018500810b45041d00d55587c00c4050000c0c100f1520021b041c50503581012486c1140708015410825260404408651722030310000394000c0000c1504a20b641812103501e0100f01c043c41c11100284d4544010441701007648140200004a10180050403c55a0200850803e04011001266944201000917000754603000350a1002000e0070f00810440e6070035002d0f212510348810010008040f021104e0600c07103014001446940341 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 550107500 1250 550106250 550106273
    0x11e0f18021009050301051009110a020714010504152007060e0411070807050307030207050d11012001020c03211009110913090605090d020a0308100b070b01030c1e03 73
    0x55810702c1c1020340c4c0e54000007405d54074110f17075481d55541030000c100300c0308844e0b000c0c124200060b0003d040c104410030784003e564003990f200300100500724203041c20302c0764000d02c00c8070090000d00800760f400042170400901410240440c6d8031075440904d9035910070460129155040d83d489503940300040f00c6d424104409094141d03040004140e0801c40f81d80040c00c0c03079008281c01e031f2085014545425442c00c0103070918026500041c014040030035508000f40c2400700010a05200f400d0508038400d4090940943d05c441101e000c500e03610000e02c2c11036038500003001e440195541d070303080040d680689400200c0e00354140da1580d0b2440d40c68109005800e00341d04800c040c1c01c28070780740900306600e6100181311a00f00300d0402100c3c6550300803040c24000640202980052031500501c003500284100170341e2a51100d20143c10040c601011070f030445540421310006040c0b240ba80b03a182e0005040c080d66a9001780b004030b034088803600c400a0325138035143c007448000f00b10701030f10b442003461900d0321500c122 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 550108750 1250 550107500 550107529
    0x70605030a1b0c030813030507020910030c0617160e0d1403031509150603070c03140c031b01090305180414010e1603050f070c14011e0f1802 62
    0x1034407010720084202c64071400700c02d4007180c1e83d41d101600e141c40c103003d0500340003c0c1c03d441c050130216424101198000c000c451038903a06845d4520305a40b84040c80501d44019080117001002100001032080d41c03024036642c80964101040780ac5841c2d82d02090005040d2524040c0400d0076181000d140e46800001ca07820503010310524031010101a080c542141d004440c0e0000c50031601c0a4240e603401e081d01c0303281c0e1005c44450103100108101000500500009104a0400c0f005035410020141305441c0c8c201a103003141c0241d516007500101164907904000410100c900c07800300e086c00101014003030350075100d4168503500c2c03030b154820300c0107504180c0c441c1c1013940150300c0d880f5600c024602080994028000700301811614188507540d0f00c0d83d06602a55501054240402d11280c40341c8980c00982110341d81c1001180d0200da4a40070121520001912042d5440c1054600c810341f0014019031040b100141d00704410060390718100225402c0b5190700342500d80b00e083c2c64005081203108102c419 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 550110000 1250 550108750 550108771
    0x604140307080a05040f080f0c12030405120a02040b10141b0a03090305011b090e07140d0e120f030a15090608071404020903030307030f09150e160807060503 69
    0xd015911030800d107a00c07140030f00000603000101001289688400c4001808141000d001441c44009500c0c1c0c6d5a444090344510841501c000140d80c01001c104480007820041c0000b410032140e0504a85c40c1c0045280980c0100d05100d00c00980f80f805e00c09403403030000142c8580d0f0907415807003589803943d0004030b4408031146210f4451000c92008100050001707120f59100c04109095107480b609507030052a98002000d2084147c8030965046007a8409907010281d00004c2da9842810440f0000050b10050010100024045a4102d015004400002c00050880b148070240219a400078428840d42801c000014004206003600342d07003141c0e14210f45800e010040b141c503802e1143c1190301c15445184a580051801c0104102c0c4500b4081881002c803021810602c0748404292039203c001c00182c105036403138024405403850340d402000c909420002003280340d43e50300201c500800043d4940800c6205a0300a0b0000d024034100140660303d102029102d030a14209054030a038101403c0300090 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 550111250 1250 550110000 550110007
    0x3070207030b01170d08010b0906090f0405041a10030f060905010902030609010c1b0302070501080a09170403140c1c081c0605120c090403082707141206041403 70
    0x410b00603010035001c0c2c1340750444440404280141c081c0340166400c2203105004170b0703600411040da0303039005403614282c0a854213599101c00c02c0004840c480e141c000554814035000c20301c0240120030415020399480119030050742d486850394104030b03600700d1100070b080c090142d1100e80003540a40050014520410000c90000300c1640043d08080c02140d000792160354030794188407441c2d4082c4031890000c4c8012140d8030005002c1d24001d450320401d005080c180902000459034040103076000b414050b800c00d004084038dc01c80035805505a00c1484180c481c0c0403184004403400070f0201e5003680030000109036400ca210210389142c85410341d1030302500c4120040c48001050702c01600d141c040f4108400001078942e0803e000c1000070304059a02d60907540c4184a40380c0c035a03c9014402d81c1098060408903460b40d0741801541074003414500100000c504100d140300910400103944050f50758000b141d14405201c9401d215444102c00d02000e01030348480041000300301903818001c00e000001c0107583c074 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 550112500 1250 550111250 550111253
    0x7060b0409030513060905030709051018021b060f04060b030a050f10050c1314040626120f1204060b031902180103080904050606131e08070305120307020703 69
    0x480364840000c2e004070b000010031240d50003d50310f107500903005a080500c1c40509000c0803e950b0203d900804c1561a521408202e86840605610b0010a41c284246c4154600c844c03035030700a500404209079225804402c0800c9102c030100d400c0380319214103814131010382e803603854030740c0503188030b004503a014000c0b442000d020507001c0c40a0031030321440f03030b0040803803109410f00d40c42102c4004002c26840300080c400e541030441900c100c2700840e07848001520403001c507100024001c240c1e6500c01c03c0381018140a00d911035000e00034031020303420780d00c0070b580d640b06090030300e010b16100c1c443e44445291410007428101803081e4001c5a003082c050f100001da8401b400012a1400030700c0c0c400103030600500d007614030440c50007542590301515001e800308619450b50b520328080303000388041c080c802c58540c40002d40707688404c000d0b100013a01da04c9016841c1980c0b09070304071505541c02e000403d080c05025000c6490640003400384102d0340c1c040d0003400c00c20f40f0449030f01c00d0b50300045e01c1a4114022500c0000 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 550113750 1250 550112500 550112509
    0x1203122a26100506031e090c060307081f1a1e04030516061d0d02030f060c130f06090e180d03140f0709050f0105070c170d050705100207060b 62
    0x4500e5020004100c80c00e0a030401402d41820350300051107810b0401c10403040070114445556036020030307818075a0b641c0b00c0101450030040000c100581041c0f01004000c0c3e1680c0c07182e01613008600c50103d81c86001c066140c4075180355018041c6c8800307151011211051000c0750401044140241c1405e076001100050000c6a65801035005031010391001d040d8503103440035101c206000f80142d0801e0a0031900d008410560b07050014100d0344103090140e001c0082d51414042080f10001c2541610303154500741c0007101e2940c21081c0601e204090b818400b25002d820481c1d0f00080d83e62a032034a01c81145806038205034640c0042c41d24075400a9021f807209658410000c1c1010b01c82c440d10017103060307003c2ca001c813001a40001d00c200410705088041c4104150030030000030569009a0741e001504142c2801621144036426004050010421b00082d641041c1d0000902124040b01600d411115041003102c0a0181c0c600103083d41c0c01c012440701c82c1203481e90007080030360b10ce0b400101d1006041000178 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 550115000 1250 550113750 550113797
    0x313080c070902041e06090e090c030f030a0e030604080706050603031605071401030b090105210601080f0c011d01030507030f0f090204050633090a1203122a 69
    0x164043e801081c2403006460700f4120f9054402d0341d942c5900c040c3d1501e64000d00d01c0c01d45100d03444000030584003203142001c0501680149440207001c480c1000901e0a40d155250302c082091701c0058186040c007141032801241e40740c05035411040c0b15040015544604008240180400d58103100400000c0d40b1070281c1040c40d90918010b102500702281390003851200100008084c03810145030244d117818654a016145065460980d501c13026149100a80202640180c224002d24031640c0c2c0001480d01c0d0000e40b262110880c3c0c400c1d01e900c0101d000056400d03d00281c10f03440801c0d4501d6840d581c0c0e5100794401548140f091502041c481d01e40c072200f030100d61100d80002c0c0e0041d01c4581c1c0c0019070506020307081c0c0207034041d01d07100f48403003064044850051a140080c011a000c10b0043c94102c5017210030795942d00401170003402c00c6d0340d03181c001c44500c050361103044010440801c400703089500d46109a0702054000910010039070322170b1901d0040180748006040a00c981c1184104100d17202c542c00 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 550116250 1250 550115000 550115009
    0x7020a150905010f05161805060d0f0b06131e090603030201020a1d0d080d0609020c060406050a02030f040f0f050303270309060906071a070e01080f0106050313080c07 73
    0x20420300c1824414251407582c450000c500d400e00e030510626152920080d84080d80d20314161503120f1f010700c0c002011101c82e42c44107904c0b0001003a000c66a1400354060500c0800546042040c028200140b040c9070180300754540340d035200e11000300400e01a400c1400303441410b085207541c82a840307140030012541150070560050707501088030807050b0341001640c540414809020107020b01d41000003040d2009500006141d40c07004260000c05402a0700208060404890159100d5110b03052041e5214400c84083d504141000007045c2c1d984824400c4134003410310300e031004d80780e41d4464641004204a80b070044401d0340800101c07202103542407000e07600400d05140620381c1084841c0c0c90010601c0a03001c0200d16400c20002440e690703903008110307090b402c020b441041c1c4034501030800c45214036080480081100603101080507403036011a41010f159805d0303d4070025512141c0b101d4607042801d010311008514104041031510741c000000f03808251040b802a4600082564130a0519105620 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 550117500 1250 550116250 550116293
    0x2a12040f030807140a1b050703030215010605030f0408070f150501140a0f1707080604030906082409131b030501140f04060908040504020714070909110907020a 70
    0x4460415038492003943c0c100c10580340000c0d1005007910030400600c04c0f000c05500303124013000340010525980c10a151019084030948060607075a050103522450701d40b0041d8003072000b501c00070541c2400f03401582d0258841c003100003c1c0d56115929240c8030f900000050300c060f1140740f405000220340780310881941320080000b00b141d5141000c00e6504000c8c0310502445003185120038805803400d103140d1401c840403440700f10000180170b072545090150f03a80100049005484c00c0000381908812300c80101d03982d507a04e40c03240e50f0f00c204100c1101c41ca414803c40045942000500040c94207601190f00500c0351300300880f400c0b1081e40d445820503a8203540000b62848100c007001401030a1050b940700a02003c90800986442605404070000c0100b00030289a030b81c0f0810028418014140c401030100504215981d034150700b0038800907000351000350901d10986001181c2038000340181e0701c565030700038100c80501010008000408000814a030b00314032403a4044800301c0e03014032a02100314104c3e403 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 550118750 1250 550117500 550117523
    0x50f1303020d26070b04170918160c0b190b0a0815180a150f05090109021011030a05070503070c12060b0405010e04020909010b091504142a1204 63
    0x20441e0451080c110383d10141c01c05000740f0020401c007030110b90b80315500c190404482d04500724096024040c0700784254011880480b0b010113124101c010b0780c0158603490015040b114403132030440e403101d050503000f0248207030130000c208085036507186042d10705144000825028000404106174010560002c8a00d034040c3c8800c48844d014003100da904500f0816051161813807031010155502684140140318000701c0303503125025042c40c0d00880b9049a14001400b4a0801f5000c4501800308008180d00c1204a207003002042402100c121415104605c05541400075040058920380c0200405880345d0204100752000108440046009012503008034900c0440d6801c1c118125a92580248e01031071405005000b040728035040c050303219a049400c07050559500d820070b03004d408204a169001000c0701e05101d01007419071150024a85c0c2070b10200808100403e13007024039002910200180ca80e085207001000203009010812072412010741d0740341448048055200c040201c900b0341b0590307883e4 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 550120000 1250 550118750 550118783
    0x90605161203140a051b0a111605011209050601051509040903050703080c0405060904020c030c070f150201112a0a2405040209070809010b06040e07091203050f1303020d 74
    0x8603001341c0124070980108080d1400080044210301c06c40b00ca076050550102e2504040c501c5680991428000340c01581c940d040c0e00070050450b24410b02580e4040381e2001041c11180a180c0705405000c1d0304800100078507460401031080340748214410300c0358800c1c100003001003901d980c094000c06502c070340c0e5207990751002d0f82030060001c1e50103040d000c01c90401300000c0215555450550724502000c650060396580b17a242854914424507102400c0c1d4004d82c4000101c49944446403012111034440001c40b09140d000101e003221714040c0c08281155003800344081c8001079045a00410300c0c040b070300d00450500e070030145140c1b0120346c20031039a1010300c0d03a19070241c2142c000c64044102c0071410a00280c100703640000e4a04070014a41810040a040010311220342500300e00300480c809401d0998803901c1d03072084280b01c00100c60f01e80c04a010940002821000502000d2810350569034060402102d20340024495010302c0310b40491000c00240800580d947c03048242103d440b503400c040b88031701a07 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 550121250 1250 550120000 550120031
    0x5061f030b040c17070e06060d02040305060a09110105090a441b01020303070c021f0c0c0608090a06051f0b0a0306050307140f061e0a080f0601090605161203 69
    0x84050303034160b6801175001044800a401400c80c4c0182c81102d00640f283ca401c8072000c020300842d800589a80300e41c0c000d1058080e01a8400e0004034020720341900601643c00040d10310f40701d1811020781005006500300107040841d1a8400440c006209074003503810605c04005d074450f0f1000c1d428080c1f40c1009040140b0180c00c0052100c3e00407000243c1d5080c00344040043e4030707800001c04a42c1400052140b01c0c046650f1003044041d00039403144440900c1d16041d1008041e00b2840c1c0048500074120074002c00c80f113004003003091003500300500401403640c480c0d40e1240a008050301c0120314009041c0d80d01c001c00068204000a8429121407545810070303602c000782510a25446280680c2101c0c01c03c0c0f06403060a10300344240c0390180c0d108504912400f003c02c41c18410040816121780540c0305039600c000382280140101c2800340d888000759101e400e18105e0041081d5a035501003000c0001c00c09c0010700810151001c41150400c1c0703241d404445c2c540c4c03000403542406002c0000d54074580c0b00f890802 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 550122500 1250 550121250 550121279
    0x30f0f062c010609060809070b0301060c02090a060e0127050106050c010f0b0312251b08121b010e060903030a0f020f0a0e060f120f0606030405061f030b040c 69
    0x260074a000c0410b502d001000750102803140a000200b0100b40006034a08078200000001410b06000607540c0b503a4900c0c005200c0c07020700c1001c80c4120920008654005018003c80d001e90703284140c1d841c4564a020540e040020034180c0848400220806165400c100c0d407103807900910b00703525000e0740c0c0c651101150303003101e03000750040d0303491031801c000890a910b000401c8401804d02c2e014503070780c0c1c00165050308960464429654901c0541e81540070400400f41c0848a444030319543c080c0440340c0b588109626164508403003c0394610501c018282508141010450311034503100009020004031b400904140040311204442c1c0d00010138080ea0030002c1c40303503c91425543da41182840c1612411010500c03800858400b001074107400d0b0700300340d5030310303000c85000314020145281c2e2521a0041c0b01c05c0c0940c101c8003224247c140000280040c1418030441c1c2c0300301c1d80a40580050750303a04030b24006003041018016512403040f0300c04000071f81040c8440c1e004900400c0380da0025032600c40e19002d402d2 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 550123750 1250 550122500 550122569
    0x20a020103052202011202070c0b070314070b0a090c03020409120e030a03080606031e090a030e0418060518010c030e0d020c060a05090d020d1b090b0d0201030f0f06 72
    0x28986030443c0241040c040c0040541c0d42480c040c43e200414a42c46d80c080e02a00c100648090340070200001c0001c4480003c1055074400d44034039403852584031144102c0e0041000107041505000300190042c1d10560043e2596071203144422480d680300d401003803c4a00042085510300c0d80300780e090360060340140445401040890040c2201d02142e0313401001c012014060900440001c07012030808081340f0000c800d1044030180d0b8810a241580300642e50740c50342d120980101e420000301c2c50300d500307003070140301880410110601e81411030360b0365010090800401c000040060301d910b00881c20001c0c0955202107141c0d03a000700354142c1c100c02c540d00340600b00080340103650010301d50f15040d888003410f40d0a80c5402e4144961190043e401217101000d4510000354048400c1c3c0d20442049460601500d070404c81803031101d421034480e0600e0741150025048070341e01c030500200000043d2f229411503000118420404902080d09814000980300c00d0f8000003001c04444421085d0050400da1048440 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 550125000 1250 550123750 550123771
    0x80712230c07140d0c0f050a0203010e030d05070512160201060902180312040e0c07030309150f0c02010504020f0d0309050d0b060108090c010507060b0105090a030302010605030c0a14010c031101020a020a02010305 93
    0x450007a02500860180000414a111002600d402d00a00b88070059040e89c02030024080c1c00180400305849500c0240e40200f014030300703001700380c4161160059071910540c00c42c944d10162620070104004400121b4036100315074032010f0109104159001418154445000d080403101088042500b040e420720340300c007041e0f40140010450b882c00c5064154100c280408403075510307010790500b11301412010101400d92420600e00307503003c80b110341c0109031003030390110100b08150804a049080e030b80140d5001e503002d51515128041441c10141e00c03c0607511a080c0b4000c000c0d654030100d4035444007808181d50103d080020031905580002500e40c0c02455180035140c03c0307680e10006000340c02070450150480d039641d40420940c1e4040c4080712604a0010207d040c02a9640f4000b80070700194001c40b03009010749044440c0b2800c140290070183d5200348010b41c251110b40c0011110f01510030b0301a010840f51b00c076405810701c420701c001c044104ad154045c0c10140d4480c000541034400140802502 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 550126250 1250 550125000 550125013
    0x9020304081b071d060916020c010503070e0919051f180b18041b050604090c0302040b070c050108180d03091401230106080712230c0714 60
    0x5104242102c2e490802e1000b00b0071550700c07588500346040c101d50007603000c1c0c002960410206a021100315841440704690754a5241d48151058103441014040c080c0542d11065801c0f0256015001450b80403c080c07511190300c0803488002554100107540f4070050850720a07089014081a0050303a40c002d02c0d080015020000c804840c1032861528401c4001459013018041ea07400b00300d81140384000c400800c043d4411300e10750f0b00120450010741d01120800c0c04d818800f05800006188403080b0390b00100614241450480d000c0003400020001e1800c250b070030400810440805c40c003810040b4010601291900d0800c400507106000140058801c0319494824800700480000d003d400040b4510b8042540c042e075152240d01103454000480155090421003801e0400240401c0910241001a030320283d030b84102c1038601d6181074500304006011a0080c030540e2825402250100613000f003440901d480141e00040c180c2400d4428510b0260000744078811321005801a2000746c05044c0a400c0 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 550127500 1250 550126250 550126253
    0x60c120809060406020703030f021c0f060b0f09030118290c0405060a0e09161d03191b03030e041a03300403030201020406270e090307050706030605040609020304 71
    0xa4600c00140020302840c5c00191000070988650000c03007022046400554644c1c880d080d40b4074241202005083c3c0d8a85404a004c038031040d00c0c0034207030898192480d002e20700759a1000b81e400d00d6000b41c4020b9003540d02d8401b201c0c9044480c03c508500240542800400f503017010f1340001640420003403002c1020503610030b011040b96814122001c81d14100c5007950398210807102a00c0819103d0b4800754003000120810a09c58040c03009214004080ea0f03c0800c40100f0240c84071103801100c84507138069008882c03080c00b603a4002c0d10745500754004c8501d800c2102007401100164441d81d00104c4c0010b10751300112410f0305040c02548201d00009044141829140d40401c1e03960142c6100d14902c0d03052320f0000e01e42c807203180c18a01604024503011030364072516410003078041d601030700c6450005921181c4500354003007920381d048103440003a040140810702d0034009080608010308030031518001080072000050f030030840c02c401440d0540700405c0052800040000722640c41d4050070030103004108010 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 550128750 1250 550127500 550127503
    0x905030306010f02010f0c181a04170a120201020a08010522020d02040f090204050315010806270a0302060403080c070512180d0606030b01050625020118060c120809 72
    0x29401072007807038090703038140440500304d01400e080224081e0462074858100c200a510001002c28400e051108154a6555100c02c111090580b4207018002130140010322095441c0d003c4582d5242c0141d08a0f144030100d40c40b80300d110380420b107426001d42c2d030000e6040034064008508500401045074071000c1c42c490580705005d40e0034510301180c4c2043d0b0005440c10f129100340e040d00c1c040c1c0104040421159229040100254801d0061074400e210f00c551800f030918402c48120f058440c840083c1506495a104000c170844041041e46942e052041c540c241c0724604021a80c40d4600a5000340340a0a143c200a4032400c2c0c00303072901c2d0409004110700344c04102c0004081c00d01c1c0d20140340310340c0c0c1c40e511984c81d80300d0942a000180d40c4454100d400c5400d01040750030090035240600040045c0d030340c0e1201005458850174010354040f00c02ca070064228101095400d0500071700604203030913030304405142140c200d24580c103c1070109088441d0740043c0018600072a28242140c2403d510605122210300d = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 550130000 1250 550128750 550128757
    0x90e06070306060f08070212040f03060501150504060c03021504150515010203180a0f03120f0302070f02090402010909020c010603051204210c0f0627150e041d0105060112090503 78
    0x184211070010810040c820020480140681141c8c1500c0b107441d2410546009984d2105807500743c280800880c1d0441d40c1c41c115500030302691136240c0b0f8a45003500503240180c8041c0141c00351f0140154101115400780146071040d0f2240700c48141f071602d6280c42c0ca049031405441c2210983c19600600341d07598000046880c0d02900d13211588106810900254980b840c1c2e0300411082c80010000000704814a00410b05d0143d1a464524030142d40c080110228082c14801500b1450700701c0c520000360602c01405900503006140801e0001c0e102c0b00d80c07000340e03404510b11042c160b56590040040c098144081002c0b80d2000405615041c5000c180c6009582050015200c3c140d034401c4036800c01c00c0c14103040004124050a2401c4940d4401c4050a20030745440e4070004c404504030488041c407011000802510f02841480b0300e240070780070084640743d021040554100d41d4440588a14642281d00243e4280c0c0301000841c0d10302c2c243c000102040c01010000e100c0e08c0c105400c200001d940071003079 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 550131250 1250 550130000 550130027
    0x1a0a060b09042703180b03190b040f11040f09020306090103022b060605011106040302101d0a050102180316030303180b0f0f07050906030c09030a0c090e0607030606 72
    0x4100a0365860806800d1500218000c9800c0c0000340d10f00c1c10140c10038111403000c0c4002c101142c072030350741e0b00070308103140320407100040d401e58a0303280c00049100c1e07540080840100500001134034408520b240e402c44d4004445041008404a010044414448240809028500d00c19810741c100030002c507a1041041c08001e00c903960300050305003000041d070044030040c1c8910780e1b4061030740941d0800720000c1040c0d000f058001000c400100b402d191001a03c0703405264541c1c0200140603c03c900315004040005002400c142d822806440300384040001040060040700010b03510440c1300002042900050226030181e004400e402c8807002c1e04461400c1240e816080c040750282c40580f0750541003c4804005020b03110351020b12140301c1140d0f010f10f104040d084458161030301e13192000e0b00d2030702940604940c09007040000070b01e1201d189001c0c103503142d00942140d40d90b01240d900c9203260b15058010341050f594400010030009000c1145640080140c1000c101450500d500108407880340c405 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 550132500 1250 550131250 550131259
    0x41b08011a0603060d08180108060103020a021c0909020f030108010506040606080708040816200604080c0d08040801020c0a030e0108060a061b05030316080a05090a020909030405040204031a0a060b09 87
    0x11321640301c44444940c038a40c08501569904541c00a034800c2c50381c07403244180010244000294154040d10880c5c0030750940d6001800030051480218241c2c902c0042681c00304594154000f0742208540003504074031890007000ca8403981801c1d005401c43c0c000510203440382e4146142009103981140d04030f03170802030518010865035910b007043c505900c9403100d400680c011014403181844100805558600c00c0c454540884c03562081c20007905000d2400b9284c000c1e00050b10409081c58030002100381a88030f44201c50605a80e1800603089030444040d5400f42e0f0000e0504104056001100075811002400c0501d040c0c2403400c0452207c03038503070289809001880440d00b030341d000100028004c090744102140d0b560310f00740c3c3c3d01d180c050032600c0202010400380000318048041c14060710340700e0b130204401003c003e560b9400300140b00c2400740140300d00340020030022900d525140024801b1b14040c0d04100700718802020000d04090005214800d900e150050a00414001d141114615441203a = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 550133750 1250 550132500 550132507
    0x170d06080c0d0c15020f030a0302090f010809070b16082b060605030112050c030a052401051c1401050f040309060e0d020415050915040c0815041d06041b08011a06 71
    0x400686ca070680e500000d4800c0d1001041c80052107034143c008040000d002e44801c5034802c00e2400643c0d414030152611403440e000700c08148206c10025010b06000c8406081c1c16042e000e4036118800d1941c070416160341441980000200c03281840111382d840d0003d42d803020040e031413030302000400501040c0135405044070380b01e0914050003010001e28100c1e02c8010241c7c0c0c04014180b8140d0340d00c000385058034901c0341c0242c004c03a0702d818041c88110704a880183c10018100404140800e038820500780840c4d8900c0300c0101d14031403140074400d2501c510720707030011454035082c90b04000e4050222503112100f041040d0703003680c916840e00c4000c00071007a03058501082d1613400b21400b819501803034100b00d41101e4002d0800032418007958003030360800401e4404005c074600c074030b1045a0851049440a00d10228490540d40e03609003035000041d41d501e07000b10300040060300303075460303081080a0328103584681d4810040d007850254007560b1801041c151001b00603582046102c8000306105040c1c0c10720408010 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 550135000 1250 550133750 550133789
    0x30909110408060f01080c4f0605091012141c020a0c05040605060a080c0403080c010203070305281104080f030705010c0318020607170d06080c0d0c 65
    0x507140a422901c0c143c403018030b4180ca042030308407001d20501c1d1341e51181458810050805900094050741916100c001c02c41200780b00c65200c1ca281851803400600700191144880650003800603102101c401c00318410b071074401000088800a40480c003008024402000280011a16000c1840d48042119000d01c1000c41044c1402039a940da00c040b105840100980c4640c0070903c8030034140702c0d08003580029121030601003201d6944c0070319034000c0c40801900c590359010380d0f60300f0b0740201c06d501510b15041e120343e600d800c19040031034548500d80d0040103020905e900340c00740b1580030b11401620800b010b503802c1c18007050310b00c80e0040c0740070039954103d00024080e1a000c80d809808880c08803010401c3c048200c556941c03043c04299100e529091803c3c0800d8402d00030100c01d6442c821000548814a4081100d580c0c4407074800c031160185079624004030003018000c0d0406100c0840c0019000d803911200e20300303100641808600c18150942d00c100000c00c10305402003a1104002d4070405c0700c081 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 550136250 1250 550135000 550135031
    0x350304080f0c010503013804062a12080405070f0e04022403060f0102010209090903040609081504060b0f0d0321051e0601090b0d020717130b0c1608010c090b07030909 73
    0x2080017412aa40000c8c011032456046001d00702c0300b00399003111070f11410502401c050a548040001000c20030107040160145103c4c5c03e4140d0024090350030f9032261940c0b1194100300e0760440c0d010f0b02c1e031a0100000c200641c136110405441c180542c03002400e1264401e5442c5c0f82c8e611006115a120b252603080c1d91900741d00c01d60545065100140c40d02e5080e00706400e071580d03290020b01c20903001882c40e00011038000400b2400c8060b44405d482e00040700d4079103540340c902610545001d030b03402c540d40c1c50602c01d00f540d540364510010380c0642c0359030107200342e01c41d86403100c85d076480e0b4030b600824140018448001c940107218200c45000c0074560805031900300c01250441951781c4103140315100800c10200c00d140c00d600414006104110f068110300020040c42c0041c081c000038078001c9501c85a0821110702c43d4402003090741601c90980daa848200c03c1c4103c4446d010342c0250002d070799100b5202d81c0043d04450813501604e4000401d030f04112565500a0071a58140613143d0346903210b00050654851 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 550137500 1250 550136250 550136339
    0x20c130207020604090f05060109030b0f06060c0d080103110d0305030f090c03100b130b030309130608012307090506030c090a03060c02030702030c0a350304080f0c01050301 76
    0x1401080d0540e44e655071403c02002e460540840000c0070720b06400f2606942c0640307040300c2201c3e03002d1b40d480c90070b80c0d4000002d8007840c4020320301e98114104120011078081c088c0700b00d000120194984103001c0d415801c01d0709018a41c41c030301c4c5014200c101a070314003094000080d00e5221003803403540403203651149400c0d400d102c04030b51160380511480280b0280c100c80307608682e00c1ea202c207444482c4426078030040002034410840209030150800c0106501134205800034480d2040605030100784e441e0349402c210308603000e6800030000d00804404004903241c6100c1e12503001290351600001880c103150015900f44409410b40d202003d0000302d039101d640380c600d041c400035600032404110841c083c48002c0c0d10303584100700403881b80c012800c20038601c0c80c01c10b1a100c00d480c03011105142c07541010300c0b0500001d42c80f0344d80380c4070104051407083d0445010801003000e071400c54040d083c0d42d640e0703950b414945502100c225060000600040c4200f81000840321407480b07500c1c0b128195500703c00c1341a0000e05 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 550138750 1250 550137500 550137503
    0x40612051003141e010b090f0a0b0306150103050108030307050405060c070f09060e060a142709150f04121416060e07080a080301050f031005070e0f10020c130207 71
    0x503c1510068014408070324071043c001c00c440b000507a41080302d11603080b980030100c860760010982010400d10100e13105103a511240900000034911050000a480d06e041103a100403a0b4407030009096807540c0c14050140144a1400294103500742444094140d005502949002d4100030a0f0b00b0310003075081200900409111913849062503c0d200601d0151805014200000246101149803818015125021903ca10039441524402c101c1040014402001c500d0342e5a00481c00e02c87e82014545040c900a82618006154494244980c0702481c1c0c001040c1c40c03081d40c1001e0400000c00c002c026004214140c9203000c088003511080201e0003801070110a08180b881c4d1003044003041b986030700c80140c4622843c01c8420a0ba542c2081c541d654603c0b03140108031113402d000400032810a081304200451000b419541c030341243c40c90000031102c04940c1d103000902a15036030303146806c1103c1060030300c074000d40340c41c500c50120110180d03454010541d924000c079485200e24240d07264076415591030030b = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 550140000 1250 550138750 550138763
    0x4050d0809210c01030b0904120315050402120a0605030a0519150207060b040e011e0e0705031c0315051807020102090d150515091302060906040602160803040612051003 74
    0x30b500440440d40d5541c802014602080c50a100b500c1946016203d05120326486080500701c14035a601c1200038120510b403d04c0c070804088400b1541d03a5507030019111207415800c0c0e00303251307262a41031b40096648540c08140260803841c030340070100d080481d95108060900300c0014403d4240c0c6045941e503026080c02c3e10155101140b9081041700e04c0d0007085510030b08035130078415440c0c5d202c581400c80351400c031000b03100805000c11002c50b003040d0700311140800a90003a91101c1d56101c01090078411051406290501305c03003210105942c00d842111941c126044440044c20f00b080045260040f00103d404250441c2c00005030301580700350106d54040b8000b0b002043c5000851800c8500c071921500d04000b61410b040c0052424058009502d0064400a026094540302c80394003207443d448c8020280d811500800c02c10f0b8503520350368028002400990b00404e811880c950346146a555079402086003504100f001700910741d4030205040000b902c0e03080000c4e00d6110015203004040056000030b02c030 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 550141250 1250 550140000 550140049
    0x30c07050c090106170c0c03160f060507050309010606030204050904030e0d050f070609050d0201090510020a290f0405100c020c0301150806070f080705030612070308031b04050d0809 80
    0x200751712941182010640e40a20192600c46042401e414020b1a048480c1a4824030032291411200d581224445000740039140f0400402c1d19090b084d2142140c410000ca0000401d0060f854824030800d0014a01d502c0d0440c03e041c2444009100074002a101800f00440c100642c3c1c2203541d00c4086040c0c407503022048441c07520540d910b16480d00550321034000424102003001480342015940461100e5050303659500315401c000402c5205000c0520301411845240200d100158031a01c151007911050f000d20700e4817403c4111008c4003004024101409010000d0078800098170024170114000480f207004110741950031400c034640400c22034183c0d815801c01c3c40c1b9201c2c0c10009045102075aa081040c1d41141d40c03905400da41d10301120703044900040390000000c211030b1080000d59003015005023410010409035011515200350340c0c00940b11500d000003030051080d480704c940000b080b10842d85604107071410380080e00d501c00104024041c04c0c000505d04465aa485e18000c3e000e100062810f241c = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 550142500 1250 550141250 550141259
    0x40603050c04060e010b1204031107030614241011030f03040b01151706060f0703020d0e01090f14400501181508030a031e020708030c07050c0901 64
    0xe9588081e0080c42c001c1c1c1c03070b111011407101c2070204030700d0581d040d0401540c60203562021000714020300420950402812800c04140d01d03000f407060070b000314010407010502501c104070700000038070f000e00148070115940c2002480500c810181f0701c44400c007201e080207244172a0005039107450103202c400c040b602000a0400f80d4048100240d805035014030450040c40c3e8032107501002c810840c1449001080c42c0c48a060000c0c21040203d60b0301c220064420750500f42e000050403800c0e0805c19044025030090100c07a44a00d91081c400a908171092170941452031900b881003292182c18000c429401e042000e03c4c0c2d15986511348214240ea0030010303200ea90004100e80007040100c0300c210f00d87ca10010652500c1c4072292405a08d0607900b82c5021180c0030070007200c0400007004138480c1000c81021640340000c0410042c00034111a0701182c40108204040e614100140070344030f408101d0580c0b05001d80c0d0085102e4105490384840d112104e0341d554880c604195207071007044803c131580040321000104 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 550143750 1250 550142500 550142503
    0x90f0e0405060f040f06020304110d08031e06060409110909010b030f2d091501080d09080102070b070f120606030c021903270911040602160b2704060305 67
    0x144118054025954161241c000c407200f090300c10f48001c1c1545980c845030744003003941c0d507005540007072103010802c044545100c0840d0010119082c25210a68013104006014020403111496200702a98000783c07898075000007030003400356000b40703401030346d4a10f00c0e8140c1031400011185110f10081200d0079542e5035405149060f44201c030220b860708800408901d0812001c1d4140c00601401e100815010581185404500000800400700c2d8406ea0a07807254250405240c9400b815036100605050120480701524901d09540030101a030300c1049208041080e03556019004441031400e0b890183d40d5040450307031440008283d000d110f251040001d03400d60103602590951020b502580e600030240100d262450440c07490240100d0071052480c9048016503034181d0074105030191074050710ba203807050031045405095404080c4079002400f4807455404000c40c286402c42010804015814006034001c83c1c002d482d001d01d908050b0b00d5a203220348540c05480780c4265000340c0200801d030766a0400d80d = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 550145000 1250 550143750 550143779
    0x603120a1116080d1119240e010506030c240906070c0806010501090501110c040c26150d0c1401030f05130b06060705070e04021c0b01060206011d0610090f 68
    0x4038018045e20744241c0008034100c0c107000313900c0f0210304000c0c0c00341c3c84610380c030b49020350092201c4001e03c070260440c0400d4400c00000300c126500029507807410100789460105409d44192140a5461100300c00020072200340c0340d0603e0300300310070f900c80e1504800706480e8054a18001c1203c04120804200803c00140030342c1229401d0380c8100311390743e50b10019542615915070910b01a0004601301c80f282c100368000308040c40151424014100131800075030b0500d5040d58041d0f20002c80b141c107118a18050001503042d918080360034450b1540199100038504074140328004c000f0304040b05034801a800395100080c600d124550074045031400902030300c061049200100c400c5540304000c11140d00b410001d0b1000150f000e030003031040301e05083c41d80d161070200800807640300c1164850f42c444d00b1207190095440910401009050703504001002c0e0608070305800c001c404880f240c2c844405854810306003500620152030008805140b843d08032a0b605071a0403285101c03102440c00205840b0712481d5 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 550146250 1250 550145000 550145023
    0x290703050907170a020d05162301021203041202120a03050702060924060d060c090306050c0a0c081e0315040e06070f140c120703080603120a111608 65
    0x3a41c0040e5140c0e00040710010540e0303d20301042d803000f40310304014180340e002221118003c01c115202c00e503200e039620382614040c3c1c10010041c480200c80f402165914022501d600c5024005840440e44504412015000c0200040c1031a5012100088618000e000000d030300c2a041690035504c800148010300540016203c0200501c20034000078001a40424043c094403144501e528115003841100042044080c21151384890307422121800240310344248000008162202c0701d95503d9030a201003110760040000c02a4103041140d43c44c202da101090482d815070000800d41c41e9414035003106411103a02410b0208050000107200341c1900150720750440b0041202d0034826244030402a50702c44505403038000204481d0380798501d070503000d844684110840b1800d064180100c0c000b010346401c0054820808800c40000ca000a0541c48550035034420700c10ba004000005076404030b0005441a4640c0c00b082141d0340e0413003040900140103c40411000c22801d00507240c44120480d1500c1d843d021 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 550147500 1250 550146250 550146253
    0x1c0507020615010f050901260609070c050c1e0306042006180111120a2c090402060306190f170601080a1212050708040c06030b0306042907030509 64
    0x362003445004810350395640694500d1985106502c0a58454000f401c030103040c490303094204400c209003840c144c0014914941c0d23034581400c009041c401039484c043c1c0020100001002c103500172072000100201c8411050340c50b890100281c00b003800c0c03102116400780c0ea1500aaa040c0310500c6600b21090712100003143c1003101c200041d4041040d2449840391240c4007800c1b11010001c658041d40c030281c03041e240d0b4416604c514102402c1c5040d154401325030340300801c0101800d1450604d000b02c100740c50810411107050380724610790019089110042009108020000010708142c40e00c1d102209140981800c03c0111a211854860114094060010b20301142c2640980b41e2200051160407158500040c1001202a4803400b22215482d142d140900040c0405002e0b454418815148510560381e142d103200c1c01d00d40b4000841446035480201098140280c80306c4981d0003064090704181c0c00303164440c1410700304031500c10800c80300342d02c500503055801c20001c00982641205202d00300050 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 550148750 1250 550147500 550147513
    0x13031d04021908240d171b0c060a0804170405040905010204080c010c1a1312030e010c0e4207150606050403031d10090306110a21021c050702 62
    0x7211400e020b280320313503500408244a105850500f0300c078085480d1036001c0d086440610680503011780c4558094582c601c040142800c801405450138000306c40da940086411902d081e1440d40014010300000e80058502d26091381f40b070484100045c2201c3c01840c01600a110300ca0031428164001e402c9803140e0341103409554071480c103542c45461040f2103103a200d5400307108540c28280c045503404005094030030044804400c4004034501d85243d915280c80c03681c0200742c81120900050039108000c41e020140001c120f031a100a0303586403081c01e1900c0c2c0303d01170101c02d4035103840c220005508200203058110702c610041c402080448004103c9180030701003441031404500e14400c2240c60501c6501c0c009103083c00284000303441007064420501b04c1c00752500140744580b0004d8840e20340141a180031800026041003040300f5402404d0704503600031203440c2001000300018020385154034150044801c41d1150048045440e419281074500c0340000c0d20500d0b5a080a00e401440191003240140c0320741c1 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 550150000 1250 550148750 550148761
    0xe0304090f0912110a02040527010608031b0a020406080c120d020703120e03060906060117060a0b070512040905041a090d0f0e030a0605011d13031d04021908 69
    0x34026500060f511140d084540c03890303080112845a20100c0d80b01c0940104c6260f4805a40c0314052076002c1c15840a114901d0315440c40d52206104805030f841c0030300d0741800700401c202e100100568103107950100034001c0344c5030842500ea003440000c1d00021b62140c6006008120b400e40010504100d030030540312148420840f00c04030fa03880c20100344400059000850030301c0040c0d1041e5074440c42d05c50906240b170480c54040c002a080030811207012886601820420503690390250035511000103800c40306119080c003d0100c0c1c034801745400b80000d601c400061007000c1040c1003040342035170b01950482688998890101078040c003816102601c8034070100074401c4560350a40310181c01542c01100401d0000041581520720560800080092040043c04078515482c240700c0010500c0c42200009810740c10000300c01000c4000c2c10140c84120070344410070580082904448200a4043c10060b4400c40c04103400b000700800b0b04030b015045400851004074008002c00a503202e64100d03111030020350340b407 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 550151250 1250 550150000 550150031
    0x2090316080705010f03020903100506040f020702090f0405120a05070302070902040b220906080109050106090b01054f0603021c090804080303040b0403081e1512010e030409 76
    0xa4050241c01c0c0d0400542003200798080d42e80050f49a501d410003508105d40c0d040040d050480b80740000e91095250001c0241500d01441581741164003501c0460074402142c01140c1060300080544644035101c0340440c0601204000d010b05585401c6070242d6a01d013910710050040e08800c004501500c5010b001040210660082d02c042c0c0c0c504180d00c9007416a0000c102411120b44811541c0c40034a00c140071072190580e014100c0602440c100100306003c2514001e42101c4440d80f000e050140b44c60410391046e030f4405d00300d941135058464846201d0080124038420194074400c0e004002e0813a94020b02c006000345082d184c0d0042d807601400c8440c1d55030f1002e070207920901c80140003002d680c4444644075819640300f0203c1600035070459080648600e0107615540c01076500380d07a04d03240482000109a801000e10354043d075001070641d41c40c0780816030402002405031541c01402c0c2c205410b0080da44500842810090080000784461071402031100e40705d03481405940d10071800c0c01c0349120756039034 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 550152500 1250 550151250 550151293
    0xc0703034b090303080c0904200a180e01030b0c091c2114070c0f030c051f0806060d15033f03020f0706090c060f0f09090e03040902070501020903 64
    0x10141c840319501ea81703000210949071f0001c8401e0394015a10340d86400103500c049030030184040c58031030995480d074041002034201c041c003e000701e0401c9600740f800c1c82014003401c88241142c0e8000700d94590381d00c4019074951280107000348260064940202d0340c0d41c42e20f0014000050727a00804172204408061481c0f050000c1e103440c0f42070007140c0c2c003460a035840c1a20740000d01c07036a40205508070b00c5a0f00c40c803490900200591043d1400810b082c8240010703d820200b88003c030000c26452021000441e1010f803201000401c041e00c00e80d004108413500f078005405c0a51142d24042038084840e840b40350142030382400d0107c0b09018814610f2580c0c103401500f1074144d40361941071062007a0340c1611000c9010354852900304442100a000c0c807000030700e85016070444240b168654424503428907400030300a00c0129030a00800c09101c1206000c50f03004090142516040500411a1908101e400b85540704661020008510000d8503c040c8003041d400340044950440594100b80203240b600410f000c1c = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 550153750 1250 550152500 550152503
    0xf02030f06010201090f02060d150807031a102601050403030f1503020a030803090319050d0c260709080f0a0215031014010309020429060c0703034b0903 67
    0x2e80a0701c4a0003528020002c0c1c28030109804001c1003504a503003400c0742d00300301584810320b241c4c801c1e44143704004d003c0c1441801c000a2074007010941c5020380a54440541a00c680320b80305c0301030304414080d11900c014014a0520090082c0050b0034186001001042000c10402189203400d8810943c01030008a40080380e07001401100e400c0d0464846006070340c8003402890040c0b10410680c24040780800300c65a80d803849498080e211108a012001910208082c00e010043d80c000080710a17000d2070403e010340222941680050380e20044103175214501a0000c041901c10204009981c000014084d00320610a0316000003000701500340b4441c07400261010316142e14101c40034000e01103100d4440c00c450105142c045581c0d5075580104049a0b0000340350144d041b1800018110303003104030540c058180040d50114a001c0f18003000c542c9400540c00024200034946040c1480440d9603d40d140784a50780300181302d0143c1c007084101b0264000604520a01046080c0070064140102d401d10b0482e03 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 550155000 1250 550153750 550153763
    0xe010e060a0e060f01051305041508070905010506070f050f060114150c0604021e0d060212060d15020a26040228091e0501060908010f06030f11010504090f02030f0601020109 76
    0x13910ba400564040e0807080d1000c542c200075075400100351f5114040d12800110294035a8007060400920600704107803500400c030701c5401d110040003c0c2c1c5844048400594020441041d95040ca150141c20310407400c501d15842d12410b400440d50301c1e5080031901920000b12201203031182c00e0056818540120803214281e030b00709a00280142c1055060300242c1454084145c602141c840005040f47d08100c0c000d0715444e601103050002c090030300052076040741c002c4850758030340b9480d80c1d21002c0d03480040e0611140d1540204054010354028000701e403c0a181003050b6055840c941020145024110780c243d10500d40580010070411406115001320303040444031065450034202110040d0044030b148480d01c4070000c044c0d00300b017480743c803e40c0d0207494581e84011030f03d4540100c680c00d44680d928072680b010301e400e00802c0000c80c4d900011080690001e40301060345034240041c0c43c03a0142d030340003d131541d0402102990071103083c0d00940c03040c4552b0030301551030f440d0301b0f0049080f2521510001d049 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 550156250 1250 550155000 550155019
    0x1091508040c080102041d071803030f020c041a030105010e250905060a020604020a15090e131b06021501120b06060d0f0603050609010e0304060f090e010e060a0e06 72
    0x8451248422641c414000c201c094812a40d4501031030072a40300e988040d0200540100c81010040461040d0381c1000491410802006015a5241800520f803200030103000015031028408e500070b00c00500103040c020010805240400c0d602d210440149410f140b1035442d00c000421098030603807000340036502d0320004c2601c41542c0c504450000c0e4001901005000c114800003030b40d0399584005021410440c2c1c083d098038181403041c00700b0000c664010a810340c3c2581d2501c0c41156000c1c80840803100a01c50351246911400c00300481018595030140c41015850003440b00e803000010f0030011213103541d08844119141c1003003402c0d40442802021700c00d028103180746c80450800c0c03900c1604480002d0038940751515901d40c3c0f000312a680072aa0181075151281001448014802564405008002403100d600b1081c0c4507a02da1099001311802e00161070301c0700c58024400c841d19001303008058008001d9507142d52001101901c01c03241c181c0b041d40040c802281c0c1680e410403040c0529000350905a4 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 550157500 1250 550156250 550156289
    0x115081f09060f1b1103070305130b1911071511010b09090106170102090f09043305070f1b08161a090c0901170a170903010b0109 57
    0xa40c200120000240d128411040441c156128108000080a02c00180d07450303202021030369400d01040300c50600c03024132010030b4229004400c40f00410b606180c070554130190180c0364003039402550003900c07050b600400c400031080c140e04580e113002d2030f0980b00c03071b0030128641070081d903100d00c3e50141c14223881c1e1280c4110407450280b10f44042d42041c0034000309000c102e032004559011001c0b03c5494080c2c2d100e50741005210743e200c0340e000b0101002c6009515018501010a480c036640840442c050301070200013030103104610b00500c1300003100d5508040c030440b2125010082e40c0c0880403600100d45084003081403940940f001004514460700c40c0c081c99500c40d5004040b12400407410740f9091401c208101400140c8520003c80500ca4017041790329458611083d01081c1d0010554807041d8080b4842500603541d2025950448070307410207407507074450340d106102d09010f501200100340e8000c8010b0207105600c400c001d02410b00c0c0c01d4000b0459084c18100442c0c0c0350a4502c260100f2601c2c4140540 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 550158750 1250 550157500 550157533
    0x250504021c0507020102130e040803011502030c01020c0115050105190810031401230f1612050a0b3d170103050c27271509011508 57
    0x10111001c4089424101010310420068510441c1c189005035400140d0303126580c078284150001d0080300e50f4030007107464143e80d110114441030258007113100e19003c10614452080040788c0f2003c00217002991120f460551141c0030303100c40508242000c105450218595101b00f0035100704001c4c0050049000d403070020282c4800c100500701207118030010790080040b618049241445084034000001d880390b08078901283d040084043e4050b05119000b84588011066100750704040d4420040301807056202068030010307840225003c0e80d80c10035041190114180c1c1c06500c0c208030a07181441d10300f003202018051148280180c00010785440100e0074403881c07254280c2000d071100c1c02d1040c00302c2c0d4a60003000c4071000036070003162650700c607282464403810081188800e0241565080003544954810460100002042c2c031840c0b00084a24800c07204010103854a080241400d641c480e0400c0c05103400b81d5102256055120343c02c00c0440004207448284a01c00c0b142600e0290038480520075141 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 550160000 1250 550158750 550158757
    0xc0308040c1505120108070f0b0f1b0102030603060609060a1a0d0e03040924050d020a0323010b060403110d080c010c03091208040308060609130c080925050402 70
    0x584015141e440d020a4441c401d8144002e861410b80750507840d101800c02141c00701105800201850300803410400084860800303030f00540781c5040c5a551074000440030030940740181f0301500e4400707111406c200000e14041d802580100e02c1601551001c2c0d548506000480314290782043e00007281c480100106040020b002d014003841e10369861502d22001e80e100c003602d903000c0810030f42e42c00016040007420b40b50302c1440080280708200c45181d1203c25801061100c9030720800e8010044281e02400f10f64074440035001640c1d1005200c0001401c909440c442e549002205014540c40d103000c1d0901494100107136001c90b644000300c1508000a5018400c0c103000e0300d1001c40744820240546942c202081c00f0f0341f00ca202c800d590001c1c03069100d04207118501551102c0d442880800018000417a500c401c0c2154000e4003074a185984403c842c011030804840c0180c0c0c02d4000c0d1400614460103a030144905004842a9044030034910300c40600d04941c4225801c0000d89c444845010005410941c015 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 550161250 1250 550160000 550160003
    0x60108060d0c0506070308070906020c1531060f030203010f030204020922051006080403090e061206040803012606060d02010c120e100207060c110402190908010b060a0c030804 77
    0x10303040a5507440c08104140c02030704007113010800c51f0040088042c0d018910200522083c070041c10300f4400080819121601030340c405042d007138005144000c0350440d0102c1160901c05409080506800b2911003104686074042d18001a440010700304000d882402942d040c0d42e00c2421103c8120f28650802000f0b42c00314104640201e4401441d04581d2843e10940e21045203042c804600c034505854018014926600008103102c0710702d00740000309920855000c1030721021001d80328941c80d407000007040340860440002441c032504080004101003000030714100c0e04c005061140007a00b80c1401c400030001d200c460811580a100014907070b203484c070112a07085006041140728081292510108030701d50a9120000c0303020404200c169040090040384540d00b5440500b600a0601e500100040a0000e02074885040c507443d41b8110b513900e0f81100c08000400252562403640a00701820b800814401d50450394605402c1a2090070300c2400c0381c4500701030380ea0340d123002401ea0703400740c2e50032001410 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 550162500 1250 550161250 550161263
    0x11100e0a0f12080109021603030e070b0a090e01050102010608030a030b15280e0d0b040501020415080a060801060b0301351b03010605060f180418050f0105060108060d 73
    0x34610128a040409509140c007a0034440718041001501030200702041c1d0102c00c02a1042080900e1a514002e2058603030344d25140200e1500ca02e00b102c01e2512450390801004140c00160a04585030045030b031134105d59058005000e180e9035500168200d680c684a4000c180c5c00400441c820541300e9449100002c0d401001380008107550a04c0300301c0741d0480d099003503480001e0034000112001203440881110345038a04030a50b41001804a021b080f12004018650000300020804104003901510003504922042c0b45502d02d1048005044810503660b02003900d142c654045612a4180500420b4a2107860750a141d640380110b0744801004011448411004810b070030109168901c8080300036a80c142c0050100c8004400d182c442290718040f8607100382c5c5003220400c03450f102c040540c1e48409801543c246c55500b483c3c032256407800021401944a40352a60452901c840303400c9608486020b10102c81041e020001e07128200c5005841c86400b161030b02d00010041d00c3e100007c000203902c180b5 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 550163750 1250 550162500 550162513
    0x20a12020f0709060501020c0d080a050a0e04020a080103140105010308040635150303040e07030e0313080607080a1e020a0207050a140907020303040b150a2c060111100e 74
    0x1403105003403071142d42002883d035448141c10880d81d0390402503407071102c008942c0802c1c008040d0f034500c0240d101d04c88007181448008591401c20b5809020381c40000c0801a0095645110302a40141560342c00d020032038080000d101c3c00c0094000501c103a17030680ea84000300701d00d020b090407003da9024a42c02c09486c41621011405541c11112401441c003005071502c100004d805c14181c0d0660440725074072010300a920030f100400c4034a43d00d0582580003090b60800003026401c10308001d0451041d103c4002d05401c4407500001c1004000894900c40c0040d82e803110307071a894a040c108242e03031086074044107202800c28521461b040c5075009080c0c00002d40101d0b500b9a40d81c0000c0303402c50345164050f85183c036030820091b40f80e0914041d03207540300040380f000d54030314505940c1d502030090000d400c82c044c8545201842c50b03981c44205402001d04100c107100034401400c4590320030305d1244101c80c00c01c41010000410001c0d4000c0ca40b110620029070080c1144514011050740200151849880d5910440 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 550165000 1250 550163750 550163773
    0xf0717190c0e01031d0705040c030605060a0504090c030605010c020f0109080f03030a0f020a08130606030204020d05150f01020a02122805010b0315010312020a080a0906080108030a020a1202 83
    0x107100d2262a0009500e5241901d00c205002404503240c90b040224800c0c2e025040c81688100419880203441c400c5400160140c90070000320018400398204035000f88002915015058005c4042c0c400c452104106000f11001c8a1080301a55001c0c030541c0e010a0303a10a25000601c0c141c140e880c604901894204070850396010064a40303101d07040402440c2c1c200000340305500d0404c1c000c80040100880041d803070420080801003805000420711008060075410200400c50503800c014001c40d0000c00079900c0e000c1c0c1a42101c000e19054030101c000101c208a0103a86040c125040f205062058001e440740c21250b80900108014024602216014004018070340071524081090324040b209513071415030143d445c10a01b140c8183e0f054a01c00d0340120072100c400003c0459044c1901e9010380d005684180c0d050b81645004c110751801003072203a000c142c22040303503072040c0034030304654680d80c60f0441c60342c1c0d43d80c086440c1e00c144910f00380103801c4007035a103000c00d5007601042020f450a104460484004 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 550166250 1250 550165000 550165051
    0x1180e07020f0607030608101a0d080d050709060815060a03180f03080103020112060f1211030604060509010f060510030b010219123f1806140f0717 65
    0x45542101082e5140070500047c841002850b05940b42d10100708504004901031250600b028542c031482a0180d283e0481044401d4041d500c10058065040c400b905140201a003c0c0240303010303020024120100050300003142071400b608104020304214900308281d80200d0103080202103068042c00305201c101c3c0043e0702c10f502440c00ca03001766102c000305c2d415440014051846560495151030030b101050011a00d10982c010844200061310620501c1c06e203440c011402c600400300354140a04820031061121035000383d0f20402e5a14020000301005940202c1107c246000d41c40d041102d1b15400301031240a60f0000d440c0a00500459000c2c0940003c20003207440d4014044520420400d042c185103500208001b9100d90003000c082c0b4098440e0500100c00c0c03c4c4102000ca58801c900741804c007518680d0f0194501e80c5030702900c80444912820404041e1140d1641d0145403254100003411826004185d68060000f5507901805900302c00700344d1410040c040c150381a1100c0c5010341d5840b9464 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 550167500 1250 550166250 550166263
    0xf03020c030f0c010c110d0503060406080f0705030c01020f0606060c0c0a090b01030506040b0d02011d030a03020a05060c04061704050c130f0e0d09210c0b120601180e07020f 76
    0x85000240c0c0d40c007044980b1400e4500c4d00d20030b6802d06c05100d040800c0e021011915407803907021490a1612035545000050182c001540034907403501507840b1160814102041c82c1050700c0c0240c5c02c0303c2c4014400e6004a07958540c034410510180c2022003c60528940031004021202d814401c50790109000c0d00001c1d52411250305c0300d154a607581c03005140558050103020350000040f40c00b0044489020080b9900c0f1501c1c0744000d0421151485090340d083d00c425410143c00030142c1141c50241c0503207000b81d52980d00704015141c0d4401c1c49c1c00607522010040868094945954815081c44a1010810000d21002d4422252400740a002541070740b552912071148030119500414004800984403003100c01c10001102581c004030014038005402080ea0411180c5010b813640c1c091a142803504210100154004e024108200700090324800c440054100304500540120443c1c5035100107652340e1071030946070b2040c518041c100f0021220f80042c1181e00a1050060b03d00707058100c51164244003 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 550168750 1250 550167500 550167517
    0x9071e05060702120d0807031410090b0a1e03020114030105012a08120109050f15120705090c070c09020403050a06180218011a07050304030620070503180105190f03020c03 75
    0x290491308211f9a5070b81401068003d0a8403460304040c0d040c8242501d501076010f01440f8119504d4001510050703c0f1b10710f680000b001c42c03402001000c1d100d40191031204107107110a90024003a5441d10710401c0c0601c007281e04a0302c050315400906052500c00003410158015403490780c1810801400c086114500140580c245014440c041c03981407030382c7c6030300712000070f030008400d80829400c000702155002900600c1030b00460710902916240300045240c110345400094006207110140314806049501a01c551481202503000c0141c4640003a4224000c5200141c81030340004c0300d01e004609640d002903a003901034048801e041000c3d40200d5606086110407800070706804004220000e201411207601941802046140501b01c0d10f40607501d000300c2c0000341c1080e682d1012a0050783c1e040040d00c628450480c0415201c901c00c1c1402ca840340c000c600e103945118020a80e4003075035840394040782d07041d5420304a17012920300c90000448180000c81d224400341542002400c1c200d8504101604405 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 550170000 1250 550168750 550168757
    0x3150901152d0f0b0a12050f040605060307120605060102010c0804030e060f190c1b06090302040f06080f1b0d030818210d0c080f16020a080c0609071e05060702120d 72
    0x140d903101701c020550022034000e4811145080244a1000c1c402c240b52078100b82c06c1707400807809894100010b03040844950110038080b001c041c501040201603003000d441950300f40c00801c8031a1900700140d8a0240c207e41c004d0001e64500611146454204050080c810900d008241000103810301c1c1c22001408583c01008103003000c01e0401006a140400c6500c0ca40642d031a050132407038500c001d8451011400700a00c00c940716074941520441030360103034000f000c42104a8201070705484540d611030910710102c03140c0c802498060413090811741c0040a0f02036055982ca000c5564640303028845490147c1c029a1074025040700e08001481c8a0104010490f40010030355500c0255034428202c404004c04502484110402c01c0022210494001d0744941c0245018069406a40741203050030040080201518404540701000783d0000170390901c19060780d022034509a8858a5010b500445c0750800c1d222188841700078022030030400302401c482c034170142c0268501040780341c10134240700c0703100c60a2002 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 550171250 1250 550170000 550170007
    0x103030804150e0a02120304080d0507080d06030812072d0e212a0904050307020603040809030c01021f09050c04061e060f0e010f0e03150901152d0f0b 66
    0x5500c6c1031960301210040300402036142625020110340c48641001d501e00500c40c002ca1544103001d0104201c6420090254003004034580360301d01007500343c01035081c5d05616441c1310006541d050149001100440d80e0b014203550759900080d0094504100c0ca0b040000c0207800c03401407000d5200e43c0d8900c1410b1009000390310f040114a603400786410042001c0da113001400402ea80e03201c1c1d40b084050f440d5000d007504d080703a44e660307503080540c69032007030b500025000b0f0000001c00c4103002080001d0240c07035100710141c68001294900482e0b0352404281d031181c07921149659083c1c1e02c045035008181e41032192003a10554028440010b00300c1c2d1840d4803040d000d030040b101c0e01e010700c0d0941d07400801508103424030700391880c0b1441c0c0c02424103a0b409902c505011000d01e40e0f10703e60303000b101c00b11043d1200404803080005d0300c1a00040700c9105031581001c0c0c2d0309250000c2e24110241c00c0075400d90704d040408113180c0d2100550100b20403072110501180003003c00011440000059900c00a0b02e60740030225030703 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 550172500 1250 550171250 550171253
    0x60325020d0f0305060d022404060f0305070c021302031909060c0e0a080303010b0a0c050307052a060708211e01090c02030a0e0a090f0519020405090103030804150e0a 73
    0x40400d24403450308052130316080185513696450f20804c0c60350107890080c0e102c1704c422600c3c4070078200440d201140c44400f240004030254020034502c801207080c2d90a0103141c0b120320703041d104104030300d034000c0d440068810030800a0342c2907805141c2c042e01b2118050a40750059103020129442810240c40b000d03100c40c08240060b8002c8094019540c041d9440a980c51a015802d6164007060040e00020800058084411403082c0f00142d6460307040800c0d2a603a40040c58099039a00e180315081c607040c034a00c617002c00781c4182128081d24012014204624080950791a14441c0d400004003004035920a03200444685486122a11845514000d41005540f0743c1007903400c80030507803018501604040f14001d0381c0d68040181c1d13800ca01c8504001207002410400140c0d03007001034020040e0b040c900b03042c41c00c9000071034102030300889042c00c14481c0010031900c100c4c164401ca01030503420019100040000a100382081c50344140a007c0d5004140a401400e2044c0c503e44a10300d03c00ba805078101c43c0 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 550173750 1250 550172500 550172507
    0x908070b010503031e0723010219050f22091d0111070f0605060f041e0b03030703020c06130b0304060606020c01020d2a0b0c031605030403020705060325020d 69
    0x1d0240104500840c1002d11202119101005100e900c044050002c03d5400402841980d40ea40c1c0001d00d08818000c4845c00e40302600035000701c4030901e48600000800005580104101e4079200300304440c19141074040120b1801501070b502d603060381c1814601e80090f10140038821640c0149020000444400a0b081a103003075031407041d0307404c000c080208080d00c00190700b502c40c058003d0380144041110742e141c0b8005482003240e14002c58015061800d071120030701500581c0161080c920400300040d8070724105140d528028035800901507801501c00c41014680305001d04054100821800c030050b0315260101425001030310f0490792951214001e000751034040c003441e20030810030f2000380400702d03001d04000c08407114010020300c4541da0560602105601d03e08126100303410894000703284c01e0091800165510803502e19078484046404294094810400c8902070354140d80202030980c20602041080e90002d03195a04052a021084032907203004e013401600100981c000c0d14081001d0980034 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 550175000 1250 550173750 550173773
    0xc010509030a120c08130212100203071808060f180102070c0f0b0c0714060f0433020d030c09030f030306090b030325022107061805030a02010e13090807 67
    0x680e01034148100b185601d51710000d581d03402100c004850407034080c1800424107036400400d00700c07843d020305030805001000d20b0700114003a01060392000d00012002e81d0881031107106001d120800e4214901003802795079080100d5800809844880400322002c82c00c0f42d0032039116241c00c8410303422204c000c1029690340d00c0c0b23842c010b14144603034625000545100a071240320900904509000038080b503512a150308003980c58218281021903070700c6444111403c641c00000c560720b1640b0702d00812a0545828030802114096840d40040004444000080d805011003a03050382c10400aa90000f02042d280d100c8610701074002d88000400c241007591213402d4480c541c104c02d000364801c010004c070041040b046040080c544803441c00246100384005031280300d005a111280d0113200e50042e54051700890450100e0350580c07201d14a1014003403210740da2109900c075060349a08030302031410255002d091051450b14009010241a906d0508280c085030860581581e42101c045140030070000207040c80c = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 550176250 1250 550175000 550175027
    0xd060209122b0f17040302010618020d0e031201031e060f0e010e01020a0507060f0b030106080d030b0108060a0e10210201031514010c110d060912031407030e030c010509030a 76
    0xf4402c1616041c001400d4101c3d5245030041004000e400541414800c0d400f07140a4050030ba154592940602c0b0100040c4d0840d00030307103c0035881c18452403240c210000844500b103030116030000a507071868a400200e044150407804d0104c0214a04800049840c03080d0840c482020308002403607552082605e013102e24940e0f509015a20411182219940000c1a204403d0b4070a1002c102c40500e03142c044c02408100800c3e079019805c00a0115000901003031100c403d4606907010840311030030400450705030740300b61645600715800300703810300419402480c069482000e041440088603954000003509409594039080d0304081e11010600b15a89800341d000001c86240642a0301400d060100c0d901020307001525040c44901d81195040000280380c56680200081c803451000c3c0f02400c0c8070002c0d000e030810488071441040407500146001c2e00c140a031000900c0a290400e6681a10a40080507504ca02e4940d44c0700900016a95030300034014a4416101140030b16150800440d026054030780407401d = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 550177500 1250 550176250 550176257
    0x6080c010903230c060403141b090601081f060906090f0806060405070908060405030414100210021c09050a03020d050406080a0c0507050a030801150e0d060209122b 72
    0x40012450740314034503078414440142d104240d501c0b419070501d8140c01350009074000402142c000305202c40b5801c20078540d2908801c0d80e0035610148004010740700c2801c030040d8882c140740d01280e4554403a0341500d90240449840c3c0340b9040c814030a07011400c0007607100c10002421a20b0902030541e01c4090b42008000c98040c0c040c4081c140340c0c260752909001030006001d2039948002549a80c071841200008105040503941c0f60304007800c200b91a40e015008070b800c0030380c030000b0019503070070800720250300c610840d03001d064001d540380112800b0f5408400c4100079904d00d00071060f0046e50b54440c0d005054494402081d2a4002e4600603080c107031698101c0e03081c40301c184820007074140c20004842e0310021855001992140c1170009846a005411010306248602142c110405401800700c1e816503524400740e40017100c2032030301103030320075155954035030080140c40c0c0700c0c0d00049164000e0003088800804006c480c50104404030301c0c110300d08400c69100b0080c000302c4108402c200c040040300000c40e24 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 550178750 1250 550177500 550177517
    0x6020c0615010c08092808010c031b020604061e0c02070e090f19080712020109110306160c0204020f0a080f090a080a0f1e030c03050a0c140d1e06080c01 67
    0x101c1355507080c00b0780a062406013070a1104070144214190302038400000c540c403060561500c40203001d00a01c814988200440e00d40a940e00994030414600913603610503900030a100e54a84d500c1002a111030303000359502440364a01c102c0b10171020b002d110503c06042d402004110300e40000c070461403201402d0b407212900b100340c094584070302c0072405800050403200030380d09200d03032850442c0e02c5101e01d00000d45840703d00041b0300c5000c0c0c0c2c107400c40d8000038002c920380040d40c6c4442c0101030701d500e42038503a090a48440410101d40381d000d0415a00c256000410042c21304d480b0340a140700552100301b081c0000348204003009950000202640e030030284050040c404015181d42c1c1d03641a1050402d208140290075217851b08035842881c1400380100500d10302c0b48160717100c1c074003d00a0800ea140391004030341010009076240b003803441000d52615450f03a42030348168807110001001d070301064051804c0341d15680481400840c0d10151411050070f03010000300344d407a2150850500030101c00c40c604014180 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 550179856 1106 550178750 550178753
    0x7230a030608102706060e041109010803030601020703230a110a080102030907050d1b141e030c0103051003020a0e0f0108060103030f0c0f06020c0615010c 68
    0x2111000e0f880d051044082d9000a0801d08003810401044142090b15120f6101524055200054055118080100b081100300d030151030011a00d01d0804440c207250101600404640000d94214109000003d4681001340b2020300500803080d0080c3c0151210900c1da003010010f402242c116000c00c0c5080500c2400710700c2d401340f01e5070001c1c000203004141070080b80c1c450318114000d000c1d1036092100300700c01d1441d4040c0545a103d0b20100080c00c16103080c2002e805042c403441800c091030104c804010702c040814100400d800506028955a0780700091400062402401d001c01c2c1d5aa42c402e4107584c01c1081e80c40a075020400040004a00d02801803440c0a036400300242c110517070b2a221101d0740d0348800c4c8801070014094070306e045c002e01c0c0b042c40d640f2141440b90a840c11001c045440e02d00903a08030080e40785039508440300707103c8008006680c5d580003003801e08090010380303640e = true := by decide +kernel

theorem cover : BRFrame.Cov 550000000 550179856 := by
  have h0 := BRFrame.cov_init 550000000
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 550000000 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 550000000 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 550000000 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 550000000 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 550000000 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 550000000 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 550000000 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 550000000 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 550000000 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 550000000 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 550000000 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 550000000 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 550000000 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 550000000 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 550000000 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 550000000 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 550000000 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 550000000 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 550000000 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 550000000 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 550000000 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 550000000 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 550000000 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 550000000 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 550000000 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 550000000 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 550000000 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 550000000 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 550000000 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 550000000 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 550000000 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 550000000 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 550000000 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 550000000 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 550000000 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 550000000 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 550000000 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 550000000 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 550000000 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 550000000 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 550000000 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 550000000 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 550000000 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 550000000 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 550000000 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 550000000 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 550000000 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 550000000 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 550000000 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 550000000 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 550000000 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 550000000 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 550000000 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 550000000 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 550000000 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 550000000 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 550000000 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 550000000 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 550000000 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 550000000 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 550000000 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 550000000 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 550000000 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 550000000 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 550000000 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 550000000 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 550000000 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 550000000 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 550000000 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 550000000 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 550000000 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 550000000 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 550000000 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 550000000 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 550000000 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 550000000 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 550000000 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 550000000 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 550000000 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 550000000 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 550000000 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 550000000 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 550000000 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 550000000 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 550000000 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 550000000 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 550000000 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 550000000 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 550000000 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 550000000 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 550000000 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 550000000 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 550000000 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 550000000 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 550000000 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 550000000 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 550000000 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 550000000 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 550000000 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 550000000 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 550000000 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 550000000 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 550000000 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 550000000 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 550000000 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 550000000 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 550000000 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 550000000 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 550000000 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 550000000 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 550000000 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 550000000 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 550000000 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 550000000 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 550000000 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 550000000 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 550000000 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 550000000 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 550000000 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 550000000 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 550000000 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 550000000 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 550000000 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 550000000 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 550000000 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 550000000 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 550000000 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 550000000 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 550000000 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 550000000 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 550000000 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 550000000 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 550000000 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 550000000 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 550000000 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 550000000 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 550000000 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 550000000 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 550000000 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 550000000 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 550000000 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 550000000 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 550000000 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 550000000 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 550000000 ≤ n) (h2 : n < 550179856) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
