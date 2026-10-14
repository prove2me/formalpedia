-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_0075
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-13T17:42:04.233322+00:00
-- url     : https://prove2.me/submissions/bfafeb56-7852-438e-a14d-7b0f8f09530e

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 13309359 ≤ n < 13489215 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 13310609 1250 13309359 13309363
    0x30302060f04110d051906020c100c0905040c030e0a03050306010206071e08090307060e160911030112080412121710051002160308040302010f05030103030c060504150507020105090c03 81
    0x19030b00102000c1840081d02c5003031501ca04d00b040407501030f00a41340c9600350402c18130101003a0007400c441d15a004561981050301c1480041180d00d40d0400a02282d4183c01d8010f112803800e01460303101c0e960381c0b031a8044141c401c4c0c2c0040801000003040b40d04110550801410f5608210317041030040c0704050000e800a48240c05640604c1103010b2000d019580900094500030401000d038281444140a2200441c119001e00d82010b03605030080d00c40d1160403422146031a445070800c03c01d49041c003500c08c0711255001d0807203046410031441d00c0c0c3c005005280801d03403441140d101801d600d000c004000180543c0003042e140c0d0f200162a0024000d088800c3c51000c404e04407040c60800d045100704100c5030a1019114881030701c07510560743c810210501007901e18009820640e40e0910104040c021940c01400d540e1041000c1d0814604544c51550010481c0c42192002003207580c0764404203040040a0f844070303082c44080390042c00207250043e4020300074001114205400d11a001c1c4000c154100 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 13311859 1250 13310609 13310611
    0xa0e0f0304090c0c0510020f070b1503060106030603050309040b01030603080f0409060509010303020a020d0602091002060a05010f08031804090807080c0d080c09190f0f080606010201020406210b0910030302060f 92
    0xc00380103031215000e05041b0328025040f0880700c9840c21000c011610014000d51036040c424002568440d502040d0201814036260050300a24241440c01c03000b030010074400000d6600380c0c00219004154500100c0049001e41040e03840204000b10200e0703100010012680544240d80d8605000c111003036581c0e041044481b028400940560000d003145805402e00080d10b00c5114000d440140c541145a00030420440502c450803006800c542d0a20007242024040d00380107040201d40c860159080100b12602c9104254003043c0080d680b5500c000c041d110b5401004405810605060310342c100d505000602d5401540c0820007030044090000c00c49010301501c81c0a11080b0030581c0c181802c403030500050700b04040301100003404c1c100c4000b5003040ba00302c00502030700040d05003a807454a040c0c3e0700e915020340608481c0c10769005000c2884855070111303503031040c444d0f02382c0040c12a2440000140047c084c411009403c44648810070007010650940c40e800c0f81c1c4030b682210308641d1041090107280d14 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 13313109 1250 13311859 13311863
    0x305070201110901050310030b09070810020702030705130e0102030a020c0d020f060c0c1501120c060c08030406091104060f0f06020a0b040b10090f09020a080303070c06050a0e0f0304090c0c 83
    0x101840f0b49030325035114a01a651000a1924070f030140b5889032110314103035204071a0001250301100040c410324100340b000c0551040181c000307509009441e80003036250105405841d0152042c1c8180241a0380c441c1c008100799100d03000215030b6800c12a400320040c0d84540040030540c404c030020070010358030005801c400041d003000036010300d03118070400c81811750201e61000c0325841000c0d404104a07000f108014020840d103449426007030a90b16003030900402c246d10200600560000b00c42c0800c00010480f40d000f903001c0000200001c403483c09450000c94405420342181c50700501180341c90001d200304040c0e076500890130380d216642e200300f02d03546e641c0801c00800c403112035000300300040c3d0400e0249810900f030000b91007002d51200d160f00112843c4200c69285940c89081e840c1c15400c18183c805e0152826034065869854030b000d015021400c880c1c8000c02c001d5880700040c000d54415841080b585801100f941c0c004001e03034101e242e40c0c4c2c115000c0c0301c440611703100721102800e01400540e1400781d = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 13314359 1250 13313109 13313141
    0x6060302011e02060703180b101d0906010302040506121617031303080903070803070809040b06030402030607080403031112010305010b06070f030810030c09090515070914030312070206070305070201 87
    0x540c4044c001c03405071200d07c444644442c1d500d4403000014020640151040c9410220010310364540041c89a403c0040380900d4000c00d03003107007800101000820181d0540b40c0603140440c0c40d4460201081034404981d004e403109004110b0201c18107088410841c0449241c403001080300d0200d400200e4a03440b5030324083e0803001c0460410000151100003903d1085c1006050340d103066034400d085070035036229100864038914006001401490070303200d503c500c41e60a0700c4140c210714059011903a6104013410740000d04c450b0300700103410940b086d0080a50b401940075400e8540940702e07122014244c0c2804222195404c01642c0017842c2401400da40d5102d40200710408086500d45050b140844041d200035400c20460002001151008000b08010040400006405582d90409605203c4810090b47e00c10142c00c06014115500c8045001517824a4003404485151500000c0c82d40c420200040c0d14140d144041000c2e41d600401c5e014411095a28203008a580b041c600b24225130320240d84800d06 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 13315609 1250 13314359 13314361
    0xc0317090a0201030f02090a030f0206040801140108070602071a0706090c150306050d0f02061b0102071109060907050405130b040f0603050d02060103080304030305180f070602010c14031b070b0406060302011e0206 93
    0x1040c08060a40311050020b0542442d0a853b40f4400e401c1d01e20b0710a0304019078041200401490104010113402002c1074030147c0810350505a200302800d00c1d02d0918030000f0030220300a824410181d1000a4031644000051011607503480360f042d06130108042040420316004000480b8108590309401440c3e1041541480040940c02c11040781c0042640711080c000c43c40b07501440c048248002c10400e070054030110f00080d5080300304880e0500003050300380501d2440041c0041c954100d019182130b52421904000d455000c8610f0700000d140301c030741c196481814803804205256481e408030080d6030040d01034400602d111038059a461000303202c010312203041000050042446a07005e15000201c6201c0c83c1000c80542200c50301c1d0449a00045040e50031007207003000590b8091040001c07900903070410349903800041d014080c950000900c048803558410380d4030104581380750111030a0591201e074402007402c0c2410000000c0909000c201e002c0360200302c51b8080c100000c1c1e515034555010758000c18507 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 13316859 1250 13315609 13315613
    0x3090a032105041a070f020607050c10090b0f06010203040b090f010908030309060906070c0f0609020f060403060605030601050906030c01140903010c02010506090109020909070c0317090a0201030f02090a03 90
    0x4610418022281c0c480040c0c114200d1801160007031a000724020320802c0c95102d088404009200c201506250078081c4800001d0400c03600442c4c4241e0054140c00c110b41c954184481d0142405012128400014a401050307420811151202c130f000c2c0840f6000d83c03483e56200f100584ea03d1003540a003001c83c1805100c50a150f00d0000701c0d515227004180342c1004410b0ba078904551841c3c10030340701c5a503160080b02c00c21140140c100b1115502c01601d00d811607013100f2a865910540b01074040151040b5100c038160030554850041b4505c0e40d810141c00c0c140d440c0d6803400c165000348101d0282034840e001c0d480c00060b00d468062007007030048000a0152190307900d01d60041d540d005103090040c00c410028071010b0f01d6546c007803141f551420341680022801d440c01c00204440d4890507041845041d10500910440392101000c03680d100740d1500340059a14014107042c1c07480000c8129101c13031050304104100c5d89000102e101500c4900c00e0f203082c80320941c800120740c20f0380107884146810250400003040 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 13318109 1250 13316859 13316867
    0x5070b030c0301030b0402030106030b0405030702040b0103060b0403150605060a110d0201050f01050f03010b100507031103070f1716030e010305060d12051e07061d030a05030105040b01030b0307031101120203090a03 94
    0x171b00544000c00008003c1d9495880c104404001c40701681c00d5007001c1007010641c10180107444041ea42481e0170041729040c9008030300740d805180000350000b141c07039054403075040d401e074014030241000405071500e5840c24030004004090652580626000e07510400c0301150050103054010701d6402d00c0082c89a08010502c403250310011000740d81503482e1041e00317465454100c8003100c41d44040d41e402b03035901c0c040d081c00f0f040ca60b5108502c0c10550302c1000004c0118284c20041413a040d8800c900302c248040b0340c6020349032409a040004c0f581540b0700d54a4003055001004402c04283c05c0c0c8003844540d8801c01085500710f4126805800a0b112840c5091000c0c0300320002c02c49007400141c20308085140c80001007203900415401c540160b61107048501b03160003000c000e0045034000000b9031030200080002080d40c0010302c03a06004030344507007001100368082c1e0040e0858910240468140710754074240100c02003254000c103404500014114040d580440c02181c0c030071083c050003042181c402d50f400322 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 13319359 1250 13318109 13318111
    0x82202030114040602030901060803030405250803030a020304060b01051806031003080403050c03120703020a031803020310060f06020304080a02150708030703050a1103010501170601030e01140405070b030c0301030b 94
    0x9a16540e81c0d02d2440760040c0581045000354050100142ca91522030041d50840383d00742c0119280381d2040c0100710005400142c10051080b5103075a00e8286000d028602a000c24107412031b40309408088100610003c50383e0245205500a14080c0010b00748034006440501c1071551b000080104031130300c00707180d080400040d5005121034160b4001d0031390300d413503c1001d17030030980080b1295001100041501e241c1007000310390301040d911280c0e14203061039801139584c0c480c0000c01400e01004118003820448124402002035130060159682000382d542c11800506250080c0000309286003c049075891001060705d0503190144001c2c100060070b5020402c1030310340c0d143e50402540d0f04002000020700030314003540c010f00c19a01c01282500b0550564010703070b030001c40b800d85048000c0c0700420450703a0042c001c441e014040c004c0071406884000040f8040c01003d03036a00a19802c003020010a807802000c04c134840c0740964141d880c0740303031242c1c01d40107644000c1d50800140d00b410b00040c80428540301c806 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 13320609 1250 13319359 13319363
    0xc0d02011e0e100309060e0106060507060b06040e04050f060f07050706020d0b06160510150905061302041508060d0302031209070812091801080607050706060e091c0822 74
    0x100200b16078000541540f028164500025194840c900400007180102d002c0c41c15000000c1c440345052070300c0103041d8020180098882925070b090348a842d00c80310101c602500581d060484941f03131906100b82c0c6e03200c810310f90301020702c52000040c4444202035030140c0a000717a5030b201d41ca084000e81312503020390030201801750540d6a40c2c0300c010a603600e100040c580042200350880b001d950606045042012000150300a641003404110000b40c41500c0d10b0250f075102072001803a615840003240e188c8042c0b040804559100142c0419420341040b600c4003644c1085c1c3e01c1c818242e65880502035095005600100941c0c424004c511403d86104aa164824509000c8a8ac12569a00349070301e001e0034480c4a01c0324220001d03082c0050b051048800e0018600c001c0b2074034407075250070400340d540c2c40c0043c00720f03040090105e454800c004d10342d00494010302c1c0a09a41c400c9040120407a92a466400303400da41e9402d0404034403c070076004400d101c1c03040180e812034101301c03012915049180804d070742d41 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 13321859 1250 13320609 13320617
    0x705180114072402031510020c0a0f050a1703070609020616030909060504020703020a021905040f0501090b010807170c0c0d0306031b0305070308070206091201020a020c0d02011e 78
    0x49a2100c01000641062405843d82c0b0140420595040c0b040428040fa07034000c0030b0040080010081c1c1400030009407420a40e95144030301c0304860128140b58002950301e80c0080c00e105d0010b841c00c040001402640d500300c89a0403280d9440c001ca048c080d001c0c8800100b41d8006001e0480400e2099010404003030000e040c80f0b142201d0090020300c1038160541c02c9002c180700c032000780f000c058540f190360044c0800f60380852403c1090348000e5650005064004c3c41084825207101d40da100c0303003103040d008020160050044001540c000310103010240640c11106203468101142e40d032144440ca4007501050320b5440f4580700c2c0341c0d8080d2220078000e01490000d881004100c988003010030074014442a56500001c40c542503203003601200324001040400001e02c0b400500c003103640402c00400700e9a0120a05030b54140700d202044d0301e40034503c00c060340000c911100d001451410340007418118502d42c00d6404c200e034502c0400c44201080c41c0068009072103101c2c1201040903030030524460020a041c = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 13323109 1250 13321859 13321877
    0x80615040503120301091404211103070f0b070e0607120314010603090c080f0c04020c01060305010c0503010f0801140f060d050f0c01090b0a0509010c03090308030f040506070807051801 81
    0x7180c40c1240d0600d0381404090000010040030116200f030b0a0309003052070f0040c2d1f5509090300c80c0604c507072000358201c0340c2d00041001309041a000d034410060000406080e66103d03480d0342000301044c0c040f010161000f4400100042c8035501c118010118440010459401d000c00c585503110400d5000c0200f5090680d11801044c140c0d0070035100500829040c3e902041d1030f103062034003020800c5141e02603402c96000c950729154181010540d807903140d20682d00141c4544404100394050714461340080c0441d442c201c0c0c4000d00c07951100c0158141d03401030200120659490188500303e0300751182030f00c48000c1c0300010130b40d0031000c1002d05402c031800500d540b0300c450b0551901d50504010600032a0a1340c84001c06805c25600100803000810040d81c110742801a0288054198072400041038100312544640030101800707100c00b03d000d5500180c43c0c40e16450034072110780710f0070000e40b400d4609200300070008010314402d00c9502d1164070680d0311503040c41080700700744000e0381c4141040b9041c00240d030 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 13324359 1250 13323109 13323119
    0x902071b24121505130c08070c021309030e100207030c03030806190602060a0b0306101a040e01080601031103012003100803120708090a03020d0f0302190207030203010c050a08061504 80
    0x4020f26424003500310800d503000745403004100ca60302146070880c80301070030030b50760244090700072030320651240d40d604203810706000500c00a01d140708030380300c6020340510300f091042c00d266205413241b040c80360540344c0100b01110a6000d981da42001c0c4030003000e04004090910000740305a49070b58101d000940203010720350ba49030317007100422240c2d08a240144c1c007200420881e03c0e00341c0121054520250041c1190b800d08000708900c141107800b40440c40d1039020101201d1071501c404a8000b042805040303291940c541d40300301e441e03800a01c000e9840c08070391102c480c1c02d803070188200c1001c0d40582c005505e09031400d000c2ea84407900000c0208511070100900090081030600c01003100891102c030850151500c1c9a01504e44a0054450000b03a0300229581300003d0b00050150512a40c506020b200c1c0000001c04901034881c0d41c00c11600490048860f517051030b000280d95090724030840003401509010300702100e850094000c4000050801d00c04600e4500304603950742c0802c22840d5000307181940b10 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 13325609 1250 13324359 13324361
    0x1d0106051b1009060605010302040e010e06060f0a020a030e090919060e0f0106050a080309030a03030b040b1c03030c0e03030403020f0f0a0e1b180f0a050306010902071b2412 76
    0x1820200c07145880303d00710000c01c800c1d40b159202401d000d080840c1030a0511410b40401c00c014001c4030b02c0b00303d111004c078046940d000300342c881c80c0c2190514907035517544510b002915005400000c4000c20310390014000d8a00c0c11001c4e040c07056242c080180380c001131480300c07900c0d107904402055900940e11440c80110000500031040b0051400c0c00200d801440c0000f80001c071a0981c0c0515010f4009000c3c001d01540e001c284084140c0d0540340105480303090b500003030300810510319103d0380105101060500c50188445070944036001c1d0b00e04200103080c1210a4402c0400d486905a03d600f0401003400107281555580d52070b01c2c805010b040e0b818441b4400b02c1c078030128507040414100c2018007000f0741402d4980803c400010f000800b2802c141650380d0000407880c8071004948680151140c0791000d445011100d4000d001c018100c600e01d5940e40c02c1580254001401550107039171422400300401c5215080100312100312241c0748003098811044084116590040f508101d105020b1488030441 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 13326859 1250 13325609 13325623
    0xb120a0915200a0e0906040213050105030403030b040914010c0807020d0c050f1902030d090b030103080306040906110306040b0a0503070b030c0c071d0a0506010804060b120307050102131d0106051b 86
    0x496100c4d1031140d00c8440c1000092800244440e102d14010820102c40c650300c0f030140801c560003030030025103989030380c5020f030302614140c400203400918102085003272061072000d000c80003a5400c02041100303a1204112400102110aa00981c6c03100039008143c512031040141500d000f0700c2610310311010109540c1c00d00c40e420000080003200a1000c0066240920042180546606011030710300d1404050500d28001480041e0418101100041c55030b20349400278000264841c4e0100054030000c0303206080f03504240da41900035490016440140e041407a180d80c01d60740000c0c01007001c0380c5400b280001d66070000f0200350120b00280300c2c0440d032003c00c02646000d4a141c0840a030000504201d48900d001c0c0100482c1845040409010700c0342d0300b0040c100d400c15013100c0c01085491b2080046141042c040d02c281d0120b02c800a0003500740841913010b803071140c03c10b10354424442e41da1000000007004052107076050700c8080c001000b41500500003018005465140848005141441c803410600f03 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 13328109 1250 13326859 13326877
    0x91a010e0609040203011401110a0c050d0201050903030304050706110a0b0406020c07080706080105090708010e0601110f070b0301170106030206030a09170d0203091c0207050f0315010b120a091520 86
    0x8420004d41f1010340c0c00180140c0360308182c0005220006581d140c1010580e10383c4602800746402030341ca807040da48070f04200c80000388050212070380d074101071410a83c3c544051003684c00190440c00040145200400c410b400d04e43c0002c40d20200d03131280d0710344100a41c8204d0320611940700d030310030001e81f000c42440500c0081c4003a854140701c540c500b078280001e102005081804000311280140716424004c1210303074100c0300c286800504001c9094045203001440400259030344540c000c0042c40d50301410045050b02c11122443c0412000c5a06017400e9411602001350300031000d100050209003250301c03e0814601403100c100420b10a040703020090b030703c030001191005800000300f080010b400c00c0040711078064092459030f8400b039110020346555041c0030707403441f4501c4091600c8880c0d5080242140c02c81d0101120b240a50b07582a040c4241da0284404101e680d1902d400100305215038492070040a4001181145201149024030020218095008038618144003c5640c40a0403006072102c0d003 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 13329359 1250 13328109 13328129
    0x5130219030311060f070e1302040b0a0e090402240706050c030609070801031203020c03120a0903020616080f07030207050d0807090b03061020160f091a010e060904020301 75
    0x7801c0d4100240b00001e200c8400c02103a000a050243c2824400d20803944801c56142000581005400003010700c440840d840320862300100f0086070380e01051000380340c0807909441b802203c80b008814040e01420890300607500807100ca20100082ca21200d14560036042c9241c0140fa000305550345404072982901c12540011011080141e1403d0441d81d140e080080342c02c180f801c1c2d6256569030040302c12202d5000040640128085484440800c143e40c4000551174841e55a80742603e2054003c110240041d030061007407801095a40f003110080603401d0245580b1105595220f0054511300e0710007501003410580c0c2041800040b450600044000c0e50b02662207140c8ad06082000030080f001c90740081216017420414084039946844100c41440c0c1907003401145a0700e82118030400141c0004040146d00810140410344071f003080000040e075040c0b801e6003804030303203070300d0310808071456101da280610300c50320300c524125806076100440c82e0900920380e515146099002c101640c00c03c0e4441913000e = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 13330609 1250 13329359 13329409
    0x6030602180306040b0103110102030d06081606080115050a09080105100905100605090d05011b0503040501180201020c0f060906070c05040e0a020102060a05040812010605030601120c050a03051302 86
    0x8031180300305401c18040300301d0080c00c4504080e1101c003008001803000500744240d446a010083e40240203443c0c111000320010040103640c0e00c1010781351a405042c280c25000c0c10348000c600b10703020700d80c3d1a05071112441c3c5a01010f0b44010203407042d600040d401c60512640d100d00140400007405194031503511107040e410a00c0c5842c90340005d80c2c401810514030940900400e1041c6a4404103440200d28112010022203000b81401c40c01821030180d00ca8031400c80880c031038001d0303030080002d40c0294070520007041711a100031512651240620030003030040e005414101e407280341c40c000c01d51410710010b0282d4034119150340050990340c4910011114011161001c00c03403032416108a0751b440500002400c03035a1503690000b901c1d460b00400040d15240d480d00860107002c41c910503201c0d0b10840c81204409540c4881028005400071104a0b0008880040c84250700341207008102240b8401d446160425010000c1a0040c00700280101d40c0d40036401201c2c07016a030360912480030f04612030403100340 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 13331859 1250 13330609 13330627
    0x1205070507030e0301050105061204080f030f040b091902060c010b040e01090303050109330504021206040e070b180105070c0b120c07020607080906160507080d0c0b0105010305100906030602 83
    0x10f51844020880c1c4a6454480100003586403841140c448071211411003220307550b5071507d007400c0c0c0140a05c2d614211004420882420395180f14103010f17500460300d841ea5550352402c1107584084428408820010b0461007400600f4940c1c042c02031400c03070380c00102d410a0241c001c1011940d00c00034040c003589d1072302140b50515415106450141c0701d080410b012619011034108410001c0b901c4800c3c0342c030f00c0143c0d8078606149904514010b003100420a554520036103165070186c031810303540300344103510304038001c49656000500c42045940d0303903210380d007000e0400c0c0c3e10f0700803044160f000c00d0500c2810440d140002d103182c00301002502071502040d44950f0f29040366906a2030080007140d250504100300c80240c1c0c1c9100545101603070240900c5c1d40c84100a01045ca1030041c001e58284024001c82c41400708030011862405440e84182250003c9000ca041100c1daa1a070120140248180500620565109070419640005d260580700f62450350b07411140201d81181e0710a8a42946c00f28801c00 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 13333109 1250 13331859 13331867
    0x3010509030d0c03050c092119020a060c02010c02060a030902150403060605010903080904050606070609110405150609041808040303020115090e060a05061c05100b030307030207060c03120507050703 87
    0x1050f084503180c00c10951900c101c07161028424541100d02c1030704020030818410fa060b0301280aa26401070960b0b00800c8000510010700b032003590100c0c442c1c0100c03d004210540b0501d05140342c16016035845a14043c20b4080c440c5a0b408849107404140c0c07250403420142e121450029072500217091201e03030b9540345081003c100c90003038001e10304003e110102000405c56000c10f6800344078049800150648884000498078822980010669030501e490386090182c102207040f00040185e07010b0080c0d80c4d400d4072102c00e9980e10391081d5880003085c071982c152810039038084244c0018071400d44507100516180c114903a08664400c80c0180c0d1120ba40001510117160307448010240304009201c0c040f203c1c44e025841e2800103041612040e640c82c0010303103540c0c4020100503141000110300c1d4540c401030800a031601030341004242e0803802c0809032005800c0c000202c80c100750b0544e024240d82030a02c14215008401c1e000180c04004603401d1a000d10351091091602900860b180e103a5504024900a4 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 13334359 1250 13333109 13333121
    0x9010f0b010503040605070201060905090102091009060903060e1002030f041a060d110406090c0f090e010806010b0c0a0606060804050d0201050121020109030602030406090218090304050d0302010b03010509030d 92
    0x85495800c04880c0802070360030105903608560310180110b5a0354910700228010314969024445050a00d81032010905042d03005010b45032003610b003150300c4020070302e0644180905125080000e44066802c001141e0a58804641d0858400a07620a04034410401043c1e80042d203104400a000c04288800c00a40a06121016801442c400490700e0901c00103500302041d204041d0013442c8040d0515160b50f1154000702c05011415400c000c45e0014280040c81c458802c07a4800c0031492000011482ea146203a1441c101e450450042c0002d030308110810000380c006090000c0396120f07160034400065113a02400c0003034242c03903440100518060038a94074107422101700c041507914003001408080240e48e40c40b0315a52084106406c1c4c42814401222001100e5101402d441c1c404020b11003048125040b40c1c0032075000700c8000080c002a846010130030071050b101650305500400081007282808080c9100542c0680000201c0d441b5241c0802d0075900122034810f00380d0030005846960346214420700c = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 13335609 1250 13334359 13334381
    0x813030b0906070815040504020f090c0409060801050c07020607020a1802190807080610020a08030903090405010b04060906030c12020706050106032909090a050f060106020c09040302060403080603070b070b0901 92
    0x1341d80d45003002d01a10040600c0802c0983c050750b1584000b5080d51660034401c2402000034100d601c4600e044600718034550440c1c060001c846080c000f000481000c14003401340101e01c0118440d180c000e05a0800c2040d40c403000d400c070b8001d19124000110f580c252080700110282c240d40140c0d5807445e400342c110b041c244841d915801d100241c81404850fa43c001100b9a0001c42901c5201e0394500c0d074a0264039180b502c98004140d958000200001c460001c000b6091200c419503041c0442d9890700b801940c0ca0040340241c50001d641d81004100c880e00c00e03000003001410302c1c01c0010b200480024043e0030317640200000e89110382c8640040040507414450703900080041401b8071858200010a082c28030400140c0380e108154a60105070b40d10805d005402e0410303401022038080d10141d60505880d05002d126003005805002613501c3c4c1800c0041500b441280c3c164007410341d56942d030707605503440c0c40058207103601071040ca40d002c00d03d941e07460014510540104d044410b10700d404104c043c00d580400c800707 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 13336859 1250 13335609 13335617
    0x2030418140a0e0705190905060604030b0c03070302040f090b01090501030203060f120c030102040608070e041104060c05120c07030606091104170a02090412080a0e03040b070813030b090607 83
    0x3003035848401e8010305401201c03004010401201d07001806141c4021034000d6a80813801c1791200c805440c02807102812682480414031003982c07004100a070a0159101c0070f4406001400081c1e4446081c0c0b0045070302c02141e040044c2415100c0c02c200e842400303a500300b0000703180e0b1000c0c61070320340d0b800000a000038542441d0075031551810001050000303600c0c490650140d0f0203103d03249a40001884003442044001d4000c6490b10703603401c0c00901c0c01c5001e4a00c07a0200d0ba1505c9041c01c282024001d841c014404116410302d4030b80740490840d40b05801e80e40655031400703110303001c041041c1120010144504002d004080700c3e807d508250086489903440000a189071101c0c8145006d1820140d03411580907162200120b270200d141325013400301000000790b201c01084200020001ca610144c41915110759034510b07165903021448007100c10055a03081581c2c0180401c00141c1c140780300406015214500e41410b01101050f43d50308c048482d00100e4070003004101b0054500c0041110580c05242450 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 13338109 1250 13336859 13336871
    0x21c020f0a031710050a0b07150213060908030c0319110d020706110f06160507060501090504060b060702030a0b1305010501090b12060c0301050d0611160201020f0c06040e041406040302030418 84
    0xb0009481007100d01c100c00d154800441c1c3c4002744050001420031550496030107540e242c044030062030034468140241808102c154070003064400d000400e545401c030654008625140115490074420480f803202e0504100030030840c80c44a00040c00014051400d03a001004400d01f015406040c80014a49241099000720300d11aa003241c001442508490311a0040b4110301407908115120b10400c02c1c050048c605100c00050020702a03403002d88a280602400c008602c81e410410400b4031400e02c1c0a50706501c4940c001010a001c0048290005040c820403481c000d15640c0380390a580007640204a0303142e440302545060700300034111480c22414400034080c0e920300820071015900060103528044c1000030f020a080100c0b560000040483d02d00d0021b4448a400701d01601442c3c403818200c3c01030040400d040b03c030342c800064201002c100180b149041500f440d035026070248004000f51415114041d520003104070610401740520700030341c082c0d65038500341600030800380c410203031500005207000 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 13339359 1250 13338109 13338119
    0x33040c14120a06030f03020a02030d0302190e041506030b090105010201050405100b03100608010b12030301050102070612020d05070203030103050111030105010c020f0103060f14120706021c020f0a031710 89
    0x40200d49070308641c0307400041c298a40c07000c01ca0003850070750030080407a1107020090091640000315185c2d40d610880448440d800c007a10110103a00890000346035842940010301481d81c000c4401ca501c104003e0800200c1070710344441c100c00d40c050703036001a0109a5411642400c1d0a1400d602805044280000c0c0458200759441a54411000011600e83d6580d00703811440380e981408031180440c50404203201250710341c0c03000788c004c1c00c1e003160b0075109007a0041400f80484010040d241241c50580152092901d42841500c1c0042c1000c00020340340e41c00c21081e01400c0081c481c240c06803689600442d200d42c150b1610600b1075010301c00d0040401c0c010303c01009140c0e030040003c4a000e86c1aa8458866266940103a0107084982c202003c0d075201070700c020401d894444039000e0750803000c4600c82c401d905015100d5850b20300c240a008016004603c200c0f0101d4009003010710b85007201e01c103c801e04182200c0441c00d1000480080300010140d05d803407903007019050b40242d0410300c29101e1003002413502e = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 13340609 1250 13339359 13339397
    0x5010510020c09070c05060406020306030f0a081903150e010512010504020f060c0f012a030902060706111209150a0b030705040c091e030209011d01050933040c 70
    0x10b030881a00c01c0c0e080100060580340314001a150050784041280e5a500345850a040690070459800d0301a10880540040d51540062080015500000410b280c0003400e00200c1041101d400c44406040d01ca09420b2400b000d40300d411801480744071046412035041204101c902004208a040030b42c0c106410300000d84e450804079aa45202203400310f81c0d40d2181425603040a01013070742c0c5007440d460144596480300b007490070580c08848070840c145801001c0c400c2541110700c0e12401940145060005200003103940c2e00c400f1244868440d501d0034048880300302910614121703a00111500714014126819001c0f0716103540041b04050240300345098400441c1e03855a0317602c612440b9688030080300030008d0154910300050081000c403444c40c6010f50928003d10300075440b040380101d070280c00000380701c001c82ea010725100103113043c804141e03481d02080201c145005055079110b4040415020f001c40d885844400d03402500702c0c01010034412030001c02c801c89464501070400e105150320b400002030301c1 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 13341859 1250 13340609 13340623
    0x10801050d0b0114131409060a060305070e06031218040b0d080a0e1c0b0405060f01050a0603020903030d06030b09010b01030e0c0607060b030303040305030a0e0106120308130804090b040501051002 86
    0x2401c06a21201413100c00080e0005008014500c1c00038502004820301c82c48010800d4482c0484104991080c0c5510044504480c224800a0055081804184105070606c0600d54011000504544e1415200081884d065203ca400300811820754100306040342807500488036406011154501c0b40900c0d030f21040810b2080144c070008000601d0101c540c0f699032440030701301030003c0b410703541c1380c00215180c1403901c0682542c054846115030000607100c18840c010b030745d0580da4090405c101107898048164043d402c002010b5038940002e000b001c00140f000c0c480c02c0005d50154003010000e00301300323013110700319816540918101401c05a0090500c0d42c0014417000c1c8100556259641c0e144509110000300400d0240c1c6605000000a010615a006000e94010400b40e0800c01884040b502080d00302e4400d403003103da00c2401c0400c40300119028003241c07640582d20f209010000802c40c0d40321340e165805508804645a6510440400c0341441d01c01e842c0075020503280e0b800e1807203c494000e540c50784 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 13343109 1250 13341859 13341869
    0xc060c0f070602120403120c050601081e0601060f050309070320040c0c020108010513060308030c120906011401050703020f010c02030d0c0e150c120a030b010e090610050a020307050f0303010302010801050d0b01 92
    0xf41e418402844148600081d0034a039402c2000c1e9401075858100c02a2601113448101504502c9000010337050380011600904844540d2200c40784a00c1100e0f041d02c0e40e030401801240300e030080200001c0070030030030108000800300980b141060084150100012520840c80c2002005085550140140d0704401e20364190f51044405100900f000e48400024104a400c01440c0003004400d0185480003000541001d10b030503960410541da55524840e80e03001c091080da40c00f201d00711003034065540500000d04905000f031040c1c0d644032100d0040b081c05d4884451441e00141d100090307084610b18544203200b841d0b4a1840c010303040c030103080001440090401d00000300d5510004064005942c200940d42c401c1002103500c945807460400090010089200e4241c0880c0c024000c50000c0d10f040111544947d00050180f0842070310390b00100c44980040320208194442048000b001c20000c0240200a8889800450b0350f51b0451000600c40316041c0d002500503048000d900001415180d480760560b2 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 13344359 1250 13343109 13343123
    0x20a0807050d0e030f0909010803070f02060d0902040e0d030609020a050d0c0507020901030c03110604050102030a082a0d1401080304090c05040314061608060102100504050c060c0f070602120403 85
    0x4442c40703201c0c0024038809883c80078a100004002806519031809801c01d42c608861183c542d17aa5031751001d4a0f4400c0080c020102d61400f503841005151260140101802c01a0001204100c0b540401e0440d07d009103049940e43c881090f04020f10f6150242201511203800305504005800c040a003181c012010540c9000c0c0d111800070265501c07038001d1780d010b1a0001c20030011035959080c030344844c40e018001500c2114030f848a540c01400c100d000c950440c0d4043c4d0055140c04540340707044a050001401d03072207180c04031070258100c00f0341c000450030185125500555440c0b44c01d2030300300d048078800d541c00c5d6810798408004026a01004c030a0f5001c40721241004a11803000000031546442140c0005005c00441c619010788a80c001444911902d51a6188400c0e440c0804050761200b078122942c42c0164021aa09040c80542c4e0300869040f81c030820807141c502041d400015850b07046460414426030242d000503115107410401072004000320300251030100c80001203010746118034003001d4100 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 13345609 1250 13344359 13344367
    0x11040609030b0414011d01060b070c060309020a0510030e01180807030507050102041e0e06031209040216050609031215090109050601020a02120708010f020c19020d0506040302060708010801020a080705 88
    0x31242c2a408000066400c800800c4801804807041c4180000c40c06c484043d50700e840c4002c101c040e041c0003120300a40d0800f00034a4140d14001003100036040100089030040c1842e000002c16440da1b1030040415019904c0100d28900c404410034211a0041420001e55202061000105942c40704544a954240c078010b6550249410300714003a2159a100c451003140342e024200614842c00003080030340b810860502c0ea19266042010f50f19115001d03541c04c00082000b0034540ea01c0c20354014241c9a500c0e9040314034401e010b8556a04042e011521b0102c0740e000000c40f0309449001000d026031103424200d00a8041c0c600300045051440140075255106540700041407150f030080008a54445e801030481c00c500c0c640000894640c101c5102d10100e540c01c2883d5026203a030035009549041c0440c10040c031403003150240440c0f42459104040c2c1e045003c10307a111011407000e000207803003240207400a240324149032078018a0840168000f00c000d174414401c1146469210220303541041d010719146840b = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 13346859 1250 13345609 13345613
    0x8070b400b070203220302090703020910030e15010f03060501050303040e0a0f061e06020f010b1507020109051804030f050307050901031509023103020306040b0406090c09020c0111040609030b04 85
    0x2452080e02000d100050305ca968494202d0401000c410030349200303580700c030402e03210307141c0613016401752116560b4482482000034009521070b501042c03c1091040c120798019045081c01c00c409102030b0031040800300494010300900c941401401e00400c1d054004510f06441c0100852202402400c00c1050a0b02e0b000e001c0d924800344d030401000303031034100b00944031985201100160804640300310005405200038410781e854062203140718012015010ba040c0c405086649482d507803142008906114034218045a03a40f200704c444894498407400624082c141810003815104e0800301c414100041042006411a031040a5522554080c01e021402c071140000d90905d0b6802504103848592020800740b5094075064551120f4420109030059031703038a0344078508061411800065019400400400c1c000351101084541c086d004e503200042c114000c2e0b480600307913055540082c1a8640105440c408041c0a00c62680720702d4505910620306031070450040c14000c414440500498080e20000701 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 13348109 1250 13346859 13346863
    0x609060204051005130602060c16050f03070807150b010e04020a09030b07020102070201030b03121e07050d08040201030b04090b0a02070204021303050a1505090309060708070b400b0702 81
    0x5080003c0000e4001469040c00819680180c0010b200525036610700207403450010448038083c01204580c82c0c80c0c50003014941d84021040c40c03003200c1c0c40c400c0343c08205420b401072024281444c402c0303041996540b1030741000324005030143c40c240362680c0b5201414040d6030b0041c0c2103088002041da80582ca942d407102040c0d440d0200d542c0003501c000611420440d05940c107500820910740b003601e00b00f04001c0241d0506686101c010540f14200100b0886016143c46d1402e0000700003440c08000ca1400300b03540d0300d181c24000760a20450205001c10b0a120466801d03024854031410156801c1104003400c1d01d42e2142840054501d0010701c0c0c0c0001d4200c02c2d511180c0440f01c02214264400403c0d65036803501c256251805001943c2007007003004010000040c5028650096042c10021030400401c4800c100469011a0044460400030818000001e480b8034019109481565203440481201d51603402888141501030201c0d007045994280740d003a4181c07070780c101c1d16005020102c9559540501740c1c = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 13349359 1250 13348109 13348117
    0x31e100b0f1020010204030809060c070f03060204030314030709060305060a030221060708130b131a0105040501060509091626070e010c02010c02010e0303190201240303050706090602 80
    0x3070b4004250b0040c0c51205600310b07040c48500422489007140860f80d56003014200d014502005014039000c2000341e42500e0207101404110742814240c3d19070341e80c0d90603600c10111143d0b208079031142e0041002c00602d83c0201360b030742e841c40d81e0069aa180d880d00010007055466a40100c0d010b2680c0c031030100d649502e50f4600d45000d194040d0a00b10846034203140110741d9008520121600e01c91000001c0d2003c1c400c04105006881c0351014040318942651420a00c6100070f0501d4110740c018100440814549100444118804030380c400786541000f081c0b0058444c160040414401c04101d00081600d031030143c0340e0701c0012080f0410304215050001c035041110f8202c501e68141641e0102200b00143d52076050044840e522070303090703507100100159003c43c0711a001a0200364203000900240d40100a202c404141c002c080e01d2030500144024040c10383c0902c0c1d03000050b903403070301150b85c0ca0071b1079205603200d80c040c0b4032440720451540c0e50040140c45410001010561076210750820000960155 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 13350609 1250 13349359 13349389
    0x100f020903030d1a0607020a03120203070209040605060f0105130308030a090501020c0304060e0418060203040212060709050f031203010b0a03090204020d14060405010503070501030c02070515040302031e100b 91
    0x540d50724002e40032600f01a0a11011040ca24120744015030f04038136049044603081e941c0601506004c030f207152101c1034600d50009140742540400c200c6030780141d86514801c0e128610a20700084c02e810580148007000c0200321800781403010402c081a1116241d540b218221b81e0703c004c505136241d403403603103042c060715010900420a42c0007184138644041b002c400303003064542d69a00d03440b0009100c41000b055450b420141c42c0d94103070003410318021583c560001c5500c180058040810500c50200441c94080300303c81c1c14001a00b0178a0038421440d260001c0c41c02124200c0003408841201204a0518031062064262001000540d5400c5900070f411001995400074004c5440710800340c0c000000d0401e40c201003207030b100710500140701c903d4144581c0b41a1680907000303002d028100300040d0300030404403020f041944580c410004281e9111040c125030807542c849419181e501e14418581ba114220403600703008a05040352044004001940c41d10310007170280d010804046a102103a041800c844070 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 13351859 1250 13350609 13350613
    0x1020c060708030103170301060507120c0c03050115080c062a010501140405010909051b040204050406080a0629010807050d15080c0d05100218030a05010c0f03050108100f020903 78
    0x5600240b1150b8000f0314100c07801911003c0c0407004810350303618284000d008480204800f03000001c0030881e51110005445c01c04d042000e00d0f88242e81300e07103030803845a03802210707643e4485a8004003c081050804002c10210000746840e407600000203403c0d025590246009402c3d895003e10150b1440b00ca030001821000c0c001c100303558541c1d03055406081c58208950090b42000000556001c09101e1144c2c85504080074040650089080076041100710031034039030141d02440041641d540b0b500c503110052507004010f002e545c91526140c0243c1da4006504000c00700d009015201c07410118480c8242c5900034070745469243d441480c1030742c2d940620496600414036000c1180d0000c0c4040c4400c406449501c000c85074141d9034142006041040e04400130301e00d802128a4840f081d0103500580032016409000e00d80003070b02c040100c0e02d08841502c089d0388aa440d0400303a00d056030843c403016503802c1c2502d0305020350340c10301280315070741d50b050712a11078210380d11640c028004e0150f605440c07102c030000f02 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 13353109 1250 13351859 13351867
    0x3040302010c02010b010e030d030b0f1008061318030c05030d0f090b010504110a0c02030703020928050402010504051e0a080304030203070803120105060d0f02030403030e10050f060f01020c06 84
    0x28020700030900261003001640c0303003000f02611076000e41d518815801000703000b05113050341c4007011009401d060301d1141d041480045006026901e00b440620400010303500c0c54250303c0d0100400c14107180c00b88041c1c03055031a0404000140c01c0306030040a81c03a42600703012120120758545580f441c860f404002c0007003860807204850100c0b03907030095031407640188410310f030303990b03c80081004079142c24504001614080181d80d070000e010300c24050f0054002030070ba6100e681e9070303000f08222050072510b40c41c00c8421440e042c181c030300c1c00800708207078071aa14908005514003a80042c001740300324000c4d148202d40981c0d03280e00e1000e035118000e02c01c0c10098083c6100c0c951342d1307404a070b503600240001c0f03101e0f005820b0b01090360380380041600d07075030765902100245992a1105010b0241c0c4021341841d0003a88a952a40d0f0298090005500480c4256000a0102242e00200c0e0809003500d442c24441c5041c042442006480486166000360b01252620301c21404400140d180a02d50754400b03800001c08a = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 13354359 1250 13353109 13353113
    0x14040302061c0c03050601081501090509100e070309080d090f050d0206090d0302090f090417040807140603090706030e01090b011806120308010b03070504260705060a0912050705060304 81
    0x2c0e00c1d0b180604101c248074542002c0030603419200100d4409000496080029640641d03d5501c5580c61006050110340240c540001c101541d800b15401300b4501d004560811801108482056000c8d0003442d040045004070f503a65040ca20a141d552030415441d2260502401501c030314808c4030f41e82c007000325510100d4160019407981421642031646028001078100002d00034001c0f01c030529002031a40000302484002c01c03d0f4444050004c2d81d2030081e1548600244026500070804ad000a00040620605d0203001001200c1d03254038050081c0c0060050114421002841c1425600e80c0e00740030454200d108419401040d01d101c002c0d0500e04a4400080c50485554201c503812100c10780500c1600d0b11100e500c0d0444910b0640280000c2c40480100042501e40300070303541013401071500300c0c50180c0d10895a105010301075200c4010655140350000055010031090f00249001d66600307080006040300903281040907c2011212040305001104004c03050082030040e00e80200321a40780d08186c = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 13355609 1250 13354359 13354387
    0x4170105010302130605090a110702060d090b0a06080d030c02030d0207060212130305032e06050903010509060106020a020609123f03070302130b040803120f010305030a1404030206 79
    0x82c4002c1e40105142454407802c44e00c0c0e4000c2c5010399034081e1180782c0da610303070001101c0201a0b042d40c5444000061000c03c00580d03482c40101b8803841c90010200d130841460910391180e01000d8040303001186407a4080142100c007188a46d88403440f4107000800090b1007500740c0c21445507500a54540d40300144141c00c005607607018245007201d00c500f00c1610317a9000030700807840d80032203000b0700414020301c002002100031050701107088000e03050b217441e0030190bd55090641030507a0010070200e0004038124086050034030440d98042d0b20360b001003826515096029486940364480a07028000c0024102110703228070060b2100c41c0c03a02c8044801d02104013240165852480c0440318001055004101c030075100c11654a000c110241113541c99622240307000e400940c41600d5003400040e034040001380c812210301c040c0008204c0c0c1805143e9072400e4440c0510340010062882c10b040c4002d10060020550003c00c1c1c6401c201c1c00d050480b0240d0301002141403c0c090750b0b1000398000000940ca086032210 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 13356859 1250 13355609 13355611
    0xd03060f0803090303041e0902070605010303020c030705010801060f020a0b0c0a02100501050f01050304050c040f020306100201090b0c03090f070609060e01020606090411040209060d0903090f0803071704170105 92
    0x40540c44008240c507200095100c0c0b00710f540c0103502d988244020701c61402c44003c00844041000804912070b41d603038009001f80d070407180d0180c6140782c4e0340c070040080c50f805100610a0040450140c5005420407001a100311818010002000030030305826148038001c1200760032164000c040c1545034a011007000b040c0da81311600240050085d4050f442c1070b030b541c901919044e914010f054008603806d84004550315040100f00340c5041c403d0803003200d05910307140324980002c6002d43e00075a991410b1414000c025440c00050411a03146ca07441e58081013104103110340080940c4105507980e1a41d1300302e640f9103240700c4480f12941c000c003980011819003060350f00003151095200c43c41c0886500005a032504002c441c22a0442042c0c170004002600310700390210003c4c00144010708181024021801680010345611481d0790b403108070b4020316400c60710890040c1481104144014104101107031203000301a00145590303a540780040e0140ea486094901a288082011000ca540d41420901900e4 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 13358109 1250 13356859 13356869
    0x910023105150a0206070c030c2a05060703051602010201060305071502010507110c010c0501020c0a060501030c0e160e0d02060a02030714030408030f0706020906160b01080a020a03020d140d0306 85
    0x9108125594115642d030150b94514907690068101540c450200380c40010b401c107000c80400074825803080004102e13284141d880c04880055084407a0019002054900c035a00020b00c43c001c00d000910010342d010b0f00320f501004c1207001c00c03c440c0400f440140d014082d2900b006016020700c0e000494915000c45288807030046a074000d00c01ca072101c55050702c2c0722600400c0e502040d0400008001c0301d50183e0080340055201c2c0c3c000518051440855504004c086034044500035102e10041080c0100344804602130200000e5140042c107003114940480c10741900b525061244e843c0027681c80303070742c1d14540b402c2140d000790902d550366036039010081d202c0c0d0080f141250045a0000105101e8100009071400c1d5103034000118500b85484400707a400d50415a400c42c1c4040d02000022466110f03100036100944a03c40400c05040b003a181100f64041c0c16003142010b5071001c003101000d40c1d03c4c0c1d409081160340684506c4c80005050405000130b8240c4032100200e03105208100700b40f154941d20540841e0 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 13359359 1250 13358109 13358119
    0x9021002060f130b151302030c04080f1501030312020403020301050103060b03060a05060f01140d06030302011b030209011e020c03060c0a020706021207060c0504090e060a140910023105 81
    0x40d0711003150409503606100044c10806100c00058003c1c000d8010044200d2001440d01503404061607503003050f64030844110540309800303e0200718a41d400c00203c0c60381001240604be820f02820340015440781c0500c000390030442c0c0c512a07940d510300540c3c1260003540d000f50086c0300355070716030600001802001c44a140603108007000950041082d01c610350040600526648001110a004540020016034082d4060804200c06400b00b045449600b0083d48641c00114054000070042c1103040003106000040c14010486080a682d00242281942003107440d061010100200100e103000c40c030440300b0307405100c0c00d0203202c4c2000c2c954014007482d900d10380c00c4030709980d1a078804a0b109d400141d9403401042c018441c070000238081d80c2104a0ba03c0c2d081c030304a410640d442c0704513405c1d40d0509034940580c2e0054400c1c40030301030341c501902c001035031030310440146410000c500d5656206001050620143d010900c0601c9000401c2598920850070101d080008024080281900414803a6130b00c51 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 13360609 1250 13359359 13359361
    0x5031306110c011709011401030f02040608070b0a05070309050d0308040c0b0a120b0301090b0112030e06030106050a0309021306081c030504031b03020c0d03050909060f0a120609021002060f 83
    0x249400518982405010303596114080e90800143c000a90050314030b14655490b94107d90121040b100c101d13008502800c0400c804c0e80141c01070000701ca005400011080e00b1550050154002603400c0b141e2807900c0340360056568071242400c46074181581c0000c3c0c4e00404556842050541c0103048074007660207410100d03070141d81c6c0c55410b0494896001190041002070010310002c910703980c800014074801070004551940c0641e20040c13048000d03080281c00c07441c1c40c3c080c0c0040c1a8007a00c5100c0008003502c4040c91541858000741c4203000d10100c440400d40c075002a00c00710345958040c04c505030311858060101d25220708485855910b0b240c1c03c0008150b1f0100c5010000d03210f40121030080340c02d80c80c0c042d101500080c0c04852900d83e5042502503204118988005031204d00801310410300030760361a44c50781b070b0010401141c180041c1c01540301d08440c003070020322561019020380458007500c01c0c0c5c018241071890802c0180c645c0e114080d622201c040380746112503030013040143c4a0704099030140d0039 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 13361859 1250 13360609 13360637
    0xb0f0d0608030a09091e180204021b01060f030201080406020315090c0913020406050304080a09031203020a170103021f020705100c050d0305130b040602070606080705030f060c0307031805031306 85
    0x84404c560012107090383c0e21341c0c05041c6d0141e2984001d0203e014000036090300b140640108040c5da000c01400c10000030511b40f50151100e00707201e1000601700107400714041d1071130358000a22401000c0c0000c1c143c0f41c0c0c00000709107040821100341d40046070241006909180800220b8080c0d00150180c9000309070040700d5012440d15482210103569040c0c403075504546444c3c441c205940c000d0351119040c040c241a01002040303c920010021441d941c2e009a81c610103100028402c02e005556030b0710b1082400e00500050307a400740c54251203442c2945100415006100c12440d0200a0340056080b8801c08900802c07142d001c101e1488903405201140d00d41003c4203004c804441e4110780487c0f00010500042000441602d13115411600410025040039219101c200461380c06502002842e80040d40030042c606050005162200c2c165015091510703000720017441c5407200600500800d9a00c01100c041c002040b103071a0b4071145c104007140e8440e00c0d4540d50b1032011205000c2d01011800004000003 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 13363109 1250 13361859 13361861
    0x1030f0501080601170304090906061a070f020112140103051b030607020304030303050604020714060a051602070e0601050408060903030604060b0a050901080a0609020c150601050306010206010b0f0d0608030a0909 93
    0x1040b114a0b1009084503840c1640e100d0840c1c4006000111a000811001030440e01500400c000c1a000304000944c09140c41c6188590070004d4981550003141400703008089500403040c0301c6001c1e020f0812030180c4440d01c08404c014000e14200070000131f8404008414884006245041c01d949181c1e0244040c030752070101541c07541c0460f50303007005074010071013031002034031903040641c0015010300051300b002c0f07050781c620903032140ca074110040325440701c81004240981405602d41028410340b009005183d0038500940340c0c0c48a0003800b41050811011804070b9100b2000c4800812035a000e40e4a41d05040907a152647e0068900074032171030802d071020804805081c101d0f40014400d84610349490500b60040d520001e00400c0c0e107450305d54034680020300103024002042da814410300a070080c000e003800c1120102c070014154904010050040141d035903000034080d415180e10242c542e13280c14440701d10b8005e91007000c1c0c00d074010b58140302002032113000010140244090303580320200703015100c2902d10 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 13364359 1250 13363109 13363111
    0x1b060806060a0c03030204050909010e060601140403020d020f191401020319030b0f060a02010603020414060306010506030c0702060a0306180504110103020a03090203010c09031b0b070201030c0203090a03030203040501030f05 98
    0x140c0c8424100b00c80b455a601642c0000d2200b80702e410098142603480300050710f892400c50700801c0c5d59441e40381115210784144041ea91007042400c0014052859034204041070044d4000280600b0760040c1e45015503651008000f40d01200420541c18403a80c207444558200e05845080005540d5103c1c0c011a50b001000ba40c05250282286d003200c0071403210101d01609940072280d41140d20801d81d641113071a400014411549603400210307800d0314620520040751420003c40303840c446070600b4090182e402140c0e05046a034110b45898807a101d800d0207503982d10440100030f501100024200c000c458140e0090002c445072140481ca541030742c01d0404054410844d4024808202441076404a6000b98040c1c102a035440c035000440e8403490340030070708641392201c041c004140c080c00c0400030040000303408452000300d100d00c00c20003032909480c00d10602541c40020305050319015841c13007507813080058440103007000b000586c01e15540d0070080d48030b500034059140044c1c18441821030b1585c107400340c1 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 13365609 1250 13364359 13364371
    0x200c070b0715020304020f0a030b0123150a052107110c01020d110c040203010b120c0703050f0a03090204021b060901020703020a020904020303040314010b100c020f0103050a0e01091b0608 82
    0x12402d00048204644002e500c010801c030703841400350b0340c46462500c800840201652127544207101ea941451050350040c0b82a01e41c54010851000c21035525498003e02814074180c001c08140c5c441039224130030f49050003015000c0d450108404030000101500001c068000c0b400c0d84c540c4150800d000540f103031601075041405016a10180c0001c04a0b4800c0e0640c00344c004041d8162810b07040f00074001400e0740e00a87c490303490100b02285100c10304080f02c40c1c094005810900e200c1c40c0480c2564060154050089104403110022030610151406904021050399000380119070325450b40902510b0035000190390700192040500148070710505200711204d040e0160020440d800f12a400c1200c17440008008980502082c000000014038003040c100e4051400710011420300030103001c0c0b040c12840d82c26010b082010b122201c81c00f58403210fa10b410403001c00c0c42c022895590f008221030280c001415040c02540c40c05449406000074818454111081441170300401640d4103402c0f40c01030740941e46 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 13366859 1250 13365609 13365623
    0x60f0501050f070b06010905030109060504050609030307020706080606040504060902070323040b030603032218230a0605090703150509010b0306060703020a06140601022103010b0a03200c070b07 85
    0x103c201084059003182e03480300c1c0c145881d400040d16100230a00b034a00e070b2031044030b4090712607046c4020400107004d0700768001240c50081d800c61420a8000b942e4003114401c840034041c1c0c4402144c0030f40c4882080b41c1c064400540203001b02039583c2c1031a4020748c81540305400150040402404000090403140c42c10100640d002d420a406e0002c56411036102920865052000300300c2d00d02462a11980030a26450700d00050305902c0c9422020b050702007401d0003000e116440c10f82201c00305400c00d48a401c0c1e0b060b0410305002103540b41035601000b04095040283d000004500b08a102070f0305806c404920b0b40c0814140305815501d00900c50000400e02036405040401d00006600341415800742207220700900c1103d03c0700c001515000304a0341840c100c04441302c241400c0020558041140d08003c803e2148468403001d0b1190340e81c1c000e800180190b041c1a68009001d5860900c2608100c1e44a00d0480c080018202c50740f14070b25041d800a0714005043c0250000020040008426174002c6a0000a = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 13368109 1250 13366859 13366867
    0x1080105060901111f02070506070e03060a180209040605070e0f0a0e0705120703020307081815060103021219060509160305062b02010e0d0f020d08190201060f0501050f 74
    0x40103449418124a40294502c605c80c54500580c2c03079080810750000c01d10500580e28085404d0403410110010403000c14018103141d681c80f551030008400e640a42081d00004401041003541c00501c20181806903001e501c01050005110250340624050740980d01e580e80403500b200140406048201030f5507600c11a881400c05c0b00a260195007544080c031440c0082c0f0300102d2485120070210196200c030300080e808001c1124942d00003003201d0300002d01c11114500c1c0741c1c1280b44940e8842410b01e00d080c54002400200303500d640660141e800c0d22040c42c216021500d45401d08109403041142004c1600b81044000079440c28070300703013544c001c00d02140b0300404601c0d45c03101a405440049d0016801010150000004a1020301c161041245030b03483c284180e00c40380001052405c091a03c00c0c403910030b461090340003444108110b80d205034144c070400800c0101d420010814061052102c6110362010740340040d00e0f50651040c0c0c107580a034103c03610b26030b40b900c00458403800745118220b0003400c200 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 13369359 1250 13368109 13368127
    0x30b07030c0815211608010906050a0203010305100b04020c0f0105040210081605030408040512030a08090d0f03090503070606030b010f0609050906010309060b1003090c0503060411010c030207030503070c0303020c0108010506 98
    0x1130182c1203125001422666100500d0700038484001041c0d1050304c480e5500d608040070000d4602519800020207003042d401d6504544500345c0311140c181c10110101c0e92010040495220780d0183c80c8800d0240301524440d0b404401301c0c0d4080c00040750128400c1406540001009010380c0f122801001080f502034038410031407000750344940c030161040d10026001d21002595036a004402d0b10005440d0b4040c546a0911020281400c04007402581880c2c20480384000602d0707200d001d03042c00030034914001c215003081d030034281d0a611500c0400b822540c181040441440341e10300b400c074103c0302e0642e0f400c1002a52040c0480704140c545c000c1c164001014004034406600c0703074015090f070b18002d00b0001800405440010050b0841801401c04280c8801d0100b052124001e000d0b801001c0580282006240030b5030303029014414203c400c0d042c8074079050b10f541454803c02024003e103900408481e034500c1581056440001940f2003240144596210312030294030501045d4100d850141400e8208501e41c = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 13370609 1250 13369359 13369399
    0x30a0209011211151b0c061b010c020f25080105010803030106020f06010807181b02010b1e0d0209130506070e0a050d02010e12030f07080c06061801090b010504030b07030c0815 77
    0x28510b000f460b11070105410f005559001c01407801d140300010f1120303104e500082c61425074130600ac1c0c20041d50041d100854800001081c03071104402c1c8440c588900400e00303954040c00c12000e40101f6099860940049090075002004505942c40d5400321250f26102c2d601043e910202405064a9500441d07000c21010740a1000514600c00d00071010410300f080194564045070040c01d8000140e450364207041070f0382000d106a0034492200412012482003170302c0855518141c0d00e200902a030720b1103000440350482d0f108030140c001d030b000050300c0e2036040c418001000d400328404220700c1442c40b4000010280b8040d00e541c23860039811b8444900610890b8100034901c030340c080440541c0e01040091810a102440007004421f00c5841007540720103001b1500c5244c20401050709025100706401280c0d0443c100b0b12041c1101c18002d004a0f049000d880100d400e80115440103159030f40120900c060160584c011103100f44050741d03544034a54030708840e1040c10602d80c4880760410300070100400c03e1550 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 13371859 1250 13370609 13370647
    0x2011d0307030e0d060207030306060806030114130f05070303050409110c15040203011508060f01080f0a06020a0201090b0406020c010b0301061428030503130608040309090b030a020901121115 84
    0x90a8240a113525120ba01c140c0c2c4c4840422800295221b5052020580001906822000a0b0020041c5c1455078510b402c4400e800f03050b02c046030b059240c1403400c111200ca00c045a00e903009003900c652a81e6460003805940041c09608045400d01403203d5901d4000c9045e10034040803140101414024140c482c03060200180003681c05540360b04c1d802c850340020100550081140400030052031500e040d0090720703002c060700141000d800a44e10381c443d41c0400984154582c1e00700030300507580d03441c0c403809900629581000070002c030146c1040009101780e6901030082d20320f11400034490000e0742c0c41013508a40d2075000d01030440b40c0300c110000c00d0703091001c03070881308401c00507914400c0781c0800a200140000da41c0112441c0c0c3c0700080c070302001400d41d002800200b044d400c28444500302070341c0c0985000d205000d6001c8403a9925007034142a501084140350f4150054505066940c40d4a1804149051183c007a105100c45e4041e0340803604000b924001080c21108642c1d08222000140d8460401 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 13373109 1250 13371859 13371887
    0x207060f020f0406020f01020c0d12061a031e0c040902130503010204090b011101060503060109110910201203060402090621040201080106020f1011071401060602011d030703 76
    0x40d0340c051280e0994241e100528051001840060710303640b40c104001d1404000841000caa64018010301d0103c2d403000420000100f101d041160f41042401c0316940206140d03446044e030240c084000c4074041d03078840000c6006004050b03054010f8580104911030000081c1c50150640d48100010000b00400c0d601808841000d1020a0364250b5078100003403d98100360044c60607140d50b52040c0a9a680000c6c0070303951400c00301c00a010482c07a080000c2d45030041403181805545c2c0300c00c90703240a081150112903d804000f84004a40b0541c1d18006040c0707090380d4462290740a036130307541485040d4005140c90b044000072403628610350300c00050001070741254040c1a00000c061019890070b1550056940c6550124000030500749000e0000518010040c0d0041e030954005801403103c91034007048644650140230300101c0c18a0710008140a1807241c03400207404640d20b01105151020f040d0071a404030364942d4000e000009070100c0c00d1039110b0000341d0340c2400d540300300f107400c1c0020700450709041c1d00380c = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 13374359 1250 13373109 13373111
    0x30f03020a021203010e060406080d0503040308040201090302100207030c06140301030609030203041a090306060f06090d0507050d0b090105011401020a0318030807080307020708010b060d180609140105011406030a020706 96
    0x414020f41110550421b82000100c10000800c22070541014407401d1300522594009015142d515a0054004d00c00540058100117403c00003400756400340c0c030850015640902040c52050f58860025102c062070300040701d030400c1e0802c0028880344101c0090b0f0300c2403a1100010701d103074659903500d0000e105072a0101c06601082c84005507410b40c1c6860408685107401d11140c0e103041043c101030820900800706c0c1d02c50901190700403907680b22324040c1c03203c13400152005288070301981809031030710017194000303948460740513568001c011540542e54094042d0000911841e600d13101941002009607842900691080502d04040b900c0340e03804a0a08200e01d0b607014100d61680c0f01c03444a64801c80c41541c0150b00001441034080d0704029940003440582c008205040c1c0280001ea028411b400002c0c01f40b80e16074030341c45401d00000065094040d4032a2040100501e9480c151036940d4900f640b00c0e03183d5291000001d04c2c004080c80048282c1c100030682d40c99590303001042da009400c1240b0945180d = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 13375609 1250 13374359 13374373
    0x607060905030c060114010302130509090109050609010c020f120901050d14010b040509060103050c04180e060403030603050609030c030d0f02071203051b040803040303030506031005100f05010804030f03020a02 92
    0xc207000340001c080e2070b031854014080031741c100340705092080040046a410507104005e544240808240341c1c506039801242c61a1164444100b05400343c040301c2400b0f44507008180510064031030560107000003a0b45030b029039624000c82d0052a840c2e44404c003949140c01c0c8100007154140d8030410051a00341104000021103c100b00701180310480d003600f00d1f43d900480082e09211b0752800420181d4016400d103000d000525004440520f1805076219030300c2401d0f2030600508207480550484107204292004403135031890035041c010041e00640c48192418010200071460070400403044828001807140110b1600b100000b100006103500707041c140781240d083c0b00b00400560300020004220003a51340100d10750405400120808403107000b00320a01d482082300b001914008010b403000c1700d416040000e215a5010042402d00d0f030000c48221030780d842c050030408401410301c0c0301d50980d280e008040b00c07103a40710b02c010740d14200240c5015004c500041400d5015611a8000741400b044902c103503041 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 13376859 1250 13375609 13375613
    0x5060402150c061e0f07090504020901020c03010504110a0f0b03150117040303050a0606181802091801150f080609040c05030a03021b010903020d0308040305090603040524090c06070609 81
    0xa010066400c0742d0103281101030f650312000082d0390a80c000b800c0c5c001818050400d444080c0a01d40c2911070b0300d006940100322021b2580c002d020b081c01d000030143c02400146050711740262441074402e84c482c800c250301c10000c40e140014100c404241e0b10200d18051454907500045100003000c1d80b0503d0403c0303102c6001038041040044c90300d004511036240424241400740010007540d03a01c0d040325040110202a01a41110441582080b02c0071044011126071205071000f020348152442c041e0450306e03200380403001e0b10b04148013504807030341800e074415203414454045031141e107c00d00c0440000c1d003070804100707a4074102c00390703980207440744490a1025a40300b0100c1e017001c0c0c19044c15005030b08092100004d40a41007403480034405d09103810401c503411940000c64480801c170015040000000005040501403000c4440c1a14011700c601d4a07441d091400e0baa5a6810340c808d80c00d04d440e00d0721040011303005202103602640361003000e0302031000796809100c1d50707030015181503c881d40c440d1040700c0 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 13378109 1250 13376859 13376863
    0x301051806032b021b030d050705010216030c05070509150f01020a05011a0306011203020d08130609080a02010f0615030b0d0213090506100b0d0e030c07061d0301050405060402150c 79
    0x2681580400f1007041c0d01510300401390401340521031480c1d01c107000081c446050380d8046284031048019007051a240c1d0f003036052040c020701138844110740091140c0d80309400d00d6002005041e400e803245040340c0c011a21242400340040301560303030102031208402540300b0b914102d48129607020301841203400718045a02e8290a4074401401201c80c015441c010101c1c4d810244162400762207400310b2203007180100e40e8006e590740800d00c480400c0101c003d0202d481084500f0716528583d800036003c3c000101c5a080c580341c10b0b44400705400140d8039000110701028114060081120350600c4204002c1405110a070050805010840ea021103403d2060005030741d903d40c51030030708044c2200001c50000e241790051802002429040d600160203204110400f0f20404072a1111105c000100d070100c00700b607601e80740d4054541c41c006180120000402c10a910403c004a100380d05020008284075410506080318407d69014107181c01c02400100581407000ca0068104120340c0110318201400500c00c2c = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 13379359 1250 13378109 13378153
    0xa0e041103060a080109080f070201090f0602060a0609050720010f02030c03090f120a030b0105120403030c020d0315030b060d02030a0302010501061d0d02090402060f0409020702040c020102030105180603 89
    0x40c480320210510245090405103600030305035070402040700c0611a210014980200c0800c070211940001c0c03601c0c11644224002002451281c0c407140009031180c2020352125000c0743c422014614001c00010f600e0002c1c083d050144416031141e4190542d1581700c002c0d5620102c031582c0031592107004480b4801d600b40300961069010460164490a10259042c20500140c2013a003240d444080c0259a01151408907843c40d400d50400060103074074040140ea80c0d01980b070201444401d008200130605800d030b040315030b81401503402d8031044400c10200713504482132140c0c0d411120300100070500004081020341c030f4103c040140031303280b002406e0f40042e1030203d69503230450050b511100104052500305a24480e481d65982000002c1c91070340d40824800092030a0191092151001040a40d1140003c03109080000d01525a50b41c1c1c8807180c0c04041e48c02202c0803401540745c000402c1c4624818801d0b0b905aa1006205d90744c81080c503200031002000241045515019414440381c01c071055280c03803 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 13380609 1250 13379359 13379381
    0x3080901181e081b06030c0309011805010f050c030705041e03020d05070f06030603170d090c080a05070b0a02030306090c090a090b130b0a0909030201060e0403020a2303030703020a0e04 81
    0xc9095604100f66507080140b100010300b0461800001e80065a4490007501e5004001ca1529522a40d40202c041d002d403003203034020000f07100b85c0c40501051060640110f02254203e1005000d55140c21890307000764881103503a400040d806000c28040800401003000c81c80d450261114102078580c0c000841c80022060304603801e81c8202c40070404108030091210003042c55080c1008868a1034480a50380d0100351689008182c3c005004c821041e00ca9006c00820f64000320ba1403a510780325a0419a81e140b29007090300c07103115040c0d001512180c0c000c202e485001c1e00d54040d41c25920741405000f46541d015003aa4030022003071100c2c01d902d48402d0303a03440050005000100d43c0400140038000000c0e402c1c00100c0c9200e0a111408540c1c0e00c0740003c48003160a071800004a94800341000c90040106400c0210540d401e8424003061581c005046880140621040e0742d02180e4440103107554807810f00010700301c0d0001c0c070028602c0e82c042d50142c2115101424601540314040000400711030b8a2400703 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 13381859 1250 13380609 13380659
    0x3050610031202030a0203040306020a050d0e07050312180d080c01020712030b030a171305040f05070e0307081207030915020709110c0303010902030a02070b0108030901020d03060308090118 83
    0x100304184800700308116100c2d05580051880d121107544025224815800054103d03034000607000802ca00c0741c4102da801c0709406200b00110131802801640340e41003442803902c41e2003a0343e03084409a015404862200c1d18948015400c4201d080078800e1181141805503000002030080b0031500c0d100f800100451441200200c10240305d440c0050300300e0380c403546046d0095010081c3d20000030140e0050318202d20000040702d0715000c0e004c181c40030002d182e40109030030070b040004174441a241d54228501410594403a80403452001d0141035865030702e4400c01245a2101c402c042011900030014100710b4001e180050740f8580f00c40c01846882c1615045c440140d00121003088425003a1103002a01980d030f00c0694039201d04000b03c1c0303940b408107001d5800c00702c0e400400f14012800560444e0030b115440443d83c02c1d0740d079407201c0d199205c0d00010b01c0d060141c012180c03211100c0b4440d1040c201501d81c000030403070138643d2000c01103495030003140e028540c5c0e010704c510110b140c0f20b90081e003803418404010 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 13383109 1250 13381859 13381891
    0x90a0807080d06060c05031b07080102040807030b0c091011010906021b0d030e030405040b03010605030d05030f01050a030b07050c010b0a0f0501030608030a08040828030b040c0c051b010306030506 86
    0x2c0000c0350219030058082084441c204030001d800407088402804600d1240c102180c2a140c02d107051080b180d201801c103610014000407403902c0400d03070404aa01681c0140416603c012012401d885180c1855074810b201704503500070325001e0b180d6058004004000012080851b5407440102d91004650113548041c40942c4c64002c03404014141e007401043c6814801e1504052000c1d9407809203000e040c0c4039649550008045450960241c0010b080080c00c030b500e4040c803100040c015520503030368840c2142426002203401d0401c0d0b00d0703d8003140c0c0d000d003110038035079641c0324122640e411600519060395210a1203c0395a80c9154213100942842d0240c00182e034507010000d02218074903404143c06400c08d0081e12001a00428410350254101c07040079510383d882501c03062490844203240094640304c1050b040d4080e41750f808044200c80946041003040c40000040c2c03007504040b940100550302c58002c590000c0d080c8481c510f803184d070606010404684903500e1038200102103402d4104485100 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 13384359 1250 13383109 13383127
    0x1e01020403150207020f0d03080a1e050a1b0e010e0114070b0c1c050603070302010806030307080309031c0203130201051608040306090302010b090108100203150301021803070f0501080a05090a080708 87
    0x141c2c4200e404202e40007c8840d00f03564026002000060808807040c0d540c0c460312009030030003101c96000301e4030040c4c00c00483ca0b280080c100205009220000510940180c034800d050080c030080100540c161141c45901c0c2c0108011209000019000000004144401400180000c52243c000e0390000c010780d40b5644200f00000c05c400980140002090510091145684004c11074901341e81d020703c1c11001d240c0d628400319146205900c00104806000403c00c9048180030000e8240c505003002d03079407030720000c0c035001400b079010688001d0134410101c2010001580079100500d0080100310880300c4540264036140e296030045d51050f1103143d19901008105903083c401c2001520007103030310300d45950400e5542c69807020040300101d07650f0b03400004115504100010340c0b0102c0d00081c002c0d5564800f0011200124091544860103031080080101e910320004c81807009640040c3d5500e0129030318070341401e0107050040c000c04000e01420a080000c03030103120040c880c26009200040d5101110 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 13385609 1250 13384359 13384369
    0x100803210c070f0632040b07080103030518030f030403030801030b06061606020d1407050702031c050703050912011107050d02060f061009210308181e0102040315020702 74
    0x608a158100003001000c00103a40c031012421110f030000c40006213100301000c013002c80c29801074150540c2213805a9020400828011944910b02c1504440003c0c2c8400b0401d0f09c1f0707140700703010007004100144422400102580310302c2d250008001c0c2124020b403100c07851a4115803054000b5800148004018014044020101a08141c090f80c079031703240c02d5100d00301500581200000070030040d00041c103c6c06c858580c0c0c20003080b40d02e107603200c1007041c2890715002d000b42d030059404901138040d042c50ba0304481917007400d000c402c1c07440c0e407070301d91801c2c40c1e40c2d804640f6907100c030b00da01d5440086552081c0d0f035201c091050200f91203110400321307a5904a8140545001012481c2200b103500c01002c00440d02d4005200b03540100040e124203c000390b403a94283d03400d40003a08602c4100403d0008020b5880381e01440442090098403850304617125450304a00184021180e01250352024048591522070400c884500c8005900010304003130703e0b42d440c014400d1100300741252aa8020800c04198070301 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 13386859 1250 13385609 13385611
    0x6030703020c0f03040b0405010807110303070c030329060a05040f0e01170c0607080705100e01020307090609050604060c031205070504060e06031902030901020f030412080105120303010e10080321 86
    0x36a10044d0304143c0b0740a07555841e071103131380203031742c1001480c6020131201402104851500c400300b2054079120715203460010070186244509400184c14114100035040303048840c000c2c0b201c0900040da0000c0c41c1c802c03d015547e84a01c01c0501084001c0000103200c11903205a44007515a0710440c1c0000d51400c19100c204d0b040000600104c0d40081c0101105a07407110203c2c0d028960010050f0f0715402d031400c1c01414465088010716803036040c48041d4500090650080d07104501c6600c4440c0b12940b603840440d084041070143c05d80220741000706210403401080c00305c1801c2e205e490007502c1c84440c0741c0803600b520015110403020031004a0240311143d001402a240c11030180d0340c2605501e88901e80e401c2005145142e0342c0466400408180603820a40440302c500b000c501805640303082501d09000d1290301c00e141c420000f9010000401c4a20b400110404541d0b8000c004509503400d00c040c405a0301c10207000d511048480c2200060401800c1c400f41800c0c80210180c0e6052504000210a801c0301c = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 13388109 1250 13386859 13386883
    0x1e062306030702060601080402040609020a030906060b070c05040e0f07060e010815010c02011103090307030f0c1403030a030506030109020909010f0e0c180406060e0108030a0207080a1a040f0206030703020c 90
    0x100c240104006103034002895540705800b440c2514a80c7c541e070021400a207559000010300f43d00004460001c260503410141000e4842d440c00c00003d981d42484080c20700aa40d4014010325550707004110614064221440051054084c0d44c1d02c10071444009103031002981c40307000412601b4480070380350b41c1c11800b00d96014012a542810b00b14211000812044a90500034140920000d001780740040c1002641d10315070014048880da140c490500b20b0742c1c07400351481101e014800040210751088450100648400043e004500300201102c007a8040c0c00d004100c40e40640d42d880140300540d40b50b840c8540244a08000000d059421f232901000b0781e03280c0075050505601c54088c9900daa00c802a910300c0c100c00c42d0f1803501250310f4174680013010b030131950702c030044121220300003003954403000c401040000410380844030341c96520000c3c142c40e07040c40e400103010040310910000e04241c0c1d0080f41a40b2030300c104203410752900307107900090b02034100f941c0c000d00190340443d001d41012030800c48240d4080d = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 13389359 1250 13388109 13388119
    0x506070203030f0c07030903050f0a05100c0503071d03010f0c0e09070509061803010f0b010206070e0a09050603010b18060307050d0b0a0b03070909060c0e01031a01031e0623 76
    0xc0f401540300001e200d40a080541071441c0010b080003818411441000078540c8441615003200b0285119541c1c0c5044a40c1918207015017034908a0003440c03445a4031048216403503190840d0b50f08070080d102d40881074010940704400c9125920703a1743e020f1040040f25084c559000407480c840c502c0090524050f0500075028404d4a81804407441c0c102c01903c64444084802c1c5545480071380d401c83d420381c4128580c0d5099030801e28209100d0f8200d400c880c0f6021421303400c80b8a180d0715440115461801c80c0921608148080c00600012507240c2120390310110180001c0307000e842034800315814501c00a60941041107603c1800400e26061100c01c005241c101c0b40e04a011000d91241144400c0243c107900324581d80d00b40d002e44d1510103000540040041e5182000017402608007078001d00902ea607001e00042e03400302008019030280c40703906040111005615800c2e4401030040d002400c241041d425081c286606107a8081e40c1402160040c190181043c80c200c0080c404c0d604400700c0c00c41e540c910079 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 13390609 1250 13389359 13389361
    0x3030f0f0507080103110d0212071a19030f0e0a0b0105040b0301020a051803010b180709090216110301020d0e03070512030403050304121b030f090b040807030b0a0e01020a0903050607020303 83
    0x141d43d0002400341035035048003031980d030310303840c080001c08801d24042c000390415101c51181d034801c0808501c040448404000f150a02e410300d104188081c030488a20400c442c9030f102900701c11178429804142c414004600c0041c07d0301849040900e4a0011102201e460043c04010312081c1450b0080e4882d5402c00e500030350034a80031030030207449801869840400324422500c0030607a5682500540320b80307a4050203000c01480c04003610f4129600464031300000c100d10600002c0e20700400d02c2111014818009080040100fa0f500c9218041661800d02e92540d020302241402d0902c0c0d10465804980d41e0005664a03105890f01700d0070700e00003000024a440060080001090f040401c07a03510581c440e40c4000f6010f100c0c601541c03907071030781c1d50b5080d2664405444581016001503002d11200aa92510366880e507039a0060f104500ca01d0150922541000d141000002c0b11840c60640100c030010010800c3c2e580c0c0d040c1c0c1c600320b81042d00700000181b18078000f041408000e100d45a044452840514030f9 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 13391859 1250 13390609 13390621
    0x160309150509040504020303090d03080a050601021501092301090b010201110702060301030b07110607030501081507050f090d020d03020a1208090c0105030405011407110709090c060503130c0303030f0f05 89
    0x91402010140b030b008540391400101195424421100810b00c0103003405400041420014202c00046075000007192409000c500d140d0300000300c1d9054041c1803906203240340c0c240440c070000340205645d0800070110080b203c440070001200d00d035029114269000807200030b220002401c1d40d01d0300c4684030f042c031410000440940c039008212030560303801c4507030164035031944d01d4100d542c160340b03511040c0da43c002d0307000f48095558103030051812a4056011203108101403041002c03e01c00a56010303010410030060310403440d88040141007400001810f0a02d421000d40105013420752980301100140c02800755003040100810101080100d2031402005c10314214410540e910f140f140058148000440050704000c025040800348413550481100141003481d000340250780200c140411a00070014041007061507071140e08080b40d00300000c40c1d051850b00c10191241d6002600c0703102700c20b0810301800c0c040b03080003040200445c400c1e64001070b12a01c0164400440d143c00c2421445103042c2428014 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 13393109 1250 13391859 13391867
    0x121501030609110703050c0304080a080409230f06040908031602011b0906030b040605130b04061703120402010203040e04050c0307120f02041d0109030c0b0604060509010303120f0216030915 83
    0x255181c1c541071050340ea071f9000f0101e51550040b548080b600f0702c9140d1190b0308001c6c89034041c0c42222181042440204c04803031448440160b0307010441400b0760148001000402d01c0085550000d1015100151078a00c94850301142e600441c0d1040710404203041c1901c442c0c1d424400c4195003c66030000300c00000d40600d0041c9000201d2054200b0140c07101d40400301659143e10500047c900101a2014407450b4194034001d000c160441a100706d1401000240c3e1400050402e5074071034001020750f1800400c500d070310520b180050310030303411440203100c08200c800504803841e015601440c000c0400407446010140341c554160040c006290b5030f02003050003c0c2c0360100700c850060b4110350110721041008000036028104000c4002300398203210783e03c07091680040c1c80d405010b02400101c12a940d55605120541e1024410141c10040040041010911407500f80300304810341d490220b0301c51502c91103041660402d410346140700d401c00c0f185000b010740040d8414002c02c01003201c0d6007040c00d4110090 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 13394359 1250 13393109 13393117
    0x309060714040b0d0b060301030303150f0609050603040c05030a0803090d090308040b16060204060f2307080a050d020d0b01080f0115110c03060705070309080102030112060902010512150103060911 86
    0x4183e42d80c080f602d101c01c0d080c41c4e0802400c4a401411042d2690303900d00b0b00030302034803400d00440c0b5440c410290100d01a02881010019104640c0752440d01d80e06d00414490b45a00040c81030718401c0c2c900d08003007041d54090140ca80d0300380c042d00c2c3c42078503401c06080c000c1c248680c4400d6001030103002d40080000401180560b804c84039018440c40c1c880d951140b84405103550307072034018545d500c001070114449821085441c6450020340d616000c5890707841468442002000c4002c0c0e030300100f80545000510210010901e4000900e0b10b1414100c100210606136001056440c80c3c0300d403a8426030394a542d121310400c1e0b000c0114800907060f54034040d2a00405130306540d4032810420854154002c3d00001c0040c0b182403c800b40845030b00789013200740108039400580046001549800d00001c42150500a0b0b9043c0c07903401d880702416200b80d5441c0343c01446240c508906005040c8101001424218504c034418100d0002c8000301c608010001411143c05400681040f032803d80c4821521005600b55 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 13395609 1250 13394359 13394369
    0x2090403050309010b030a050106090e03030919051e03190e010c02010806030304050d050d1404030b1f0306020c0109021009031a07050408061911030105010f03110c030a0203030906071404 82
    0x160b40d507501c0d12502c45000d004030702555505441212051800c1080550144003101c2c24a20300700260707441118103e44a1100b0346040070554448001105121814480d080c5003500c81c01c22181e02100c44403402c101034503100150b2140ea000402c91803032080402414000080d100d1a129808104810000c2c3c00b105a202c000307410041741c00e0019903551000c00488000d02402081c0070f2602540c1d150a5544042d22a59800003e00311280034181948000a550541e94041245010380c2d0340d0301c014480740240d0822020b5941402400080450001d100410051030920b001040e4a0428014030100000c880544020000d40810401c04108a022107018841c0c50201121180d1210f0001310b5040c011230300422454094002440388204508c0c0d40000c4461200f00c3c1400020586a4001c1450000b441141e0120b0407405090144a10a07481001c0b048121410241000c5803040c487d865500310110403c0035034000414400100001c1004581c04025403401c0351001c2502a0345650034000d138460 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 13396859 1250 13395609 13395617
    0x4140d1a070324090c0206060a03140109020a09020c060105010908030d020d1b180603020a0e0d05011401090207020906030a020307030b090106080d0c20010801180209030106030305070b0901060302090403 89
    0x2207103101d40700340c21100c0c8000c00084880250441c0c990000c1080c2001d1181c60700c0103141401182d54240040f84040c40b0f4900103052409540ca903458803680b0800da051100c00075540c1c2c0b10f0314001a910350301d01c0c202030300150310300588500f4100d081c24a8150103820032070501c402d0b00005c0140340800400c48c0c4000701d03524400f60720703100c48203503d40150101e4425030068144412804d24a990702c0b0521a04030100511100d80b1255240c2041d4100d1103000c00420005010068810441c00d0404c174003100e2510400c0001210600c441e81c19a18440c00e0b007060b0385c0c042c0c000400c0820351805260381d41d001801140a8481c6d480c0907030000790b030307002503200c0207096100c030200103070400b4030a504c03810003850042c055032000da821a00c000c021140e891012a04507000790b130068591030906500300041d82042c0c441360681d90070406502d80700c0e80d0107041c400c80706808100045054074207015076002503110340c846a840f140c0e680b03041d5180842c01040f114482c0e240c0103041006d0380d01d00c4861038216070507040c = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 13398109 1250 13396859 13396861
    0x5072609041512110306070302070308040b04050f010507050a0225050907050c030d0605040c020102030601020c060c0f120301080c03060705030a09020a030605040b0f0901060f18020405090c04140d1a 87
    0x42c0100c2020900d61042c120346203400c842c90305109000d001060744039800c909442c600d5940a13400c0d0100e004d1040003a00080104000500051001d620390345c001e80264120303550f0b5000caa0380a070954000300c03032180001d03501241101030160104004595610f286c04900c882011102250361760700c000b032045030310441000002c14511070242080b82e42014008050325503a02000100c480500040d1151500892030000e103900914810310075640a00e505901809190601c103007007100c0d40c0c0000742c1c0d030b4585000c0d8080703000d400ca1080112001c40c8106214441d10380d1726080d511802d0010504065001b500920304100916a02c2403c5903403201c030700d0350f0026001ca00c50000c200c1c0c4500d00d030402402203141006020505c03001a0686105451045075042903a4800040a00faa00184a0740041003507160b401c2c03103480f201718080b8000d001005c0c40141050368070030000741d803044244d0315108080400241132007501450840c038019503100f03484954403000c41d51f40e020241c0d4a40c0c050840b000310708070 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 13399359 1250 13398109 13398131
    0x6080a0203120d090804080a0c0905010b070b0405100204080601080f03030702030301061103090d0506040215090102070e0603010b09010e0103060c03060609030816060f02040e0f04021c030207080604030507260904 93
    0x1d400132900300c0c3c1040c211500c031512440d8042d0385000184041d1101b10a03490300190240b1070340030b014143c0c0c0c9640013a509006040e541c0500c0950068001c440300d00411031b401020302c1543c8081d000070080d0308014a690351404021a0034903181c0c852250080d0001c0080000f82d0350000102c130b04441003460103011500c00031000e1030650082d00c0c000ca60140d444090b410500c0400140540958000c40b185044142100f8009a0b40e01c02c0c0303811031f40540c1000504000d5490010700c0a40d0000002c0c00104880011100140d11340c1004d0300702e0710f81d54604400600c02d2010510074900e469400d03003020890030341403034070213010008107200c010a0100001200c601178000500000c2090354025024440c8445030000d03500a5003040c001c03405c02609440000709403a0b15494110301a130380240c800301e24090290b1030040655100541034041d07128014000904000030480c4622650084c4d86440d142d52091520740000e60344122200c0109000c040d8000c020340680044451140d000c440010b090314000c = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 13400609 1250 13399359 13399361
    0x110702100c150f051501020109020a06030c0e090405061e01030b0606090111010507020106140103021204030e03070e011e060c020a050103330504050108060106050d0f0e0a030905010306080a0203120d 87
    0x40d042e0724105410207100340d82c0d103e511341215008554122440d1540100700c0c2c012800c03a050524060b501c00000201080802d02a500954001c0030926281c0800703424034010601d20780096070200d44550200c070810042ca011fa54051131aa0b5544000314070b00d51540c1c0304c508020101401c650710920300044e0b1580541e008a058400b030900c003000a0000c1d00d00380401a0080210b0700c540e45103080568a080f98a43c40fa2003124946804e9041c902c1ca117440300d4804030354890002da11590984541074000c0768981c00070120368000c0001308030700c3d0382640c0302c4281c050b070301e4110b54400018425094641001130b6552070b03492094450070f10380050400350784081c2004940600604612002060b4842c14010040321003d80c1a1881034505102d2660703a1148156a59024400c0e480050350034400041c805209030072015943c03003d2039000c60b2440e01c00602b281403100d845411000300c1d1480c141003041c1e5801d030042c1c2005011000242860701615000f1a80b100803c0400c1e6100c52030020f04a40070400f2 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 13401859 1250 13400609 13400633
    0x91a030606160b040f0b0c040303091404020f0d020a0315080a030c02012303060a08070602030409110708030a0509070906060f030905012304060e0109080a030b040f110d110702100c 79
    0x400409000d41c181805c107010307030414488081d034000c40700000007000c0c3d021401c00c6404480d071541d147c680070761502603014200085000c40d10340c465001c2001ca03164403521360103010007001c2090010781d40d52003004003404a460b02d170740182ca81300b05034a08012440010801e00801074143c2010035001c1090310040340c506d229850100030400c082c8210385490130000014502ca090260740103014151142c1d4110350302c44040c0f09600040e44104802c0c000ca00c40da8004243c5011100c0300b95082c0030709070703580c2d2520360401c4800c003180c1d9980e1410001410020800700c4001e00c40500108551410007000030907044810480009140d2607100440c01c001e0309602406010418078640c0c2d41f910610b800d400c00f44842038a041d580e0360700b4086501c49405d07040c41121302043e07111100300d280201d0005c042c1d000c1c1060841c03142d0301555400c90b0300000f4100340106258002596402503948031100a01e008444051060b0b2040b48000e000f4200180c50b10f0340c86207111009414100240c0707900f8500441e641070 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 13403109 1250 13401859 13401863
    0x804030e0603070905030618070b0a0c0804060302030a1803120b06040b04030b0402010f0201140610021501080d021911060903031603050403110f01080411120a050c01091a03060616 79
    0x10000104110300c1d5100d60800b091720000c40a032070003500d0b843d00d004140300c80c0030582070180e0452007040108080c0c61004154000c2e4038108903d03182d0701502d03000341c2e64010b40d01c41004a50000200441201c9a00c50007400b0400c025200030041c200341c80051204590050f40d046583c0d070380f40110b10726a241c005a0300241000440070307549907180c4c80c0c24030301c0b40c0c000e8400b07d000c9401486450003c600601882c3c00400e24014075940680e0303841d0801c0350a0440c0000b400940c05640144162440010344450181c03818400400c03090909820003442d02d020442503424140c1001c1c1c02c0e0700050034064003400d040307600f141e505459811080010b811482903071401d400c6070140d6807014080581000140c400c480c080d09e03045226905074001d01c44500036680c0b5450018034100009000511081080c059000025020b0a105229001e0341440e08441017001d031815070003d448040d10f51703442010302c4054405041482c0e00554129001e5083c0e000203003100d840340c40301090361261040480c00b4556019 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 13404359 1250 13403109 13403119
    0xa020a050f0c0a0506030c030420030d021509030a09090b0a260c0a0b07060c110307150515010203120718030b04020103050601050310030b1305030a0801060806030c0609010804030e 79
    0x41c81c003580d40c41e41e41807414115802a0188400055140b40034404e6038400c401da40304040c61655544d5a00c0110403403070350383c410255040f54132802140c40400c0221906030068004140402c1404480d0103c480c00500010040d441005080034055010303950004844000030f002c14507810382c00001d1842c03440368000c07030f400c1141d5400201c0424084081e00c000d4505c60300584a14003010010b000842d03d8500920040e04010082d040c00500d0b01c0d8840f2541054a01e0b000717030079901c0d104256081d0380c4018800d0343c01c030000c9a005504052240301d025046a1510300c0c000c2038a1f40031002030346038060407d00880d911036880000d40340078014501043c2d071803514402d205095480b403070072251070700003a501a8000391070140001c0c0c1950040007200d001d00b0109400e89415491940c40c1c002c4200001c1c0708081800d1241c40e106c00064041010b414140b0464850b118258105000208001c1c0020060351095021440805090300c50340c0880e4803003102071030500031aa0719070409480001c0c50a00c03603a000 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 13405609 1250 13404359 13404373
    0x60309030c010c1d040b1806040b0907110601140108010b030405070510120e060403050405060a0e0301090803070212030601051821010b03120c030405011116030f0209011d0c0a020a05 80
    0x6903010140a030000c140801080303005000000f400102c1b240302021a801c100340010030016400310311071917940500d00902c0814120b0f03d51010400090080d1503076004100400d01003404000240000c50140020443d00c144031100e000008200c1c85041c072856111050000116003400014000c82024280140601003025a0f03858018611a0550103110f05e83c0c0c50320600d11000440071844a000316019a111402c19042c002004510390180510300180007000d01d109500313480a00880c5071752030251004540343d14003002c0c0a07082404c1c040c042441054204100002c60303030040309440307640b2202451780011290200214204d040403001410b9580b0000c0c21314491203c05420462540006030240c4810880311070514030700707015070b01c41c80c04140c10501c001c2c07144d9403050b05041c2c13940442e035088841c0301c0c40344800d40300e0003a4140c10503118035185542d0041075003000c410060061070310b04500319034444548216901544050b01d1450398610006030707129075610801803c8030f0560082c040d1203134 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 13406859 1250 13405609 13405631
    0x606040f120c06020d02070b0d1e1a09011802070f05060907060e0a0303090b030606040506041205010605180402010e0109080d0203030105040c03020f0708090402070f0302030c010509010c0c02060309030c01 90
    0x39107a01c15084440034601d000214180c2d00c01308a00510518580041c8111410b12402040a8002480388a02c260399091034003400058180c8a01074800d803c100001e5044400300d6a035800e000d42c165190081c1e41003001002030581c0e40900c0d566907046001e0041e01c0300d4084c5084250385d0a04100136007240304d20401d0058100e0003043c80c20480318140c4800804107030301c00920588400d54400500446c2965208200310201c030401181e1181c0001c0c15185095103031000030700907400c00c0d00048003160440c0c500e84c0411400340709200c040e14007207441c07410303048140741c0000d07400000510003410016500091103259000e4904003010700b1421040d1840034800307800096032070308244240f034404c604104a1400c09070082c0300310f81c4103080d03021105180008603268200d007507119100361500a503003007041002061501510b500f40383c0c82540910f0303590002200307030b40c2075440c090007070300c5280d250492101269400071310310301b50294156030468a90b03032081c52080c158017134800307a00300302e5081c00c10a4134 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 13408109 1250 13406859 13406879
    0x4051203040b09060708090a03080a0f0e0312010506070b06041e0c020a06060f0e1f18020301090b0a05030303070e0301090203010f0b0108160807050c190c0623030408030606040f 78
    0x11180c103460080300e50a17951241d0840e000e410035a040c02031a004401814040b91041c91400e5100003410b07404103040b0200c210079002c80ccc0350600a18190340020440404607240040403900500c411100d85040000e151280e107400070014142030321542c2c1d51040c450120340800480e54140888180400c074003080d07131034069104c00011000700e4805103421404641e440d0190140700589846907544120303030b41c0b40c0004c0c041d0b0130302d00b121000e02100c1c03c100000c0c00d604001d800d11429800780034096165407602d28071800391140900c42e24031903512540b040c011910700200303036544506180340c0030000112103004a401031110f0140a9019402c0400d00802001c581d0042c802c050342c00e0b038588603a560381c400503007a08200c045699000030605804100410320480160a0740008031060b0345405101403d19958500c1c806001c0b65980256641008100d411138404d00012020440850b2680c0000585031142d02c40180000d1003250f021001c00d00d07075142e440a4501034031000c40010b4009484541c031407 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 13409359 1250 13408109 13408111
    0x19141005030d020106030812250c11030105060112020a050f0301080106050f060304030203121005040c0e01031104050f060304110d08030604050a09212109140601050a090504051203040b 81
    0x24002d100341e2540d11007103481441520102d139045480d2031304060018050000f640c4014202c007010b603a522248d0303000c0d41e0420141d500444000e0f2119541003e082c5058521400241d400c2c03071099142000300036080c1d80107005185070301101900141e5a454044090b101d80c05801e4130881a41c50100000c1842801503014400380c03903049520309075607884d01040104d103210484000380107030010320820919004901c040e5401a00307030500000902d80300c00c0410110b820300811000001c14203566220196007500c44c405400c1c505203255840d050030900070481d403000a20b002801520300000040a2010358a00700d414000000c0c4490308400c51418150119001660214071551901c40400c0c10100244206404030794084140351281d0300106400683c660310342011400d04c5402c1c5030b18146103180e0040410307440c100b004000703107480c0341b0304081c00c0034200d070320001d081603000000510139907480100180c01c43d0500800450ba50780c0e20b20700181000b00e074808180d8010804010701042021801201d = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 13410609 1250 13409359 13409369
    0x5040f0f1403032a0109120503040c060e030307080f040b070506090d0e0a120204141f090501060504150c06020406050301030204050a0c120c0203070f0812090114191410 74
    0x18595480079201055180d11400c1e01c80c1d00c4039a101044140c05542603040d41d001306030310030000101c120941c0c13500d09407002950980c600107280002004108a048228480544014640343c1030b03420846021130756922404c14003420702c1c080419040c00602011003110068001540c44a072100c010b4585a42c6d2401d0543d00728510b030048480350600715112705140d1104220081880b101c191401e5042c1420060250090b0380264841c014005a1064264054001c485041c8000f0f90150845c404c902c2500780c5030004c0d40d1103403e101c010810140d200c01500c054844180501005090011099640303500c603190003040503001040024a041e0490080c5040302c0c020f64051006990310602c5008075403460f02c000e0082802c0c3c44203031300404816445400d0310559401141d1400c0c40c191100e41c1019078414049980d10000280b006c000c0d0000101150840e40350802404242c050451881010100500c1c980f800c40d02a904080b04c00040c0d0445076030703034a42d1914015541040c401a9038402403c1c010 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 13411859 1250 13410609 13410629
    0xa02010c0f05030403020304060323010e01091404020d120507050f01050a050a020c0601030809011101020d0608010b03060708070e06040e090c0f0a0f0e06030304030c0602010b040f06060c03080705040f0f 89
    0x7540000c90300a004591041d07906501551a01d41840c400750300a00550140082c501441001e84414009548d0f10314080c04440100280e00d41c94802d04605072994150103034884480c0350180030068884441e500b02c82640014a541203480401c021901402404005452403050301100074185e8419408103025011064007440540e6482d42940d05a224402c18400160301580041020692010150810310014900110410b000031212400e98100825811500381e075080308100f50602489121140c1c003040d80070307100074649031101800c4140000d02c0c140510028000e400903030b54a10045602504003a0510701031801e100c02d64175915428962164044c940d03140d40440540340002c07000c81100d401541d07400c00ca909014940100038409843d0941504c01804040002039286200b01e000d0b0200d580002080c401807020001903e19040c0e41000c0d00b46062000d21034164000648190030f86c0500309500941c6640c2e0084440e44900e91100144844000005c1944031620b1214011a508030704 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 13413109 1250 13411859 13411877
    0xf120706051006020d1817010b0a0603180b070c0f0f0b0906151905030106030b0406060f0501140a09051e15030708160908030a051c0506010203030606090d080a02010c 73
    0xa00850080c0c0c0075143c05a03001c2c0380304203801841030400700e04600884550b85081951071403000382e00803200c05884016511040c0101b418100f101c5a4801042945030603c508021420f54006e1801008000f510300007031000000c1001e400b1343c3c00c0003c0b01d0b0307000e02c68104030091414044000c440c01c0600701c80708080c00005c01da03850400030302140500701c00b0001c20100f502450412400410002000c0300b25440c03031500182a980c02e10484009501907901114140350038503245044594541240c103112030441410720290764010703c10201c6c82064140e0599401c42e1590944111420780c0c08268402c2186c804600e1034502c1526002d4051400e64905d803090080704050012030004481c03200011741c0e0f0600042141c0502070700f940301078000d1b0502e41070081d1200744050841e4011090400030641c0090b070400e80d511040c0200401c0d03203110004101c54109100002e480b448040c10240c440c08021824000594401209400090380062722550f9038500660180c06000800c1c100d1300400e84940b = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 13414359 1250 13413109 13413121
    0x2060601111e0705120606030d0f020705060702040b04050a0c0314060f0f01120507050301030201090602030a020c040509031303060b010201050105030604030909090c05030a06090203070503010c08010905090f12070605 95
    0x80140031150480c01616048000c0d881c04039602420080c1500d6510600d00009120307207075000c5d040d00200c041c802806013441c02e8000d140c50100310000c820204440e44962071040307640426030009441044801503901c0d910b41c000030707025158000350540d0191400042c020100c1032540294a00c841c0c5440c1448071100740d052049090504a50017600b00d10320b19081d1245140c43c07242540710030300506011581007085d01c1c0d00001c8410031110340005c500f0000041c070a41d078109842200030806c500c01940b60a1140030025141c8803a951054003d50312900800e40001042c000e030345c4208001c81005800540c0e904012014090f590381540c00b6500c0d190021400f0308003c030303109200310b41503140e6110321480d0200c4500100b4651606942c0c81c685041e0210382c0ba176040c040c807040300c1d00401c800b00ea040164010107082010b2376224a02c01c2c3e240201c0880f403280c004a02d40d0458240c0800046e4640e40d0705030f9542080800088403644e40140c08015202c172440b0030290404600607001009265186 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 13415609 1250 13414359 13414367
    0x320041d010b0f010509090c030717040b0601120204140d03120212010504150806070e010302070b0c19020609070b0d02090306010b0c07140f040f06080607030903021b0f0d03030204031e0302060601 86
    0x40c5c4206c1e04034447d4400105040c1404004642101041ca000c0001c00e1240610b20905542900c04840c00303c200414081c1a6902000042c1e00100c3c2c8082149030503d41400c010103034000e00201c034002c11212079400e0916024003901220948c0d0f02509550b41c03101c5050b80110708600f40540d510952a056a82c050034205001400c2990410703401402d075070b2502c10f0281d0314800a07103000380c10180c0801c003c200140703907450031a000c0e000286e00d00303440e0507410340400403010511800ca01198001010007541c076a0001d900700842e088a4800c070f6481c08a82840d50180c81108100da4061041c03800010b00c0085000081440b941c0c080c007592181e81d100d20507400c0341c500c2c0d12180d43e44449078010550b003503c3c00c0da10880755010a01c0001a44503030300c440c0c060a1100480e03000000c80c0e07854410509148e01800f4a941c801e0340e9104c410800400d03000043d48007556142840d011707900c0400743c0300c04c00d40603a04550146811105083d029400184d0000880f103e000f8101c0c014000d20740400d14039402 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 13416859 1250 13415609 13415617
    0xf061b080703081312050405090a0e06060d080706060b030106020d0201023a06080c030f01060308042709060207021c0209040b06030703020402030a020d05010f0320041d010b0f0105 79
    0x3102403500c0c50000d05840844a00340f015140c80d092400c2981c2001c000781280c00b90000312203094076600e468601d8a02040401c0400400b0410b880f03042c030030320b01c025000201d111076012408903100341400049052030900c1d07000320100202403910340b0101145415055000e14102c03800c076821101080b008007012807e0780030701c6080d10381b0680d080714182c0f01100c101090126154251052410040d0441d540b003040d541c80764040c0c0c0158201036546600d5050a005401e50307135110000901c48a451035031401c0691103284140c600706119519986204da43c82607560180828408040c01003414909045000b0b500c4031400f2446064046e02401e000c60700e91180c8501290028104030040d50b594503504441d0764001c141360b500d400b8580740400140d949201460050b01c0810700140c840f800f0701d03000812039006801c003c2015110740000c10010b04c0e6011035001032250700a4400e40c9200c240701040103042c00643c2c413001110040c02c04a074603941503005001c1880c00325800206c0c0e8065500565441c42 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 13418109 1250 13416859 13416863
    0x5070501050c06060f0409080d0b01140408060a09031106070906020105071704021302090d0303050901060909050d0507020f06030c0310050123180910090b0303030601050901030b011101060f061b 85
    0x10f4400101e0915000c690010090806003011402c000d26580d9010310764002c035066404281d494800031815640300c4414900c1c0721a0340780151615003843c640c5076403001e00600d02c900050b01c0e544036004242c80740d00901e400500150445510b82004100a040240340d8000c0800540c030740400039004c00c0c861000d140d01d0046260700070340c450310707241c0a0100000c1c89c1d00000d00565020040031105440e103858602c1410b0103550300040505103600441d0949509900c101255030410034407201040c400f19500d4100c8419043c030346e64030300007031005c14144c100c80c249050b40040003104101d40c24628800862181c00029145c126513030b201d00040d0390380780002d40201000c004400591012001c007400400d0700b0202504400c210100080004203114000c4441a2606441030400c21068455000d2107001c1c8070114080e50540c545500020a10300941403a10b04154480016181da64015180c001381035000074001d1081c0303070301e443c641c80c102075143c46503c000805810f400b0400395540e10890f51072035 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 13419359 1250 13418109 13418113
    0x402090103020105090d0c12030201060e01030b0c07170a030218030105070206130503041707030203100b220e2a030613060b01090b0a020a0c0b03040f02100c15060305070501050c 78
    0xc0d086400444d059000b0500c0c05030050755000c81320010900060300d1000401041d40c03500d4072000ca900e80242920161362110421107035140041c000038040748002d03a804030800f8086034072480705040442c18602400c128820700301d000900d07940072a0785a0002e040c042c4400d80348424800350402030600f21041110341c000140c00040102d030b40358000300010300b4041d0103842200d080a0321130804070721410300c801d41d040301c0341e104080800450905026900d0b04009030b00003001007801e0100841c10200304064151810304110007841010303181c641c00030201040a00445110b0307003007070301c00e03220141000303203502c080c1e03030314003148843c1d0380f40010300c50344100000c5845445008581c3d407030402400301480031030305014801c0f50200302000c0e060044c2c070710640e90340c0c02040e26410504066445250070741001d4601441001080080380720741d141e60589650589254140c0c0394900d20841c1e142210303800c010812203500e4420307050414150000000e42c0d00520a0720506542c6100554261150000c400001c0d = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 13420609 1250 13419359 13419361
    0x1030e0a03090b0c10150303020106081c051c050f0a1104030f06020c07030f0501090309060306081b03070b0706021206040c020a0609030c060203090624030a0f0f02090106020304081005040209 84
    0x2c4004030307015141ca000130004070703165100e03251103035001e99002d40c41001c6400780300ca00400905d80d090061400502854020303181135082100003402178140c5104078001d20100240314180345c04491400b4886c18010b41c420005402e00d540c001200e07a8054504103052070a1131905a61511024220303804c0b2176020814510001c00c980c1c178140a5004110340c01e04500032501c000012840d00001501e019108600004001c185440c0c0603007c1c40c01900f1620401d4540407061103440c400145400c041c004450300c6491440c2172100080c40c00c1001d4011001d5018049060030411511381c000c0c04d400342ea42d05e0322881c241d40f10401d201c129400c8502180040e400510280080b603003036400700196600902e04451802526150384069034000d950305486a4055010030401031b02c00c0304155440c0d01d051144007c41034030000001d65035504030401034040500c02c650103040080b500d0080ba6160f070b010f050441c85680d1601c01035200d81142c030a80c1c1d4036000e280006030700203040e0701c1407511466000707000c1815 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 13421859 1250 13420609 13420619
    0xf0c050a0507020d020307030807080a0807030b06030a1e0606020c010206060418080d0204030f1101020c010f0816111005011d10090b060d06032321031b0307020c01030e0a0309 77
    0x6031543c08130080e038150090380740c048041075540e401002c100d4003400b4119a10080808014a0100700a112808042c589085244950351703c50440f500444a00b0010400c032500105120380036929420a90001d0b180200005030b698001c2001d0485000036000d9078030742c0c0d4070b140600060302d0600c4240450499400a03900002e8400c40c09020003190100c0010304041d20f990b500340c920603590206850401c81d4552513021580d0401003a090107a00b032802003400206010054107507400900810003442307040076003c11241c03052201c2c1c0840180181150713a50309c0c0b441c07040c03002000d0a009410b400142c039850107581e0306880e100ca50041d210b408030358444030300e00410f200041c15081c411950052040001c00451081c1c0e000d09400303107008a04511011005000d0043c25190308409040541c2000202102d0315540881c00203003100e1100703076641c0c0d035503400340ca200d101c0c505221005440180801808142c82d80090840c0c8091000c0e2010072805980b0110707076030345107004100100040c5003c1c0041c04 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 13423109 1250 13421859 13421869
    0xa062907030c080310260d11010b13020c010506011107050402030a0209040203090709180804050405090c0306010b0d0510080c040902040209030106140f0103050601090605090d06020d0f0c050a050702 87
    0xe0181e0091a2101e0a54110383c0c4243c2c00c0c1d4400d807071a00d04031056200900003c008107801103980810328060041400b243c41c0042e4a803000c00c4940d030140840045d1320106070f42c0a401a18503114010481031100c066003030581c00079004028098550340c601000580254003d142c821303e21101d480003040301c0340c902020003019500003441045184e40912a881c0103884600156004000d0030700500140c50601c03a2100442e034007594505101114050180d02003045c80d000c0b201030b41c000b0b66021545513503c981080c40c0122050300e050701480b80c24000a800030548000d0107010a20b104284400d0b100d00302c0c40e070010800c0f4040d00703160340c000c0f0f01244540e01c0c0036882001c000e0b20140001d410403040c0c000007403c5484541c0600d01e01c0e030046094150f5440c4c41244060350010900341008507051140000b001c03e0b00030300410b406d004c0300080d40c000568403409104c00950344522f056641d40d802001c40e401410003264210142800c200f02000b0960260b0250380255880c1c1d510642050140e8003045 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 13424359 1250 13423109 13423117
    0x8060f04081207020109020310051e040203010902060c03070c0b04030803010605090f03010c0203070308130b042004060609031e050d03020d0603050f01140109050f01050105030703020c150a0629 85
    0x280e104104126600c00b40203400c0046200f0350b02a0000228000d4600606040803015040004400e280204100103240c119045042101d0454156500c643d12440070900500d000b41c03019600a2001c680c04600100000046c100240302c4d01e5001d543c250780f111b090449001c2ca0100500291091005000c03182c0701342e010f0000090020581113032003143c100428211919141c032080140c00c005071000a150b007203464250405040d80c4001c401004030384071802e282602a0004040d8504d229a050342d255121a43c5041c9020041c070400c502562000d01030402440c0388011104150009694504803040b00042102c840d006406000c0a02c2180d904400960000c002814000d81d25000400401c10411640031504c5e0110b00002c0c0c2020580260000e071001640000c140509140410503007201d1a80b500d81150002c1c20840e8803a1901c01055000c1e01410415010602c900742c08481181c1508400303a000e018668000c001a6031034044540440441322001c2d5200340807445900d03c00040c0e20014 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 13425609 1250 13424359 13424363
    0x603020d06090302160b041d04020d03030e1f140702010e060103170f030108070602070b0a0f0c0204020f0c0109020907020d0c080304060e0303100302010311030108100902040b18090601080708060f04 87
    0x59002c91943c1705101c10410310765007103900b00000c04a401c0c86042c3d00e813520442c0d850300e403595412007031400790700007075500188040003010542c8030010490121400c0043d0010001c400040320030f002c1e00c3c07505820040040c00100c044881048010520480c0107101d8411a0000303a001343c10146c1c20f54403141240c960307059090312110700800080d0700359030b201c80c00346010b444404040d00c030003454100d00924041181e0031007002d2410804c910102140c000d00b41e00211445404c1ca40b040308080e00020b40240602e096a03d111200081c40f030111030b0042d4841181e0038422260000302c0e40307500800701c3c0c1d00e45468043c40046103004005901041c000d001450340f00d03100c0d07940454010000300311035080d81c009940f0341600807a8030f103040c001c561b018052100c000c2c500005c013608541c036100d480c1d5030b50000140d448242543e50030514065480e40c0d00f000602d28005060080a4825408054040c21040b141407046008005c000300311040c3c0400c4c0c1c0c03822103c04400900d15074031044180e0602e12406441 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 13426859 1250 13425609 13425613
    0x31303020f15090c0105031014010516060509100501080a020105160203010603030c1101050a05030105060306010c020603010621020a02120c0c0907050403150b060d09030207080105010308030115030603020d06090302 94
    0x155080d5400100940321403100240202c9034a41800205145424240480c05060080900800c40c04001042200742160480c2445496102440c80180d401f44a64840d031a1441e4900c3c80f41c3c03003800f80c0360300000d0203608100103c41071074004640d44400c4030004e01864409400c00320024000d90312502c05050000f0b03900401c9610300815500003400c44885510807008540004010780c1800760300506003aa1080038200305182001c1100028111700c070500070588140c00200226105074843c0701d030b203e04031b42d010309802d0b035a584942c0080c1c50001001c1003464011407000c0811100300c920300a0f6081204e140d002000d00301c1600c401914980c10249000f06039118010300c01a080d546d80180c14000c00c450780700c01d55501c0c00c5050500400d541c650700b10895074100500d00c40c136a05d401d003c507030109450010010f0132035602e25040b4200070719030b400300425600f0b1030000301c140083c1000950495103000e201002d006401481034090320f10302d00c07004e948840c2c4025554085a820303080350702c41c2071103481 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 13428109 1250 13426859 13426873
    0xb1b0f09010504050402040e01052106040f081b010e0c0a0e04020d021207030b060909060405070308160506090f1e0a170708030a0507031802030c1201060b040308070b0a060b03130302 80
    0x490200d070030681c44100b0342235145004004030700b030010f003a036185070140070800c407070340c403d81d00580da1000f02030402045820b120410100b40300d040b60035218842d00c18503003081252101e20032076018000e112607405050140149128141c5811000d200c12030361519a03500c1036940743e4003001100d80308520180d070400d00071410003611200c01d001c201c014503c5900c1009440c100203041c090200070040c215081035101d0750904c4041580011020100d0794043c80ca1642c6055040312508207041080c002001d07481500305004840e403000c0b846189503210f006c115428019080d9507101003000b120740300415a008440b003080411040d00a5444c5882074110192504006541e030b8182940215440c40c029a910810b001c0c6a660600034038914034480000c0c044c014049800290704c88501c40125071295a049081100c000790a4000c00002c1080301c000c161030300d03074904001c3c03003e50020600301d500000f13050010b0300d112440d10581050351010030b205420740c3d075200350440035a81c03840c2c816405c1d071190030 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 13429359 1250 13428109 13428119
    0x304080a080307030c0516140c0a0e01031412190905060a0201020702090c09030712150507020d030c030c1b020a03020a090f06090903020c0d030e18040b1b0f09010504 73
    0xc2800485032151400d00e6807032504240040440303051481d60f40400504100c88555448003010081c091500180b041505402e80c03180c042c90b06c10104ca10382c4c0c00c50b104010010310140c5910410341200d008030210415500314203206038998480300c02d0351100e070f0801c0c020340c82030440284641f40041c4150412420340c030348600018150703402140106006030740000da845c08509121450300d400007402d89050b42400382042c0000e8a0314650b004156848080d83c010805004404501c586a6240c90208101504083c0c0000f52100e13401482e40300400d0400f0510003440c0d20900c100c405a00790740c1d0b180031060200d80c0c01103a44020201d400d0768044541200440941d413880328002c001c3c0200d0740300007540705222002e00182c40041c0d01c07549600f4a801080c034080f81c4c0104204011072030868502185040e1481c050702c1000c400c0c000c00e074104c003148900b1144a40803082c1c1a00441c0188d0810360f10780d0b10b4070009000300e81480b10000380d4240038010b12000d801da010141541450504280b414180c403a = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 13430609 1250 13429359 13429363
    0x406080c040308121510020d0e0103020403020603010807210203060105010c0602071202010204080106140604031b031202010f0b1e040f02040b03100f08070e0c03040c09020c060907050a060206041103030408 90
    0x20340783c000749020a02400100354030760803d554500e0042d201b80400b94007004020351940032580e1010244150061100150b038800d42c1100c0146900514880e01e9503140d480c2c59a03648128082e09030055400384c001240b00c1c40d0040c502400310750040052110ba0700704401102c0d185484141103a0641e0248102000100e00140107050302020b0390006850b40e1500a2007801d4400366070102d150701c04a03200b03200e01c94441e00101d44c2070703a0304000300ca01d0480340400c1c40040803149034005858141409034200d1b00e285c0c10f40001018000300481841200200070422207112a40c4484840c85042110b0b081ca15052070340069442c130700c49200060a155460804011540c012140040a02c0900d0301c18000b8407074800f5001d001d486000000c01b00c10741403502055285901030a98982241c0100c002420851016a0100039100d8a04190f44030304001418551350700c410b4420751400e0003520404601428518510003c450300e81d8018900d94545071555a0311a6484c0c010a8141c0020400441c000d241 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 13431859 1250 13430609 13430617
    0x20702041404031707050a05090405150603150a050603010e040609032006090609010501050d24060b0d0506040c020307021903120c060b030102040605121005040e010f050c0c030406080c040308 84
    0x707030319154003a0814008010f080140146200300381b0505210322203146a11105031003416005450010341e0341c0701d200300f001d000780c040c0c001d00d070303000c1800030400038112a104e0443e40c250000781d030780c80d02850b194410081c00e07020900680d4800850301000901040044d00096007050203402c001c814002902c5083c102c2006501c030342500c60744100184204d10030100082c940c4189160000c004d154142800120320586000003d8030710740c50f4180c2c2c4c414000703105400c40e0038050800b80800503550741c1c00f40d9101030b41051134003a4030a0300d42800075080b414940034980250146602640c03410340350743c2c00c202041300c0c10100501c00d0304225601100140310f20000c410316511540f542c0100a900d072502e40142d502d01c60f4814000d90051100f0802e4a4210059405203190302201070710036522500002c01c146a0780d4030090703110303003040500c05119106500c001d5000c41c0d0040c1c10b00c01039592040050081c4904264400b1560041004003c00e40c440c0e80c11a070030044030700010340b0700343d9a521480c0003500 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 13433109 1250 13431859 13431863
    0x305010e0307030e06030103030806010f02030c030d0504150b06030109020d0209030609031b0a050d030c0509030a080d0b0d020619050412050d0801081603060b04060b04090c020705090c0d020702041404 88
    0x40000b58180c1410f0304481003518003002241c86038a10740c110703038000300b0f1545d001d0841418461403560b1a44118024400e03580041c44107001c51740c0301c0b0705070340340c6c00060b2809940540d003290001c0314a440d001801d0050382600000501311900d180d2804c45034400940c0714031030700040da65007840f40c184503540038000b440c05460707800c005684072035000b0000c003c10001011310001c1c61340b0034045d0350300207100440c40c580101540e007800542c502d0000820340d0306214100859a15000f00d8410804002110300517140800a0fa101000264115070a016600102120103035220006100c00100d0b103401010417000041c0f036242c403030b040555540d025001c0400003017003100c294018074107103411140e0103903507680144501d50051969030071346869440c607407695000103041140c0b10080d00c1e901b52a240c10500040640d0785055994580c2d071050075005200e504c90440c0180940080003130b0a10785002307124082c06020002902c1c2229403440100298001c0f030f030803600543c0307801c076425002c0c2d070324070711103100714 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 13434359 1250 13433109 13433113
    0x1406090c040905011d0c040e060105090607050a03090602070f050102070302041508030f04050405060a0608070f021c091706040512030601020a06020403060c0801090509070509180601030c092a0305100305010e 91
    0x740300240d070307001140c03004006c15030145060000300f010a6082003181c1c1c1104003800c10310b95543c04200860000c0c451410003810610603510180d08056002140100b00c44403030307080c2c1e030b41261250041a0f05107103522405005902030041400035240ca0303440701400900360302c968648550b4400b001780c259008800c41410a910102e4208010300300307409002d602c00d40444807031103030504048003e0482d84c0054402030420003000d0950041c2070003003000342480b0034a03192919000d2520403004001c0c00590207255492a00003550559500e4001140741c05640e2040203040e00441d400d28440c06900003e1809045100c1c0008403c04217155200410240d8001c450100f502404800081c25642042c0e101189042c50700702080452040460004140c0340d0031900414151901c030214005142c00001d1091240912800041001441d0320460115440c242d024040902000392256801c0d1030300003d02c2c0f000c40b101c084203080500c030707602c481e51280034070b0300b1030036810f4580d02c0d120f0861f414503038500b60039 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 13435609 1250 13434359 13434389
    0x1401090507060f0e03010b0108040b090106030b0c090a08070803070b040501021c09030e09040b130204090204050a050105030f061611010f09030203030a0b090c0904110d050702060711011406090c04090501 89
    0x500d612142d89043c8001c2540244020b212079800200340c00001800a8079840c1d0bc0800708000c10000e4001d0001141c0011001000e810101c507540c88650000c104584541c40f000c500042d01e20000c2411400c40301c0c800080d600b4042c103a02e0342c076411000207000700d90340d5508000301d2410004043d4000e282d40d13481400004c55140c0352030080d0100c03e1142c0e41500c58401041000300096565241a030700900002010042070202d1001c50041e064881c2c0007503226080c002040303203110045c1e214a048500032021600c40264024003142c5550090312202112969481001b800f980520020905500508000100000da03000e100c0103c0390814030490060700b000040c0101704c04240104074440d841110440034600b406824a0024415000c0c07841c0900e4845950110365515030007900c143c2c2c0c540203810b0142d8606500c00a440704001c44010000c145050309030f0074400b10502c0303410140c0d50350152070341c0030f41c40e46e204100b480c40b80240400200201040045a40e02403400342900818181e110780c559 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 13436859 1250 13435609 13435637
    0x608070501030e0f06190f020304080706110705060f040c0b120106030507020c010504050f010203070c081507050304020d170405120c0a0611061306060b030114010806030106060903140109050706 85
    0x16511800e400c11055813003410350b40c04c641c40c007040180d0032030700c3c411140540800180d4800060070000b075131701c651075101100304800e000054000f0512075200344403c00c900c50001a580c0414012094044d080703500000000b040c1000801c10680c119001e0110030340d00954440790b8001030342c4903040301d42800104000400109406000e401c0d04030803070380064104402c00c8000240f89010b0381c450244101c0300c01100240036402482120205504103e807121000e8450f18020b5580c2c1d02102c0c0c000400004c400016540c4e17104605483c05654010030f07505907252031382c440030003a18240b481703044072100400002806070303288204202d40341440e4018040302803145080194024055100f07609112040017001c0c2d0007040440e00c950310a03001c02402113000b1980c284280201401d03000030180a00020003c1a4203106c0b071055205030b034090761144203507a0b4040500d401c1e981207200c0c14012a8050310305200007102a01c03200c03242d141e2503000050344003480d03c0c0c0f5860a05a5032141020440030b03141690 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 13438109 1250 13436859 13436861
    0x309040504030509130605030a020409060f0207080406080604060e0f0601020f010e0a05060609040305031b07020d06050105030607090e01060509030c0907170a090b010b1b0d021b0a080304050f1201060807050103 92
    0x180a89174040d040080b503107884040790f00d03142e0041c802841181c0d181500b13403c0001c01d0f8400310144030130754411510b4580d00d14010381c0c10350050080030041076240000403560300d4540685826140c44060340b4496850728030b08c02c0203900c0c1c0500480d040d40503000c100784001d80c09229400c440012040103048521460034041e09108024040b40e00a805040420001c80e401c1701c100c0e030300109400b19614046d0758444108030b00b0700600a009500107084c0350b0040a20450780c00c402e0598100b10107903603035504d5480064a07164600e22404040080600040082d940a0b40207094480740190a58203118140000113001640843d10000464a40407000c0c3c04030244ca20115440030b1900400c00c1220043d0302c544010101c1481105004800051200b4419103016065001009200c04440c02c000c1080700c06922442c0000782080d262140c0071400c1424030303002c03410408484c803038005903203000c1c01d000500c1100844078007000e82010801ea840317007580e0824480c0500802814000c1d00c1102c2c14000014 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 13439359 1250 13438109 13438129
    0x3020d0f060b03070e0a080601090501090b0f010212030903070804030c03031106040c12150f0518070501090311010e03030301030302060103061121060a08030a0903050708060705030114030309040504030509 90
    0x24401a01c0c007441481007034103810449401012504000400011000000300d070981c0e26045182c5c2800b45d071000080c1c80c1d480b5040340c0d059a991207028840003a142c0107100101c003101c0790160050344500c0903500c407000f60800840c0c0042801081d213241800d0f035151020150f10980c0b040b541e44605110030014182d00181518040c42d0f038801810480c1080d0300c03080718260f8907000c2c5100f200d10300d802c135004012142103082c83d80f4060b50401e00c0b00c810001c00500c01080c080b60b80c4040900b80d02194400700383c02207110030135104140c494081c0705040d519000005c0c1c07800c030210350510603c2e00115629940c10000342d402144645e00a00c59503040d0314040301600d144800138054143c0921404c154100b00c140f690400c0309101c80b1191542e95404002401e4042c241d001100b03a00001414084203907110790008192401101198492651800a03950b1000c0c100c82520000f0001e00041c001e1049401243d140040c00604480c10801c10000040486405071000c4021520001d04c0311036074200b11680c1 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 13440609 1250 13439359 13439381
    0xf150d030c120504030309030602091c060c030605010504051311070204060e04060b060301031a06040906060801141f0512010605130204061106040503180d050a350f070305091003020d 80
    0x890b00305072450b5005807094147e07001c010b0207680c01141e405869100c0d05142414a0709020105161780514100701c4001c0418040c0100080d090410201d002d50107841220100c1e04050840f450840040c020307617009103d00f1047d203c2141e001c200c1940960340b40d0244901510b401840c0d00001c1c03c040ca04141189c0003005018007c05050004001091f0031030301035901c4001901010f0642c2d0780e03101c00a001011000001802c0900d8031901252800055002c40e0f000d420303514807132001c1e0300e42e550304a8450b2140384094204100b400030a02036800c00c200d41801c0800c280700007080b020f13202d01c00a200301d48484c118040841c2d021400700301d042c0d80f15514402c0880d452000d0086c40c10291581c0713850748161051400c00065658070640541c861100d402c107080d40190546140c0d01262034030005045010b41040030080644c0c1003400c81881904002481001000c07030540f0300403031000c1c1a18036800044094050000a01003116191502c4125140c8000036a40041c0d94000c0c001e944403c4482070320321 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 13441859 1250 13440609 13440617
    0x30712090e070507060b0319052107050303060d1e0501051501030902010207090b01090306090b040b07111c0c0b070201060906090b03030d0e010612060b010909140f150d030c12 77
    0x3485405600102151304c2d09400c10030100d40d410310400482c0c680030003501c91411911321721602400340003011940039000028030b0800c01590300d0810701070b1241d019108028043d07420400108009140100740300e12000c0c4100242030760080400d4050b011298501815282039444100304850381c104641c1c580401002402d0401480d003894000039036078441c6009841e8100c1d502c5030728100d03680c000c2ea5031000650740114180301c0c420396807034190f80481042c0c404481c181000e901045056000d00741400100305004001c107141c03210b044041d20f0b058214040d40040c41026481103010400684086104010359000410f0351460507400c02c0440e01c0da6403080612a180000d0500f0581c1c0200480d000310302c4960f4040b443d646094611801000300c0c0d44040701451043e1004010400c0b542c000300d2040109032164880245c0e0744d00040290f900208910366582c04540016080122016000740c015400c5000d00a811a08001003007a2007803106c1c0076400714075010480010449240c1b80d030070070300000d803030 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 13443109 1250 13441859 13441861
    0x105070c05030d0b1302070503040302180112080d141503120307050901080a0f1b1b080702040c12050c0408070b090307030201120b0306040b010503010e0706141b030712090e 76
    0x1d6850b1280184100c0c01001ca881d42d0110105950308404800c0f000c0200d03008540d51f20350340c91301c69901c1c0e10620089008110041e030340e21003a510004010304071488ad4031603070300114582ea0b5a20040d4011070b91080666660f03c8488040325856150f64402c5030900554111460a0000c15281452003020305943c0d60b000c10800c0b075003a9200c019208410fa007800d0554584d241c0d90f0148001d040b4564894403d980313000040410090301c01c00c142c00c00c26103604c482802c90a00c184550104030444000351044c001002a030307005080ca50b0000c145150700d807602c0c0c0c15040e13192000d54190385c07050310301c43d1441038003260034002920184440c100510182681c01e24050094000c2610340d044c61002134180b0004034422a80d1040a411081000d000142528103904d00307403824106802c800e0040307601a42c80c01180000708040080c40720255066901d0341c1e01c00c0741a01c998198958054140340c00008144401000c900d0420005020801c0c801e10401180000c14440200034280b150301014003819050 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 13444359 1250 13443109 13443113
    0x3013002011e0e0d05030325050906090105090d080a0e01080108070521030a0903031b030e040f0e06010311090708070509060a1e0903030306080304050603130203070b0a03020c0105070c 81
    0x2404225694012600070119506460685000480100140d04040041c0700c2408012003c002144981e0b6002354182c292840c100d080c00842154a00010104008008203e15880c1040107440c07401742c1403502529003612540820039003880038078115491032010550b01000c039041810020034410a10380401c081d0715001c9e240750340d481c4030320605015002010b20202032852036440503000329103620072a41d4502c01c5180c000c00e015660311003134001420750070001a8000e020a5011345080d003548d03a640e030b40d03840041044000c0c4845144034000326070b52041084a0802848160b00a5015142d05462407080f80309001c50040004c11080400c114203040110040e085419100c010f40265411a2100d801003401e94070080c41c083d282c1a04980c1d07545940c001380e40030813108140ca11130b540070300c00d80ba601e40580369030780510b01030b441c2c2c031410034000100071303090301541d44801d1800101183d035803135928202d4221680c050759035200005c1c1c000440b03a00341c40c024042c2c250008414944070002c90001d03 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 13445609 1250 13444359 13444367
    0x110c0d0215070303020702060408070f0f140909030d060608010e060301060602070b030c090901140a090209010e011103041203090f210303020304061d0a0506010e13020607170301300201 81
    0x800c035500300d080e50105060b014140b0a5060f01d4202d0350140c40703681d545407624012075592280303120b601c59101852401140c0c0d0a038174404c9004480c3c00406150301000400304010300a000144045440d00c428000c2c0f24003220980910002481a91a840c209505000301802101002800d082c040d83c1015001c1010741c1e030001e0007000b00c55807004060f450751031755074400c480c500c40c0c0090982d1014100e400070640c0c2000d140c1040680c0c004540c2e403443e45a90712114420b901840c26441e0100b100302a42d580e65500a00244003400201c406607032410741c4540e92007084610b10041a40002c1c0c07506814030111460001203c082d00720b042c440998400c1c042c00d6140010a20100142059000720200d403c102280e003290300031440402c549800c1c4c40b64190180da4541da41201036680c0d101303407000090555000c01c00c160040390845501c0740b1aa0b0f498007800081d50050108071903109034400d118081c603865101070760127000c0d00c010764001c40603c140c0c04810f07003a510030203844017544458000300613a00 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 13446859 1250 13445609 13445629
    0x10f080a0213020409050708060f0f1f0201060f0909050f06060307061b051c09050108040803010b03190c09060314060d060510050d060b0315040f0b19020a110c0d02 72
    0x1c121034a6501d9107240d81882c010307000e540e005650060a007811b001d80a904089002e100302c0c0142c501c0c42e50714075030104014040440390711a6820920300020302031040c03003000c44441c401c1c0880c0000b040040d5140d0010048000315400420301c1640d4060000030017106224001d00307001500003d2681e401c0000020381c6610451050b6800c1c08915525600c50920015070b07000002e42002c02c1c1c41c0c02214481482a0010f0001503490000b0175005000c1095802000c1c1c00f8021504003161a0840e824440c505526a05c0130701204840b0a58003c80000200a03000b5420001c00036604c00031214605500601510348450030124448800400c110094645180c1600c0f03550f08958089242d0f101c0a2181209101d1a000540c21003000d05603d428003079641c00003402e20405500710303032030102c0c0c0042002109005590043c1a444102081d40128071031000c001d401420030341e80400001414031941c0308a90103807008901107580180c9003d00a0414040154100000c2d42c445001c21481e5000654200b1 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 13448109 1250 13446859 13446863
    0x901050a06140315030109030201050711010207030503010e0402030106030507151202030105060304020d02010e061315030c0503070522080a030206010902030606091507020901080604060c031802010c0317010617010f080a 96
    0x102200091000d0340142140302d2074003005d030003003005188a08009004c0c0004482e0316000c1402080b0040b08400d0520807290b00c1ca4155440ca42140d00788544170b03a0400003d00166815926000003201148003030000c4001845110244698410400c201824044074410a003020610500c01080070740c49401c103c81c1d02c203604841c1c410302580c1e6407005a43c0711040a200907000038010401700892000c0324407440c01c1d02d241415200798000d51920450656030403044402c00201c0a00c00300300902d000c0c3d0040c0458004000031480113030b020814040d20b48184e40d000c040aa032000070070000385601445074070f014001c0d9003425840c40c9401070104089200e4030042c140180000c4c1d0304510303080040000d441689600400112041d41d4a090140c2c0d140303002d45054a42c18500380305a100f43d8080d104407501c82c2040500b11420380c1090b0010345003099088400c2d400d10070544920b0f6014145a040a406003a640d11742107004903860003400b00182c8140c101e051082425441407040c1c04001441c941c0481e = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 13449359 1250 13448109 13448147
    0x60609040b06030a060c030204030203100501050a0b070c03050d0e01170106080105010f020c1905031504170f071202010608010c09050303070b0c0c0102040f05010f0e0a090209010e12010b0901050a06 87
    0x1444003000b03e490320610800c050701d581e00d020714080307807240d241d00108102d9000f20120f6601d11a100d078a50121b0700c080c821654881355800d0104000d00c4018041d02403c3d0150440440345603880d01e450f03050617042c4501100042d410003000c0240d607000030030348400030340076002890a58100303607014003000e006019040c14001c1c9090300e5031007030f48204a5201c0050014002d0405041080225a001201d60280742d00c81c0c01348480308840180c0001469102e260010985d4180a00d900d441009a03404816211360800081004034042202081c81e5940b124041d4000a800d6140ca4080c0d42101d0a03560003000b04400313102c0400543d900002a55080d50708002e0007a800c1d01c035030007018520700c1503005500c0c3c41d500108000401461401c0b441046076000c4c0c85100c155540e8003402c80d4102c0b42030000942c0a01516000e000d041803941c007902c01e29034181010780c40c8411303c000141190b5814200c00720503070b458914080701400c051071000d0050509440d807640c3c0508054000c0c290303e07240c1740d10017440 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 13450609 1250 13449359 13449361
    0xc01030e07091407030c050a080402010f0e04140406110403050307020603150d03020106060207090b1e03010b060d0605030c040c0915090b0f0a1e0509060304060b04061511060609040b 80
    0x144981002442c00740c0c401c201c80400d0310100c06070010226140800703c5e1600c9066041c890041044820f20102643c602c00799035a640e0043d25003103c0e111100c010098401c400f04025242c511404484030a000c020710810328182c42d1180540744a40d07c0e02c41a800280b00400c0080c600006035003e4540c103c0f90315849581c1d050a2520161040d180c031544208800401010f143e010751101c41070310b2442d4295410319844045072003d0307508041d039041c4c2220010300020f40f42080e0018103101030382d0050000c03440061040c001440c64000b6600c0000c002d0765001c041003e4602000000e906800c10b890034400e00c500c00340040c20b212014890f900c1004409903070028030350700c11005880941172910b42c0e2510b400c21080c8000d401c1d0020b10640010841503071146c142450316540515900301c0c280d440a24058451040c02640c3d0030141046940986130390700001e055650f4010803000c3c1543c21820310a00c640c14200410031182c5030707c004541d410400c18841300b5250703a0701c41c07640103401c01c1d5280d0365 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 13451859 1250 13450609 13450631
    0x31605041d030307050c1011070f050c06340809060d060503060a0b0f09010506040b0a0903020301020c03070203100519090f021f09050301060e0f061314041e02030c0103 74
    0x110000ea07014809000010410540c00d421402400f030000d9075500f00c40c5203510b215580b01c2110302c42d08042c0003002082c082800040c03000720154002720320540581e0041e481c1c3c00d01140c0c054000c5402c5400794000c1d244080400d00c2c03071200b03455480c41104c4151310000040e444804162240c2a0200e00401c0d0000e010f81c503c480a03040f44000b850007800709c03021413403c0207015004000181a1511803907403502421024507085100034140d45d0000e10062030640b82041e5002d05901c000400e03000d0012804000026030307020303c05000c1000c02d100203140d840706244101424140800da5641000f45000c05100805890943e06060060320400c00600791006040503140ca02c8000130095000d140707a04540902c0300c4420b540754a0810688402d5040b0f500c4404240c240c1b04c00f0300440f0a10a14500010751a03484207482c0da80140004e0580c1c070701107110b030034200d05a0300301100748100380d4880303c01d0204000720094001d030a606000d400c0c0600d0a4168006611070f680c1c895003074105500c50804040b = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 13453109 1250 13451859 13451891
    0xc0a0c03050c0303040c0e24010e0102010e060f0a05130f020411040315060305060c0f070f02060412060b031603050309360f0a0b09040b0901020f0c06041103160504 72
    0x9071002c140c100e03070302c038030702440c02c0c41d07010219004108001c045580440c0e010302140350340200e032243c61900010203050301c900442d1814002c11005045649a002d150b45000b81404028060096603c1c000040c0c03600030710807801d40e000a081044403820350b8403c0e05c0401e140c0c152041c41c480e8106c0f4041841e0f80300c8002ea44150240c1e40000c0c051014110009505410692050048a06c140306560b450395400c190b170318031401030380041d0480100070000d840015103208840d0002503c02003800e42015125206510700703c00e80d071400c6075295903900880170289000c0190341043c034411005d00c4000b508560307400c0d4481c0105440c09000310086011484a041c0800030a5888840c403039401d80700c05030209001c6004c10003640d001c8001032000700801c2103070071280641d1321082c40c0940000100d8a4aa684c0e5503128030040149110b035500380b001c08a04240c0200510b0025500c1d8000c00081c00c060401804003081c010889219601628102440243c05250030048032001c442c0002ca101e140c3d07905003 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 13454359 1250 13453109 13453117
    0x403050d061203080603030405010c060b0a03080309030307030b03030f04090507030b040f0b011b080a050705030c0d0e1002010e06011503090507030606061e0804020906010c0f080301050111060c0a0c0305 89
    0x14494140703603000c10b4100c50302041da4031050183e40e400c042611050181502c030f1260703000d01800249403041120101c0d0147d08a05103082001c0d19912172607641e9229200ba60300143c0b200440c0380c00000600500d0f5038140200aa281811400b441c500341518103901c1052146100d03030b1700c2c02074445000800302c45c003a5008140e40100540140482c130b0400340d8400040062055a90204099052105152250b0507000040b10f6010550a10b0089024070680eaa03400ca410216140e100c100000f054100b024805120140515110b10080c10702402c04c011009041806c04421689001c00d2048100f500041483c1100c80c079054860009414000483c00f608031050040c005114943c0c000081282c16800041283e1a681d00c4c032188040b098010555403820500070030019100760041805031034500702e40340e084081410000c44140166031200d005656a0a0a83d0420f801100400003540c001c481030710049a400060511460100c1d4600b074940614240b50b800c20121044950406015508407 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 13455609 1250 13454359 13454377
    0x30312070320130608090703030c0f080f09040501060302070f141002040f090c020708030702060a090504090b0901110a020a11041104090504020406060305090c0405271507090501020a0b040305 84
    0x56580703500b041e08803240743d40141c0505034921038010340090b40520805003140144e5506000d460380928544044440000700082526030300c0120400c10700144140b0010500036808080650720f81c1c0131700c03082100701c88050b170012040c5401000700d000002c0070040842d403180d80c04610840310341c0b0210946442d040c01941c801c40b00300d20025004c6210010901c01c042111410181801000e000c2c00301241c484a1910640e80791703510074031500005141550103003003080d00364074004c0c24981d65040000d040c0e61421034241c8400468105101c10b0006c2070241e6010354070008280c03031900d00d00420095075000250310183c2000c0040361042c019541d103801105500b0382045480da2644d80b00c410103030007040c0a8030200d20903490004001001c4d4041d00800e0b10420884018140740d20401007404040c00d00280b00a5282d4030341e190001000420580d01442a507400b4010200d010030343c1078070a0050800741c8160305019010004005580c0c2c0050030a950550100b8600c8a0f80c69034034060310280500002 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 13456859 1250 13455609 13455641
    0x10b0402070c030204061e18020f04030609030206010608100b0309030c07260703030516020307030213091515051509090408091807050a030e210403021002010204050303120703 77
    0x3454007405055103580b01a68022103040250325640e114884000079a0a0440185070a107078041000d90f0f40c00d40b50281a030f8504030090710f01014000b07641c90310707407241e001180d100d60384400042c2450380c1085030a0142c0701c07034207011855040007404240c1e61201803207071008850b00080042d40c948004d005031240700e1604000c40c0c0340991200303412080c0c5510030b04080c003d4000320b0080c0c51422400248881200c1e011b48610340303892001c400190070510f00c12030a0360036214a4200000507120700640b6245107061150004000799a031409041c08811540c00640031400c3c4100c540543d4006112174089581c00c86214400440c1d00d410708080f400b07012a65a400300104003000140709402c0c004054000742228416120140c01e5078110f4421005d856040018005202c500d20b0b99029600c400d110030001821550f503c884046c011800e10040070042c01c1c0002c020030300300110b00b440c5002c2070b42e43c192070009606003400e00d00807070394a006030b82410058400c808089040107000c0e500000e06d80312647c0e0 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 13458109 1250 13456859 13456867
    0x509040906090f0b06120105060105070201081810060f09200901112a090702070e09030403060e0c0a060503090d0309020406080a0609020a05040e03030c0717071104060506070b04060e010b0402 84
    0x200203251301c0c003c45d681406840c940303141c105500418803802d486450161034041c24500c40e5001181c2071030000304001c03610f8009118003d0000000c02c00ca1340142000c0c2c8000c6103031806d00c0f001e040985255440744641c039041c42c441034ec201c40ca0650001208002400e2551900741c0000100d45a4021030301070b00700c0d4080c40c50441c0d0b40303c2c04220742400100e000c11041100b001c1d03243c103000740780c030342150a60300503004104180128200d41101c0b54000304076004032810325840c1e0f00e8140460b401c00320540b00c9648480501c0103241042440d250060005d801c0407411403800e144201c2c0c480c1c0030305002c0790800d5038525108007159138035031142c00502607442c2202c003100e404c0c3c54010014282c130170069100b40c03100000000e01d031a15024041c0fa4002c4d88002e0750968440540b81c11080c3c000c8070048a5400d6004090740f80f03540207402809105010312198103500c80c40d1000e100403911683c00080c01140204420004105108100c3d9005540504009100380500140c40d00401c078034003000354068000a = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 13459359 1250 13458109 13458113
    0x308131508010501030c090302030a0311030d14040c0608071b03030204090e01090204050105120705010e03100c05030f1506071101020a0b01090e060a090201170403140304060203010305010b090105010509040906090f 94
    0x15441c030b41610003c1e2410015105000c205846841c1c0c140b0009500d5401030700395000292040940c07414006036482124202809081c0060580340c400940ea00c021056008100602c45611986030041c115400d00c1505428160001051440e030803240036564903484d0292000c042c0b00350b04480042c84150420041c0480d035038060743c049c00850b5010303846581446c1c00483d40749020750700c5120442100303000b4101c0600d8240190742040c0c01042c10703039150143e070745466980c0c003040c0108100c545140d5605941ca00d08009038101c65a4050b0802c9240e80720600c24016944482d070442c1c039240d070000c42c4507c0c510341101c0102d10708003202c0c0d40140030108500c000136035108250800300303140d103452055030040da84120040c1c3c00c840504c140640020702c3c6164240b105200c0103000354000d4005d1414044c0100081c0103002c0d103520594085641c80d0b4000300420a00c0700c284559a1684800c40d441210741d45803400080141c0034003140184200c0e5100324203000c00010b90f0041640311b61150400280444038 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 13460609 1250 13459359 13459367
    0x3030c0f0803010f2903060d0f06050109020306030f01020406090605091f020303100509040b0708040203030c0304030302060f1e0105010311091e030706020304180504020d0b0f04120504050303030103081315 90
    0xd2260000c0980c0100c200a155440e959445508170f503181841c1e81503550701c10800011480100c410390300c482c8020b0521010a2403406458041d000d200740c0941e03070b8184042810301d0051030702002443ca9106000030300c444c650200c02d03134048400501c0c0541e200c1035500001898110b201540d00791400340d036410032100d42d4010024611405a0700d84444d8800d940d0b82c1405090942100d000781004006000142c410317000310507003034006001404490a0084211a40745564030075001940542d00c00c00030043c3c604620710381c2c03543c030040d91a0b03801d40c00e041004480320503401c18051035042c540c0f01e8400041028220061355010400140b0400070b61b818100d000000b54903d40409004c0e0286031008101c507070000003110216020240101c91040c0d071015541c00929010340101d901001156101010070b0001203018001e20304039640755506d05140c9068184140740c04001401d1100500c8104032503600441503038112134002c0505555200080820204c050841d08540000f0703103170248511940d0380c4 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 13461859 1250 13460609 13460639
    0xf040b030610031b180507050f040303090e0a09030e041d01060b0409050c0c060103060902030c0402030f0a0b15070303180b0f0a060509010f05060a02100f0c02010b0f010903030c0f080301 82
    0xa14812112110450207011300041d00d401950490080c103031a100c01080d0340c0e4130280e4003034038034a07286051400d0351500c5581603100d5030050740050390410050201c800b00032881604a20a107904201c504600d96005d02164110a00b481c422640ca4845207121121400341c80310380400c0600801000f503c844641c60150000e02500c0030603450300f000280b01d804c5040445081e00c001c42c005011700e0303203150394800c082c04c01644126054014440b0510301c43c1c8460003d50b010740104001046185041c24608089504d00110b6920400c115041c0110010092044400858141c54042041c441920a2a040c03003034140004106a4101c8108007002c030002100c2809515181000d00c4095920300800c0f005a03020300a01e00c07201901c106c100894600600200b004078524015a0450542031106104450650304080310158803105a080d8080d42031040902c0030200300c1c1c110f1341c51034010300000d0007604d03917000050134400a00356503020701200f80348040074142d01503d220703a43c1d82c44a281c90034400c2 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 13463109 1250 13461859 13461863
    0xb04021c051c030f0504020918150c040510140306010e04020f0c0109050f160608090114090705100302041406070206040306050405031908090607081911071a13020f040b03061003 78
    0x11400340184012181c41c040d02e401142c00600b106441e484040127440303e401d407103900b481c191052820029500048890b410700c07034084800510340312860207060125200b001030b4401c0401652807501c6030220141e0b010b40341c1000d07007860188405404200420000c1c403441480c00c02c1e607240441c1d08520510150000c0108030321410a0b2146034070a85011030381d50242001c00098a0300413072080c0500352003002b0181c0d00080800004c1600102901c4607207084900366035885203500040c0c0c0500007405e104083c956090002d240071840e0910b0f017403440b0101c41e0301c03007001031003541d00042d103505658a07102510081d50b0880402c200d1414645480d0750740f07502c403410215158860000b4880b0681c01610700718468001e00020781803540e54027001f1904000300810f4800810b40c0d00c501502d20096620074400715042c51200e19a07070328190304140400702c0018055903050140b01c1c0070010140f106107440e854a66050b80c180d407020b110a4005800f903e00700c240305416100d1042081168090112001c04a0b4 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 13464359 1250 13463109 13463111
    0x90f010e030403020f1206010603050a0603120e15090607020d0f0c06080105030705040507050d0e0f030f12010e0402030d0c02060d0e0109060506060a051b1207030906030b06070b04021c051c03 84
    0x400c60a02a00d5441b40540891a410000040002a000c1c0d000164054845070380000d403661240e0791040c20300c07040b9281c000015200207402c034081c00e0040901083c1d40400403182c1c1040b20700b000080581c429020024050100900551b00300028240c0c03000c0c0e559032002c0c5c00080b00da00c581b802040b5210910415100e80b0075800001070711300306031180034099031603681c83d140340141d810b08002c09810210031039165441200f512811641e411300240103241d07071071258140c0d20030107214039000b41d11060704440d002e080d011080c000140e8000a20340c040840030304024400312018000070788180520349464440c642441e4070614019010342c000f6070748620030740f010040b85d04c40006202181c0202c460801c0490300801c80600c030144c42c0745070b21007148000d400b1914120032000000318560410703201100031400c1507806001850309402103a98071901510428246016030300e4645001002074400303406030019120094100e50711500e0501c11a0300700044505407414580d00006102d0040c442900003 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 13465609 1250 13464359 13464379
    0x30703050706020a06060504050f01030b04020f04020d1a09010509160302130f06020d030902090a0209030a200901082d03091002030a121112180a030801030201110105041a090f010e03040302 83
    0x2032234144034484c0910010481141d082c3c2c29640c03034211400c0094410ba03409801a00110426604e500082642124046012404025040b034158080c0b10104426104802000c010701858440410381c0383d20502d0007080c841e24206640301500280718440b140780030408408404124030040c00707076a0044a56035800c442541128013021021500202c000030b61140454004c5070310882540c01a04014400a00390340d200007996803044031414142503040305171811001072161525040c00428010040b100c0900380d042e4600071401c2e041405114a20186841c0502401c4807404c10004e50320014130140c414104d50003200750107541c070b03004505a000006e100c1c01d017180c002c11060107412100c015000301141410b5035002020f051002c01022045440041407021000071810002d4422980c0203450303a1a4550450000402c0e1b0030001610415582c1844148400030780c0c0c03500e8854000860b0f032302e0611641c0728000601d081965141c0c49480542c00c0104c1d9142c08a00400108200c0784225002403807 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 13466859 1250 13465609 13465619
    0x312070305160f02030c19050c0604062c090702070e0702010606120506040213030605010e060f03150903130303020609011d0703060203060d120f140c0c010e030703050706020a0606 79
    0x3030301c40480b0003007010074000045852007402005030000c0c2607582d0064904260f0003455081c0350000a68000c0004103640c0104002c0c0318080c06101101e503001d0354610b241c40d040010140134078915003921160f400da0700107004040d0040708180707030303041d80000d00ca01072600f0301c294000d5841c41c1c0d501074400c1c84040c84011070990713401440f0301c4d000c0703c616032910560b80000c154410001c100c01032015400507000c20441e2224441031785a500614818003000a0301d504010307901070720346002005180038102854000082340d0b40003403201c1c0c0c2100403400640c0d1560b81c1c10100350850242c03010705548412003103400300c20990086048e506c40c40307001c0300030401090414450320720414109640c03103280d00031030402e00100718260011644800081c1450039110440e40d22844201d4a2620600c0042c9800d03500d072001962291034480000c022640c4c542c1800c0d410048140c03500160351886042c010780001d500243d84060180c8801590004103481c0c445590303420194803060806030440d10a480d00e040414 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 13468109 1250 13466859 13466861
    0x3091003091b0f05011101020408010219090807120f05010e0d030603020414070c031101180f020f0405010311010c03030e07080a020909060108060c090402070b07020106050406080105040f020d030504090e03120703 93
    0x8a803203103410101c19900e0400103403031b603880340c0702c81d1300c07055408000102c0c0c0d5800900050140404000042d4041c0803038001c01003070b01c00903400034901600504010003190114034550b0b11002d4120701840d0a1920514080b401401d000d0507a5016002c1d10802640c0541c05a00610443e030080c0c40030b102a44040c400310480200c1141d0140116440d10480804240300d05c80d4800103c002100000d840306203000c0e28030b9809002e070341c100c44c640391464420017103017040700c02c881520b8010758080c4055411642d49003880c104d130050103810000704040303140078107109411002603103013890240d6600544940700306071590100c06082c2c0c0074100c4000802e01110700007400504880751107019168070740710911507800395840401115407182d0244081408618422140c600072141c130b400000b20946008103000030344081d68001401d0340d1500d0304100108504400010110303504480008410a03145030035540c40c011a0001001031303142a84c4030180043c00001400c080005120000c01c90784c079010120 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 13469359 1250 13468109 13468163
    0x50306030616021207061b050c0a0803100302060c0706090510050405010309030504080f0609070501030b010806060901031107080a140a020c0d0302030408010e06100501110304170309100309 83
    0x3a0180d000c080001c1c20102e030080080c201240c544180d4080460700b513611482c603013041c04296001c0b59a1681500c090210700502c100c8448141000d505041c101d441440e141c0c48480e5021b40400400030005e0503104031588044095035004200540398031146810b13943c0c501c2540100000310340800c4003c50189001c2118002160455503200c0c074080c00e110044002d00f00c00b40c1d0403002c2c440113020100c1d1588044c840c3c85c01204462005250b24a0a00c4002d450406a0761040d414035107045541c849599000103150341c044800d171201c3d541d544452004800400d1156011030740d4140104180301004950401007403c0807950350b50b50010301907548619101e118400303540e00540d04c1038250700c440f4241640003005440c00f0740180c03400c1990341c2d81d1050968900c4414a4520307044001004200040f03549124040c107003c2c6003419120348820101542c1340305038060605a0344c030040e000300c0c0c0b0640400072240c44074400740104829214040000e000341c00c3c2d0800071124581c3c2346040614585d0f28503440 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 13470609 1250 13469359 13469371
    0x4050a0203131209090c0309050c0109080304030602031306110c06060f060702010c0203010f0507210608060117011b0801141203032e060905090c030601020304140d0c090b0a060503 79
    0x5540d96004a94419000105502c03580051010800000030010b45c60f1182240340e614641300820300f10340b01e180150400b24040052418072a078040c0601021900000f030310305682e03102c0c2005940351128642140807850602d4018042c50414114030480c514520217029000d10401c200c502e0307078403550308000012643d85e03c0c4075000101031040c480035610500c00c1c912403d0019000241d1100001e4462054803800c1750083e001c00c800d051803440012095040030303002030342d80d03504103d007034100381c0c0007030b00c03008103100f005501c240842c42c64a1b41c50703081d8400a041c410071800a82d03004000e220140c10001c01b446078011401c3d0381c00074602e95051030b9000741c1c03145419001841c5035554101c0c0c10803641c4112451440c3d0310b010400c4249034040c000024a002c0c2c0055101e1040440c030381001c000c0307910401400c501007070b13000f0b1040c450380340d80000654080c0c3d1009840c502100743c01310040340740e01d4100e01010700301c5032800c00001a000715560006031a10b5047d202c400d803c60312220180c1c2e191000b655a = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 13471859 1250 13470609 13470631
    0x9060203180d061a01110c0d0f0201170103030e040509031303080a050403050303010909020306090a050a1112030307030903030c0906020a021509060301080c0306070906020a0b071202040b040504050a0203 89
    0x11900108401c0c0180c00201d2074024074035072488034140c8a1008480e1000d80031600d0941444041940390781011a000000d50210700078000c80000201040c840303101120020440d560401402c0110fa0048624103452001c1e0003100c1010760f13480c20700a008001e00311003a40900d1a08011903074162000c0101c455015240d003100310450310307560701e641c11a4450b0300c15900308101803102000040d81400154020141c8100c0421120328500402d410402c010700359601551128941100280021915840e010f410040707031032001c080d803000324a8240c00404c2076007081c040002045040c941503400300150f58000e541c10800c10030b00202c1034504840500480001d1307403004414400502e0110403d50310100c0000e0344604200080021036070540003a0030a81440d000000d800300182010401158040880d28000300101c0ca014006074071a40751080161000031844001080386001e05000d185507550424110341d125503804480b001c503005805024170807803c010214102d404103001f42d0307009481d503100c = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 13473109 1250 13471859 13471867
    0x50405120d06090b011b23030408010203011a0403020d0f03020c0904060c0e0301020f090405040206040e01030507031401020f0906070c0503060c0702030105010803040e070c0c1d22111306030203030307180609060203 94
    0x1140140004c0140c107440130a12041000300a0747ea05001800c010280c81c000541c483d41040190118094440d002c0b940c070b801c0600c01000075907100f085070b110701d5030407000110202c00d1a040c120f00b403c506a2240750001c1841c0709010030003030558060300b440d0307a00307070380310b0040d080c40b14201400c3c0d01c81c000b40381070030b10300c1809040700c1440c1980c032440e0081d200411840c9416a50044481c0070700e0240d009541542000004009224107290070242c001d00900c02180f40c526a85845103140c052640741031b000324408141e01d4204012009031a01a001c014115050783c41d001d0314400c0c00f40e100c160100d0184d42084c000144d017803000405c0d0340c2680d24010421013a039540241c1180d610015040503240d10b4440790001034800d8250543c090808038255001c0a0740c504000d074036044492001001c0080000610380d80c0c0031480e100c035420028a811100f001c1c2c96000c0d10b4409001d0b10352a000070303505000001c28802c0060b003103652403010300982041201202e42d14501035907448000e00c15040580c100300 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 13474359 1250 13473109 13473113
    0x20606010801050f130504030206010611030708030f060f0d050607021203010807050f0a150201050417120f100b0c0f0105060a03150213080f1e07030f06050405120d06090b011b 77
    0x2550698501001428108100c0d07086503c100561b070701550b0907009608440014886c19500c800e4051040f46160010342c580809655102d15520004100702d0030300700c119001c42c0c0e03142d8482c08440304014008007405001c4086082080d19040c084e600580035210f4650220415030300101640c3c1203a051901a00c062450082409200e0b011440c0a031b0703001c10800c0010440f0010f010282a11034266400094140b42c43d00d4684801900c807240c550800e01c040c001c400000e420001c01951161022215014544600112070001441504444055600803442003040040042c5120602c05240001e00158643c07a00748506161540000340c0f48002d0404c102ea816121038000f8403050a810718074901c601d0340c2d00c0d802c60074032001d10b03040388850b00b042212602030300810103900c0301c401043c005000c84510b15a28004034141241c0c1c01000d044d00da4000405204050240c0c041c0006017850007542e03070000c55090001081d20b805005080c5103403205000d5654821914103010440340042d51048144d66 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 13475609 1250 13474359 13474369
    0x80612030412020d020306010807060f110606191206020d060b0301080d030c0504050901150807110a29040b0103050607020307030e120a05071805060409031e021513050d02060601080105 81
    0x71203401e03a0070000c031101e9580142c404107c114000c01c0c10703002425140c4d0070002c0c0245040c0c480c40309482040481e003141c2c14124804504641c0180040324120100d810701c0c1003201e000c50b100c1c0d102d035038403111402c00301c800d01480b0f030014501d24100d0700040000c01d40703c4594408602080c01280d8050b8094240c0b041404d0203a4800341e244540c50516070b08040e07507800003803c0b151098101000c4101c5084d1858140f82e0001074454103c1d40700e09101c0750708220b46080740d07075400c8000c00203495044166003000c6040f52243c80b403041200405d022900d2480c00341802102a1030a10085455201d0f14000410180c4007200341c41081c4c1d0305640c3e41c00d83c1c031400300c2084100740107074031500a40e0250844800c0011301c1002481e0040100c10030b0a100d05d8450541503044400051000c2e000d141800c0d281400a5840140001410250301c1d013000240c0d6841c00891420f000c0b1415040f26180032800c1c807084640404c1580140e501ca50b0840c0c1c082800784804a0300d414098031124045204100188468030389 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 13476859 1250 13475609 13475639
    0x1090b010e0409082b02030103030903110d0506060d0204060806090601060908010203071b060e010609050702010b01090803040b070c080a0501090c050d1106031506031302010908070602060c09130911010806120304 93
    0x1a10459150490302c482c5c01030403a8005c2e88114081074840c4420020866031341100408100c044480c07180300c69060b21003a8562400600040c813030a142c1803081c08650352940a030001d80100710858040f40780c180c04440c7d50b0002801103c2c0407400c500d5001a40d22014000c0301e00c1104150780741884c40c6112502e0061701000e94004590064480304140780e024402d2043c0c10003000800004a1603082c1050302130b003190180c0c0407850400496410502c81005c000048808982130020500e0b070399030300790804110b808456004505603001d18903441041c054150002000c46000740b074444d1040f1b0b980e00c200141c1d050b48880091000200402c0b241d0700c0e103018005075610941e026500000710003100d00190199100321004000807036240340700c80a559001e1400c50241c400d800c000c0c0125414900065030704c2c480103144500300703800011030241796151400c031028003c0000a040c0220045d41ca40100c105140720343ea07900240921b80060500d29140c524102d006550f80301452605003031010107a800d0a07 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 13478109 1250 13476859 13476907
    0x50402010e04020d0902040b030309010801051020060105010207090b0d030c020301020d110d0606020102070b0a020304050703121d03070f12050106050603040803090c0619030e0703060501090b010e040908 89
    0x12002801142c5441c00104000164401e0015142c4610703c100b004070754058440c40d01940c0148090710140e6049800181581c1080754400c0341001030400c1147d1140303148480c0e40744101c000407202104240001d21506070703a400d030244d44456846003164011560810000c5502099801c0c0c0940428040d03420001c5881c00503002521380304008520b50150344074000290385502000034580c80440d42403040001034141c42c0300940c586412501c450000300c80141c480d80800354000045001c1210070803a904c0110b50184000d29203110b145c0016000100f4900c20400d81c441a00050b2020302c1c0c08510030041c4d40e5030110044026080c18081048403a980b1001c803220741d03a4070804141c60391600b02070351003070b8402e0201035620700c1c0100c19181088100100e07240034070420b1100d0f44001d200c00707080407100011440d0004802110301e101320b01d080c540368805031402c0c3c64200041204090790704800c12444007a00c0c0d81d403c400420302407004a41c0c010402400540060081051903401c446003a400c00b0 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 13479359 1250 13478109 13478117
    0xc0f01050318070f140904170c0a050d0f11060f0a0c020c060304080903070602120909070c0b0a02040807080616030209010c05030c0d080f0609040b0604020706050a0518060405070905040201 83
    0x41c1c40d144042c1c54010039400c105140c11150408000303c1c42c10030707289002e00c541514007046c00d052607034a10300c4244001140940c03d6401003111030014801704050f48a0301d0b003060880781c4102c401d07007016103000580807001c0d00160808095005040000410342e026016a081c0c2d1405940e41034404001000112803890450207103441d15207882d50703014080c501035405800e0791962000840b040500c1e004075035000c1010341d0484455402c100360301c4c8003030790440074050710001141da0320083e0403528000341850041010b2100c0742030050992080e409401507603c032208071140a91a0f1440715030741e2100f10b0f80e003014800342c00b804260300d503c250050280c45106040140c065144c5542d01030440d040408684141c1c1e03c541c001d40e2460313500034400c5410120410008966060140120307404150052019186054050100e03c103501c03240c5c1202c0c000e13034100c42e0810a50405881320005020300740c0f546041075041192000c650000868101c0c0929400801041e0310f528200051b005403030003c2c4180c2c144 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 13480609 1250 13479359 13479391
    0xc020d050f07200a06080112110109031509020f010306031502090d0203060103050102030901050c0f0702010c050c120f0c09191512030302091009081515060a090303030b01020c0f010503 81
    0x14201035a140c1841c18082541840c3c06281c00521101c50056400714041000d000d00422120008003005892290031100003503450035620700603102c070f81c1e640e400200801d0502400303003510005a4449a116442283c041200d40e41c40d0004405a600c00c3c000500701090100662041317102c1030707005026000010b82103c050300d0940c0c0010782042c0c0241e0059443c1e94000040000c2c0640031f201e901e070711800610703082d410001d098211140d20300400c60002d0500404080d50001c0c450108451416080e0042000e542c62007004003003070301c504450041414600c5643c4108510380b414103815481801d2a1115003188030801e440700d8050b052045004507802d1400001081c800047c8071104a02030203614050784ea680070340c00b40604c400240c03071610104041503505014240e400300704a0110840d9001e041e10a844003401d0301203004115018a500c04000501e182a540d042400c01b42140e000f1386003003024000c1d40d00160f8030b035141311025a6104a5840c0c00d0000707980104083d64005ca801880c450f24 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 13481859 1250 13480609 13480613
    0xb0a03050105040803040b0105010305040c05040507031506050406030b2e110d050301081b01090b0904020f0a0908060a050c0409020c030d0c0305012c06060c1204090504030e040c020d050f07 83
    0x844006943c00e8406110010400061044907002c1c68010a0f0a1904004074a09a2500032070301c02503000f403911613901c072004900361502c6034000501c0300725024184000140c0d141c10260443c0d0251040e04048ad080c50b42d10703039131803402c00401098070a0081c0900c83d005070902c0340302e100d407505c160247c09029090070b41c0e6000700030801408640c5035854807281c0d034a504002030300385000c14007524050180c0c50000e0700134a507640020040c04a50f0003001040e2035409900006001c2d005000308901c00d442c0c0480c601194592100d4840111140e070310584040c0d8641c8480b15056034400c861107a1503c4e0108010440140c007075008108200842064078100045404800180d818400b00c90001940b03030303001070100c01380b03000400b401c104002c2c548030360091205804540c03512004003900e04c10180443c007210307440001e2160484c0003001e9001542c0d141e0301c0e4401c03240241402e460a40c001419944401340d11304180c400c0e2080c0f440243c000f081004c5a00e00c080724140c2c000520f4200c418014031040340 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 13483109 1250 13481859 13481861
    0x51002100216020901051c0311070506070c030b010608131506030b0a0e011b09050f031207050105091207080706051503030406020708010b0108160e030a0c0602010b0a0e0c0901030b0a030501 83
    0x10107118907070750b41800c001481c010044102810b800c000d200700660400c5501d80c4001c80c0c02c40d00c40c290f01d82000c407403c181410000c3d00b00021a4881d41e0404c074001400c4041254440400c030960b4031402350300d010760740c892108407a000b200b1940c40da0100024403104c800301c1c980e801090b044585500c4046030042d12507880401800c000d452040300d50b501c84401510b4a5801c0c041e02c40656040d081181307800480381ea00901c44403d034444c540c02141c0310f04035407100361420312081c08007400c60395015a6400c0c90b490418020070048074000134070f000750494400200840000c403510a40c00000013410210310380c44900090801801c5802c0411030502c80c0380751038134240040c3c40207001540250a00510700f800b000d095402030702da0581081380b90320401041407115040e42d6000783c401c0c034062013040100030101c0c2c6010550300001e00ba01c442e042c030004000341d05400c14100030070300f9212035012035a00d0321014020300c01a120340d68001814032440c000c82d442030340004d0641c4401410b04000350341ea40c959034 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 13484359 1250 13483109 13483117
    0x406050708092706040b01050d050a060306140702070e07050f0306030106080d020c0f04060b03010b0d02070204051618080601050123030901020901110609120711030f1c0302040e010510021002 84
    0x300700e6180051004552004100f00d690055040d80c1c10710008030309070f000030030502c900d8020750041d560303e40100702000e02517440080555800901000011f49c0000560790041c0304440420040c0714600d40171814946554019000b20000c0e100c1d141070880604040c219500000c00f240d4042d96900c00025840500300030315162443d85401822100861106001d2820030700070007a0b0080341000e208028070710520003164116014150a181c0b03410300050014080e200f1b940d0040d40c03290a0105100007091032200000e00f0304507a03110404c00800d20740320081407803018441c2e1030700c030340224004200c154090484843c400c040c4407280780d5404042030155009400540360104140e60205d44c014080d45c00c050a04541000c0200501d61441c0901c21240d54041c0e5902c82406000c010644808014a448580e41c0d080b03002010f503041d4030f030480c0c5040d545125100d64880c481c082c0c614078070540c900a1088400703640d41c414000409a0a140522440c10b540c4d501100862042007201c0041d120144094 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 13485609 1250 13484359 13484389
    0x305061501080a09030201180b070f02190204020906040306140f0601110705040c02151005011404030b0112020f06071203110703080103080903070807090608010605120a0b0c0d06060302030f0906010308040605070809 94
    0x21271202c1c244070900030480207015890805660110b00d40e5a03000854580d00c40420383e040b9005682d03005880c0118495001d0ba520081140d410030345492101084055194410201001c1c00c4010303644500044030748503a0b0401d44403842e00000024003582c00d0680001000c0a0300d0300468801c03c202c01d40351030700450211a03a09000319030034020b018a6a000d40c580020441a050340c904180c21601e600558020600c070301d040c4204034034226000c544421381c03201c0746020010a51510380c0c074241002d41103040c4801d0820002864040240301c00d040007401c1d02c0c00303281c1603520b00b0841e80c00d641c2c84020690060340181e9152241c003a001600840400000000e003450100c00703c4d610703142201050a4400c0e03038000f684a1100e40c0c8844813410380006002c0c440c2500444018001c3d152604003a201d4401e40c2015603001c3c0c00c0801c0820f030603030990003e46c09a12800e02c60680c41d0f8540204607141c003020302004045c40b038200410000c051242000e005924016900a13280c16000400075114001e20300f91 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 13486859 1250 13485609 13485623
    0xb011707051c0501090e0706050a05030901060302060f0909010b031611030c0601080d0806030a030509010309020a210314070b07080403030204090513060c02010b03060106050a02010902060706060305061501080a0903020118 97
    0x10702220717006000c0c8004c407450700001403001d61305101e800351060182c060311800308080440010044103007500403400468014043c5c0703585220b0720100721605d501800c451400b442c10302d0b000088081e840c3c01203034455841c075045510303d0004c00a048850b580784110f202d400e803109100340b842c0301a05114890003031000000904804880070805800c050004100e103200b80c00c0b00d80d088001c25080412200d06d00d0003440c000960031036a2002a40301e110750741094202c2c1010b6010080751101201c0d01400e0a4000e880324082d0542c4000015501d00c15100b00400260a103000318040500030a0b903160010310038207002d82065220b143c03d10446004a0310000d0040340c42e080407040c41150b110340065461184001c1c4202c1d4940c60209654000c10310841081002c00030700c03040d40c0c038400c0d403010108a9004220545c0d800310b5060107406442c85020544a601402001c179206c0c031081c0803d10441c180603143c104240d40c03600d12900050850030010307000c2d5500c5580c2d0f042035a030f0307114824103081e21a00d0 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 13488109 1250 13486859 13486861
    0xc09031e0f0c0b1b0111120405030714010501050a0803040f06030b15070303021c0903080103031101020d0501090b10051602040213080d020d091208070f03030b06030a090302010c030b011707051c05 86
    0x14004a0302d511070418001c4031792415407000700200d075510481d1302840b03c0040c5c038011070319039162a6146100381c41000e8601d414004045c10740e103206401c0304c0e041301d10072903609070072985420240761244994464900500186a4100001c170700035007080502000081401e80d082880c54641615540140c004a0000e540001c1101904261412040e12842c10000401c01001c00343d0f000b0344094010700018040c80401440340d204541c003501120185415540c0500095944440355805403240007150361144210301c010b03c00c442e02c20030a0320600122403035502038014181d02400000e41c0034400324100c44000c140e002c40e070024104020010f06107507900602c540d080f0400300400c1c5290075000b0000703030f180b180e2548002c201800c064a880f584c101680340203951880c601a401000318000c41a00100f000c0704011001c900365009100c46030198000303000c5200041c104034100c81c1c3c84c041e442c2c089200048406502000030f210181d0208003070602a1070401b910311100d00c141d507903414405400f03440ba0 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 13489215 1106 13488109 13488127
    0x150a02040e0a1d0a030c0c050402070302030301060f141206040b030601050d080c0709050103050d0908060f04030c111302071502041a0d150b0d0c09031e0f0c0b 70
    0x140840310214813520f0702030b02c00416004160780081e406000092582068021030b044c6960590285145a09200c0180c0d00c0c50f02055142d0108100c03071803415080313013125000303144038490f210301c000f00ca10341801004256803032100c01f54007940113800104a1038840e1542c52401c241d001c003215445100c4005040d28108a0354000f0b4891400c01e0000002d005011600c10b01e0200140e980074540f90300c6411490342d0b44000d81c1c170151101c801c400010702181c8100d52440e8428481c60941030643e002100142070144160894044a80e001855000300003041c058400c1407407603401c0941c1010300d010f1003500d1541288811001c0010001250060700309030354042c07080c100c0c182a4075050b031501e801910711650407207810701e14034603c3c001c1c0e81c0c99442d01604410003145d60201d0041d23240c0301103060109410303110502c00c80e9240c00e0b00c040c8600082950304507001a001c0c40b41d4940e26000e0b01 = true := by decide +kernel

theorem cover : BRFrame.Cov 13309359 13489215 := by
  have h0 := BRFrame.cov_init 13309359
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 13309359 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 13309359 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 13309359 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 13309359 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 13309359 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 13309359 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 13309359 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 13309359 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 13309359 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 13309359 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 13309359 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 13309359 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 13309359 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 13309359 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 13309359 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 13309359 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 13309359 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 13309359 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 13309359 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 13309359 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 13309359 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 13309359 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 13309359 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 13309359 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 13309359 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 13309359 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 13309359 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 13309359 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 13309359 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 13309359 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 13309359 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 13309359 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 13309359 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 13309359 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 13309359 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 13309359 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 13309359 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 13309359 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 13309359 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 13309359 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 13309359 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 13309359 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 13309359 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 13309359 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 13309359 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 13309359 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 13309359 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 13309359 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 13309359 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 13309359 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 13309359 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 13309359 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 13309359 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 13309359 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 13309359 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 13309359 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 13309359 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 13309359 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 13309359 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 13309359 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 13309359 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 13309359 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 13309359 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 13309359 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 13309359 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 13309359 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 13309359 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 13309359 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 13309359 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 13309359 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 13309359 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 13309359 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 13309359 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 13309359 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 13309359 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 13309359 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 13309359 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 13309359 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 13309359 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 13309359 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 13309359 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 13309359 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 13309359 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 13309359 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 13309359 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 13309359 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 13309359 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 13309359 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 13309359 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 13309359 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 13309359 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 13309359 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 13309359 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 13309359 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 13309359 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 13309359 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 13309359 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 13309359 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 13309359 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 13309359 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 13309359 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 13309359 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 13309359 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 13309359 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 13309359 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 13309359 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 13309359 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 13309359 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 13309359 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 13309359 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 13309359 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 13309359 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 13309359 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 13309359 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 13309359 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 13309359 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 13309359 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 13309359 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 13309359 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 13309359 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 13309359 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 13309359 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 13309359 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 13309359 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 13309359 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 13309359 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 13309359 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 13309359 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 13309359 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 13309359 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 13309359 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 13309359 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 13309359 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 13309359 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 13309359 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 13309359 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 13309359 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 13309359 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 13309359 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 13309359 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 13309359 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 13309359 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 13309359 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 13309359 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 13309359 ≤ n) (h2 : n < 13489215) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
