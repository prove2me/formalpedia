-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_0025
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-13T17:25:17.262979+00:00
-- url     : https://prove2.me/submissions/477f56da-85dd-4f1e-bcda-9bd185c91e62

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 4316554 ≤ n < 4496410 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 4317804 1250 4316554 4316561
    0xd02010506041a01050d02040308030c030406050f01080c060a050d020406080601020d08070c02040b030a0501060e0901140606030705070507090207030905040b040519020307170907050102010b100507060b04021b0a020103 96
    0xe2182e4105100308042d0542140702c15080c110900f8055900c40b40d0032569000390186600140080d0004800c018415a00707000461003280315020030001c503541d0420007000b0140030300034504203521403040c0302c0b01c60070b000c401071a01c0c00203414251b080800ea02c6500302aa03009400c03840000b828035040c000a5601000340c0d07121038241b070410004a00c2c1480c40100300c28484440a8815500c44540c0d00e29030700d05004084100c0d8024009002c0507488401ea111076050a40e0020550341c6055400c02400303102e542c915010345001080d413032443d203801104840d00d03040903200381c0b01409841b200040d110750701c1c4014a0b01d01d01c0390310f4181c40140391200b007008a48545898a00440c10001080800f554070903100681c84446000140c807a16400803c480607444050720b00040e810800602c0b103901d00020303010003214001d034001c0c82240b03601e9042c0700081c60044800f00c04110140001c0380040c080d500030000e03080f0b0141c0010705180e000081000d0800d80409000380c1078102030b03018170079544e0600 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 4319054 1250 4317804 4317811
    0x4050a09020a0e07050a0302130815060f06040305060402040203060f1c0201030606080c0a0c05010e01020a09030605060a03021f1b0303020a08090105090a030c050106050402030903041d060603130201020703020a080d020105 97
    0xf500c42c11107140c0350310702411901c034003ea80c43c10540d001405420003400704021002801c4900103c2d0040c0b40707510020b500201003501e00c40e10801f03440082e5807a80c94502e0498095035804005010030703449560901000e5040500641d5101c00e004504a2580c0c541c0441542551781c0c00301052401100c900014080320455000340c0100003402c0200074002a021040300c0c03041d102484c03e624030000c00d050403401821000c02a200d154000107a002903107070300240741c10990307001e10402c00150304c4201c20044c40b40000d2000942107910904010480c0c0461560404010501e0915082611030b40300f036058003005030103084012981c045030405e2215480401160701c0040d4000030402ea040001d4001d42d5040071510040400207540c25107001c21200390840d00083c440600306548905081285030340780e0308580501c1c1428420400040502080a00058054034000d0205450b41d1504d440c41c0c00c10902c500e00c1a415845803401c0040141c81d50401c95005058250150111030703c145402170035030700b024 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 4320304 1250 4319054 4319069
    0xd030b0301060f0605030912220506090901210c030602030414010603050709021b01020309071503020319090201030e060a02040801060608040b0c030907030501060e0402011407050c100c0204050a09020a 88
    0x40030a0040e001d007801c40e42c0c280c0d002814995200d50741c00580710300d0410b4560707403044400308c003160042e0740c1c00302d480714000801461010260820b8844040c001d403800b0b500d1910794406c80790300c010401050480c1201d0800b0f010518400c07000380c02c0b40c8035042103400316441140d44503400400c09c401e02400303120030303050520310100a20080d482c1d501c0390ba5592116000b41d03126190b0024001e01d43c20010b800c81c1c140914084025901c1e454210f0b0065101c14003449170403510380e8003480c0c1100007442032080707178403610845c520b800980c51140003a4000b807400e48400c034149591458000c0c840e000400240f07204a0000c4c3e00566142d00701151a82503402c00e9000320709000302c00052100040c418000c86078410382121220707880e640c038204168035201d640d920140095103800000310381c80041180c850300c40c40c000c1e20341440c40c940180c4070120300d10400300081c0c000d40120040c1c10351441c0400b00c4810a88403480c10b010b03082c1490700050115041078828000450f5115120300031410b251a0f800000e0415 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 4321554 1250 4320304 4320311
    0x5030706240b030901150e07020f030f22080102030a0f06060905030a06050703060f08160f05010c0f03020c04020c030d14040201050417030f070506060f040204080304030204090c12050d030b0301 85
    0x352040584a40682c1c1032180000c8005030b11540251300906100d078260245025441d516040c039481410259078501c018018002c011000f4400001210868001681070798646418410f41c2450f440d440740e8105070b04e031000c0c0340010320700c10240003941c05000b1414000440ca40541c1d8030500b200e88580c007840a0241c2942c0c05c000c41c1d07402140181007a80c000300c0105566036610400c80c0207201c0ca4200140c4443d060002080761800020341340100042c0d014008401611034807008580300315881100d00161000030301c4e0000800780c1c01102100780c4a80111103209017942c00081c1603030440c2103055650741c4041060040e040f00e50140d900c40b0f02d12030340b41306218149a00020710354403c40c02a40061403070008450081002001215641442da010760b607104c0f001450000c0c1c83e108191078040c4940060001410310f0301c0d02d4400c59003219560001075160034510381c01e00004d08030051094030030002040002030400307400f50600e004035104d03c1c0540202c41c4490400b800301c8085a00450003a8503 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 4322804 1250 4321554 4321601
    0x1060305091b030a020f040e0607020a0618080306120c03060903070606050906010e060c0f03160b06121b010e06040b0a090608190f020706140106020706030e0309060714030705030706 80
    0x14041394080c40ba03070701901e81c0c24162150074049405030141c400e1110141c841d43e0304001005a0100b03c51030018881c40040c49502201200c1d00c0140840c054043c00010707041001c83c0c07482c900300b200f000a5030721581c20340310f0039511240068100030007280c0000554100103030340010800507104a501501c42140c8001190030103c0000300a0283c01100741d0040c1000141c1c00d01224080200003c0321003140e0840f903590400d60440398002c2c20300c07002162207094803404030b111468601b080e81101540c600c0280301d00c4410001204040d03104245860501070b43d410411100d4590800400150101015440e42c415900e10001d1038110305604c03200c20070140342c4c1071012044e8151500ca45803610180003203001a6010a00e5000b4071078640e00400c00361401525092480000307415904031902502603454055862009805403266420b1500b0541c100f00083d18142c03400707801030f100301c60081d010b01ea005240d1401051079a882040c0070781e5107600100d030310010803496019003403d036113668201854003607 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 4324054 1250 4322804 4322809
    0x9080609030d020a02031201060309021203120c0d0b060304060504030801050d030207090b0a090513020a060e0604090c090b03010305010209030d0302040b0901121e0e01050705071e061401060305091b 87
    0x40c220b40d12200e95000200ea00e61140308005440d102d0f40c003e4040362040d65a600050300402d0f180c4000c03800b50180c540c19445503e400700907134441c04401c6038044030a41c1c0702e90300c801040c0e1103021080092552540b0503205601e4090140d40324610410b0001141d0600c0d08010b0301ca4081680442d03c12150b52111100181c1d0229601c411110007050110b4440d10503800a80044000e030401c4035400c0c541030402a08158082501e82c00c6402a40c01c1325915490341c1c82161300410704442a5040401080100140000c940c46007191388114074090394060b4844500350296817007070380207480e103039004180e01401e1b2406028414605a070b90504618052a2a002040324040c01c44068184030000780025445481030700441e070501c86501000050800c1d800140c40207203c6070300c8072070441d0305e008005030407240100d0456200e190000d0340803d0003280d03036035044c03200007401d00c1c103c030815101c1a03a03600d201c002c1c0403460301134441520702044901d4103c07001e610709140c4c80c0b03c0310b00d13800101d41c00008a4 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 4325304 1250 4324054 4324057
    0x4020f0405010308070b04030519020114010503030901090e060a0312091a0901170702120a030e010b09060f0d0303020d090b0106020c090f1308090d03020c01080903040509010e0a1b0f0908060903 85
    0x6592140001d622551f80c2d0030107036103074000c10442e451001e02c008541001c00d58103600c40c1046001c000800c20890362158140756407400307100d404901003880b02005102c0d00046403034690380310b20b00401010702c190b240e54406e0124212820312001141550b003003441010f020008418048061040d030b02c0c100312010000078404ca030703c8062170552588010109101c0c80c401e1100d1038500f148444d186a403410035013001070040100300c1e0101169403805143c0c400c18500310480501402000b00100c200c1032220703003006134200e0340b40c1e4214107255007040030350b8100b165030181d001040c2c06081ca8a001c1d40c584940681010b00354480c441c4103d41040411002d5200785602d1500864a203040b801903d01500e09401c0714410124016402105415820304160380020b103000080000e0b40c5d03007006512660001942c03400b0307900810ba4030040d404018400d0719020801c130355220a62002c04209200320200c49125054180102c9000400942e0b0b103a0074544c104030700e003004280c0c40d07004061714584005078a44a = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 4326554 1250 4325304 4325317
    0x206060d0f02030a0803070e01020109080927010305030403021c02030706030513020301021201090c0903050a060f0204030605130b060303040806160512010603020c070506040302010c0209090f0109030804020f0405010308 96
    0x4000000e08403040c00581c654012800c0d901508460750f0f21071030f04203520b1540086036040002070048001890303a52041c0140030312a6131103032015007451540801c1080540708a00c0681e4484c200c0c10005012407072110300309000710301440c0034690b981d045005104c250303072584c28028941105029940b0040c4c4000800e601201c079240b40008454945c00c0c0e4004642d001e01c94065407540c0041500307030645221686243c100e44108808008613001c01405840b038000e91b01c4050002c1d003100200e40e000c55035a0b0005002000720800044c41c141d2282c1c0e64404440060384c81a584803000e845007020040f00480868125000b203000391300f80fa190105041d620400104803503c85c413000e8417048401809102030742e42421151000780f04542e11030900800079000781c0703061126071240080000f0581403580480e82541c0e0181d580215290464080c4869410050b2036a0814442d020000144490070f10030004450f10030380d81e600181c20240104403e108030300d8940b81c8568a040c5c01000001c03000b500300d949 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 4327804 1250 4326554 4326559
    0x301120f02060910020105150d0506070e010c0213050402040f0501081207020301020d02070f030f0306060801050906030f0607020312010801060605030610050d05040807020907030c0e060f0405060703030209030601090b01020606 99
    0x1080031072001c6101801801001d81d002040500342034040354041d0401c520901a410070b42d0288040c4a00308804601201d40240290300b06001048440d44141030615981606042c4054020340541c08140c50500100718001c0e007a6950050000f186403500980d0101194908144450b5062528503516114407186002140100081c804110345080d01503c1ca6007124042c215200c140b00d0a0a03030140788030b40703005c03000070710400da141d480b5034082c5c4152810f03200680c3d85c2e51016801c007018002c450740b0281c13034560306204003101005141c400304000340c4144000e6000d1a1600c02403c1903011880c0f06030800405030741403400611115501c0b20650740e001c5800c44400303410354202c400642d041e121306000b80c0000780c103120401c01441400001410710398030030f550f100101c0d940c40c081103003100c411140d007400240039050300b0400c03407504e80007030302d181a1202103261a1503034900000d803440e0311041003100401d40229050169140170b22445005003010344003440317981101d800003916407000421951 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 4329054 1250 4327804 4327823
    0xf0504050d050109060905010606020d02010e0304030303050403020a0f03020c0f0411030f060604030b01030308040201080c120114030321010609080a0c0b0711060a0c0606060905010210021b0a030c0215030112 91
    0xd05001094001c094004e81040d400c008034501b500300140604000d00403140944203002c0055480742c414071440005480b200040e6003071a0469034120040d02c40540240c045200782d094203004101c83c00d1419540f2407103500103000e031205000601081180c2c40320302a01c180d10300200c110201c80c14000316544900e088041e1202070342d5640025005024940000d00344410b6600040b08241e04000c0c07040c081c60013602c3c2c4542c2a40c502010041c50f00c100001303400105c0304000108058405039100c4154071380d0040680e0709110045a498400341d0100300a03070380c607880c1e107001004002e0b04200320301d0144c40d2a40240c1000301305c649075500c841c42c0ca0f100e0718140b00400503510040c8080d11704440b104001c0200440c1e3780e4807130010014044c1e04250340c261840307850650006086801141144100c0741c040e0080c14403c1d00000c0450000c2d0032200c4807001441035160300c0f44000d4018425100254400c1e151030f01800814014440031300307040140750104020420042c80021000c00310400c080f9486400c20 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 4330304 1250 4329054 4329079
    0x2040c02161208030103060509011806050f01090603120c02011e08041101020a03050f0d110a050a11030a020c060f040302090f0a0f020412080c070e100302180c03040807030207050901090603030806010f050405 91
    0x110300400c00c040b48102180710302f4504008000c1c41d9000306000391000d07201246070ba600c0c1c5880c07008540451200800301e0444000c4100e02074060043c4400107401410041e114080440302c00380015410ba03c040006050403041008005610040b03038084202072000b000c2888450381c020306141310760060b00c440c0326804220000f1170100c0780c1040b002100464640b0340c503040310007805400b5410000030030002c9a100354100c48054000426a0b100c0c04d00e950080003603030f81820a100c803903403005034000d2081004000200151300c45108450148459090021403843c0038040c030740c116041034422507070301c9004200802c2001c49042c0004481034005030820342e1103401b01425031910541e6407240504034441410008003180c0c1c034800300708607402130700d25024040f002072400e000c400e011180442281424404100462000000b50030380134800e0045031400c58484001945862b004d0b4001c1d0704050302c0d2030080c020190b020700304035000b000a00340301ca20100c01003805812400f65008076030250101d10b000 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 4331554 1250 4330304 4330321
    0xf0f0408070f0c090e010c0e0402090109080f0307020108100614030c070c06020c01030c03060b070f08071707030e120a03140f0705010606020609070308041206020702040c021612080301030605 84
    0x72501d140b0350101803242c1d0140249090545143e60b44200c04030203107808000c15041c54103024211049586c3d0340d4000c0a20079034420040290010403038241040208100801d07111410003220403c036000741d00460b20386e07010340300041401c10002d01055090504600400c00b16401075051148400408009500d0740d0b600300d621506c5005034903015145822040c0e00003125500854a6040b40000b80d0b0180011444140c082c0d0070340e10184505081c4810410150300450024004011214442c04429160648a460300c80360040c1c12268090803a00000390f9404144c0c121a000c0a22402507818101003800c4075035042e101c8001e104040c1c00d01c050002c210312840c9040c82200d0307000c1d21b460055034640c4080d080c0f42c0c1c000c0c400360142c80094400c07100840ca400d00002110411603601044141c80c2c5403e05614203400c0328110030403199142c0901403440160b4503402140e8000c0290f500a0584004440788080c03a8403183c1c1c080210780f0032459240f8041024441181d040d83d41052001c40c03944c480f00103 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 4332804 1250 4331554 4331557
    0x207060e010c030905060105010f02070509060102010204080313060306050a050d110109091d070b0909010b0702040204030b01031a0105060a02100506030703050303010b0315040203070509040b0f040509010e0f03030f0f0408 97
    0x382003180d5207400110302c003090301640900040b90152007125581d81e01c86006640c0c070a04010404056448a202013205140118550b944540188009070810359121a00c918603040fa11000410707130b40450733061003003907814403a400080100301d581d20305842c5000041643c02c0c01707400001d81003c00329040200564050b408840040400e0356041013038010650720aa20300300b8480d602103546c01581d8000804402540c15101400401402e0300c030141d10740059002c01d0340c000002243c0141e000d000020210307000c2c01c0304a0095000d030000110b4001c10701980c2c840a00142c0000b4401e075410f0142024441d40020107008450100710001019150039002a00d4000c40d5800100b07a40f0000002146100309880950f014000f280070a8145070340c0c020411050380400c0368980c00080c2c050118603c1032809802101b02c900026107081c00316440300c0c020800b502d400b10390303646030307a9110520746803a41020448003507804074003005181541007603400e8a03a003080140c001d18440814402103401c6c000d200c070 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 4334054 1250 4332804 4332821
    0x901170106020a02041802030c09070c0804260106030b01061206080a0602190206010303050d050711100e0c0105180d05030c0a031d0d0201080c0f09060c010203040204060b0f030703020706 82
    0x241101560355a0402541c2e04103204041703000ba030400002c200d61345d003180d1100c400b07a40d0040140060842c03400501c01d1803040140103208005144181501290815000340090f141500e0340511640d179460030190164100f80c4202e18907890144100041224041d100e03055a10515006842249030503908002d80803d07040394420b805041b050324100a0709a0040c00c2d10804840000f42108911005036143c034024480600070030003c006440c5c04840350f40c0034590084041c1402d0303204903403070b0b01003610b4190070382d100008460341c903032121f07041d01c400b002402100b0034240b0b011458101c0700303401c079400c100300d400103170380181e084003900070400c0300a100342c0760590300200841ea90702d8084d080080040f180c80e000246e003213200c44003441050504400b00014107406071282411a203c4005560440d8008680d82c509090244051241c541d40c4200070b08210b12030714005600d900b01070040100705c0307102d5030140a03031100402042c1c11003040d4805482c3e0090060070010303101c80c0c150609602811000 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 4335304 1250 4334054 4334087
    0xd02040803030a0603020f0d170307110f0c03011505060412080702031b130203070507020906031903021c02060105032107080403060c0801090b0303090415030503120f0a1802060901 79
    0x8020403500c48401ea00031400c0b82c0c007c07900008030741c06a006111200740060b2000d00000d0301c0e00185606000b000c4001e40e00107172103180c034650030709203006814140402c0c1c0c43d81420903000b080c40d800440c0b03000d005820318078070b204011142da10704e00303400140d0601c1079124400b42c03000843c44440a2050704015a00201d8018041d20001081c540700e908003a41115030482c49420305848800161544e442030b41d2290040f03803940b42c9000036030f4007007148600c00141030766410310950784005804c2151500e10040d16102c6d4000700141000e0810311100041098222411580003e004000c182e9000a40b0140d5200442d12080a200040da040c29588a000800340c594440000c00104001103a4455844503c1d903641d29000360340c0740c84000080d90f445030703107855056106000d00c8459140544c81b034803240d48403c14100c003480c1c1c1c84e9070345421a0080c0516403068080d03070040004503818002e03429400811400c04010440780304030301c01c51980704140041d01131100030501c40901c1e402041d442c803050300d24 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 4336554 1250 4335304 4335307
    0xc0c0d08040306020f030412020105040c17070b0a0201020c0c0d030903021e030102070807020102010f1104140604051f020f0609120a020c1e010e090606070204020307170a050105010f02030a020d050d02040803 91
    0x1045c00c140a40c000d4601310392019170441c44c40701162061188500580d0300c005404012850003013000c5413040080c02031902c500032a100014442c0d50302000348200032a0303400250302c40c021151600e041c8010168150f0181d800313200340b000041d60000074102601e03070454041c103022450340c15110001c09520700442d050740c4009101001c0c40141c0d0041c14119100741d00a000340c00d484a02c510542e40344003076202034010148004e00c1100030541c000840168090b080d9030515640794000f4140500d1030609465401c101917000c0405a814010300c550030065000820741400c01030b029a07940c08191100c110411030114014491600c20301942001c2800100302001441c000741d01d00c000922070018440c0800d010329950036183c01c0038803155205035801004a8140146502800003941c00206810200703c1034007485110032045000701c038040e00251400003020745c189800900501a1921040c2c15544248021a540c541c002104124507000340b401a8443c81d1004400c00070780150780161041b80030 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 4337804 1250 4336554 4336567
    0x11406090915011202130c0206040213090507090506040c08011202040b0109030b040501050901050a0c0507080c0109020d06020a020601050603090303040609031407050303100501030608030301060513030602070302060601020c0103020c0c0d0804030602 109
    0x2c5403284c0d05502402103c12440b41c552810038070b41190790041414000d078202e0740c00100075140c00c000918180c1c451000100780882565181410403201d0340106400316500c100344451402d2a00c202141d602090410a8140d4186203c1d42c10224800c1d01c0248515141c001d01d081c1031b40308032110801140d11158030101070400b40350040c003070f01c4111210f00c0c0940c0b07058005901000e1500405030420b0951301c45a150040c540c030f440000390b0042c000348500d5901d40749030f9801a11900e4074a071500d8044c150058444810090003400c0c510103030302c1617100380710070b00504c001941c0100c00c507500194000c1002500c0f1246140985240f144850004d20200020407848207200e000300046104030383c01e8442c0607680d600c803001942201c06070b0150700f00030745c030a1005110040c0600c00400100c0780002030100c03159940e42c0c41c0170130303640405d8080300140c000c0c40c20f103c85960100300042c40c800d0242421347c10488145241c80d9034a02044030a8070507610808110180410001140d002e550800f20640d80c504 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 4339054 1250 4337804 4337819
    0x30a06090f0605150a050607050f060c0c06060609180603100c020703051204030804030b0a11040603020a030513050303060d0813080109021008090613051005090106061101140609091501 81
    0x20301c14805480350303810040001c0130090100301c0c203200f005000381024034441c28a0140192600100c1c003c45a5202e00ca01000c8400781c100f03c2c00d84520760100c80180c2d50b241001449003440c001620180c0504400e00255010303641d440e0641407000505900c540c0b0030742d120000640383c20407840f0300905207842c041d0221205035020400105980c00740c0102ca4000c900050385040310700c03641c800a48074004c2030209000050602010135000110000b01003081c0c0403600303059800e68030540c400c4000c0f81d030002d045500150140192a8003904051407034103910b0540c0c90b5242c407031000411803407041c0000c003150000c0084443c20b030741c501802090a041c1e001d4031140c0b5140204010b4401313034402d141140c1100740e41d41c42001300c0c900c0b80c0101c40203040c454842217000e980701d41c440300701100d940c060646000f1a200ca170340304540c03180301a403002141c0c41c0d01e80480030303211252941464495904014040030341d991001c0356560030010541d4003551503603c482142c0d04100c03a2030300c10515281c48400020300e10 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 4340304 1250 4339054 4339073
    0x4020d09061a0f01050306030d05030402030f0616030c180314030706020409020403060605030a030c03030c05160308060a050d02150307030204050306010605040501030f1b0c03020f03040909050d05090105040b030402030a0609 98
    0xb00416144400003214540054925000880320254550300c1045001042d511884c059904548041c00f114501107000102c0b60a140301260300161340c400340720001c1d0a40e6071600030007404204c00c3c00c2c8503100c0c0c0000b80c403c403100c0845020140490b600a401d01416040400440d883c42d03070407420031034807145c40b58030030304c0079501508c400d4454031b041c482d001c5146c0c80c012400b2000709506444186040150b950f0550182005c0441c0340103005e000d000350307103000072500040e01c0c40900c00e60340d03407405180250030408010b03016041207010310154898040140c6400c0da5012100781400d0145880b41e4a07618100e010344150742119030140149800011229000000340050b24400d8a01b03110071a1482c0a100440c5c0c01c41d814150448100200520124000c54000c800903000784151282811512a0249142e00c80d6104032f800c1030303aa103000024482d040c40710f2400c0c1035170f602d006403a004502c40020400e0080d40600c0d00f00c0c00e0b00001040444d9020046070000c550b0001e07040c444000d260801403610f = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 4341554 1250 4340304 4340351
    0xf040308040312050a050d0506030304150201240b040303030b03010b03010c0203190c02060702060901020a0206040f060909020310050613030506070503061c020901090b06071406090d030b0108010504020d0906 91
    0x40c05258a41154200d0080058030702c5c0e002540c1e00c0504102c1302c3c6141d01c0213000050301450b01030008220100e1050049900d2560200c520340000c200031162454808851620300d0768982140d4582c0c0081c00503c0701e5908590407031b80c040c41d01098105047e0700080c018402880c2c0280d042d031820030000421500032028085a02e005031134103e848012110a5503003003070256000f076118008100040052410401400c1002e5061045440d001e02c20f07030105030254025041002c201d6903954040051a9100b40c442c0040c1810500c29400c50400103100034051a0078006c542c401c100202d5104a00c545103039003000295041000c9801508002c4800750140c0d2094420314021142000d90351041c466450786207002660240448210341c1c41c003549840180030f40e104059106c04200105d0007c40c0e01c1c54289100160b4950240c0000d040c000600361802d0b201103003410a160401032a0241c80c0e0300500e503d1704490050300c02683d18143d440244004002c4a10010030191a199000f403d11b000020242a03 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 4342804 1250 4341554 4341563
    0x509010906061707140f130902040f0902090d030f110706050301060f020c03060105040c0302120108031b0a0b0402060307120c080405010c0c0f06020c190602090321090904080f0403080403 82
    0x5410100d0224951000e004c0b80d05801103005c004d0781465040b110b6004000040c00321030918140b00034a0b0056544442e80d90020b01840d80116090009401103c080002801340600c00c40c0303403180c01c0004c1024010320b504042d042c801d2240210a450740100c4a00c04a41f5124050f2450140c0381d0f5800b8000347c100b80140c0c4005070220028032480e50000505d0845000000c005142583c80e24003008080d024441100c070405400784006281c40d00030040e554080c2810300d01954940f0035209041070b21a16401705180da960124014001240031441d51a8006405480145e40c9a503540f00075542c9842039451891000d180c21004283c0580c4101502c1c0901e2062009105030315200b1411541c1d444c144601030a003400f0344880700f0003d82d0b60381c001c103c05071110080e2400010600102034103417002c40c4c0160b81072a000a019106841d052100c082082c0744000f4001c01401c420541280038010401c105000e201e0b660045400e002c0313403905481c51000301e04811503480e81c0304e02e8903031440e03041480103e4 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 4344054 1250 4342804 4342817
    0x9070309031403010302060d0c1101020a020307020f04050f0a0c1701090506090604020f0405040b0a0b03010f0f0e0c07030e01030605030111040e01080705100c03090e070e12010b010f0507030306050901090606 91
    0x320322510b9804890489800800c05410100000c0c00c0e40c3c01000407003200d81c11f00c140041002c40d804003c1c00540032918194015503115503c034014402811308030900e89200358076090070010655802c0103015005013034508000352101500c1d40940340107042440303410b5109651800060740e1801500504d1054000b5202c06030562982d10034481640a00d01c807018207440c082c8000d001c203080c264041114402c1c01020415015900c02c0a010f0316802a04201d24140302c1e91001d104020584850b80010a620302c20f50750135242440e03443c0c005004400f00202042104024820b0b10b07071182c2c02c81009458028001c020004604070031080c1a03110740b00d070380f040d191020000501c90001103070f000101c40b03000d1b102800458100c0c1c400c84900500040881c103100410801043c20b00202d020745104103070985a1000007c178142c20040c010300b15400c41d0311241e0609801680036603001e54000e0410b0f10900b003103901e50307856260030f501401990f004250462500c0e8000544507000ea04548103c0f030b560b86911 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 4345304 1250 4344054 4344077
    0x6050103030f0c030e0d080417030a080702030705070302041112010e15040509060402010c0c03140610050607021503190e03090a060804080f0304030e06071406010807061407020a03020907030903 85
    0x342c0d000c1000c3c40001d130200394400106002814410803440082d442074040d1403500741c680140902c0c988040c0428013450f030010910a0103d81c00c540380ea030300300420740019810101c40c0e50301e4981d00e58050000a0080d40c0740c01c011804d081c01c1c0381c280c40d00400b40c03c0c2c07031421540e1200b1503070a80d00d50488010880b40149040e14065080a03c1114001d1240308080d00c100d6955800649100300c0f4004115540b20710880000040340701050350342c4401d10b01f48040c00709410480902a0501c225410207071081e1401c021105c0140e503500c4400340c0f5120300c0d038407850302c0750741e06400070040ca050145440512400d200030604050350210062820b42c4040358408009500c44d941101e4a110071180203013a6401000445903404020300996486446407511a4107001e081c008600c0b01c0d08030090881d8502d64405d0140d41c41d600c01e00078580034181000041c80183c0c80e180005020603d0701c11043c0c4451800901d080540d100c0e210010003464020f404d9a1160610060040051640000590024181d071000 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 4346554 1250 4345304 4345307
    0x1b06020c150a02121b070803010e01031a07021507030204050a030305070b0a0b100302070c050a062f1b060904050103030909050105030a110906030c1003020c0106090908040312020a0b0406050103030f 87
    0xa6440030130b010184001690b070b40007001c0c90941001c0c0110007020005202d4007000804100042d4003a0540c1d8100d0f144c00e5156150252410650b03e400c12000300c1c40404026030640e000a408900141500c0000f00039121035030154002e01c0b46811080e0440c00181010050580290040410303521800c1e8090f21903541107401c20440304400f490341e511840420182450a111b034001c3c00805000e144550350155840c8001010814207500c5100420600b45691130404801da000d2880409803524804801801d412150384500341c480c507040441c0443ca5a031915078803150140c1d07904941c007401c200050f584a040c05400390000303104803070480d8203160020415007804504200341640c02a44442c403554501c017009a400401011150148594039210405984080c2400c1c00070505450069a90688070101825501c0f140c0104c10304034148144540011400b90132202103e0304000e0302014000d4800007241800d01101e0081d00f821003880506c001c6c4005503100a040b41c0c030944883c0d1a00c02103100 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 4347804 1250 4346554 4346557
    0x10801020702150a1101060f060e01020c03070501120f0501061e020c0105090405060301020d060311010f030b09010611030c07090f0506041404020906040e030d05010501020f03030f01061b06020c150a02 88
    0x2c2d0000155441030b03c228460030b0190208455500f800020728001c00d40580c21560503502090010000d4041008900c0e041605550380103001e2015000c1e034203c0300c1c08a0303a203081e1403066504121303103040884200d40b02544409507591901d501441203503502c9400414098402980700389030820743c0300a00c1d2540c00000c10100001041e1904c900b81503030304040200401000300a50780554080181945840141c421040a584078015039a03401e11711100041245400544200c180741c80c09940300302607922844002e0468400d441c18046014004150302d0a6000d481c890500c0d612420f0f4011801d4030031500711041c2c00300424030400c01030365400c04201c141c07100034a8030282c0c060520701243c094100101d030203030700c40e1000d407022561120f40039030a4510751019080490441d6030f240140900e40c1c0c148020101514510011410341c248400c10b40c1e0b500c00103226000a0005102403200c1096500c0301d81090140c01000454071042d27040c0b4156220000100c19a130f0501c0c048001448201c1c5520 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 4349054 1250 4347804 4347817
    0x90c09090d080705040312020703030315080a020d0203010b1005040503010507170a0c03060807030f02090609040803150d0f03030f0501060906020a0204020310030c170d050a050304030f090504060b0a0801080102 92
    0x400410300150507103415603101d8400381009007081001c00000c40030a0740c071111112a49031960051801925508004003107a200c18001103441482440820070340c980080c44c00c140b40c0c0c0496003400280740e9407001900400039a014103420201c2821a950a1900003001d0310441b90182c009100c4c035a5501c4ac00c0356880160050820308144650104501351080c1e03000382d030300740c00324100000e415132a00740c81c903e40030b00c2c1c3c0d0048480084808001045042c403035811a00268251a0204a0700346a40c40c81914000200384280c0801c0b1003040d815940c1da440028a0b13416000b04001d040031046080003406000070302d403c400360500746400041c45c03611840b11013080700c8040d805086121a2682000043d50014000003000c0603a000003101155010340010004c19801c140307650019900103081d414001c50004450901005100c2030340c01c141c104045941c1701d5030600c2d01e00d10204124800f0380b801d45031500495000762821001154880c0d07000010040a5402e4403040c1042e82c2ea20343c01c60a070700c00c14 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 4350304 1250 4349054 4349071
    0x30501150503040611041203020c030601080607050c0a120e100c02090a0905100c09030507090501030305040315020d0510081605030a1101140a021506040203040b07050d090206070605090c09 83
    0x2010000d44080c400c41c003940d0014402c080101e950800710000c1392407900300d604484040307000740200008242d01000980100e580940203007995614040c041521200014645c400384000080c100d0349400007413108411569010364040756965072441c000341545c1260380103500070207a0306030000c001805800c10080d00359000308045e1896030307181d40d000c0190101c2c8008481d588500d002c034256600300c1e4028480841320b140d440340c402030b143d81002898a4015440541203614010050022a60103811501500e402c0090140003205100b0010001c4c4031f0b0010aa45c0b00d172404092141e5a03c1140303070102220889002c481c2100110301405244480720302c141681540299190000160011521070704620141045002c0c42c80b02140041c10360300c075195020058001100125210b010250390b16000307039055804505510b41951030b50f00d410b0014107103005000c40400c0b40040e010158001040b031a80c00390164ac0c44800600c0e004c0b01801040d0761461050180c80750b14003180c14045184d5210701c4d41c9 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 4351554 1250 4350304 4350329
    0xb030607120603020319020306010614040504020f0702030114060a0605091c060e070b030a050703020f090103050603031606020711040e0a0303090203070e011e06020706020a021c05060903030115030501 88
    0x684a068900c41d03500e411001145031a2900000540e0701404184880c15500128040c03002842c8101810b04905030401c000f0b02501900c980c001000301d100b90342c15104190390059854403902c41000e258066400300950545c00c0c001a000281550004a070080400381d030810803a80c3c5076001a0381901070303201c600c5c1c0c000710b5040601070700d0351404040e414524003a420009202038154032190800c14032303030000d2440450000500075444240d115045d48100e0b5454214140340100c11110443c0c89401070403810142c80308040703185a0b4082c4102c40c0d0700e51520407030040c620140c3c9402c10194002043c191203140300d4256041c86402c0c01e0050b455079030100740180450020310b030781c150000d00c0424026a01842403a402182900410342024043c1040c0b1252001000980d422120700c00401c0c0c010000319041008104025500040c1c0d0801080d41100d8a021840107180e0524941d45a00005020361280d10b0178040c0d807403404401113050301c0001d90381b03031202076120300154155030085c807440007010390 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 4352804 1250 4351554 4351561
    0x105060a030b0d0212030a12050f06010507030228030206090109020a050631050906010e030d030c020a05010f0204030c0f030b0106111510050f0d1101050c0708150106030501090b0306 80
    0x880c0d400304078541c8000304101d00d0b43d5895008a80104ca040c0d00501550784000345c04144030b40c11160101c1c003840c1c1808280301070f180810305031603000707000b4200c14103000c00440d0030000c16000340500c1c0d0400d2600c040c0c400d400190a8548003204c1d00000060700540103440100e05010410b01030103a000340c0142141011901c3d0200f07000305c40c2e0009010261610104860b40050905204c03400003880c02001008005410324041101e0700d02c2c041c0000b4180280001d41c00f081c1d44002ca422445e103131813420001020302d1903980682c14501c6c82d210051983d440c040309840c1048140c0d000e441640d0113018050a42500c43c82690364000c02400060005031280d0010410030b441a00c4a9215110707a0040d5007052410b81000f02d807413941591290055031480c80144000e0500c1d1007240340c003910444e0074201640303d0b83c4441d0044040b002126041244c001141e00301a54200121001843c030310048820050010782100460f48080c00b0700d1000034200000003a0000030744c0181a004100100602071070348 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 4354054 1250 4352804 4352807
    0x30706140d0f02030105100e030c04020c01090b040602070303060509070207030f080f0c070504050601020d0c060b01050c0a0308010501020105060f03030d0504110303040902030f13030c08030903070602030a09050f03030105060a 99
    0x1840c40030110005401c2040284103507190007070002c012240e042c090b8030380d4185410044030070009000c1ca0200a90303000d45448907500041c04da8030155040da40180d0366507110687d9405052648005007126460b9028401040600d07030003465030300c1c0266000c0044948900400510100c280da8100041e40210030510100300700308500709500d449103c030546403c400c807614840540100d0b00b070708095001079100308030900b02030040d5980050700344050710088100120107010440140790140c407050b40c640c8a54101d9029030215511003d0000c21241e61078114a40145000000d006850055083c071020a41c0d038100f03091455421100200a142000250000702000300002401540c08142000d00310040352801e0000300007500d014030b0b01503a246070211402c400b24001900e503804400e000144140400c0e401120414026801546c80b0740e40c0c1c0380c4c403e8043c611700612402070700711480041401803450482e030003c620a0720690960314803104c4000703001d4030703030000344121074000078204081c10485 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 4355304 1250 4354054 4354067
    0xd050f010308070305030a06050d060209010f02030f0423032a03060609041e080c01021806030f070507060e0102190206060109060219030c05100504020109080d050405010c140609030319020306030706 87
    0x605903010001d10b141e49c070700009006000e43c943c01c1d68100d50014160701e072540e02c003010015464043c001545081505160b00c805803203184281100c1400d0310076400300da0041c800c045505050014201c40308914180154a408024a8110800304007040a900040d04010990a101d224001c010440c182e4554a80c0e00000c90f4204400d510f400c8000258000a580e0b94090240c00c1c4000380016250140011428030350141c2070071180c40303804140200a10f04c042e020f081c42d408a254900a600c4202c941782c101e01900c499001000d00754001b01e41d105501c06d0095503d03440a18640c2210601e444001c015074190b0014000c8500503009a020140c004204200100031148203113400c00001010b40c4946040400a00008200356250403d03c000d40d80e100c105e28000d082c115002e03110503000e442c1c02030604d129500c45c0c58140001e41a1101c103010070308410750b9040c040e12081d280c040c038102480c25125071003140c4200c1204420769000001c14207034429030f881610b02030001c26072a428440180c1e0744 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 4356554 1250 4355304 4355311
    0x50931050a0b040503040f0902040b040909021302040b0a090902030f0601110c0306041103010e0706050301060305040c1214010f0204060903170c070605040815040308150402040b0403080d050f01030807030503 91
    0x184503298005000039070b4aa1440c2c8114000c0020f152203508150016102e100300c0d03440301d490140140300502c203101801c030440d0102c800070940040c03056035510100b07000301034003040071114038030120300050801c1c0715200504d12450b1550305e003e290740d20b841e130f04012400144d4100c0c40000707031000002c22a502401072710034000500000c07038149807540c000091920703a0489084481c0e00441040005030700302406800280c1c8000c4005e0001a410310380020800d02052040c0020592140c000c2824132100d821103030050102811070500005050500360340354802c0c1d8000c0a6590329008a51000205a200750313401e03998190784081a080c60742d15007003034100c403000403004a200e04202022040c081041104014801600d0b401d80752071a18960505100e00100d03d22001840c400c10000001d82c00040d0303640c0320690010700ba40d250130000200c0e0081c001d54200141510703001601205122402e40501000400c0f0b40081c0170fa9a92900111001c3c8800c0c030004008007028802a0b0000b802000a10752 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 4357804 1250 4356554 4356563
    0x30415020d020a0903060e07030b070e060904020c01020702030709050606070215090a150f0306060f08150a060c11030d02030a0503040305160c03030201140603100c020106050303030c0301050931 85
    0x8144071061030310103d9019002c042c0200b85400410810070403d40a082003900c0d0000151407000d1135030301d84000388400140311000304098070b2009142070b62003d0903240081d5010b4001c6490f151243c1000d0300070b40c0800800d0b44248183c603030002d2144024000d043c42180e0161000c0d0403e00e81c0e0303080c0304903030245e4000c08038000d40034024040315440b5100e41600030f2000c074900c090254100074000c0e0011155030600010181070080503c41c00340c10044101c80040f880c40c0c00346107a903a0300000f14404a1028045d41e11294010002031800d50001403811039500942030b507005c41030741d90105a543d081c6840740e040903810034003109010a018034080c5a00c01c0c0a81421440e00002c3c440f00a0f0111100d40b0403101c150620f1820300c00d0540c244128845075406414490160600c1070000303607216106450071409948520750a0740300e0780300790081d07401004050304407522801d002c262102c0d65042401a6405104110005094400401d40c131020740458491004102c502822014403402c1c4260f00c10349 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 4359054 1250 4357804 4357807
    0x1030c14030c030d03230f060a06030c09050904050a0b040302030405010906030b09070e130207051b04020309150601030f020f0301050f01080c030109021803060f090106091a13060810091208010b03041502 89
    0x102403441440507d01c103a2084040b0b00481c0342a0341003103d0301045812184c2011b18140500310b60540100340c020035070300c0484058205d55110701d001890035941c0d6000402c803029840074401050380000c05801660400d89035494415114082141140e40b0749580ea42d02c01c541d9004200010f00806e0f01048c0b8000140042009a88841031441030740e000c4041141c01e903000788101c000c00c149040c003907952a002141c0a515509110030032079902d0f1a1103901040c4900c019010a607030740e0281d03012515288021201307640740c0884030007013007854009104a6000b6003c4040c0c9403160341c495039100307206004440c442815039081000300d0009401c0380046164604402c0720340d020790341e420050f140c802d4060081c400c003189498036100b42521010752114545a08182d290104103801213042c1302c5220044d1011403e0000d50070ac182c000e030002d94490312032400340b04030402110307150b034000500c0b103809664420034024010f403040b034a200d0700b4440e003071803c0350501c007140005c0e60144521408049845016 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 4360304 1250 4359054 4359101
    0x908030901020a140f0f030d05010b070209040b07021006060305090705030105040b01090225080306010e060310050d080904050702060115020d0903030507320106080a0201020c0105030a0e030301030c14030c030d03 93
    0x381c0780803c2480386d100c5a5001042c0210401d4941c0900c0f8003424682c03502c2400d10380c0c0da502007032983c00050402400b0050030030014083c1d901c00c10004030780510b80c01c81800740558841300500240b0b0305440c0641d440c0521440400c140c10140211400341c0d500c001d500500740e2800c1d5202000350000c5491034a129100c5640b80400c49640c06140c03034150244a40d03d98900305840050212031802030070f0360182c00240704111030b00e10084d00c07003c1142c0d4280d074002040c1c0110304d0032032400d10841e440c4036400b51804e010720110541c001a40da05a8403018030071507003500c611078140e980b25442c03088400020071141043c00024801c1005d4410715100e0540d41e150440090700c119071015620340d1000c01499135000204804c0b50074080e05004000e068054201e0392000c0c1c000039220114030b550326060080020102d20a400294080d00200100f0380549440396140e00e0310078400c1c05507100c5d20301d001a421640300c84924021407000a4400002c004240d4940548000e40c007801881b84000960000380454 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 4361554 1250 4360304 4360333
    0x1509070503061005040b010201110405130908030906180102030103050705010c02041409060717010e040f0c030804061d030c030a060c0311070c050306010b1303020609040623010908030901020a14 85
    0x56806510f0340f01c2c00c0c800c1541002c040c01700321012a0b04103030440e0b0500641d451007071107020844003131310016688400007858580c00744000c4c1c50241300041402d078000003009259540480c0741401a1190902d40468001311140c0038242c0c0000e01010b09250005041000558007400d40004024070107000031443ca02e44445143c81c42d20110340260686e0001d00400c0784040d80603c082703003445040122800d2650601c80511004034000384020480710485034039100f03110506121400942d884113100d643e440e2903800042000c03502c0600d9060907910030000b0749440c50049034070802d200e0040c008107900407480d1180c0018003000d03a580e4051598500e070385496800b000d4000c0c8055801072002c4000c848c039007001e2614040f0140e211902042003801a0141502104102411690100d0f40d07503840780b9404000600610461380060055030000b81c0c1240180001c0340c40d4402110709886151002d542d520301e4684920440b45400c2c01a00204100070003d01403034a10501c0095120446511419003201c = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 4362804 1250 4361554 4361563
    0x9010c0605070c050601050a0f0909020406030203030304050106090f050408030604050c0c070b0306090108070f12050c0901061106010501030506030a080d0e06070810061e0804030c02090c0403020406050d051509070503 95
    0x1900340c00194442c003c90240001040f0301c0340184419202840c8403850260116958809070007401801ca031100040c600755a00c5c0e81024010310340003070503640da80c2070620f00140200658400c40f00220b04008211502010900c42c0510170390700080700500d15a00c407001c1200600c0000e29480001909020035a02c80310100035590260030131a08450741c900708031b4100a240300e070503031002840f035010000500020341d17a58000030031034007403c0c605443c60100c1c0c5003071400c0c90424900140c020013490000103e8550207542e00320441c2280d000d5864076600d0300e00450a80b6411141c0300e8040d8468110080003030540c00c010500103010346000035001c000d12020364140003007900c50342d002501200030300440040a01c1c3d0b0b030005040c6400c04d00e002c4000c1c1100404010700101d80e19061203030b440c0025043c54000e45c90103020300d9008003160082c0c030301503a540010b9000b900099024500e040c80204685c00c1080e00090318581250090907540d12480041c202c0c158014200029070103466000100d92300c0800 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 4364054 1250 4362804 4362811
    0xb0d12090602010e010c0807120908040b090301050f0103020d080f041a04050f030622050f06070201090312050f040f0305090301060906061101020f0301050603060105040806040503030103020f0f0108150a1a070b06010c0b060609010c0605 103
    0x821156860b40c0d3b20081500b0b491014044a00c1c02180c90010401640c606441e140c28071392080520f500c40060a90881d507901a0380d000302c6200303001140d994101e40c00c0b00010804d885044907451031008007170041c10317610340c3e088a0701d9940100500050b80c0d03040103140c0c00c4114903c00e0003156a02003102038403c0c01e02c01c058880002503911034803000d040580206070f501c80451411810401490405441072800e13402900284c181e50403400002d00340b510450448141e200080c009210059403003000340000c0c160340c8074000001e1022442080e1102c010700884030429079508880d41980d007040200000c2d80c0c005804103061000410000600b483c0c01d06c00715105034052009140c9942c95401400380c044100c070011b0f80300d00c40ba0300646145a0b002980e0710b41002c280c0e08910707580b06111002c030f2408000364000c50f078407400c50102d801189403140010042c07648600104c25094480800544064103c450010303c0480c480c80060320700c0c1003000183c40c0344041454014044411a141e0104565007603 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 4365304 1250 4364054 4364069
    0xf040b12060103050c1206010311070209040507030b1005030304050f0402070b010909060c0e06030403030c030b030a06020705100e0d08060307091a09010e09100b0d12090602010e010c080712090804 86
    0x8420411590f030184a980e40c06401560010b2404d41c031580c1c102c9511700002c100ea81416a0f4150399841074295405450406601030800125414241041c07690f03903440d480f08480c0500200c002400d100711080c400c2c011108040d005508207800e100401401c2c942500038190070940c00e1025030040303420356003401d0080202d100e00080d1a5814100383c0241d40403030440380240040001c3c6c0040b552102000c41e5030154242c5000101607410314021005402d244c0c049540c14440d6512510034044960b0090042511400844000c03101110810043d1400483e080000703030004914070f60050b004407503859200000801780c03003200340c84031010301c101ca01e580c5240544131881484c048607800c060f540b650241500398040c041031314228442c43e540306001a601030b900754072404542c0e000c0c0c0301d0041070492180c0c06030750b2100e07060b40420700400464262050300300660810600b0b034000301c010301c40c6900c285d40300d84d103090542c0e4483c0020b454403040815400c1d000f40d61440c040300402c410754041e00141116 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 4366554 1250 4365304 4365337
    0xc020303191d0307030803011809050706020d0e03070303050f030711060414010c090e0604020a05120f0907060801051008090a0c0603020c0d1b11120604030305012105070504020f040b 80
    0xd07038003010900030042e207616000f0382c014403082c00030411076000d0f40e044480303d80e01c400d51101900d05103000703070444020040244c400c0950114400b0f0300402d00700a24980e50f65000c0c0260003500c10542e681505d848040e022540802c00014a07d000700001d66100e001404c2c4030f003910121a0315a0b250400407201600d022a90140b441e044103000e00552200c80300e180741c014a150700300314584044c0280a014140302e1a400035071000d0907401001556924080c000001000d490400b040d020498001c4603550b15034014294007207407140c000c00d4078a050318005080030100681820b0195020007000d4800e4010b80305100c200800180c114002030060710b2a99030241c0ca42c80f030086014a00850742003a8400e20210300408803401200310801007809030044e6803408407034035100214981c88600c45a01e00e8500410080000b81901904054100c0351303600c0d4040116480030542d0442c503503440e0030003011a0060305040009141c00c0c1c014244102c2c0500030940340660f1012400e00580c00745070110701c950300d0b = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 4367804 1250 4366554 4366577
    0x302060109140622110f040e07050c030a0305040317090109050f0c0f1005070c0305070501090b0f03070e0105091806040f02040b040905040305070204090501050f060103020405010c02010c02030319 86
    0x828000d68071482d400c590320391501e003845000904a0140ea0414154a42c5403400c40c4002042540201c0c5000802165641d0f5508000109501c0c59009000ea06200e00105000c031710300911030ba00711070060498102660525000c18400c8020f0709020342705508101c2002c044210003c81c0046031802001d4910002038807100031700d0a0b83c1841a200c014034440c0c0c01a800d44840c0d5203c913003401c86040005c031440d41160388ad40300207070b50302d0140ca000582034030181c603004000c0220008040069a0742600e8040d007050b903d03040c00e0140d108210349004403401c144041150203014500e0340c182c0c1c80c41418031a09064000700811302c0d0106500c2041c214041d03000502100e0305162013a00c4c000c05101105502d0a4105851603200388584e2007051907903552000044d0506200d04103450740c03254000c000f4002d16216080c01c42c0030b860b055880e2040d14001c14003040e2558064801c540464906844800c50500070b500190b80301c241c00c1d0400e03a09030100f04100703071180481000380ea542c8942500c5030055200e = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 4369054 1250 4367804 4367819
    0x12080403080a1206050306100902070510020412140303010b0d0506040902090c040504060f030506011502010906021201090b010801050a0504090204020706020c010615020307050606040504030c020406030c090f060509071803050a03020601 103
    0x3c04517440f45001c3e8020b2420b2100440008048800352052090b0143e507031a1640707042803030900c510f20714411092000c6000f15071160401d11400299009001c8a13a59181c0540d481c0c5e1248400e10942c4401c1c0003c0103402c614440340d4210942c003040c000d10000355543c490300460000384080b58072201d01100001c0c1030015182c1441440040c284e43ca84030800c00e801e40c0d03141680c4040c103004080c0c810b640f149151141c18400d4101e074502c3c603072011095440d800303035076180312a0000a00501a030241020600e900c1e81d4071070680141203980003003003030f040c8601c0c285c01d020040c4504074059801c41d03001c00c1584040b40050001f850310080000000854a16199204500a0030b0107220720840d00f00300040400304100007105a000b00c1f04407000201c0d40c42d43e15007031380d68289101000b500b00c0e0600400109010017102d21200301d5400480920850f5510041d010071038013180103180d40b02c0812390214085500c981c44400308240307841511076043c0d889031603c80c0b406001030012401680000014004074 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 4370304 1250 4369054 4369061
    0x1140c0d091508010312111606020703060b0102010912050d090804080607082d0c0702090a050603070504061d0615040801050105100302040501020c010810170604020f0a08060112080403080a12 84
    0xc040d035143c90040d43d4150f07030b200c0100c10102c2c440c403001c00000d00c0318200c20b04010700c080c6121444c03c0400b4030803596545170280d1901002d00c01620b0240c0781101d0a20994018010180103079480040500c07100f4048078213684c80c0c0c01c5040c50500307080d0b58071501d0000505260007480a4449403006029034a480e503c01040888010304414402c8015141501749032034841e00702014010b1030800b1030740c558507c0b040300381d03038055014040e600c00c0c0c6c1001417014a100d9940010700640054055481d801e40342c405000958500c0e00c148440031100c408106481c000c80310005404c04002040f4103581404102c0b081403030f4002d038101c030306640d5442c1d0041029150540144504021a003401d6062601d0300001039160329000e8141c6051044980010302911900c800c2c40c03001e02200e030b002050080e02c05054075510030049500724013034a4100c0102e200392a140301c281c01150061001810f43e6800c04080d03080054201d035040320b071484103000c0803000540d0304002c0c12520000b0742d14030684070719102c050001e4 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 4371554 1250 4370304 4370339
    0xc020a0606090b0d060504081207080403030c1b080c03040503010603140105060103060b040b03040203010b100f0801050915011b02030706050304020108060d030f03090c09060f06020607051201030201140c0d09 91
    0x3151402500d4040d40d01c1d40c044c01e006141d0406400602941c480c100b1600070701c03402c04040c1d0090304190400c42450340040701e640c01280242d40030800303225940c80c1942d003401e40c0d03d481d5100303a0b2005240d00028000740024010300600405803070419660700080707400e5a0054004407241d40c141d000d1840a41401d02c40d450b400b040918041c80211b25024801d103440c0709601034415100c01c0000060309540303094200e00d200c4000a881d041c090401d20310000c0c18500002e0308000001e4000000103494944203461901400380d82280144640c5480b00549103a0044c2800c0b8070140110700c581000b590742803000e003004040366140d29581e072070948001042604018a8540309201140301c02c0c000ca68071084003110200c55050024841c251418020390110195004201031403c1c02400724100c010680000212181a022120780f03440300942910140103030300c0b02c60407614a580040000d90b00c150f9400003501074142c0002e2900b4a91b01802c6e0401c055500c002c0c2c0442c804810800100411202c80b080 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 4372804 1250 4371554 4371569
    0x60703020d0f02120702060703030b0d0803060103110c03040e0702070308120604050105010c030804020907090503030409020d050903070302060415020705010507090303020706020c03030d11040b16060f09150c020705040c020a0606 100
    0x3619141150302c5005005d441c00c080d00500c03010542004140c040e070311400b14000020b050322070803a0b042c034010f60664000c031101400a800c000704004094022410380d1608541c1e6000746080508191100106c114024061030462040640000226448034000e0050144c6030302180010f1400005000594806a001074104070380050030501203a40b000505030002d5044800300c0c01034441d8003080700d0301102c6411155060200240004020003990f0007404080502441840300795035260680b42c40340605000a405600510001000214988100400401d40c0ca00060038040310b616501d0841d20121045000309401490500501d40c04004ca03c0003003260744010625180d001d000300303481b4007550b03130744029254440201c58040c0e064001560b028021441039152101d600290041400201d11010b40e607042c80c0c11500c408118a81c060010b01c0ca4015150400b0030045e214000007c0c420b0b026071800318060000c0120740b50751280600200302c001503008100001e03d03420722900302d500c1c2e503103c841c = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 4374054 1250 4372804 4372813
    0x1101090e0f06010504090c0806030c040e10050a021207020607020f01020c030f030604020c01090c0f0801050601090513090501050106020c04050a0203010608060607030504030206040603060806070801030b06060c010902060703020d0f02 102
    0x40e960620208540c0004041118952519800c0c0180d40500071078020801d52810031810540b005e030300c210100c0c07040a0071011107010313142e00c406220484040aa00c0112030300030102c0319801020641000d904600403000061503c101c042000010242c26220140141c010310184000c4980c1044000d800c03d042c1d800861801c0400d100540d40ca00c0b81070b40c070b04044200400010320942c3c0f50383c190b4115064681c020b00200c0d1003403400a60651041c0030352440c1001304000420000303414400c031441150f0685920007954201010050300b03000c0c0c031a2030710000ba190004640011020b000d014028069034000f0302030030b08010208019240700401081000d44180010020b882e07109815681008082e991036581d0602810201d0701031260b600041d4201d01c0c000340018203123505601034822a2542c0b020703a041620b0341c0c0700823141114280700103815280a02d002c10004e142040050541e13003050800065402e0395030b80401e50603040014181c001da008840704904550300050b41c4600200184003a0 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 4375304 1250 4374054 4374059
    0x80a02100522021c080406020607111504021f08070e0303070c060c020a0305030a0903021309030c0303021b0609010c03050612060f0a0e06040609060605060406050f0708040312020703110109 83
    0xc604010600100b1140c4100c00d5040d94150744071180c1e24a55a0302042c0d000d810740c0c01c2e5040803c2d469019100e22001440360b034001a010521904a0606a03841c540140110481c414000e044403540680180d030b00110400f407040781a0704a1100d078185d02016100c1440d80e2510300c00103000c0c802c00b140c0c49400b94000700890300015002e0a1030005a1340142002030340c00030307a800403448034003007a0801000e901c000034400c07950580050b0034004883c800c0301c080b07083e40480c640d580165048044020082681c0b82c121500082c02500134015861294a4240380c0c241411229440c0c4002610032050700d075910350f1690651541405116403051b0161003241c5000d025107211036407100010f013810307004482c0f10040b0b10315000782c0d0440079400c0700f0b900c02c4814a0806013002d01c01810003000843c0c80c9450208001181c1c1082c0c07045e101160810303100c1c941028078090454020303501003041159450701c10003000c80010381a0380c0b490303000c042c81d0b030003131030b1a6040d80341c040307110070008001a06025440300d04 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 4376554 1250 4375304 4375321
    0x11101091110050f03060607060908030711061602030d110d090303051008030406020d110a021807020d020601060c030c1109100e060a05060a030207020109050306090d1407020d0308070504050904080a021005 90
    0x440b50801e00a1f5619a920320441c1401e5004000d203400c0100100c2c0008244000320b40d00c42035400d01d040c2c00c40240d400030746401d4540c103100000500c083e409a00306015a2150b80d0156010f00d02c1c1e0902c0c64410351500e45462000001c907011031404401003a0b48801380458843c040c2d10720000b409005004500d852b0416001944e44c50024a0803010003040181c1ca091036441885055012507024000c01c12079449914426100041100c505005101d01103102d004180b0006505040315902c1e22101c520a5960700d084a03058000301301503641d5000c0c807100e16047c0d2a00920070b845070440c6000d804031907081c1030f007000e1a61409030825100c0d08125005000e036503104000c90b60416035506005a440a0501c01070719001d0703099011603494019081080954a004501304940c081030340c0c0d07804034a1000c0d01911403140221000650803500500140000902441506400c0002c5040c5030741416515800160301e840111012680d0080204200c135040340c0402c8805100a0807040c240400e103880da64 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 4377804 1250 4376554 4376557
    0x305100311150405150901020105060a0e0105010e0105040e0106020307170702010e12012a0e010c050601062105010b070c050108040f02040209060f03090303010305160f06030506011101091110050f 86
    0x101c0c40395881c0b00741884640d4590b000c40e070041101030f2414040c501510040318070382d00301d46881c502550034800041c60900d400034446090f240c540c803089a880c0d083c500116207920001201606109040002103518004204040c0c001c111540c001d568403001840d1400814014005013081080144088001130382c11662690700f15005031401c0005040a0140c1341c0505550f03912400c1c2c1111101aa128405003500e10340300c42c21007034950200720080c007030044a81d2042c1c01009400358001c2401445464800c2038010007200040380307601940620303942c010080368000c2c1c4c0030b101056800640c00c07003001950105500100000d0802c048940b920b0380380c03000e403c503040030024400caa000a000c0199500c031000d85100400300115942c0b40d00d08100d0869580d0720a01040d99540b0a20545040702c3c20090003400603039000c1100d84038030074a054010b402400001d0b054a0500c06481e050007680c0109202d10049580110020200000e150017800400801d03c0780e08810400100000d45c10044c07100e0 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 4379054 1250 4377804 4377833
    0x8120408061303030204030b0906060f061e0a02010b0907020d0f210b19030609060f0207050316020d0b0c0a030b03010e03040506030a140103050f070506130302010c050a0c0f0603051003 81
    0x88000307800c850b207140483c0203114540000b440c003190b1030140a600440060232a02c1070782c05681c60b15440b80d07030a0400160b402a0224022890810816814400700300e00103440044024000480e40340080000103a041000301c82060061744610300d103d0081385c0c00325940f500d0344401c0c24101840b0203030f04080041000c01e0288000c90a444040788140d0b074503160464240104110310401441d0745a10b0810003401030328005071222402c00c14031140d02d0f60705200300c4400a601ca0b006614024400d0260181030540340802d0303921049200c2000c0c003003401c0e0301a55108162210049660b03070603058002d0202e030541c007541d5000f81c1c904401a0a440000130864043e19800c82c1c03e0782d1a81d0f906180e2002401002281550780c0032050000000c00c800026602c10842c88101a5903041e600d502c1488030901449502c0846540724280400165000d60348080d101801403041daa481e00154485001074482c0d40d001500355410720104000040d0305110382504014108501c2004070720315110818a0640380 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 4380304 1250 4379054 4379071
    0x501050f130f0201020a060608010605010207080303070206010303081005030303070807081003020303030c07140708031309020306010509061b060403080601030b0306060904030509010513090501051008040b010303050903031b0105010812040806 106
    0xc240b030003568000c2004002041e8015010b003d150380301c2c44220b000e002e0b44e01c80c4c507025109010010074034002c0482928403c508030f034001d00300e6a10b51380b4100e80c00c01c00034101c01d86003803007003034081140d4a06000030f51144500b51201040d41c205802c00900a03100240301c400a07920040003440140da000c0112030300003000400d0701b51141c546042102e4000c01d03544101c18180303d42c2a0004070aa13011010b8007151100c15a420406a82c4c2c0302807a080c0c4c4811100d06000071010000c04001e441c0c1100030f0a299002801c0c14920300340b201d094180340500c1920240c0c0416106820051315607814022940e81010540c003400040c201a008a044d904000d0001418044003040d8003416074813450a881d01000300101000360241d5819405d03000308400c0c010540134020007002d01c03000c1030150b00043c0c05594002c5400006038650785003121130f500260b803129814041048050981070941703201403090b50042000052039494800a40d10f172100c1d207000050000424030040203c09404955242c0c001c505 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 4381554 1250 4380304 4380323
    0x71e080f0604020c0601030c0503060906010f0603021308030d09021f02030904020a110a03080103060b010804021806130e010501170d0503070e010c120513050f03031812010606020a0501050f13 84
    0x70346000401074043c0a03a030b9261442044000401d04c41c03555001401c455040c2c094815503128440d03030ba521030409004a0344801d080c1501002014460b600800400c1c408004061201380c03203003480d500311b03842103a110b808287c07617000302e00940c40e10104000074220480162103008074201806901c0703000300c07161b00c1d11456000c50a0711140b405541c401000011000986900340c44601c0c000e49606000c0c04251010f91504011f4051540500101d0b8010740d0000c000d03880a441c8001c00b074410039402081280c01041e11a0b0b40314103242ca9001d15551414900000314080d0305000c4403042c440c1d40040202040e6100c8000d070460150010704403a0402107510f40421b505158030010380b02c403156018003d1108840f01c1113545802e500c20090030002a8030b81210003110b5880082080306800200050b6040d0000c00106c401032340d040203c1804184082c00f00d680301041c00a455084416560205005d40c1004c8112820490284600c0d90300500d4040141803508180a070052203504200d4011328010341c = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 4382804 1250 4381554 4381561
    0x30f060902030d0503040507120305090909010f0e03040602100204030804051002010b19030201030507080c0a03020a0903020315060306010b03090a02010c0302010b0405150109060c080a05030c040f030506071e080f 93
    0x4464100140d6503401030300311228140700c00e07030040282d4011902030703482d4061081301166203024074000618141e01642d6890806060f0344c100b001031072019000d04020365036411006126030f514040d2410000000d400355032035602d0040080d08003454504140c55079481040148001032090040e9010340d28160703040762400c05090b000341d004180c884030260f400b070f484680d03a01280c40300310003900660b4800e03a0b084c8001d8840400681c2c280d5429074240c0c0101c91705010a41e0704a1003507002e802c01020340e240c6001520f036240c010074204030110440101281441007003080900701000382c40c0c010080d02c0d80d914a540f6040f0b065a071035115104000341000050101241403501c00d410501400038018000c01c0075042010307000c8004554034034070f680460100000000d000d80500070b103505260b002007a079072400450311011101540010000c040c80d00b07082c0008521074007800c08842c042c61280c80100041d0802c0640a800c0a44030440e809c03005049488a514403544064243e8006000d01324000d4541c4 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 4384054 1250 4382804 4382813
    0x6060d0303020a0203070b040b15060304021f02070302060d0606020609070308040605130506030a050a06050d03080a0504020a030503040b090310091208070905040e071401031416031d010b01030e030301050a030f 92
    0x8a86c030409070182c1203100c280028000c516120500801c24030380c440f0800701c0c03100c083c804540422a40a984180009603550440b1380c00d44013250f445583d031040c0d52a00740c40ba8001012a000362030440740c0a50380704424083e0701e40411109070003106030001407041910b980d0341d481c3c4920072070003400100040072035502ca5020450782c0d890080d040042c041900e82c5442d0380c0d4580100303800c0b12980500b905044000615040440c04440d03139940558070319200d80d03a402c201001526018104980140b5401c2d00080404c5062001d00042c29030030410a0390749005da400c1518080103481041442d40c507203810000040c40744920b032020340c50070741400407a580d900c80f070035640c55040760311641d006401c001ea034000c40ca002080c03200903503091508141a007110040110304450001d40210031450048000c40d030300070145040751180d10312500c1c0c00700d1400050207142103070411050a201e610303034444001c6a91980c25004050b400c0344130380001c504640c90b202c00200d8080c640d1001410481c0352498003c01d10 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 4385304 1250 4384054 4384057
    0xa02030f0307020a111905040203040f0b0408030703060803040b030403030f0b0301020a0302070c09020415081315050906070804050706050705070902071b0b0703020a0b0702010e1b01020d0206060d0303020a0203 92
    0x1603408022603600ca00c1e00250213511110a14011039426041c50b00c46140d51605501d8000680c001880402d88242000103010003580044e209442124100c1808000180800501481980308400490b181d04000501a0503207d69402c8102c0c503400610007800528005000daa50054144c079001c61440718111002c0010001050955051350001407003d12043c1c06400070408076114503031000001d03555004140490059004880c01c003101c40000d5400640304040e580e4002d0501c60000542444560312298518041d0030405105511a000c000142a0500005612002c035050800d07561400e07075100e58a4490340d0082109200c804651402400030401c100d2015200301e0b4011507480c0102c1c14070300c46540207c0b01070142500c0504e00891607580d82416504070b240d264004000b42d100781d84d0350400003480100881c0c1103642e60311400408403030811091041080301c1f51005070000c101800281004a09000003040d9031000c0c042c0030254403402d244070382c0d054141ca00140c4a44400c1c00480c03d6 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 4386554 1250 4385304 4385317
    0x3051806040501021e070c12021305130b06010503040209070315081006080105100312030504080c0d09080d090608041415070201060f05010804111201060504060e1f030210050a0203 79
    0x11842004100010044154010000883c0040c0c0c01c10a20030000c5c03d2010b1361250100050061480440c10462100b041c51440f280174801405480d029405c02c190000f00d0740d0494480c80011034400512061090071035406811170f00070b00c1c1c10340c6140303081d801085500720060040420035030741c4d61b80d00e8060420600d020001c1e01440c001c1d034103408414003144028001501600485500c0c5c000820040034140b448441201d03400100b80308401c3c8804401d6000340402402170340c0030281004264040c00003404a40010405501c0c0c0d614083c0c1800540c03032401341008000818031202e05402d100294001c0c4140e54050350149400760800311035010581464840d00b400c104840c080410321406603011341111082d43d0391a060024040c4ea628011150800190780140c00c000050360b044000342006204988400303107110000c154a5034500c00704003143c91a0b4040c4030700300000e509114000b540340042d890000c48000b04940000d0075900003440c444003000610f803d102002402d90f40550007401036480 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 4387804 1250 4386554 4386601
    0x606081605040b0c0304080613050604060e070515070507060809031206130606020619050103080909040303090503030108030711060702010905090414010c0e100201050106050d0905030903160f08010902010507030305 94
    0x4450002e070741c003945c2e00d82182c000c000ba50700414001800300c4030201c55018075107030010010702c4203032940e45800c00107040d004040c050034010ba0303102003540d44400302000100401c407521130f5910816030504a04040f616080130081000303d00521006100010070343d4001c80910711a081d541d291680003501d0b000310910090141400e08100154403900031454500c104400c50300d028402c1d01e1020382004484007400000d000007402d01c45440b2070300303002d411564854464240012118025140c00b841c60300244e0100440750b20005400c010080c0c1c007041840300070025188182894000d0f03002906086540c02002d004440d00710004080c4030a8005000340900b00d10b000304011b84110314010007200e201c248c818028445041054444d51051080604a40c0a03a54213404c0000c03d1800380080c00c40071505172038610051246441680d0700b403110a42c41d10303011075201c0c0c80f0f518020340700100310750640c815802a45012000005030b60402d003200c00884d4545800a0b481c0d0f1903845164800199002814 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 4389054 1250 4387804 4387807
    0xb100318060f050103030f081e070e04090803090c0f03060a0b13050c03011a090a060f020f0708030703030b0d150b061903050603011b02070e040c0b0a030204050f01030606081605040b 80
    0x30300e514240e5001506a0b4029919000505000042550040d5040d20001140c9c2408813441c01d07085000c1d01202c0c0c00031114070f000c01c280014100040c0a80b0028074068401d20f078000207111061070108101d02200400380c642d00c40501c1a480020f4030707400c0080c101041aa1035030810040350752910b04506103100d4000e010800c600708400c0c128881d80090050f08074a0003040300c102d114403854002d48813001d600401015041d0300f824412a1000080d0b142401548102d0506070340d14101400310002526441000359103a00700750070010141c0d0f543c88089801070307103a4603071400468410131801104085030300c0c0204590141c40e010030150b00c250400406104140b960383c4082981c503405c80340c05488210001d02c0030000c0f00d0304806a03000018000e4001d64040141000484500c444103a8024091a020400c480e03030391008100c103500c0300c80700b40006540010305224038541942d200c1074500c000c1c03a0810916040030b0001d0075011000d44800e0100c201c001c2040d46840c8284204c5019107108003e55 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 4390304 1250 4389054 4389071
    0x40e0c0f0a0801030210050405060d0f110c0109020906090c0406030c0e090108010507030501080106050f13021207020307031202030c0306010507050106030606060504030212010b061b07030c030308040302010e010b10031806 97
    0x14082c40c42804124400c140880824001e14402c00595041d80c0340100303403a02c0c240e40310200400919540703072403103400b580750800080e07a400158003811070046481d0020079842c4948c0304020460400034012071252080c441889040305004080d681510090704001031290740081095490004101c40141d10400c00d00021403a5407041d0021405030a00b84c40512040e62134180d03a5090348c0203401a50342220340030300c052280d890701050007081e0003040b020051900c50080360407152010211820805680b00007400810564080b00c80b000ea4541720700301b1425803c08040c4c65081d40300c05030402d41005004521030b003e00c1001c1d0300c88401075034400810424556941c101070610b800921059128202c0614041c589c1c98060140000601000b807040385001c0002000e0300001c8242c2005440e01d00c581d50000c800180c200055402441c000d44070601945840c3c50002e081d1500c51010032640e0b410405c00800e5503c9000d00101d00c0a2242004501c0040d041c108162062203c1d0010f040c041c01c01d00070 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 4391554 1250 4390304 4390307
    0x14040902040f0e090a11060a0306030b0103050601081e070b031e0f10050103090b01060503042108060a080c0a0303080a0b0406030807030f0203030f01031b03060911030106080a08040e0c0f0a 83
    0x4200311843c114040e00c1c40d80d81e2483ca5511210b01003400f0b0250711250384804094900f48000300003000e21070400185264aa459440c00e00000742c00840300c0da40100014017850340c0070818100c006a16050440d001504641c80503110300d441d204052100f2004030110703070412800c0b1011160800446890034146c038143c07030804402c903c1a9841e840301c4040304408152548240a00c1d4440d0707401c500e11a02a07407038940704481c290700081081d40c01006181c5108100413a80549052401907a510012281004002c00804a14a600c030480b103030720040e00115aa11401d8064003100e81505101c88103a03607503c1c0032809071110a0b03429601c2454103602004101c8608003030b06169003e95a02c2446880b00c1c5ca0581c0c0c0c920092314154080003001c401000040c500d20b088000c500d0851100c18222030f980d90f1a902a1800254129032107803045950220f030341024401c034802002050024201c540c11502e4200c0d213841a80681030b1403503802000a82040824002ca43ca0301401904156945518820 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 4392804 1250 4391554 4391579
    0x90c030e1507090503030a090e04020d1509020906060304050a02010c0203010e0f030714060702100902130204030b0609090705010f200304030c06020606030105010303050a050304020a030b0901020d0e01020a020606011404090204 99
    0x21003101264880d440480d2908001003987c6c0c0f204580e40300c800c0b000d42052612a03001000800484c0d10610000071000007070070755141840c00301000c03440411904aa4410000480c0c0d004007000e000e600d00707004000c08102d0000304101401d40a003003131000d1180c6030000ca0b015125000b5180d0700ea2007914941484640004010000070b4040c00c0040b4140c1c540f0184c0584601c01980d080c4010b0340310405420b091030755580201ea802d44014034003c54442c0c580c1201c0281d1700254001e842e100416400c05c009030901240d05d03179000ca684030240903d5428100082d10b001d150301040020031012103032049111424141000f600758000d02200d13112a564a132826400041d4040d100050241c038000c0340d880d0605000382da05a07503050312143c3c10071a03250001c8409410003072090780e00411002c1c0000111305000c00d2030f4062541e6100142c1d45400e03003d070050a0700d01305811601d088e031040181140c920b50120f00680c2200007441c2444400c02c55800c501c02034062500302c000228800180000c2c0c51f81d0910 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 4394054 1250 4392804 4392811
    0x901031e050304121103010b09010501050c0708190210020106180b060906160317040c050d03030209040f020c0d050918060d060c02070501080c070507060f020708010f0608012004090c030e15 83
    0x31005e40807040740c0402c0c1801e031410320350040d42091921005204a600035405080d480c03031420200c98080740c0d42e00280d482c107051031702c021b11b420041410080c15070911094006c00c90615000074051185401d00100002c44070189800d4125507810b42080f144e47c0300c00803103400c07080c000c02c190f803200704543c9981c072002c60300f0700d0840105494204841001c1e502c510042d10854000c000850118a4002400300203450844200d040581c20041e441e42c43c0c0d01c502c0340740345101a6280050302c420b10255240d00e0302114024803018400e0902441800f84e90303c42c29840c500030700064030003154231020081090035a0782d4000400403400c0400500a080c0d0005449003115400d81e40c00009854a0034400103c0c0705100c409003a41d00006018008607000e0400e03510030f02c100d881210601a52504942e084442000120700041d86a5604001c0b80d402400340c0d00c01c901d8542c402d000d40d8844441e00c000e03140300703611074080701030b41f11440044103c0c001e50161030580c00171030684100e050341003c221251031045 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 4395304 1250 4394054 4394063
    0xd0c060809061501030b0a03060504110312090901171c050304020306011203050d0504050f030a21060605040314012c0607030203060315090f0106030302030a090605090901031e05030412 81
    0xd00025480c0342002034554000c03010b0000c59900195601c0044014105494500b600f0900003100000047c8503440349500c80e078000c4c0411138040e40da040816040150181c00d08031081e006000003002940d80440f01c50454400c2e404125400074484072190031300007044030300308421000a1078540866001401180b180b4822829a421a030702c0b01004805a52015000707400240c050025100543e04c55100a80142c020011100001d40f40100d1a11b158001e41707007200000d00880c10710a92009902200c02200c1c2007403010300c8580d0403c48020401d0240d0300c409440a54103461078100443c080d8041c1c0342c1044410080c0142c005800703104040d04246980581180c4244400030301a98401c0c801e0713034010000100a0002a0300381c900b07000f1010409050001c150207066074048201e4801d200c1c00e00190300c02d0700515202d0074065800b41600555a0100003400010030500031030703964800c1000d05403a4801801e2140300c241e201c0302d1032009800b1400030500d102c006804211034080300016041a8401c = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 4396554 1250 4395304 4395317
    0x303020705060301060c0609020a0803030106020c0103140f041709040204091b02010506010e060a02030c0102070c0302100f09060f050c070e060a050402040f03060902031c0305070807020f0c010503060a050d0c06 92
    0x240c1c010310034640b01c24402d420011b200c400d42000042c03015086041c00500060840840755200c1c803d030741c1554000c2e80320340050380c00340c202080c09503094020151501c8216214604600d00310b03c42072280c4c1c00041009000b5850300300649134482c220002c2da149040060000c540b0f40d81c40d621000c000306500c226a500c0381102c0d031081c100e014414090b0510406042c0e40da44182201c00d8244541c54000d0740c8124150b010501c1043c903106000d00c003415180340100c840406461a500600c5901008640c104042018a0500c000c1d4160800c42d680100e5985d0314001c00340c0804180215124007910312015658020f4000003d80490040f0000d4021901242c0c40034002d9511400c0104a2007035200f000801060302da0200042011076000311074640c006015100c00381150b030503403000f245d01d403003404020a9030350b4248101a540301c40110381c85880c0f030000340742105120860950b904140c48941e03042100010010780070380c03901c14011004041c040d1552107103d029250400300301e40c0c18000c00000607003 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 4397804 1250 4396554 4396559
    0x8040507080d02100e0c01140a120207061a06030c120a0908070b1005030a05150c040f080d030c03020901081602030408030c0f06150109060f03090209090105060102010f0b1503060d05030f0403030207 87
    0x810307031124401d4140c40724640c2041c0d601e0411695001400c03154123104c207079440cac3d6440302c0d1940010480c80380314600015042040ba001c24000d41818108140120801d10412616850714801c0380c1c108600800c10881580c1d403103509c0005000c000c08010042e890200d5060100120709000c40d0090070309104040c0103a0310341060682c0c0306e00024015004d54064007400590800d219082c07904120403501940c50161a0124406602216070100314240d001030b000480b80c0f6450710034510418900d19040d4540303000e200c0020030b00341c03003d4030940d051841e009942c400907000300200c0b0024544141541e0310f07005038084154503909038100100181c0514400602c07100c11010076410b55186c141c49507143c0d00d00b0a1402c5600c40e00d45003118090558403800040541c0e02c00c42098898202e44001013000d20b8240002402e540503090034420050509520b02427a54481000080386e0008003012900c1c0d80e109030006000207200000034180f4080000c1c1c1c900340b011000000c01c00c0d00d0182d02203030141c65 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 4399054 1250 4397804 4397831
    0x50a0c0602011b0302031005041b0e04060506030c090d060c0203040501140717030919080a0210050c0d090305090d030c0b010b0307080f04050114010902030601110102040807050108040507080d0210 86
    0x3c000200ca80080c01c4110541c03d01c00f8002c1e4051030300030300b001c820148100c0c0c407603011400f210b130444403945019200d401c181c0c0e1441e81c49104054481801d56081c00b1769454034010031110701000d03015510b00c0b100032618001649480c0036115205400c1101489151420309001c2d4a80c0e109002d51800160740b078119400d0301d0300c44400c49001c198810b07584040c0c00c10408590805e034001810119040c00b82c3d865041d00e003074140150702011030060304c00a51380c003000b20300a481c00301c5030301e1140c0049081c0010490441c01100c2034403101d0480c1000400d102ca9036181c106e0b10751040742d103050780c021131001c610703410305d07a000c42441e0b400c500c50400c500042e600c481e44007540d07000c21552400011031a10001d10440419440309070098450030010540691115a03501d403820260403c08480d0343c00b008002c0c0c95a4400b1a4a0345041c070f100c02185010305015a46480341c503940605414810800c003c2000c010742000320130010803d0358103445c6203103869203000f500c4840300400803020b0303400c000318640e081c0c = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 4400304 1250 4399054 4399061
    0x408010b060301080c0418050304030812010905100e070201110706090203010c020a050a030e010e09041103010501050a0303020c0609120a05010507020114071d0111010e0102070204061a070f0c030807050a0c060201 93
    0x240c4c445002000040c140300204400b90084500b003660311111b44a04a000620800c007510186101d40e0b40c8a0b11440c1c0a805c1d100c0050b01603011078181c030b061009100014103100e222034140ca001c03c00c210b0303840d40d0307070340e006e0340504100165800e09000c0001c04070300b4040c05910516031544204c00900810700e10002c101d0352540030400c050100c0d0010603034000041d0003010a00249034040c100103480252003800291380b990122801c0c0c8480362843e8820016160a214560140c6030840d08021400d00b1510025900e01d580f00b2501c0c000c860005000146a9403480d0101a50205004442203c3c84078a4942e018000a0f5080c070095820b107048140400044100540324003101d070754100c107481030085d41c42046200070000d1410b022401d58500d1307020b507081c0102d884e00e2404c2400542d0320303074051041c00300302c60781684010003441c045498401c4281d1488119580c154000240500800490811807200007069000620807500080c00130104000480c1814016014040d442c034a155a0390040e800d8 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 4401554 1250 4400304 4400309
    0x706140a09170a0212030405030304050f0d0203041404060504090c030501180b070c060e190507051002030a120b090103060c031406010807180503011112010b0a02030703110f060403050408010b060301 87
    0x4403442c4408481e25141500c000d00320248080c4110345c80f168044803034041340d510a40302903840da00000f00704014440c04000e015181c6460384002c044164200c80029124010340c000c084801e40e488203460b84980d620740141001c0e1400801c1000882442d241103c0030090703900c41100d0650030060843c0c81d000902c0e640d280d07401d810054003091907079054811500c015801508030b500c981d8800c40c01c40c2d440303420018445c20780e10f0300880c241d500b901c80c00d0552820f895a401103100d01140c00d81890b6495011081d00c01c031005c1810019441c0c44045e80c518068031003542107a8111034401c00020911485d908005000c04035a1400c000b180c00340c00f17400018074400c44003076020642c003001081d14603106401101c081c40c902007054080c01e07195000242900c3d61100710407405403001c200d20441000c003101c040c0c010011282c0c02c42c50181c010b00d02a40303d00400c103000c1e0601c40c181c000c40068650900c40084440300c10000c0d0340729880e1901d005403081d08180200c80a42d803a020104030f4030706102080300e05 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 4402804 1250 4401554 4401563
    0x40305040501140d140105030f0307081206030f010504060b04050603010b030601030b0c1204050106030201030b0a030c050126090a0302070501020703020f0409020a0e01060503060906040c0c0312020f0706140a09 92
    0x503241c2001e0055407005902c200c0300e0480d01c020481800c1c3e4a28074801c04030186242c11001c1400d502d0902050b15000a480760206290020000400043c9031103041300d6000584820300ad507035990f20300010b820425419001c001d154204410442008030980c01100c499104950400464a920050508032450649a607406a010200505c086041c0c280342560200d039114049180c070310a206403076031440083d241140c0c2e580d1a042c0074002c544c1c244c010495444020b03110b0072101c5246131601c4e40c0f4140140310302030501c0300700700c003a11244e0303d40410051440c0306981d50507074905141c841c41e551029001d1041c2c0c010700030703010080b400790310105026048a07001001c2d20740200e0002c00b00801040500000c0b6480b4400030b400080051b1003032019802480b0540b40c02c0c4d200c0ca003d40070303c400903900070a070b207204629002c03215111030b8122411201d842d41515025100c03100700c0d0411030080c442c40749140300001000c44c1170410800141c1003501c01242d0482c90300c0940d21021918000d84041020040 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 4404054 1250 4402804 4402807
    0xd03020301060206070e100e0f030109060608070e0c040608090a0f030e030705030304060203040605180d03021608060f0109091a100504060b03070504030f060204050a12020f01020a110103021b0f0303070206010905040305 96
    0x810117423040340d401c0d0f0700100040004034402841c00000382110324500c2c0c1100d100d41c60f44000c011340301044c82800002c00500c5400b02c0c2500e80282e8807800d0344a81d0088205004c04070000c01c040074020042c92503a2a44440f0b428200700d5176046c003400011109031a81e100c3d1241030404109410040192400c40300c2540055040c80c0c180b51007929540c000c0d044a4921002c0002c2402030781d5586210700c22198001e0300901001c0103080c480c1c81c4500c04239041854603038040340c14405441d083c4c2140504641c00742c440003907181064541228842c0100c1c0510808012407002c1c4188141a04800e0302111401c5400b002502d40e42d402d890000c2c0801c0780c00c02d010800a001c200040784440c115002d103d0311401c0e00524213a00ca0f8001070b48001c1c43d402001d9420380781000b52003181403070301c01501072110900081c5449140c60707803000c61440040300590304054020449401568490801c6408194080140c0b129110b0014000b980c03600b0407240ea00040c407845000081c41d44807481141d02894045d603409 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 4405304 1250 4404054 4404079
    0xb070c050c1507050607090510020102070308070c030c0605090d02010e06010f050d02010507080301060c1202010b03060105011101090f050c010201181106030705040b0316030b0a06080a1d0d03020301060206070e 92
    0x2d5202280102c01c802d810402c19480040c0c401e00516100702c3c1c080d00d0b40c0821900300828000314515084c004025a0301c10000c0101280e004100320760f00008503e443c01e50f400c880c2c58119990041c007039004142904000c14450003020206014440182981c000c010b040b40b403800c3d0350f503107d400b03205410340d2504080042c0118244a5501c071102801810054580445982e411010350701c240d0002c1c000505400c4007008203c0c100c0744e980c0d40d040240c8001c1c090086200300083d111a010300c1060b040c00307030201d00880304500c20f4000504c8550808020001180c95003400ca440e0003c60725100d0040d46000c04500361002a12140c2c018107400519404180d2141c1c414007200c0e62010700250103000c818040083e020384000c008500c99114405500280b418401015080c0ca0a0b104800d2003100c080d041071140304e61184195a100103507507070120b440f107420340c19800500806480c60485000c0c400345011002c0d01900194100d402d43d41c00c40d016591403a2045600c20510703035840e54410130b0380040 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 4406554 1250 4405304 4405309
    0xe0d0b06040207020306070903020901090515010305060310020a0819020a09091503020a17010f061a071104021201140f06030c090102010615021506040606020a030804110604030602070b070c050c 85
    0x12540c449006040140740200e190002841c102040340d5407030000e560038605000710304015807000d0045c8003403c01401607013008521608007020400b0440d0406698400280e8542d03001c00409480c440d092004550b2140c0440c0c00400f0a0011503aa1811065280305034034030440780c0c821583e2a202960700c1c800710f80d060140d840003400e04052102c1a1460b01c90000c40960f49900f08403009002d145c1140b51130481341078099003513030814680c02c0801d6141a07001c014465503038240313200c40156180455501c01091800750360540300080d005800134408174212003c03185400d441d03030503180d060064211110300c241c10004030341d0102d0f4045801c07100a00c0441c00301c4003808040c0c0050981400007044aa44412030315004030104102800162f01406401440c504d00000203508404195410b100107420300502a603160040f500c010b042000120008043c0401001c19036003411009180a0303469a40b1f0802030069000f0510039581482040d020491303260103940f40b031520592080240410f18880ea08 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 4407804 1250 4406554 4406573
    0x906051308010f060e0a091e0204021b07060207080c0a030204020f09030a03020309010906170103141204080709180309150203040e040605150105030103081801030e031206030d0e0d 79
    0x52054400c0e28010340421150402e0080c514124815140010b41c24030705200103805800203070a0402462501d42650007042d00c907448041c40381c8180d1041a8007a0300ca10208000703104100e01100018a96064100f8002010404900300d070704941c01c84e0441602c60021071340f20a4042c00440d440042d00c402000141015005080029401d29147e41080c440201090600307507110b0f0110016000010124100e44c0c0052580000e420145003a02d4688201c5e0740210f000041800094180c405401c0301c080c0c810b104200703180d864031803e400e542c0c840707507a201318540d00c202e6800303560b0240e410a6000030742e0010380090714203200c0d01a50784041103850594810010400c0c0d490207021404104804540452802c041c58000ca02c1020001454a03081621050343c03009480c020303042100070001003000c10b08800950b0540e56444441440150054005070010002c20001c010540001314240d640c2c10307c0714102134403030b00e003d80540d14440031445c011180c00c02c0464038a94003043e24000e08010800400 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 4409054 1250 4407804 4407817
    0x140f03030703090f0f030201090605150306010b0306060c0d05040501091502030313020109090207030816080108100b01200a0302010b010306060522120503030108070501020a11040c14030c0406110d090605 89
    0x42132003c1500c03180c44000d200c250040c0c0540142c1e4440310600d04010092046a620180713010030b188400f100240040d880756018490030490b100084003103455980c80e0b400b203c0e0b403002d4100444041b062403c002801580140c4586400f10310070030400640f410a121071880c1c0b10301c10b07034041c52543c3d0b00e0702100e119264100c0001d030304015040702c01255446151005145841c026180d42e41a89450000d81c6120000ca038241010852031200400999000246040007034520107000300c2c100800710012284590519a440c0440c1e42124000030103110124102c05128000c1d4001d1005008950043d410395050348940c800140d4201300304084510054049508002044d40314151039036244410441062141419200ca070400001048071300d00401c403107401003000380091710104c02251981e00303010010440c0b29020303d440b04011032540d482200001400c1d80306000040c1c89080c0841c011035507410600401d00410401c1c800c7d8444044000b55001c42646550b903003001c65400c4c0710040b12183c1004 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 4410304 1250 4409054 4409063
    0x3030c03110f0c040b030307050a0201050304050102090907030b13140106030207030302131401020d020a03050712050d090b011406030c0403140703080d09020405130f020103020306061213140f0303070309 89
    0x1a00300c04a0030814000380314034081060061400f50f20b9002008103c580035110140310703900420041d00002c4001c100c1c29450ba40900f401502c0c0d58407420401d01900c42d0880741940030107a0420403241c5909640581e907900070684082d60b60080f00d8036003c0c12038100b8034841a020110500400400c1c1c4650002c1041700d1007850091b05021000240e100045150741120310303d040302008020035540e04000c10703440d11505100501008445407006441440b403004080d040940c40301e00b48c8032071400b62040711070004c010102000f0700f00e010300300b0f0100d40e2000e008900c1c1e040342510341c9204518218059900404641010328509440e40d43c401c0107114003c005a071082c024218004085540000602441c0000200114007400288108030403508014200e600680074a200d00021690220103135280507420b0130010382d6615003000203072a0380a0f00000034821412401000301058011803401001c83c421079001102440c2e0b03040958850001508080107680b0900000b148a031003a008000e640340513 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 4411554 1250 4410304 4410317
    0x3120c02010b0405040803040311030a05040303030b06070524070f0e12070302060f03040501060f03120804020105090409080904050105010e060a030903090e0414060603010b13020f090901030f060e0304050a03030c03 94
    0x440c0c045801c2c0c940441d401d8401b00c401004010a06420a40d110440745500c005549800030210025129003e50300001e8101903031015610304c9d50b200c0c10100d542c8940c0003812a04030030459105194202d40d191006a40d030b92140001c036000d113000d45501c40c03004000307807500000203643c0d40c20311981d003003100070301d10b40e0b807181020000141c0c9a40c00101001d20070440c1c0581d892070300d410801d003500c00c143d0008000d4090340e00d040012071621401100d402980d490190141c0d1210f00041700d03540940103050364014070b000500c50800800400801141d82b040e54144026a41d8000550306103080c1030055030060301c10030000030103074800c0d4446440d070752103030403c20541500c403007000450340d00442d012180b400d124400880001020060340307501c030320210000c0c80b200100c0800315400c081028282d40700710f90041080c09103a8074505c19a042e0120140c4074483d19a076905080c0301c0f46041d008192511480e1095203102c1d40300100460307007502c6019100c550380d41e1460707808a507120400c0300181d081201 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 4412804 1250 4411554 4411571
    0xa020d05090d080c0a030207050315040221030307020c03120a050403020d050106030501020f0a1106010506040b0d060315150603020702030604232b02010212010605031b040e07090503010903120c0201 87
    0xe080501388080501c0e0040006250038a00a0f2030f000081d080a442540100302041c8072002210400758041e50640f29183c80d00800c41d0321609120a20312481c800e400080308100c0d0f015400600e40e520f080c0110100c401c00700516a034183c00388550410700b0700240e000c00040c005030030013481300c50240303209100000340c80f582d07901c845003260894800c40410350000200c0401069201d68500610701c0286d0140c00b0301d515000c00101c0c244107606c9038002c5e807075000c03a00f0044003e85a02180066030000c940201c81c0d170007244821f0013048555118078107080c603044c002c01e44c60710a1003030b1251158098010305003a02d441d21012517031074060300f0b280b108100c40c10519100110a0142040222207a0228507003840807031b6102c1b4190006a4207901168030500c130200c0c81403c1340c4403d50442d10707a428066902c4c0c46010350ba820072808039007000783d6920002030000c0d000b00030030429441140182d950014143d1507a082500369650200c2c0580050f0480e803503440325048580c026000f072403150000060000 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 4414054 1250 4412804 4412813
    0x9010f0203070c060c060509010b030a02010e030708030c0d02060906160302070611070609020102010509031201031205070c1403010b04020406020a03080c04050d0309030203010b010305010e070804020301020409020408010219050a020d05090d 105
    0x801c55007103900002c5e80303c1000001c0092034081d0740c0e0054000d00003400820344d0800480e996000414020f41003082e1020b480015031020702952000d00380c15401c1e00d650b802456134051351403010b001c0700170041c8039000004050050102e8910300070b04400b243c0c80403031241000102c0103500300b0001980c4003641c2c0c46280d0820864040100219032150350003055184c024000a400c440009080c2e8000741c000708080d801c109440c400090540b0382c400d41d00001c420800d00c0840e01c60144060080014460b428040790f08a880003040246480460090102c0800c10050200380d01071845140d0140e030145940c0c01c006400b400c402c681c0400011241e6003071503a650000303001c4181d5204203502140c10342000b401581400c0c01030b900c03c49800c0c2014440d075494841280e0300b1041c010112010885910301180865034203404503070003400b800c1c005646860712075a2941c000d6200100c80b8414508044000d5507040c020b10580d0012540e03a00904006601200c0558071035014104a59000701080406800103 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 4415304 1250 4414054 4414073
    0x10608070e0d030c0219060c060504050a1b0e100513020a0c02150c12090604030210020a0f0c0602060703051b091c0303020a08100b04030f0203010209090103030e01090e06030309010f020307 83
    0x203e020780c0c3c80c10f10342da0503801071100080001c410b422031090250740034070000e504a1800e2024950244001070035030342c0c0d8203009040103014000200b814010700e00060001420b103114405848196090343d40c103440350380c1c004030220141c0c8141b43d0000c1405000542d2800302e076001c1e021400c02400c1150b20305250b5170000d038002d080e0100c54031415101090502c1c0c070420411100038051aa041c040b441d0012620005880380140d1000a0ec80c4d900300b40d600800d544244003481065070f0100301091038a00700e180142d000102070203404014840c2c5000103280e90f1281c000c05000341080c00c0f00d140c810f00c811950307151590014130b040e50012201031182c00c0441c0da42c03001c1d0801c81d010b0b41c3c2c010307251184808011311800c006030120000c0c19201e1030a2102d290808111002c80781e0003c140e807007450451000c01d02a02420841710350181000000109061f0041544184000700340e9550540c151a4610042040802d40c0d4160b0540e100b4809001a9409040940d12501280c0105c1c5e040501942e6098140c = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 4416554 1250 4415304 4415329
    0xb120102030702010b0d0f0b06130608070509070c0201080a0e030c030c010f060506070309060302070c03050105040c0503061f0311010c12050a03060e010315090c0801020705030c0705010201050c03010608070e 91
    0x680d400001c2010050382071050300000340d012144096640210344482c50304101a600240410701c142012401551b540c800254404400c00c000f8000301d81d40f040c103240c90701b82c40e01c00c140c050301c0600c002641c40c1e48920040520503905840d580c03150344401e002d1000400c108065014144800c000d403401c0013100300b01400c40c5001000011600c45040c45058050b07407110390116000f0740b001d000c05000170307820840200c1903543d1854010303100d0403103052803442d030004d56102401c15483d080912060004000c10b94080c0c80054080300d5107901ca0620000a014082c2d2044e84480e18888041c80014109000108044414580240d400000c1d4407035550744070481300301c1d501040e00000d00806c0b454050241000602c9801811401c41d031460b01d940b45901480c055031100141e5500d685020403408481e0003018007482e034000c640356406441c0c030759a6607000384d2002285210f0080001019072050251601c205804940141940d107025010340d441c1c04064603d4050150146500c0d2250701c0f00d44801c0d01d03 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 4417804 1250 4416554 4416589
    0x50f1623010603050706020c01020a1103190305031b0c0703020108090c04050106090806090604030e060a0309050102040f0306050a0506061204060209100c030809120301060e030f0a0803090f06010602060a09060b 92
    0x2440b510714a00185001c0481d8044d40c01e40d0040d90f403660940e82c012917214616604100d00c2d081003021500000d080441e180701881840b1560107440781450b07402070146200d0340d90707044043d105081c0290b0f030900714001e020301c4c1000d43e4002071003840154801d22010303401c070000b10125000701e142480001d00f5660242c2203400002c070b84280070000e166042150703682010401000e0b2019051544005002141c10050140504130001d000081d141c42580071140e000e81001c000c649481c0c445002c420a545a80f0040c0c468a0030100880c119044a1041fa4011070009002e14079004a000d50b61200101c020803d946d8641d0038800ca002503180c11491400011080d0344845100c9a1440d01600c40e2a01900203101070b03000705030410310012160102c81c150707812420071900100c25800017a1134014a040300840501031000c00350700300040b040255004011007010f41d07017200c0c007082e0302c507070303030380000d204510040e403140010410804259105804080c00340b034000c41c56a03502c8011424408140c4418034 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 4419054 1250 4417804 4417811
    0x2040305011b030b03030d050c070b1504060603020414010305061203041203140307020c0114040308040b0a0e10080a05040f0204090b06090109060503060406020c0102040e09030408060601050f162301 87
    0xd4080704012000070038410141810004c0004090110b0741c0d130f0003070b507421800495031203012400480140d0305840c02180d05c605007480c149000150000b503c0f07020380009003e01c1c202140490036500a00030394003034611034580785030216954001100a0f09010380015000601d41d21a0344280800b440204090407401a001d04090514130b001070030401c02c0d514114984400b442442040c0341e010034800c2000009203420290400d01d5140808a4070595100070050b000c001400540c40d07800c54090000101c1c03603121410b0180b0307071609029815001c420b103000094a20000119860308540c021074000d4042d410f1000c241400c2d44c04a8202e410050050705c512000c14204840c6251240d03026002d8100448144940d5107030102190f5105000750000b4400d0b500400c0c1000501d800358140c60003080c0c1c246540d149030030810308081d101c0e070050107248024025a800280e981d4014030403581c00c800030646003807900988501c0300311403603100d00c0209c0328020b03140000c1c0b405c10404280c10005112040002 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 4420304 1250 4419054 4419071
    0x100213031209051e09060f030c0a0617060109030309090509030706020d0203060a08010e0d03090f06090b040501051e0103020103090201020c06040b0405040515010c02010507060908070b041a060a09020a030902040204030501 97
    0x650380b03013284040c0f81000211002c2110302e48038a05180d82001c4140c5400e425031181d800081d05268080709001e4205140c40c40000d00150b03c55843d02408124480c039494580710400110b03038802c03080c00040c1c046801001c08000605859008940c00090101070300d007401c42c503945500070b81e8081c25061084640100c18429203190807001400108130060007042029241c00000e81c642414400210a0641e01d14044007409174407803400d00a65803004041190444900d00f0701e0192031305650589180d80f80034001008102c07600d044e06141c0c0301480d08048140e00c1c41d4011400340030944002c90450150300d450000035160400500090b1910020990303c40c2d0522042c042101c200620540f0060a160644500c1e640c100c541040c4803902031820a0341c07203015041080290407070700b1004007003582c00540202031001e610082030145210b031917540c0307201704502500300442c14150707003150b2f000c10040c1e003c10042000780d00401805c155401c02250140d05a00080c040340c03c40e0b4001e840c0b0365161140c0 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 4421554 1250 4420304 4420309
    0x207030504060e030d080c09010c050312090f010b01140a050705010c090602010c02190b0402030f032a0610050603091204080102040302040b060a0e06070303060305030703020a02010216030510021303120905 90
    0x207046543d00540c0146a01808110020912040900b03800c0481c1400643e400c52030b4403ca6184901c40d40003401c50703503203800c1d000b000810316100701c030210340c0c500030320703000400129040c01041c0f00c0d50070503520306518241100184045500100522052103030820195002034403c1c00b410a5400080d10b03000ba07824a0840040c0c00e42c7c009105440864110b0403561440308502d11503034035244e81260781c880441d900e80c40882d103028800600d2949610010074400921001d07842040c00c9400c3e48902e01051295003080c03d55649419036581600d40444102400706d030528502965205079248101c40c1c1d034680e00c140c0d000c00b035441070700015160b03500020b003032007035043c20301a2010070441035a4180c60203542c9038000702603160180d45584107000000340390342854860303080100690340100650707541c0c940c6440d0103961402500403ca015002d04060000b0305e600303044002d41103e0f001000ba01c0000090302403e002940a10b0711011603003000180400490305c11001c1c1540381c44240c81c0d10070502d092804 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 4422804 1250 4421554 4421567
    0x2060105040207080426030c0a020109050603070f0c0510090804050301050f010602060a0b010c08030a050a0b0906060d0f0e030a090608090303060a0302010e03010605040f02040302040b03010504020d0209090a06020703050406 98
    0x1103280514010012440040c01c050708a13411580c40107095240c50078405101400316420041c000070706e20012440c00e01540c000300c0c1030114039201f40c8509046590b210144101da000840b14540803602c800e4002221900825444030b03150b03c50400d803142c006401c0340034030072180d150a060b1654100890144110300302441000e80055240c1030306645903142c00402540c0744002000a05c1840d120360360728080b07902580064446681c44071145441e464152000c000400044911600c1c1758140040c011607410220341c801d001c0c54014001d5403611150140394005040c81580221910b555509040d03010842400030708807000359a0344040c41246094402070914a0203007480d81e8940040044c800d40f41d458280b503600f00c3e5420309003006a0022200001d004100c60342c06150042c0c10080000145011a402001502e100302c9080080341901c100345030803030340f08031402900103880c1ea40c9400075180c203401c2258000e400004442005109030759160682c1c01001040740031030b0b40810300707004031600241c = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 4424054 1250 4422804 4422809
    0xe030a02010c020c0a0f05060714010606050a030b0406030825020402070303050403090f080a02121009061b0206040b0109020306130c0305010302090c0306030703030f051b030a0305010f0b03010e06130c020c01020601 94
    0x46172502524102a89500c4848480c80788521071031000a912003002074144100b1110706019008001030b44e518040a0001d90000d524680003a00d0424150300a00c1e142c03003038406581d08001e1030790410480b0341c0c2d0085220070488250407111002011040180e41d280024150103110356070100346403c2a00d806810700c0c0c001d400c0f104c040c07051002c0a0040160000d540e07140c07190103c0d0904880800242c051782062540c42500800a007403050135800e20070f0715000b06c40695003942c01c1450559158030101d86440059600414141001004000c2100550099070300500000c1c00401c8814446612900300d03200c01d070f041e001003a11880104198a010180e040d1f0203000b0b15103162451400a00207611070580d1b02004003408814181c01d4a20381c03140302504d05510702c017003001000500ca4400560740350006045040008e05207030020a0454400900d44210b4007198101c60444c1d003090258000032900400c5540c00044807090a10501058081c6040150307254001d401001c0010000904021b0140c = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 4425304 1250 4424054 4424059
    0xa020a0b04031203050601031413050d0e0d1101031104060306080111070503030a0e01060803040f0f060504050307091a040f020c06010b0a09090b030a0503030405030a02010f06050d020906040e030a02010c020c 91
    0x144010004240741c07220f03140302c0c0015403800089981e60031005034002c10101c1540f0200c0c07038141c42080400c1c2801141c0030341a90052049400c101c401c003000702c91110014503002e8104444040c02800940340303030040642e540050501250090f4511208151070f041a0320440020392107010800c10410207110750b900054222604500c2c03c51251142507a4303101c00740520410a0342c5040c034544459003944007401a200403001e80e65110b640e9130100d415146940900c0490002c00f000c0041d482e03000304201e0702252805000303000080e01e8030982000406150f000c0d4250000b003a100364945955600c5012040180c4c1d41c2c0040e01e0b019080840c0c0d1031b0030b805810500f6565002c00925822540004c07c4104a4006082c04940c0410040c0441c1c2042c02d0080020410712010061108000010024101c4113500754020802a6000710250058070f0790f0313101d0a0380183e602603c04015003013501540b0391020000d030000c54546c2511082d14615400b0040000060751340f5100c000d02d41d80d0500169001d00001c = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 4426554 1250 4425304 4425307
    0x2010510060c060f0509031305030106060c020d030e09040f060b0103060506040911040e070504030218010302060a050c0109150203010f050108040206030601030c0c0c06080f010909031e02030903010203090a020a0b 93
    0x54030000c0321002050003a80148a41c05119108100c0d46800c880003220104000b440705091200c1c80580d070b50020140c0a071281c221110101d95410144220811580d440e592600c1c18007640d000c0c8240091014010b8080003000c40300502c2544030510181d000d9417162904820704070700d03402c000048079a40001141050309188042003039503150707001d4409980000000058400c0f005120030380e503118070f61007070035101c2410b002c2108154110307010340200c0b4001d6030600c600c03000b8040c11116445c0240402540f0000602407103004338403d42c0908003556144000040c420455141d0b0025103246554000060342c0000060041d2251042c002c0d0040200b07082c0140d050405500007501c2c2e00001340001d04056880d5404c5600ca8421091501c00940003814009000d80f80c030401044410111120080b241c0c01400002d501c68581c81031801254243c0c1d140e0000756485000e801c07006469007010b60840c0310074010400281e4080c4000c0d0302602e2404d0060000292610600410000c141d01100d043da90 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 4427804 1250 4426554 4426561
    0x10e01090b0a06030c050702040f0b090105030303010605160c050306180d0c0c0e060f060301030501052703090108060102030c030409020301050a05030d050f07020103060e010303020f100213140d05060c19020105 92
    0x8900c0d010b00c0542e00e050401041a0510001c1203545c0e0050180207036001e801d004801001043d0390340140c85412059a104036203a884800f490341c2e0703100a110320000a40c0400103500000c10307407035411500300e10800c2d80c11403140e540d02c0002c1c580001507030201c1d0000309043d4507111708481040140b10341400f41c1030046000c001615291260150b42c40340440d0615003000056071b658808884004840c4c00405054880d6180d041150003444200e07941c044100303042007501440130402c0340b40d40c19040c40800440c501003011004403010750010705058154841031009006650080c4080d001501034464016120349c50442000300806039588420b0098102905104699a2090449401c4040218030a03a1042948012030044c0a40d500c401b81c48a0003c0000c03081507404200400d48104000c100d80001d07004c14441d204a20459150001045070524200300b2000d030002003001854004000508110250700d6040c24104100e4258982e00000210410344036624041d04010100910081110b450b = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 4429054 1250 4427804 4427809
    0x506040501031e05070f020106060207050607020402160b070c02030106171203070e03150106030b010e03030313020d08030403080603120403030210050603010b0d0506060a0803030405060f070c06050c03010e01090b 93
    0x1146014140c100b41d00e420001c0000351611a025910000e0b407101008503162054004003658640c20032007005500700f580c0000e4484c40003480d8800c0d504c0003070009186c60f900c0e40c00c000080d80201d4070a007c0c401d00e50325480204180080a5115400c0c42c2c440b00c3c030110713480c0304042c2102d8460300848944a4284e202d41d0000d0400144441d09103458880240d4907180e0002c00e8841c00450b0030707540c1d4588190109840d09040700b03551035048a049450610a40180c00010340b2420014980190154000d00000d07034040444007040795083d002800c00e0a10461644500c51f265004031025408a000c1106020450804101c0c01da810319606018504050441c3d0f0000c0d11201d8001e00219090b4a5401060559030b0a6001c031a07540002400305101001038988540c40d503804848086c45280d2149000070601000300c1102d11460f03001c0040c0820b561100d4491100302c07005490101007016004100c8001001841454010200d075903803030b81c880d0b2401440345090368058020a6446050214203c5181c = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 4430304 1250 4429054 4429057
    0xa1e14060d0512030103060f060602030c0a150603080d020306030d02190605040c0503010507020601060207081b060706110301030b0402090a060305060402010e01050d110301030611030106020703080c011427070506 93
    0x50310031208031200c85802c0c10628a40f0a4100e540700f40508004000401c00031141e020184490381382a043c09250f98034903040e6142d0040300e0707440d41c064000c4120140010040e08041b034480d90806800640c554407900c5009441d0429113165455030360000510006160400078454280301c00c3c8002c18490101c2458001480c1440c41d006013000c2d21600030804200120580402900d40070f00200024940326000039a600c0c000c0c49600e0242c06610008070300048042107103801c0e280b0034001030310160101820700180390300041080c0c47c0c1d16941e20003114055440300c0254001d501500c41c408090078140100542c120340074140c04443c1d85071074401c1000503000310f0140e6100f502400d003000d07010140401030310700c0d104070440c3c0d81c80301e40b0306690701740802c03541406181640e000301c0041007140280b40d0781d206184020b020314805a44a11401c200180e0907034004c0c07841070148400881e20708616000700d09590b20039541c040385400010b0112404904200310701c1032030b404071801441030300e18000114049 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 4431554 1250 4430304 4430311
    0x11b09030609050c04020c0307261c02070203070608071412010306020c0c0a0f030308100308031902040509070e01030b03010902090105040b0d051501030201020f011b0c020310050a1e14 81
    0xd140c44140010030b002d020312040003104c1c405002550307079100d035440403174481d80691011110805001004144a5000000c1082c0c03030100ba10910f181021003e40490b00c403030041120030500360200200d07030058406000c0760005000c40d403150709043c10003210261484140725011001900140040b20310a19207107003040c11250045001680c44019014036418003d8003850303e03030440410800000c0c40b40d60405e017002120f002340da5100d0315844500704001d420344141302c0a003020b102030010903250315400f0b42840b86d4800c5110014a080d64407804942c814200312112804a00401458110ac0d601030254100504040307000300000314290303000404041c811300840340125541c1156070a1901c0c0c3d142030081035600f0a0417210040d103034560200a0700c0d800d000482c010b025021041400500502400000396052411030f0340c0206180c00c1152086403d003826a4184070382403d05880348407078030035180140249031001c1141120350450035030381042a0103501e421450150320b41007105000155907003 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 4432804 1250 4431554 4431563
    0x304050105070f020406080f0c0103020f0403030810090507021507210507050720040b01020706080c0d1b020105061e0108010e06030a0b010e0703050105010804020303160503040803070501060305011b0903 89
    0x2200c10b614180404032005000c0002c1d0001e00c0c180c00403e02c810001060192440c100d022118801c50758401103060f8081d141190580f41c400307000a20009000344005a40503189030410070715030b0340d101c0001c026504280c0d20f0740050b030032021641e046084180304a545c0019941068814042030291781c89802c400c840c218880d00c0d507500f011645031840781d400c841c2c00c19041020105040300902c2c0e040c40a0010004c0700c1d2086243c443e01408950002c14100300b100d0660325806a10b03900e04e800c0300342c95404100800d1001d5960030300517800c3e003144c0f42817182e40c05080c2d00000700c605d061420300100043d00e20b400e1400c00c81d1405040780c6680e01c00c1409054070b044170b03c01d400ca9194580400d1078038001040082c000306202c0004150a044020550703c07500580d503007407299998802c0150f5500d0019036001c1d400d5001045644a815126100d440e902d0f807260049914040c0d03200042415034000103070031038284e5145c102c1007082c8182400f603024480092181c1e038442a2014901074100c040d140310090 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 4434054 1250 4432804 4432807
    0x703080a0b0a0902030603060609040503031305030913150e160507020301090803040302160b04060504050d0c030615030c0b030601020706110f030a08010519030201050904150807031b0806090304050105 88
    0xd0a032202500118104000542403602e107039158240000a07410031192a0700900c9110006a082d18101e2000d0303007e16040405503286071100c030403128aa500d812016502884200b1400303a081d1961881c2c2418018a40740c006021140a030419102c1541a84500d640780c0c0030380103004081d141c0c00520442001a818600ea9401461010030b01401c04a003002d840a4404007c202c24960003180d9100410303c0402d07640745140d2074003a2020340740954042d1500260b0244400d002a04082184030441c50050aa081440e0798954a003000d07a05084a020f0108894007400c204100030951403501400841c403242c1c1c254070340b00c00000d6465101e80704081c1040141018800c01031410300450f5444c1891030280e80d51408a154003074a0b0702e40c284181801440e0407a111008421303006042d00660390705030340315840c0c001c03004100005000b511b2110b903d8240da4280024600c03a0400035240210702c20070340844040b1201c140103544414580c020b18090b0881d508100303040d0404812a400c1c1c9100b401c055 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 4435304 1250 4434054 4434061
    0x2040302030d080402010516110a030501021b0304120204020304030302120a0f0b030c150306060706060b03060f10080c030915011d0f0106080406090c09020313060e0102040b04090b01031b0801030c0f0605070308 92
    0xc9c02c8401d03c1415504983c000c41d0102c14000190001d19070361550b07685018840e04e0342c000d140d035a803142d0300c58007204070545010000185050780046030807a0180c5009801d0a140300d040400d4440d0546200d40d405070354481984048035640501c190a0360700304c000e00b040140d6603000c18100b11078581003810b242070000000303089648200a5500d0b142c1c002404000c3c0c251036a0003458154016035000707106060782807070120a440d040e481d0303003100c4400f5a1070014035260100b000b1025000901102007074010b02c2d0a8a030503090b0005004e000300966845840c1a56510fa9015640d0030042c1840ea050b00807100188000307504951483e420a90003100001c01044904025051003690f0f000b054a0b40c0c000402c0c850703c132074144082d20105001e69010081a0061050b281c02c0344034900c907045031a00c09110070003505041d64401000070006060110313000081450a0304000310092104020030900801031040c04160000e030406002c4501804800d1410b0081c05001d500a05000504000008000 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 4436554 1250 4435304 4435313
    0x41208030714030a090308010e0903090d020406090c05070b0109020405010c140a0204090b060406080303090c04090203070803030124080705070b040507170109060b100504051212040902040302030d080402010516 92
    0xb001400c00c0100110f440341042c501000141455020a50001d98103100101e601c20003119840d020f0b43c1d10328000c40c9440100814040304003c0307600180d0744070385d441d0b200151440b00750103546800e0050b980c0e22a0b803501c86140c0a416100180c00070340c0580e00c1400103000d541d0b04030030086051504129880b0000e0782e96801d1601d000c031034440094120341080c0b00f0704104440094403d0060904460500500703403a52101c40d542c1c0000c40701c8000030382c00020194101d04065120030005400501500ca10b10b46034850b140c42c0d5442031f8842d090414401a5018180510b5400154804060300c5e102c1c03920b00307004000400c203020307040d006841e840210000c1400c009080050900400d91510700328040505000207074000c0c0314480007500d4a03030400d09158100e00c0c2c02c45114206040945030740d0b043c1400c11007801081500d00705001814800d0240000a40d690040900300400c081000036030340703506504c145030034070f03d410f144042400095000d0100503a008815110481951424104419010f082 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 4437804 1250 4436554 4436567
    0x8010e010e0304030327060503010602060603010c021c020a170405030d0302040305030702060306030a0209010603020c010e0c100503070908010f091707150209010e06070507030501060812030a0f060506120103030906050412080307 100
    0xc0b400400c4d1211b60f0005081e900007025504030384064080d140c0d41d82e185000d06003038902c08803000c80141c0001c000d946800005803101d206204c3e180c8105c4034804031030740d6592120600c441408044840c0810200658942008440208100f41ca020b6017010b165a68041e070340d015403000240f0449010002410301e0302c082021b0101103800501c007881382c0d42c0da00d501400a52100d0320b01d16442d4200a01140d00b4600007801d1000c0703420140409041504001044030283c101500b11000c000c800b6500190a803002d006113200649000310004152005140c00740c1c0802003041034048201080c4001c80c0410046002d0080c144410040540d61701540001200c520b00004007156000e50041640824404001108015248528000c1140585407116030784d035441510902d0107145010000120146015004156109015070707010503000e88900c00101b594003c24201a0a80c81c040010800e06da80300e83c0d071000801085c2041c900d00350510003014056400a20b001c0d00c2e085000012429140c410007 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 4439054 1250 4437804 4437857
    0x1003020708070f020108090106050a09050a020c060103050c090f011202040c0e0d060207050709060b030a09061b030f060509090a0204110702040501080601090e03030705040608040507050a0602030408010e010e03040303 95
    0x4026030b200001d2405881c0c9049001099000a40050008842410520604060303034001403030415040e20307007914100035040080614041325000d1006402d001c104010f810701851045010b8210074020308280004100c004184c0c401400304c4100404c242c1080c08100d0040b00e406480201e01d403040c0f2501980e203030740a0440c0301d4024a2081c802c105000c06c5501800f401e5210b1016220155030392800001624414002c00468000400c007048042c00203030702070f201d003520807000820031002107010070740f042210341082c1010940b10705a0080405c0039200b50000390100f180e01b400a820310300d0a8642c1c80e461110b000f4041c3da0303501d0040e0382003c8400d007969100fa070b000748107000740d41c1c46030304180d155003081c03141d41203007800e100030303a0b0580303801109503441042c40e0b56400342080c1c0740101c121200c8034041d000342e40e04d01440750082450344401380c4207800f51980b41c00440e83c030740c54a540d550071039000c4200c020503039141501c1d0300c01017030010048030100c03038151070501511030507850030301c00602d1103d = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 4440304 1250 4439054 4439063
    0x5060c0a21020709060501020309120115090209040506010305040b0a020c01020405060a03020a02060703020a1b02010c0b04050d1d0d060b01020f0a03020703020405060402120c0f0702061602150c03040510030207 92
    0x88001c0941c081000d01041c055250340c280c0b43d03c640c0d522084410f40300f1a0260324056003082c480d001f0141001140c0015000c561000031900d1840c15002c1c1d80302c804140c00409445400183c1a40c050500c1d000e0a90002028a000c000e40d203000d4440700e4035098058003a1640c940c0024540c207010009405581c060300303004001c6680e82d11080c0740603000394010582c1e200540182000121424000c0c4250307007000304e69403501180030050200c000410804044101e052000002080010450012040b882644100300400c44117020303020190180c0341c00c40340484c1000045030402442c0d01c480321080007031544214049255404000180e082c05500400c079090b0344107011040e0305150f80011101c086038000d640802442d268034041c803050f440b40d5603014a20f421b200c40820104000741004040740c00714054581d05194803030380060f04943c015a80a103100b203c5012600035407074034002c0300d16400c02089459143c01000b2001c1502e90046105603841605480f10400358980031350115050785610 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 4441554 1250 4440304 4440323
    0x30a02040e090601030c08030a05030103080901050d0203130203070504110904020a0c020d0b01031e03020c0108100b04080601091103090a030c03021002030708070207090209031515030109030504090b010503040c05060c0a 96
    0xb00780103941d14030034030099643d150010b000003a0017401001b100c08000240c1d5456286a080d5260002640d112000003810841c04208005000c000e40c40950b002d02c0001240314100202e5004051511095070880c5200710300d01034550200da00d00030100d5150040503180136032101c0142205030303281c040110019411920440313140c420420038680c2c060507030703100f0070881c49200861850b0900180c91503a000340903a005003812401d940c000c2d0381d029400301c034100f00c02c61440d4480c0c01c003a140e41c208c3d0b401008154810801480468054000c03100ca54403481d1001d8114500440c0945e5561810040070382400400414042898030a00a407105442c000d41c055550703080c01c3c00700522004088a2140060140113000716001103d8000c840301400000c0051218940704c07190038159240140074003450300740240520620303131000c3c0900e2000070f0283c2c4400f40c030703103250128500949060048190400c00200104030005501c10a0082078640c1500d0564442c94030301c000500e0310b030a0042c0035218991 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 4442804 1250 4441554 4441561
    0x4060e0409020a060f111b04090c0807120b010902030709030f050102040806070c030f08040c06030e0109020a0905010e0c0301030b010b03070c020a0807050a05030a080904090f0c0603020702040e0a03020a08030a02040e 95
    0x2002805c001741c2d0551503139288494500c51810b95103403841d00003002541c04109a102c107852409400085040d03010b00c0d00f04c0406d41d40d41e05030b02d03e00400c6512400d8800000c0164009100181d40d909005040d0041d082d403847ca055070703009040000d01c0c0401804003001260380400d1000941c16107016200f5601241c2c91400c103401d0203841980400c0044000403460301c00c409103240b054450038040c0c1e034480750088080e0306000c0143c01604e0601e04505056603101c039900c0240c3e80e4010300c48010200c40000092070350410444002c175044c010001c1d4a107400c10070040000604c0842c106045030700c4024555203989440400710f8008400c1030700a94461007440700443d03185d50119042c41140c0d8100c400c140007030355900504d5154100a080030f0304003003082c4010600c5081c02d401c0448824881c19030101c9140c03566a8003900001141c00c0f0900103a0301107881021801c1504c207884651043c40001e004222103594003d550f0845182d000b043d540001c4081441284d864040d2000707441c008114024503d0b = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 4444054 1250 4442804 4442807
    0x60a090902131809051002160206070b0709060206070c0f0309120b06090109090201020604021002030c0f0105010801050604090b0a0b0f03030a030906050c070209070507021302160201110705010504060e0409020a06 93
    0x40b443c0102500c02e41c05034082010080e0912400b02d03640d500902618501804603c424000c1d00408085c004041c030202026005a841c04020030069120f031100e21150308002c003008000d0402a04034009560104051105054016944000256200c1700c1e10845040c5450100c0b8842401d501100d140c03030b5010035203420030400c013000f00c0c4180e1040d035545006030303a503074404400d8405460020740942c10007004500941007c000f090900980f03801140c1ca020403400c08549083c103401144c8030306075507900061015000030b01070680c01c00802c0701c040c4203c40381c41d22113010f2480c02070000d2410680e10300300c454858a0b900404d400c081402020b0380e8076406880c101502034910300f501200c0d401c1c0303000005410951707540300366011143c0145c8901c00380d5540800a03a40b5501c81c0d0010303030780200ba24200c989150500e000400004590307030404c15020400c0d20003d000c81001000c41c24143c0c000d91070911150f41d102042e20b08039121444c003000900d518001190041c0300300c20029422803002640424a50f = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 4445304 1250 4444054 4444087
    0x12031b0602070b07050f0d020f040314070602120901050d0b010903120f081003080403020108090309060304030e030c090708150f060a0206011e06080606090414010e0a06060203030f0105060a090902 86
    0x29000754840c9006945940c001c07107403071280880d10616440c0a005145101c1008d90140030015084c00201d854583c5a13120209030358410901c00d083c0f0340c850302d005c3c06065410310015486c2c6103c1080182030001075070010740303203001d40a140e0041e2a650710f10a000703a03200b00003c00c0299000341410100310740c07000f0000d000801c03a040344004039190401190b080035143c803060040700c0d008042181880d09541c01180d03594005800d00d4218803060001964a0780e03194001c6000e54030030b4407088040c5480106044c1000170740881a44212001401c1040e89504800711a034024410b00c042d0318403400b08400141d0030000f10040e650400008155511010b0700011000d050f01e0000d2550101c40300344101498855050b8081d040c0061440f102141443c03c101c0050b1a02d100010008100c002641c403c40b000b50b80d0980c8a20700c4400082c0500c410440240304550291500344051451031501001407060141c041c459140140b400141c0f20900320301c1940c5520240009420a43d1f80702400c84151521 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 4446554 1250 4445304 4445317
    0x1140405010e160510030203090304030c08010603030806010c0c05090c07060f0c030608030c030a050f0c0f060103061505090105090c0f0f0702040f0902010c020409050c040207060203090105060109030302030412031b0602 96
    0x2031060704000490f031000000000e00b1140010140c0384040651417040b0007941014000c1403103440240400710000300030a05d0b19019254420000500c18518207004200c000050000e41c10b0265003000e400100d803420018006840040d91003602986072141c50442c41e104902e40900810720b0308401207030303500c290707000641c1c01d03110356806028607a00e500c915a1a41f04200d440c8100c0e90081001000c02c500403c09450000c7c03d061405081010910382d850910022503200d01a9070841d40c0117000308400c85c070a000c20b13070600d180e4500a00d810080800d82c03413407060040741d04c036801560018130220702c0c050840e68445603014034241c8a5841c551a5606074000800c03c91160303041c4500c000d9025801e2140980054050792000000f440d1a028840200744184c801e03a05402070640c5545561141d0000b0300c0700c00d2242c01c5c016901d10f022403107182140e00140406042111000081001c40d50003c15503080d00c0342e25a441e68011034a24003641c10455074252260404008a8810b09221306035010b44032 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 4447804 1250 4446554 4446581
    0x90303090204050907060203041505040f06050901090f050303040b07050c0307030302330a0216021504090501080111040513060801060b0a0324060c050c030111090310051302010503090114040501 85
    0x2a4450781013282d29502103000c2d131001a8421f01c0b04000405100f02810402c2503282440c9103416100c60b08482d900301c03140c1054020501c00101032030b055910038440d000030151400940c008506100000342c07203100707038491380c1d9861001041800c14894140701c50f000502000302103610703041c2da03450060342700c00ca0384a182412218601540400d003410f40b00383c403a41b01c0011000354107030361200d01480c001d421510711308020b5500000c52a0040c0c80d07203645611034010030618107842e00e10703000c0284184c0e60140c0014074241d051032104500b440000382a030b07041d00d0040712070018280c2c0d080903a9004006036030001d101e42d82000400110120b05d100240300441c1c0f01c4c4d40a00200441c1d9a040f91003403505400000403c24540f030401c080e0744100d047c0950030b4407076000c1c0e072140c416040000b802d50340c002c2c8031010f840e000051116014582000190351008010b40d003070000c2d28100e0b000c11350080801c00c001c0d061190000006210710401c1d4000c0f10b450756000c0915465003800e06010307008051000d0b10b0704 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 4449054 1250 4447804 4447811
    0x3050a02011407030e100507020414090d020a08180d0b010b0307270308090102101b020c12060601050706020d0207030e040c0c02060910020106050619020105010605160f020102070504090303090204 86
    0x22410720000301d5103c96010303140c460350004684140424400b402c48202c04014040c000040142d441c1e01035290b06075215000e5800c82e090507180305013044050342c0807006542c4a4200e0000065102043c1d42c3e40008010f4074109a0340030f03402203218110b0f2090020304400010002244645001000d107025074915691a9884a09201c041004210115859030f1000c0d000c4401c000050134400206010350042c810f8444540c3e0402c031000c00c0d035684001d071600001c0c4603041704520316410002400d02c07242c1100c0e5003150001d1120525102c0401400741810800009600b8052282d19011103c40d41c0556408640c0c4018a083c010281104524541e11403424110103d01c014490701c028010315800034446441e12211108100280d00120315100a42d501c0f400005181c0c0c2c1c95401804030b0191031040b104400c440d11200a007102c1058000209024062004202c2401243d810400c071076449210300c401000b40c0c0c0010b0b4980000c0e644511b0740681000560420554550841116544241d13401d1 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 4450304 1250 4449054 4449077
    0x602010609020304050618120403060605090714030a09050307120c020901080303060f04020306030a05060118050f010b09010c020f04050106030905010501050604080604020105030a0e06010303050301080c0a030320120403050a0201 100
    0x4000341d20040e02c005c0e0040d40200e022900000c5182481c48052800b40100c0c0c048180100c101c03d580d41241c2d000751a015501d0034200890b0400c4c46034203a206541d49098010b80ca80c1c440324003100d0002421012400d95282c20b0710781002300400c00c9501c0e10390015130010510100380d200a10301446d58030100c0c02050310304000220404000284d9003d55001888941c80752030fa9028000250401804558144a401405404981d0900616001e4034501810100c0f0032824901da00030b9440c050b00c1404881c00260041000300c9503c000e071104064246489101c224841c000200e240ca080400e4a51152410000080b06030301079000204c131a102e04024407644e81c1c0d0304100217050159118500b183e801a40020340150710400045a01c0340c548e070000500c5400c0001c14610300035090f0000c6020540020051004150400c124007110707204803020b051140c295600100410100c02e134102400c1041c2d0104200c40c0710a02407407081d41813140d580d5448980e00d0609070340c0d4024048090780030602c45a4007 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 4451554 1250 4450304 4450319
    0xb0c0c070308030603010e0a03020316020a050402040308030402010f0810050904020402130e06130605100305090f03120703050901090213050709091b03060509040305030105060a0507050f060411010509011710050d0c06020106 98
    0x15425000d400d07402540c201300d00cc0810f0540002c1028040360b014800e00c2000c100303643d40380302410155009a00103626494079100250a04a001d0001020300000e041080110340001e03441e4402d481c401d68402075291203130310104011b80620002e4a030108501d00010a1290001a49601c02c440841d2a6940c1d03000000c44503003256003600449070456041024451240c0c020b0700102e40050719441204d5481d16200750050540e040300e42c07a00314100c40041400a2143c0c1400340d2a04a52000c0c000c000c424502d50000789000b203a4004007107182d4480300000c55280c020700303080e0f0080071002c800b8460403105014ae0785401d00c9103c0524003007858140040b80c0c03410003264480c403030b03585600c4140c9140d080c4810481c0ca03401c414011402c002040128000042040c00741c9001111440b005140ca41003902d001c81c4083c1c101c900c1c450401c0740034021a0026a448a07114103c0c49a00304603500c940c032040e4165101c40035581100360031258090000b800c01a400441000b100d502d42d00070410103880328003 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 4452804 1250 4451554 4451563
    0x60d030e0405040201050412050a0201180e13050709090c0305010c08060d03050f07080a080402090109020f0702041d0f0d020601080d0905040e01150b070b06060c0a0b0c0c070308030603010e 83
    0x100640020484150408581460360265400c54014184642001e42d44e116890781b4100c1c0c0d6408807811740100d00305104550b00540c501c0c2840381c4442d41da05246043c082c086c040814024007072800c00503410414400d212090042e54080d004200301406000000d0074100c0180b2064031044620350701e80349003181c00078818640c060041400400c0d062103021662001c480f560002028008035282c100311a01c00180c80600034140d03c0c40f96210340d0094905401080140ba80503400725040d00d004001c80c01000094100310f450444c1e044500007404d01c6100c0c555841c401460346030b10070390700c00c0f405201000f031800298100c00810035801c03030f20f1583c0c07507000450b00c84502c1043c02011641e155403d0100d803074540c03c40800000f202000044031948952211900d0f21a030380300c00030f407810014440c02400121100785910001c01d0703c00c43c0c50522080746403a521400703d030300501004441340114041800210446800e0301c40981101d20260b100d0074034036040d50060b55068425882c0c44500c00c0080b80224 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 4454054 1250 4452804 4452829
    0x140903030609070c03030e03030703060302030d0903080a050d020409020f070506090d08040b0405031909050102010c03050408040302061309050f0a060e04050d050306060405040e06060102191e03030b0d060c0806 92
    0x400410240d140c26006944c50130b1070050460034582c541503180d8240d40100090b6108443d10758012810314a18014141003403c0360300c0c203408001c071001041c00421088001c4039035000340c1c1d140603595808a0030081d4028080c80c1c2104170348a0001440c1794034400701a02508219014900ba5100303520f4500074945d503480b5000c518000300b544140013402161205103200d90060084094070701d0b2045051124240200144ea8040400c020781011f0216503824401d40940a0140c00d041100781010b480307c005500403884001d218100010f43d2540040200d2099002005800c00901c41400d0281c1d00386004d40085689051072442c0800000d10038080040e103c6c0101c2d00040548504080c1503400c99046d48004e0166800113810040010249c503a84507075035550300040d01410960800c0c2000a0500202000c050750120341c43e640a4089842c0d99441e00322614050a0f40601c2c9103285010740c09403800b2868564881454601c0f1028040540c0003c0f03080c0310310390f46003400c0391340e101c1c100b1643c0c4130b405c0b = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 4455304 1250 4454054 4454059
    0x30406050f040b150a050301090b0703051006050306120703080304080702100309080306040b0a0f0306020d0f06060f120b0a08060403080a0c020c010c0804080102040807090b030109020f0d02010e10031409030306 92
    0x2000ca1381e00141d20040c035922042c003078076a6002544076008a825111003190880d803d1009004220010f903161041c107030044440c402c00c8040c1407405000074200c1c003010305220310502c0000000404d080003002800e0041d54081c4010791a0314150034001a250030050b0140e0040341c0080d0310a0300184a8802c01516540c00f080349811610b603041488010045414440d80122100001149011035011008001c40c03144001503a17a9490045003030a0700e000d50540c0c002c0030f042a0091250176080100c0c52111407686c078141c54446400d040c4203016007100c11020b0782240304900041070860300400d0f120f1140d406034461955030b031140400941107901c501400e80c010b030480b268031140c0d51300c50140c1540351802100340ca402c0589134110603089a1059010400340e501400c0200701c6010140504100c6420450007080304601030b4021400c8416201081c4d84a07900c499004011603024841810310800040c3c110300141183c14000703001000602a040d803526250400101101d40000440c2c2c41890301 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 4456554 1250 4455304 4455323
    0x509010303030e011d0109020103180201050405060d0225050c03120d15081c0807020304030213050a02070609120207050406030c06080c0d02030a15050d030906050901031d03030406050f04 82
    0x25074404500400c01c8405660f555500c030200102003145016441c0c1c2c8140e42c0c00c000181c0418588005800c40c1d25070f52508228500d075110160260303030030600f40c0c0c00b01c0300c050700c25503a10300d041380703551780240325440640300032008180d400d0520103a00d1900c00c7d0420f210b04200e442040c0d03500d041503a502c81d4080701008402041102c0483d9a2031a00074400d074030306800380c2d0055292074041c51030501c0c20b0301c8200155110b02010707011815601c9a00a40c000c1c2c414006075140c58203580208a405060000c4440c58645030408180c03c0c1210f40c0c111001160004410051001a07140c200035201c1480e00381401031017002400f20f080c0c03502d80702d51406c495101d043c50b10404d01e407040075611041c00802d1031448850602c0b03150601d030034030300003540719480d14540044d00e40141107915001440d150006c0c0d01840020500310002600549031000b69290342c1007044d00c60001000407400b410341c8240340e1034800700a08440d07032a06d40000145006c0c6200304814005565121881c100c040000ca170060200c600 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 4457804 1250 4456554 4456559
    0x7080705090d060f06030c12050d0908060403180302100801060201050601050408030405090601050f030405030903070e09030d0e07080703300c0602030601031103010605030708060a050102071e08070806040606050a050901 96
    0x3042c0e10001e000708501c00086580c5d952500c407160f0941165200c8070f465591011035004214050152440c01580303400c280b05030ba0304000c11380e07684100091000341844072030329540031000940c3d00d40e07100566006240d0311b520541c078003004040000030300c118070240d07081002040c0598040c1081d03070140c1c0c0f41341c0001c50034030380b0707100800401420280049040c4902004a4403840c24403030001c51103180910000d560b0b40d10194103043c07600302c15502c905002e00f000340503c49038a2021003118007805017600d02040031200b0805003410300c45640d205036141d1003015000020090504011508000715131600d01e2110840c1420071000c500309280c0100156125031904000b03001a0f000e543c10140615002684000c40c1d00d20441c150f00a0700561301091001c000c1050071075015021a9209800703842d0000302c0ac3c50a030001c0d50722140d034000e41540c5030307a0b0403400b00c0440302016098001c010510449000702d545040c110780700e0405884c159401402c1c000d01040c0b0b410544000300407640d014040040c160b1 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 4459054 1250 4457804 4457813
    0x8150d170c01050408040e01050406030201051206010306081b01140f030103030f090f03030c020f01030908180f040203011401020d030603051e03090306090309040e010e150702030c0a050607080705090d 88
    0x2882944440c100c0024001a0036821003480780610a521880c403490795241030024011007004164000d601c00c608000d41480140d1780442565a80c0100c60080300c2e040c2c40700001a0003a000d15080440382e44180c00301142c0700c503501418100502000e894481040c0c6404410f0005485140309044110008200400010744550340ca402c3c08841450403018130358031034550301d1202c066603100390005100f8104160652038940c4800d61003110900b0200302c5004556104140c50140014100e4005100c0e1040400c03038913425000d820390000180f08665968641c081e007202c2c07034040c2009030300500c69a814240064000d100d0b4500340c1b5004801007510394195020f45000380e0010700002081c0c0410300000407030392010070490703009541b0b8402460f101c128402c18030007100c0316200c0c068000d80c10b182d0400c5c0148400300c0c80d0012440403565900496441c1e01e41a880e510504d074241c007051184152000500c400400c02500900b155652003046454460003101c95000d0116000e40c011205002d410009 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 4460304 1250 4459054 4459073
    0x5030d0c03090e04030906080702030304030e04020c0313080708060f0f0a0515040c0306090b01050403030503010b090105090a0801020406080604050622150f030203010b030f120d020d06030807020108150d 89
    0x70300c2072a16540c403940b5058520070401d001c3d1411000f0541405c01403005a400c082c400c0d07400303c2c040c80218150301e02a10000c000d03903c1001c4690041e41d0001d4103104148051044480101036502c0c00d40540e5690502a40d85105900ca1341c00c031402002c003c5200c601300852100d01a00c81c0d8055802151100d550580c0204009044401c040ba0800500d16841c1c880f402a0341d104101600c2c001081881c14402c0d9080d902000b10490400c84200000d00001e9080001d0364152801180b42940300c0900c0001600c0c02e11581c080d0380d034024503500001900c1c1c1e0054005209035640ca903183c0d6000d45440c020320040e100d00f520041d03030099408807612408003040c058074020004806d00071408145940703400d4800849c980128240416a040510039410240100c0300e80985c00c0d4014400901300c0a400e5803520810740304002c040c0c1c0000780f010006101130b01a5070115003000010030555940c0d10380b03c0500d030f2101c5000c0b40440c1041c0d0002d000f102e250381c590b80b0303044400780920102120994801801 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 4461554 1250 4460304 4460327
    0x3140c030417010f05010503060115120b03030c030c0d030504151a09090706080606040b0306090a02040302040615110c0303030a0e010615020604050f03030c04061b02040903050409060b0405030d 85
    0x15031205010006040c015607000c0c4241802602c00010088041c41007401920416040103000c3c2d44107000402a540001c2001401011245807007c0300c25290b00040c4003418140b90b480781e0610022522040003003001c002450021004401c031104080417420030340648004441c081c0482c015000c070240725003c4c070303006490040b05203145c00d0544c1d01c80100245c40c40c1d8044c0c4116010ba070100e0000d01c07456401012494100d40c003110f505043c135240000c0b088251200070582c42c01440880702041403298203030151000303164018000d112440c0c480c500d0741c694500700050500040d0b0030702020004018082511481c18001070099480d42c0d480031324140c064843d8400d100b502d50750b21140083d9605540c404c3c80c0c00304801c3d0380601418101400c02602d426040421166140c00c00c209120030482140c040b1412552542004160141a50755807483d209070028069006030400d1000d80030103501c08010001e589003450b08020094581181904900a0f40a003581552201c0580002980070b02c80c05c400 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 4462804 1250 4461554 4461577
    0x3070201090b0405011d0109080304030e0a09020f03060f0d030e15040305010603060605010f0809060412030f050a0b04150602060402130e070806040201030617030307030903020708030a020708010b0301090314 91
    0x55041d0305941e10010308030115020344099640300d00c20000d4142c010a480d4594641c40028009403440e5269040340e072002501c024103100030a01280740343d07120001034100400b08944115240c2000d480400c0c00c0350f01c115030003441802d089100300500c1c68819500e45000d40c040d51030201d00b074801820b00c19655034020a901c511030041c030002000890034010380000d14411440404c8071031908002409000881c0c2c960810300a07c2000c00c418010001015540980c0010801c03a010792100020740007000c052039500c90060030203003081a600142d8125403902441540d0030011880c0ca110599003103a158019100144c22800205004d4074201e200c0131041c0d030031100002800c440b8809494640101540601e2094000c40101b0095680502c40c0c3d000405844412451015541180035181e10000f0005400c0c0740c0c1e80c81d154001e051003004100007a00e4040304803613980034000350103943c8030518890551030751300780400320392242010300524030507a506407140c8050400b1291101e2442d00403d03107801 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 4464054 1250 4462804 4462811
    0xb0c10050603010b100302120c090d080f0d020711030607091d0408120412080105090408040b0714070b040306050a021e070f02030601060c05010c02011a010c050703140303010e010f030201050f03070201 88
    0x40d15580305d40307072041c41601075200180e50790610303080c40d00c0303d0400600100041006004452180d26240d03514490181d224154a9850013818102415070007040e215404551000c04d043d0100100801d0307003500c8000480440e14a84d070340d86000c43d5404050b01400c105417404140403180100b41d07851040c0c2151140030a203041080b0002ea00240e010100c409803855100c5140060002e6082000320f4013411003a41c55946a01c0c16072900943e41c4254800e001d0300d20030028022081c003900600c00324240740c031442a1804036a40360061a15904540015203240e450240800c002041031310071200c0c86460544010100e090305445090301f50404c0c80c0035145801003d00c0c080040c0e070180311182c00f03050b680d180c0704440301c013a08181d8211420a030000041d07a150142c044004100400f01c1c0808540910308091051142d282541c10040c1c95400100100c440003045411144040302441c16565500038641003686d070781c5900e0040d03818500c80a03001c51400c0149003980134000c03000310380c400c00500020 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 4465304 1250 4464054 4464071
    0x10c080409050702070e0a02040b0a0f050702030a050607030b0d0c05060a0c06020a020601090b03060702060604051008060901091208010b070b07030b09040f060b0103060b031f080a0317010b0c1005060301 89
    0x100c140c0c1d2049680708010b8012050600c0f01c6e8814892264010101ea04110b0a01d41002c411845030b200700010a02800495046076503554880c004030341c0140d90103070a450100c00c452403c03640d20b00c4161030b440086401d290080526007000c0d1600301085400800035000c1525080034800d680d405040308104000c2d1000070040421400e00050114040aa0041c40c140d0b152811010840b800c651155103e9004001400302c2d1a40c002802c6400410445002a05440e81c080a0003190700c40c2d4231101850240314100301c000c0d1419803000d40d00314024a40c2c031038075100c10901210100c2c0700340552015a04140006408a00c1c9030070760507130015031802c0010b00700c58440b0004401510440f0222032040300d00179000c1c00c1001501444600b0007081c00d00740005402d00de40303070865010040070007008008110700d240000c0400e4500038002c210f05404d5600320040e07810000c1c482007185070024008403031480002884c0000c01c04852665507510044c18400841d603080ba800381c80051303c0b0651564954000 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 4466554 1250 4465304 4465319
    0x9020c010b18040302060a0606020c04051f06020a02180103020603010e0c09040501120c0905010605041205031306170c03060603070c0f050d02010c030b040605010215040812010e06030c090c0405010c0804 89
    0xd0481181da007007100981898240784c02413030b10394006c00b00d500a50500d502004035a80000c2c0f184e0841a040340d0100b100d41d10341040b180f1740380c00e0b107084040d021701c4881d0000745a9008100c56207007a0080e01c490200884004800c010300c4020722009400c400f0400c01044245080d583c600d0300440030580142c504403220300002e00340e40342038115a040c1506100b000080001c15031000000307190302d034010321183d80342c51070240181c05248a1a80504004903100c82080020b00031240c1c40c0caa82100c0d026815103c00000300070f40c8000b41c1c5103d070300f42d201c3c02055032400c2070801e4920680b00117091070b1075580c45180031540c2201050080f500741c0110040b00000450074401c01c0354540a5900001c3c614686c0680101510542900580a40e00c0e01030709101030b99011681c0034403894030b811088059100c89c64084100c1c41542c00000350f001041c0700100d81824290354403401040201c0c02c0b0703400040700c1410010742c0c03241503031400c3c0150010482006154099005896102e00601050342000d955080 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 4467804 1250 4466554 4466569
    0x30c03060501061d100e030f01050c04030203100501050f04090212070303050a090e040b0403080c0d020315010915090302040b0102010902030109060501080610030302030a180503010c030902270109020c010b 90
    0x104840003500d0314018410340d64400135050f036480043c040310810302c28510118118500440101d0100f1400b081c0c22003058404200c008030007042e5000800052034140d01030a01c03608140070481c8203004030700d014078a50035030b0301034503050396030051200c0c581c2d0380600100801049590380407070308070300d082541c90406e40040c41100003d6020f40c949581d1400c0c428802401408250803a8145900610500011645005920380e01941c9030a210f0750580b1008424a200e0088500f8504954000420082d11407100c0302c1b110005007080e2035007a001030302c3d011001c12a58040c0003d80c00038003d154200003500d0540c00c030204841060000003400c1035590040b030f0039241c40403015990030382c541d0010448600200802c5601c12501c0b10211032036070855500940761321520030440b0802c10103a400c68102d0110007a0b41d4010b20004008000000c0004d2010300500420311007030303110f000200740d01c5600e500c00e0003824401c00742e0314900d001103070708040b0400f000b50052840c03803010b5903803031303c105600d40c0f110700 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 4469054 1250 4467804 4467809
    0xd050a06080a060c1814060c070302030706020d0f050a0503060103110c0106030b04020f0102030406051603090b030a0e0c01080603030703030e2508060603160302040b0d02030d0509040b0a0509070c030306030c 91
    0x8040351204545101404561005000140301c6180c120100f0007005503441120360804e04841f1180d80b0f1a45c10101c07850000182c0020794140244640000c0e069000108801303070017800c3d02c41e41484c007440741044e1411f000745040c4001240e020070001e9401d620035130242401c2101c94542e1401c203407030b000380142102e40b02e800c200c1d060310300c03402071109500e8110f46030800c2201c00d20042d0b18082c180780d00140b0902894412148101007940c0010405000b0b058000181800c00b020f00e403070785001d020700310280c692951214881c1c0511a4021815445200094480d10028005602d0306d0b6039541c0881c000d00104c8403415090241c0407201035203101c0421a0a0000c0040030717100d000c1800c141e0f040b4140280074000603c00c0d84100c603619000098040b03200c040380e404550000b080d0301c04e1404541203000d05031000703500d801010364006400350068094003040e601510100039080041062240b014081d02805600c6010741c40041d00342d0b4071485200106620920b03011940b15944d548402c41048142c = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 4470304 1250 4469054 4469063
    0x1030305071a011401030f020301030507170a0b1303080601020f0c01050d06080610050a0602010504170702030307021302030a0b01090506030a1509090b07080703051501050903010902031009050d0203040b0d050a06080a 95
    0x180c04d40c10507580d050007118020610355100318a5545103584203541d8500b14803941100c40d0b84074890095106003031000a440c990425516240d525050221000074a001841140400c1030b5002046480d48000b5960742c9039444800103207109140f140c010344081e005080f40003078072900d0302008075062809001441c0644540300552840314280010400004241d800050440e03150a08100100e501c130341d00b11480014040700300c3c2e40c9416a0003c20b046101380368020750001404103086101142940c011403061010200401c80d081c3c0907001142e41928521031640d01480a00c04500310252179032000a404080c8012140802d60f903100c020b043d184e024000b92202d81d42042000030894000480943c451000d01e001c000c18a0800400f02d0319a501c00c00b01c40c100f00d80403c915025450035402070072080d80040c1124070a03c1e141c00034101034420f003101121140121041810a40e0001040d0b0741591040c20313205040003180b4100c0c0c0f00825008146165460b05c503100000e81130300074420841054000d = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 4471554 1250 4470304 4470329
    0x515040501091a19030e0303100f080c060f0a030902090f0901140402011b0302010204090905030301030204110702011704050a020409060c0e0a050d1106040f23010306030b01030305071a01 82
    0x4140c00504001c28542c06201800c00e00419804006072040c00c032015008070b280c0312011308180000442c002c11040b1461070b803510000040c000c0d044041c040c400d08032a48120001c410036200c1460b00e880c0d103603203070106401ca41c0900c407145c071001001000c0e15440d080b925001403982c1040c3c0001c0c0d400142079840c00d201929000501035424000e000d20710340f00b03808012514007824907500091981c040003000f481045600200700342094401e4040f5401004248428880c618150030020b480741d00a110403032040349040781d5202481041000d031503515130140c50300221000703100354001d10b2040042c01107440780905440c100050307940744107682c0e03c0c1340980c0f4002901c05036105d001d01402070700ca0b03110b813145968070300420030766481c425804d9400c2d91200b070700040221204045500c81c02030f80c11403496208a0400403406811000d421001e0942640300c1d141510f0300380380154111102c9000152840c4003020052001c28062401000f041340314204442c4441148038200e52420004e80000292408 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 4472804 1250 4471554 4471559
    0x6030c03070306050109030201170403120c0908010e06060609060a110303100e060108090607050a02010e0a05031306050309030306041e0c090f050303030f01050d03050d05160305010b0309060a0e07051504 89
    0x80c90b1043c03601910003824481c0c456419900064100d40c00c1c204101390039031001c0700160070540725040c0c0e006000700000c01031040f12141c0002920700b08035401007401d01e61800d2016004d00400040a50240c0c1002d45640d14084400c0180280f560095952501380304880b1302410501d001040214813440070f00801c2d440701e6080c1020108140000b401450401200a040c00116100400c071980c205816081070341da82c0440810a0b07000d840e035155440194041d00c8024810b00c4400b00062a500d030440000c0d20384030361501d00a07030f6680020740d0880d2095001b84009240f604090348204442040704030203d40b14501c103461481560302c144203010000d40006000c000e000904500c0310094101203020b18214900002440240b060500c43d10348110150002001410b00070350843e01a0051039500340036034601a1354144400c040d48a81d14002840c001c00040c2010f02241031300d00134119280074040640300e806d1000c0180c80441c01100860281c500e002070940d0340e1040c00340044000b501807584461 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 4474054 1250 4472804 4472807
    0xc0308030103110103021c230a0204030515010f0302010302030a020706020d0903080603010c0215130c030503040e060d030206071805030102120f0f04020a03080a020102042303011b0c0305031506030c0307 89
    0xf01c100c00024107150050000c5400030380240e031038001400c3e04030800038034004051014a017584540348100860b000e0b0310144030010101d82c008000340c0740980c04640c2450001c0f68605070500c400d200d249601c150046042c4015803298000f9a0440822100542009101d0f10ba046c100c3c0d1004029540c050343d5041c0c10700405421510569020808030004c00c0402c09241d00651261030764101002151440300024a200c4800181c0c00d9040e504451001c640300e07100e1070704d540d80b68014003c0340b40c040c00d0540090f031345182022043d180325600d603025110303d0312000d90903a805014080400382030107681c200401c041c4c074248090585060b4000201165040a0700c07426000c0d580a00309084d094080d004010258a031540501304a07a8405980c1c0e0340c800910a00301c2c024061a00800c03900c0102c00c004e00380500c100c450300004104220000c0240848071300021102020280c069004207003031800c5200468003030005154001c101d80a445400c8480074001101d40d0302c2241c00aa00140100a001500c1e = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 4475304 1250 4474054 4474073
    0x902031011070215040801090305070311060106050708090f030f0106060e0609060f03090a0b0103060504030210060311040e0f0a0303090b010e040309050f040f0c020f100b090a090201020a0c0308030103 88
    0x208004030100300080d086420a0954450b02a01a0080880d48074520111440008a400800c00e0000030400032a00303290040c119800078406800040e00c82440f00c4a044012960034120303040c64031550f01e001990307a101c0c03c80e5088080b403144c2c000700620905196031005d0020001e450145800092980d060440c0505002004110140520000c0c0000c4406407500d000b11540c42c041c0c4841d41d5104e942c0d2140040c6000e0700e00c003008110060310000081003001c1c6412460046210350241d81c1440c55181c142c4040360b030a44070203040280301d00807840407030811354050042e61020006450035454502c14041ca80810ba04c0c00301e0000750b032010340c3c20030300110300103450240201160190b0541440d840051504000e800707000d10030ba404c080c401079142d035987c1c030400c140c0800c55002c0c4110304120001940b5905da4142840b800d005d0622203200110140c803c2030103208005003028a9901d40d80c259030300820300c0309001c0741584108000300c00030400c0c505100c0001e610541c4c103a07a40358110314080d880b5 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 4476554 1250 4475304 4475323
    0xb090708010608030f040605030405120c0307021305060102060604111b0303070f02150105060a030902030a030207050120060f0402010c051c0e010302030609040f0503130608180f030301060c030203091003090203 92
    0x284d800900800d4000429030040f81c040366610b1810640300e80301e0f030525030700b00b520b03004484424090000e00031126000100182010038002c4071301d1150780c1c0010f5441c0082d580d0466003136006070030500c0090380c640b5103036100e500c40606400d019400c0c070184050154407488583c800c5002c0b030780084200f1801640c8402011005c00552001d49043c8240c0002400000410b008a500c511001b05401a26130300c20f40c000318060f6002001c91350340c0b51141c00c0c040d40381c803858000d41d0300007486c80c2201e00b15200c0781340404004c441003100070175140d5106007408608004c05030003241000a40c41610b03000c500208581d45484140c40f80e03100c00e003118100c014001100c42404a03041c07500500c20041c0503680c2c044081e510540010031801005243e00d0254107510440d8400701001030b1501c00482c009031b010400500c40c40385e0480a000c04d0301e10b007103d41e95810781c1d14030b40c2401e6031003040180011445542070070f02c0745101c3d00440e414245060001303442900c00c02a52000030356150406415490b080110301038 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 4477804 1250 4476554 4476569
    0x10b040b030c0a0905060103020d0c0315170307060207020f09040302060106080a050103030801060c0f0204051f090e0703150906090f1203050105090106030207050a08070303050108060106051603080703090b0907080106 95
    0x2090504100450f01e02d585910848101c3c45c3c2d5200000c1459000e50111105004244804c200e610031485003d40103007201c6140007180c4291110100381a1382c0703c01900c02103c15038000f1030030300c8200e665800195010341b400301e811903060f005400b2180c03102d10005002d50f1180d000741a030f66041400050503408014090f2401d242400010000300350001040d5045d10590320b01100035241c1802c00c450602c0042ca0000c2d0450328000c104615400050b040652411410030b103c81340b103503a120a40180c401811121a440e003154a041002a000e4840925048401301012910149a0701d41800b1a40d13031445c140e805500030848a01040003010001800346290309082100b0b50400001c5441400f0502031039081c03550000d004402d01c00b0811107a450306500800440d0b0b121498600240501000e1243c401c440c8640c1001185407409001a00c441c07210510342903103540b4481d1400c0302c1d10310340941030742c0c00d065803400f000c0702251030340c0c224034428002e0034010f1603028600900c2c6821900300d0380c8200f1 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 4479054 1250 4477804 4477813
    0x4080618010b0901030b040201022109040605030102070503030601030902011211070308070203032502010608033403020d030b040608031809010602010e03040e0408190201060515030114040507030e0a05010b040b03 93
    0x820780e503c94540760b0659422a04c184002da58a10040c0e20b844c41c020406480500040c1900c00c0b101540c40046c5813101007600c0038001c19542d0b106040c240c2c0114040223186130014000220703e54483e03071110206500514000d0802d00c0d902030014102e0742a1940d0461400d000614481415080f120741c0e40c008196100451071440c0000303a007210312501940311050030000c804c5c0310700014400d40200f400380c0b12440a81c1c0d41c41c8107000000c89082c0a04a07121484440ca01c02c0d003030b0030380e000c8542001b140e4140c1c020b08008040785000b00e008245214100790700640d6400003183c11141080039010356030203030341d07450200c5911108000c0d8030380c0141c1c404011607040c40502005545d020003668105e81c2004543c0000c0c1d00c943c0760129450141d6a1103000140541302161400c0d0ba05411000842d401590107680c002006032141c095844240201c40c211011015529800d0a040d48520341c07003e41460000740b03000700070641504120700d024064070243c1d10380007201001d02d058401c00e400900100c0c01003 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 4480304 1250 4479054 4479071
    0xc080105060a0806070305040302010f0606020f061602061302030109060608030d0b040209030a060b0a0302031603060c080c0328240801020304050a1b0e13030f0c02060412020105040b0408061801 85
    0x513984c0c3c0c640144a14105a01c9034041020513000750090b1800c040c2c041e4081c0103d07525144029034850040c2504561441054040307100110048080003442035030b640070f04041d54038110708549034030b0301c0d400807a051741d80c0d05009004201b06125602c06096400c0103540d40707110750000c0342c0c203444820a800c0d1066104020140441e60002904070f1400e50114001c2140310001000850b00f401c15400690076014030710004411001440c1d805040d60f02c600400c0220b03080b14481110045403c44541d00c00f8007040020603400700320383c041e1040100d450700001071800d5010000034240d0b03000c00100b12807101c1240d00403041000c2491900040c100c1200214158546034441759580c114090001d01203004001050002d2403080341d0980180104a00d0345549003000300c031141e00170300741d4803041c0d000480e280c01d0600201d20400c130051501d40c00a00d2142418204000b4159a01100c0802c9050103010000092140700c641d02400052003254040c041514064107420004100041440d07816450500e28 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 4481554 1250 4480304 4480319
    0x20705010f120b09010801050f0907030c0303080603010207050106081006050301090804030b0903040e130b07030515060d020d050c04030302070621050a06090203040b040507060f02030d0e0c0d0c080105060a 90
    0x205070003001d1030301d00501002c04490041c0002c00300040002d82226042d400801d040c20150441c0b80a040c0d0348000204641d1103030052521800a4003005204d02170b140070800109204901c016003003480100010b1400302c207070391072900b1901c09a00c0480140c00c64000c100e041a581d1090500410065000f8000083c080d41e8031150b5200e903002c018291100000450280306080007941c01030701d8407011510150030540c820807440d4030f4206d000ca45082200300000d44e200d10a0040701e010b141c80c801100c480c600c4010400140ba04117412114130300c2c0e4244545101d1a000340146805190395413489541c56055041c02400c050081e002030301401203050082c03030882c80c107500b0440440306106001505460780b00311030f4050011580301c05440c0d4004020300040c23005136400c09010b10b2040003125000c46da960015207041c0350a40d00c00015800c144551046a00720742c100700000c100302c109071580324040c003000031000c90b00800d00b61150a942a014000b410003403040d250030050848030300041a20780f566 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 4482804 1250 4481554 4481567
    0x7080c0414060a090302090901150504020702090402100203190905090a0b0901140a0302040606030e0706091203120b091006080c03061f0e090c0703090902030c160302030c03180405060102070501 85
    0x1d219001d01e400141c00128188688003850246a00604400c141e007049100503001e40703a10a541c0c40409080480015540f60901c2100c8207a640500749140c0c5d07603216020400e00400c11601101540820003090308010040c028040d040e04d05620303600c080600b480305000440100601c510b462900d0070031075204580c0c0e40c1240a0445122100070035000b0380b243c001ca40b04c550f03654402508181011804030b0300c560160408110311500c3d0044500c05640d5082c219802c3c1e030244100f0030440001240d030b4001c00e01c900030181070b13600401404100c400250b00404c10569086844c07240510324100c062180c5a0310982c1c850300220311010040c00c0d03003003800c00201c3c2c3c90200020031440c8070340d542002090502502103021910b1008040110a19141a10010981c4000002c4000079900e0300d0102d40c5070014400d1b240035071080c2166506005158600d001c501e86400800d0b8258070091002c070741c60b040b041000f002e00c1841140d600c24502d059a0500064442c06000302e41550800304041c0941d982c40340 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 4484054 1250 4482804 4482839
    0x106050a0e040302010f110910030501060905060c010207020a0905100e0903030115120e010209010e03120706090201050c0d09060f020c01080c030a0902060c0a03020d0507050303060d03030e03030a0507080c04 91
    0x1100140b80c40350301d426801001d4810b5043c281505103844c00b0314401441000e010241710940d480030220740080310032012035200b40208008074003140414000c42c02c0500141c5042070032000018500401e40d000902d0414190380143e4200c0e4a4004004901c03a4641c5510300502100c8003207000742c01c01d0040c1039100d010500452900b81d40c0c8800d020380c0c0600c91008081c6d0007000d840208118004401190f02070340c84a90304a01289244003110824100040c9030f0032081c900b003150034180200c0d603451401801500d10300b079040080c10312410680381c0040c0200880140b06803108120070b4078102d00a000c42c088040d040055400c42c1001e40503c3c5d030040e5020340d204401c00d20607644d80c0d9030312800b00300034600903901941007000451079810140c0c00040202ca0b0a0082e000c8a4182e400c00390b0844983c807a00c640103045400c180302191007030410862684601748a401c000c141a144102c500e450b6420032104c041c001501d900602005640001200c1c0d00004070700005490541403040c1c01d0009105079 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 4485304 1250 4484054 4484069
    0x6070c030201082706010906060504050f060c0f1504050105060603040305030601030902040608030403050601080601050303030115080403020a0b0a0b01031406030a110d0210081005010318030806040608010203010b0c06090106050a 100
    0x1c0000c1c10818030400506409130304103182c00701e4100101000b42d403190240079540d005407520307002107402400707030013501e00301d84000348902644809681400380e0741c3c03c0036400100c1c40c40b23140c1c0e10824402013403001c0940011191650f404038074080c2016420b55001900c0513000d420100140004a0b50190840f17500c14000e090105107030040f440402d004140641c080440c038003002c01c020041000111b8414102c44084c0c048440992f242c0302015100d02c028851040014031b68069091103d004010f003541c0306010303005440400d0b100c4c3e1580002c05208480101b91741d030390f4014054513036805106541c217000502c801040d4070316225002c2a0703035604103900036007900361100d01d840031a510340d0082c0902c641d0140000c007a0041c5c102c800340003190244d03515910590040c002140b0340d4403a11800c150415400c1d51090320715038985050fa040b0401401198000340c07110008110302d0000d00055000f00b81031540c595840d16500d804e141044000740040c500e0b0f0341000d908010a5541a03030400984011 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 4486554 1250 4485304 4485317
    0x80a0207050c040608030702010e04050f0103140309030313060807090303050301090b0f0303070b070908030708070602030c0c070807060207050108090a0308070c0b090703020108010501030c0f0f0504050913020a0506070c030201 99
    0x34240320b49400545600568000e0501e840803880080c044044d0004500c08e0701e41900d803420400400c025a4030483d810100080501c00402c0883d004501010342002d481e8145d901d44552039001c07a045030f104407540500b141c0e040d01e040140a621180c035640c060f641d80342c240c072014150350b4003c211303100602c2100c02c00d980320703110b0360015540d01c5a4591880310050480740c0c1c54040c0d18204483e51001c40b100d01c08189000f0001078925401300c121007405a02209040c035001855852100a400141000d900044140100030701c8450420840c00645405801002100d01c1e0100c001d2404000780c0245040012400074000d00e0315000607111074041e410305107051990341380203003107a1058400740301a0081040c1014088941c0d4085118800e5034000ea81c1c90400c1d81e244c0005505031210400d10788001070f9a160503030003541c85a07009112fa0006803418070310f0103030b985000615103175040d64000f4080301800c407118110718000d28864020801610164140005900d030151818803500c0045d06000a = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 4487804 1250 4486554 4486567
    0x31101020102040e0a0603020a080616030c090b07030801080c0f0d0602070201030b0901090506011b02030a030c03091802091201060509040f060207020a12030e03010605030d050d0f050f040c0501030507080a02 91
    0xb0740544010309208159101e19280c00d0780d450f005044940700c1a8090040c406006c10314040100b0064811070f680d2504c3c00f85a600c50380200d0041a44030295005c100f081c4401084c10000200140f454034001d0b0703599061941081c0105040c070080090321442510400f1124080b6100e0018000cac3c81c941101c001a19070142d80016401742200581035603010140c02c0002c101091141c1c4820300900c0c0a907241000e1250b029021210340c2110f03000a580365000a0402c0e00080c420482224803903c00d2410314006595201142c100104041c80c5094407038000c60134103000d00703007141200313000404880207014451512010603107200d005000030f4030138080c8280b414240161501114212075001d0050040148e5810301d420140442c0d54080303000a4150f03d516420307240c1406501c0c2500c100070090100300e0300c991415035207070340244020b007031103521082c0f0501d401416100761482203102c00b00d540e01d20729186c50038008125290300218180751900f030502c890103a02034076880d40910741040041e550b00 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 4489054 1250 4487804 4487807
    0xf0a030b0a020c01020304030c05060603030f1b070b0a0309050105060a030c03080c0f0304030b010503160506040902090f040e01090203061008030313080705070602031b0105010302030606060708130f1802090a031101 94
    0x4503182c540f00296000100703000405501c10206208540110180c074040e4990b08100341d10b9128407040c0980e10030050000c041d0f4a0300294442c1072150600c8200d40c0807550700c2c0710303009050f0004103030400401d94582c0e45c101800004c2c003c0301c0d44060200e0b00c500b0600d08507599541c40356890300010303100a002003480d04204204000300325403000c0920031a80c9a070355034a850440c4100034004d141c000d0056072072956240003c41e2a04007a140d00401150601c0d0401e803924009421403000c403580001003038105015620789100d90300022000100100f021149401898a0220050580b140300e2040b040c04101210b00401074a401942d0350740001d100d0200d50500341501c0c00740020181403401080d80c0000c49540000003488801c0e0001d84802e1901804540300b8220340091201035019000000043e40358074009008001d0389218120040c18144644240c801c0980c264000503040200440144100e00d140a40d00c000c00c000100e041d860202c002d00443c542d0480d9200040011380310b0020050107a = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 4490304 1250 4489054 4489057
    0x10b030c13080f070303030c03090210030506031009050c0f0904030c0314070b07020f071a030103060903050c060f01050906040605100c0501021b0106150503100605030603030f16020a050f0a030b0a02 87
    0x1c0582d54100c0e1000002c5502c0c194941402d4802200460302c0d100780c6841c0c45010b0b00544c0802c0c0d40040030051683c0c000182600500002454250315001d504041c0303500304c0143c4109884213000e00010901010788c1d006000340c40e011400e605125201e550200400070340e02c03010500e0b0056140c078044036030390710301c0050716018000c900d001881c2201000030041d03055400121602540481000c03152055034950880c90040121480080342c400108010b00c0031070115000403c90070300c240703086071809481241003400d0001c2940c41c0008545004010000707031805210b600c1e0044d0040380d0800440e442e101c005007918090400c0c0c44203008403082481e042c0308007075060b581480c400486892040700f54044250003000e0900950581d41a038880c0e038500c051142c4241c070310030105a00960501030034400f00380d400780c00080c002581444100011b00c900030140c8090108240340c0045200840003620421108001c80c1e04164041e0b4500c034260503980d44e40c69554002c40c1e800842e00d5651351900d001c02d1019 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 4491554 1250 4490304 4490309
    0x4030b041b09090f0b060f0a030303150902040305061e0c07060902040e0607090515030903040501050c0307061506030f1a01050901090e01060c020109080309060324030d03061409010b030c13 83
    0x4071450f10300b6410071300c000d160f03d040a49200f8600d054403035032410200002981c401c1101e98010322260001e10020340294043d46943d001c6c41441c042441e035542c4144240d0340315400c11120742e0030690a00c0030307600075030000301c11403400701d0802c48180c50b141034540c206006402001d002a51144100025902d895012020f290210415150359103000d0030f0241403002548145406072000d4060164500724400c00d8a0180d08407a01a51402d031401004540030340201c21011030718041000442c00041141c8290100d804092a4402d502c6103060400b4040710010810306e000c040c10000349404072886218102074440090800c03644481c047e0b80101d402e040703d9002400482c6400002160050700520f410b550385200740d940150075512a1003d40d1a0302070709158a400500510100f2283c000d58210194807443c012075011201c441000040c1c6414141c460f18400300e56584d509100fa542d00c1402d00148480503512800c0300c4d450000d8100d020320004040c01f110500118410043c4159503081900 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 4492804 1250 4491554 4491569
    0x703032304150c0816140d020309030303011205030c06150a08030a09050103050a06050402070804030b0606040602070506030a090b0711120909010e06030304120501020c0706080f0402010809030904060f05040b01030204030b041b 99
    0x1c1c5c0080d91800c28442c48400b115040244110b03c0800d103228400411240d44240150255040d079107000102d680140c5901f4086a00380002e00c020801003070f08001e502e104060102c550810f09000f2024001400e004c0d81217004203400c2082030168040c0c1040041c0111103003071070009041d540740340d90a801004c560f0003041d4010700028800c024002c5120203041940d02844140106842e058200440b62107588641c00140c1c2011100300050701c2c0400107991700c0500c0c680d01042c8903401d0760300c4800c240400c131030310000300d0300300d20f04000140c01c01c00000203c0403042c10b03928030304039000e00000d14001c0140300300134140e0700c20340c0060285c0d1030500a64004020a00d03111a031f00c40c0a00d00f4902030f4105a64400c42c0d072007602c00000d10702e40b01d0000305014414082502081d600d40703070011580e4010003401d0042910080055030700c07a4032140b01e80002070881820103000181000d041000b80c2d59074510300c07410140103101c00d1010890f07a403079180c1c10a9220444680c82c401e00d2491040441c01d59000b40c5 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 4494054 1250 4492804 4492837
    0xb0c09040218280918080301030308040c050102071a03060d020402190e0301050c0702010309050715020304080f16060c060b0d030302091009180e010902030703032304150c08 76
    0x1030782550925060700c01014120307081842403038240c1e1081031207048041501c901200c10001002100c80d01c0e170150710401c50003c0582e84094407915910300ca58001c0e03008500040303050003000b041c000000d103643c0c050f18091010345019807030401e83d5504022612084a01c01d44004041089640c03100c110308080c2e03a0203402552101d80c200e039180302410f03c3d00740e600c02080c0da00f6010300c41e624061052510490300e043c070490030300321710b500110001c04c89490100d480307103c1c401c80404e00d1192400c0281e084107060740115078580c1885200c6081035160796120140d035126078071b0001d1a101c01c031045001d40300e175854070703015081c0780d800c1050141600b02015a00248a4007400c7d00303040d8103400030265641c0075103040c850241c507031000310b030b0000c82c0784036082d1001c4541d42111091409504108289140c82d000820411082d800080c10845190300c101c000c211600c041992000380300c40e606000440003141141004d04d48481c0d1911510032240980030045c1c003456903402c021100c3c054900300420b00b200709 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 4495304 1250 4494054 4494067
    0x7140904090503041a090d0b130b01030c0503010c0c0209010608070504030b0a0b010917060604020c01020408010f09050106050d0305030a0c03020409020307021f0903090e0901060e040303020a0305010e06010503040b0c090402 98
    0x4503100d80c80750003600103179201c0341e00105a64070242d04890316003c01804840c03030300c56203407121058000040c0079865a503440362144000308043c3c45d50b0358040d5001d113101659461810082500716a005001c840030301c03841c181c41e003001d82d0750f0014043c1107901500f464100c0da0f488140c01c407501d10898000500443c1034509104070715210768401c0005840a8a400400c00d844000503504885c00d0740d0741954a900080020f84d2505060700902903160384e841c009810141c844541302e003035823038204603403030002c1e5902c401100b440000d0003900b005100c15100030865800e5520001c5c402e02c002801d004205880d10001522144a64111401400d0780c100840d00d03403e1510009440722004501c20740d0084500b800c001c400103c1e480307842150340c0d1584a0b110880e1820f0701c50001458000c040d80303441d56071000d000909010306001e0910580c4244d4005984802d0220007804842040e0009040600c00c00300300200b50344c0040072690001c4e00450004080d607100e4103200202c0c072552503960707049800480c11 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 4496410 1106 4495304 4495313
    0x309100f0b060c06060901050402070201020307080a050d06031401060806010501091701061d010e09030910080a0908040603020a0801080a03051207020a060915050912030714090409 79
    0x400c0c07180e501400079105070440440d821036504110104140c0c0e1a05040310303409050111401c50814043e40c0000707589004019005201d0b1400160010006001d501510003400c840181441255200c1c50300c203841c1c0a070600038103460340c20309901040c5041d0206040c0e040e500180e45000d40e103864035080d159440f03010440b81a41d550b803120081240321000403840f421302d4950213841000d501d0602641c1c55820001c2c00b403042500140690a080d030385049001d03030140b0f138619004420303440e040040c00c000c0044e0040100007500c002000903000760107070083c0a18003030380e03158180681c0e40c809466444660050700140058001c020040c03c200d011614240c0100c054812900010f241d0703541d15044421600d81500c2c0700381e40b01c40c54445200702d070140f56400700208020f44030246507150321080d540406031000050095041c14220100d180720f06868503e9801002480083c686082 = true := by decide +kernel

theorem cover : BRFrame.Cov 4316554 4496410 := by
  have h0 := BRFrame.cov_init 4316554
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 4316554 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 4316554 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 4316554 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 4316554 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 4316554 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 4316554 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 4316554 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 4316554 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 4316554 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 4316554 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 4316554 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 4316554 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 4316554 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 4316554 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 4316554 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 4316554 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 4316554 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 4316554 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 4316554 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 4316554 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 4316554 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 4316554 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 4316554 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 4316554 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 4316554 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 4316554 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 4316554 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 4316554 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 4316554 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 4316554 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 4316554 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 4316554 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 4316554 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 4316554 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 4316554 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 4316554 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 4316554 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 4316554 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 4316554 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 4316554 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 4316554 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 4316554 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 4316554 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 4316554 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 4316554 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 4316554 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 4316554 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 4316554 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 4316554 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 4316554 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 4316554 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 4316554 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 4316554 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 4316554 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 4316554 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 4316554 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 4316554 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 4316554 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 4316554 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 4316554 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 4316554 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 4316554 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 4316554 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 4316554 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 4316554 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 4316554 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 4316554 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 4316554 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 4316554 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 4316554 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 4316554 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 4316554 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 4316554 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 4316554 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 4316554 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 4316554 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 4316554 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 4316554 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 4316554 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 4316554 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 4316554 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 4316554 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 4316554 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 4316554 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 4316554 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 4316554 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 4316554 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 4316554 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 4316554 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 4316554 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 4316554 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 4316554 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 4316554 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 4316554 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 4316554 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 4316554 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 4316554 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 4316554 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 4316554 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 4316554 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 4316554 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 4316554 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 4316554 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 4316554 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 4316554 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 4316554 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 4316554 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 4316554 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 4316554 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 4316554 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 4316554 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 4316554 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 4316554 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 4316554 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 4316554 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 4316554 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 4316554 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 4316554 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 4316554 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 4316554 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 4316554 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 4316554 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 4316554 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 4316554 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 4316554 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 4316554 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 4316554 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 4316554 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 4316554 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 4316554 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 4316554 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 4316554 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 4316554 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 4316554 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 4316554 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 4316554 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 4316554 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 4316554 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 4316554 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 4316554 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 4316554 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 4316554 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 4316554 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 4316554 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 4316554 ≤ n) (h2 : n < 4496410) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
