-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_4852
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T13:56:40.648659+00:00
-- url     : https://prove2.me/submissions/e4b5a469-d2ab-44d9-a4f3-1a87c2e6ae61

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 872482014 ≤ n < 872661870 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 872483264 1250 872482014 872482019
    0x120615180b131b2c040e010608061305060c030c0a0c020a03080a03020c01180c06080406090206030c070209060f010813080c0a061d0f03042607060e041a030c190906 72
    0x11882c00301100090740824001102080c3d00c5145682100300301600300400d8029080813001e00000300720045d601040c43d0760720200400c0501c01080303201d02c00c021410b0014846059840c03c03d051400150200c04080001c1c800c0c448a410480242c5d4410038042c58189138004c145d0000403810040d941c03000d00b895000089803000594590002c14106003107038000d02c4100420a07000803480490000034060180e5080c00340a5a88a0840030360414002c54000c00c40109035000140d069106036420b0131480030003d4282c0860501c420901da2160040b105011035450800010f000c410006101c941440c0c41400b00750200300b80c0205a0b007101c0b24400481c0c1e00300e1050710704180140051107030800c28041d0219604990710001940d0010f511182c0007450600d031034000c002c030b40d2405405000d2151405806800c0200008214980c0180900c0c3d0b01e0542e202c034440705100449980036041002980e101c0203241058a000590400c41d00b411703115481d0f40d1f0351200e140306c550700040e0010301d910b50800200 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 872484514 1250 872483264 872483291
    0x70203012322020f060309120d0209121615020a17030405010e19060f0f0c080a0b27060f0a080d12050919051006120615180b13 56
    0xa8030400280703103940911002050b01000140c01164000e5201003054030800aa080100c00345030015240b00c11140f1f802c3c218420406070380c000d034001d000003d90210300350310a49810821b41d4400c007030a00c003401408403a040d9a103404c5041e4010b1050080900e80b9440d40d451013000702007100c0750800c0050a0700c0042c1085021716038010381d01a1929800c0c02125034040c3c001080b0044482e100f480346198032521030f510034001d401e81c070f41400051660b401d962a514030050054021001c085c2d40c64081500c2c2c004103030f0702100d0a80b802c1e1030181c186260044c0d8141152003401068400090442e8495034940001441c4506080800c40d0048031250340040d1311203001400c1e40c071000b01902c3d2840c80d4001408054203c600844c0c0365082d5030b105840d03250040c00d0b00450084050700076030940d00700d4106608000c05541184c2c3c000803d100d9070142910911040340300e0055012a113602c90400c0e98981000790000c040111140c464481d41c840440c40c569440c01c8100150a0071a001030101940b00a43c = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 872485764 1250 872484514 872484581
    0x31b041a09040e0f0a0b0601031d0d03050a0213030f020a090e0a060e0c0108070305060a030501020307020304090617031c0603120f1805011407020d081602130e06060607020301 77
    0x340749014a0511080500980011a001e0160300b00e040040c10f2085040d1100d0746284d41c01b80100d81231550303030f20103161100d1000d1048010700d01100010800d60240400050484500034101d400c5184103102ca0844e010607180da1500303c80d0000842c46a903c100c0c00068910034071680000350070f51030042e0580e00b090000c6031201c8441e0180d0010090706481c0072800361035a00b02803209001400000020700010301030303440140c115001401c0c0102581c2c6035a11b003400c90b4819100c03180543e1011404010441c55800389402400396901400e01410426128568a0146002880d074a81e0031a0300d0380c001c12241d0740181c0003580c02001e00c00d550024200c014181d0181c0ca0b01000c00a40e4004200340091215103000c0100c40040c0d450310010301c49500c2d00321040e04041402c0b0b901958610310140801d0f0040d024240e0302624000d054041d128502c10402505072410800d02014241501405a8100454069400507080d950181e07145514030004c0c0c018200c0d080c8030007107a40e82c3c60100d545401c2012 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 872487014 1250 872485764 872485777
    0x40f0306151203140f070605091c090312030c26011a030603101d070323060124120c021518060411190e040204140c031b041a 55
    0xa2081d00d44842c240c2d0a10480100c0103004500742e00c450711414003106004080e0705451040007400c02c840c07984d507101610401d59040529900960403a03201c1503103401c0512140700f10b41411100340340746a07615069030407160340c00300a04d540c840040c41c46a0040019102c8800c10710300c0d001d40d090309801381d84501807081c05082080d92101103040860070310314040324021100240144500d01d00304803401c02800c140600524078929620100d008108100b140301e010b980704802660344986040c00904590880e42d441e02d03c282c0c4070a00404c98080b02d0299000418404860303080c0c101807100303007580c556040035190008640b03030001018109501180039501301080d050012038075190310083d14081c0d00310340385400e850740150003c600014110a030040c02d0f4a8041d011b0000d030403240e104403601b100c0c658418521010700004100852a29101c2c0c8513110030b101300340d001c0500f00400d0b02d09041c0002006240103120340340c204140045000145c1c1c00a0030000400074440f9401000141c2c16000310 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 872488264 1250 872487014 872487041
    0x2010e0d0c14010c02010c1403090414010509060306040f120e060a050a1d0f010509040e0a030f081f0e1b130311030102120c070c0503150402030d0804020a06030f02040f0306 76
    0x10400c0c86956226448525020340c05035181c0d0400110b503150102c00007104401c0123114481000012041d841d1070150300c0c141b240d140708208103503140101344a0850801082c0c20b11036000142008000b40e003020700d05c03004070303007107110407601090341c6d1000e881c0b2505041899900007400706804440b00d0748036009008040241e5544060302c41c3d4000d02c004804200d603a402d900c018140d0140190354420707005404001d500420201c2c1c1050300d10442810400e20071000d40c002032203010010940c6030071039115a044034a4500c1c3c2d82e86036204503801e50f80d489240c042c00c0c10002d1014080742040e050b500a411800030006081943d6041049075900000c01d944802c03144004142e070484178624044c401d440b495074540000c0f00e02d42c1c3d41c2c07c2c2c000841d030380482411a40d8800c492400320f25610100302001e0314450206140e0064109030040514002c60102d45800b00315840c1c0c20080103844012008085800d039013004900c80085030036240186c015904001482501c2c91000410b0003250f420800414040 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 872489514 1250 872488264 872488289
    0x250f0501140405030d0c0302130803130b030130020414150a150e03241005090601021b0111060906010905073605060703090e0127020702010e0d0c 64
    0x361418a0001d00d0201e40181070390300b050020304541c400540203441c6d00d080900d401458202c8030004803984100c01c3e040307941150320228215000810415401c4064510148003500310740c9042110240c3c850007591446600600310b1b4019080f00000301e900018690041c070500078010000c000c0c08003808120707142024299402521085ea0420300342c0304040c1c5800d0000e03a080060711100a8a0365100002b45c0c0f509441051200d000c84c502402c0c41140740c200d03112440c03113141007649510a424400e41c11071441000701ca0b007441810784c0c00040f64100c006014548042c07054516005844a08201414103140d010381001c2100840b00410a54142c0791540350030081a154030400b21001c0650b07180a00d0300c587e4801450098000307001d100608000d00f04400903980f0745801c0031a140780c015800440129001d8001440340701c00e4600d4a80c0902411002c002e211070305182c043d140192401c07003810580360f0020300c032000d59110303541055501c071000d888085494114500308050302c1040c070940c50487d01 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 872490764 1250 872489514 872489531
    0x31b061a03010c050a08010311180f0a0605040c0f0822060615030905060c030a020427140c0f09040f09120906020109080a120e070803070209010b0a090b250f0501 71
    0x8405480ca118503903a60061144e0859444027446a005001c4c03551220041d00140615101170f11118400e0207590210101c40c00c101c440700302030383c2c043d03000760780b0990424110289859014000d00d8101015103444140c03919001d2407402000d0351242864403510144211109002036a0004001c88141c40070302c20440e02d0001d41241203980c039a10060240d005003001c94a81307a80d040c003954100150303140051030175580c2c0201d4000c2d002081c02d0f68064040800c400c40036801c2d02c0c4105644800062240031440c50100c2d520302442c0f107074603a62841d003240860145d00c00c2d112503224584190603103004016030b11040c10841d00300800192600000348901c84045505807042c0141080180d0050011b82881102c02098421008800b10710880300d90b25103880c2220f583c02c0106034000c000c100080c654840c2503005001c0c81070816000344d207440c0350070050055001c2d8030020340021200c1c481d6520751a0400040c0c601d005e01d1801d1410b05a5141c0409582d00303102213003000329901031003280208500760 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 872492014 1250 872490764 872490767
    0x908070504200708091c0302101505010c0f0b0c070c1202030c090604020909180f0c0307090207030c05060420030606130f1e0e190f031b061a03010c 65
    0x280d1140c1c0c2c0201050800058081d0041010054400d071842015031a00340031441c0d0208000003111046045d0a1640312003000905405010500c89001403580600c000700c4200f12049034002c00b8800d440c104020444007100f804820303c44030003020307480f00d2420180d00748480083c00d2034002d81d005548441e40c9460025280642040c413059260b03003c0d0240c1144400c0001308211000010161390b0010b808000101d040d94a000c0461710542c4080d0503011180540c60318240f4002102070740780b0099101c0d640002a5540005d05030044604209001da41c4508514046440048019000700039115060a010810040c41c001c0c071150f096811204240c1c400f1801099550070058411a800c80d0f108040400d900c02d07907800a00390441580004507900341e01c0700c10b4103040092040900c813060ba5501c150820540f00348400102050030112110f0300355050b450b0b06106103d028002402e1000e92420543ca0b10048002850031a800c0041005080b00005050074500d02488a8502c00e5107400c0307101e05100e = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 872493264 1250 872492014 872492021
    0x108100c050c101814070611012a090803120a0c080112020d06150305030306040e0d050318010b13020a02070603060612050a0f05100806062d010e100908070504 70
    0x4412400a04083d442991038200a099081544401d90f00d00122040404e1421124011100003480204055844c02100403c091410000c8551603410040703c4c05020000480c0302484416041514040191020060703581e4101688440080d020103d80c40c4902c1111120b028810701d0111424000c1c81c40001c0704544820003400b4404140031020a0b110140c100044100c00d80742c4107240000384a95050304440580807940d100311126407002003040014105070189501c10511030000b481d010490ba00f001e0f00c40d0200811500c46c82c008800c0c00c0417024001d402c01030500d034000e85010030b00070305005400c010350f0220f0003200240c0b20ba078200040042c4203210351011640181e40d000300040e000d481200141c540a40045207803511b903040101d01d02c01504c00c0743d00031a080216207001d649170050b400d0030401c6c010311062203001030280101030454030303a803101c401103401030400c02c440c1811401a62000c10002e03420780c02c80c0c4035044540c811740e04507903254240c1e02032100301c502d6165034500f000140e = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 872494514 1250 872493264 872493277
    0x1e0504050403090b0a0c020a080c01110a08070206220b0405031b151606060e0618070e0d030c12030f0b120706030209030709021813020901021e0709050108100c05 71
    0xc2c030481040004d400101c000e010710101c5807804200170403980d00000c8000c40f803900501d035280c01080d9601c18941c5c02c0280200b0103018140600710800603611500d10300c1c01001c001a00541c000241c4030a81c507035010b83c00c0b074a84640b13140c5141d0b060b15181c40c040342c1d800c5801140e0203407181e00600d580701240161083c0e0b1000c0c00418045070154104030300c3c4440e80101a580e148900711801c0030000503440e000d040c0180002201550107032501100b08151030b4903800d2602901c181c1c0030188a02d0075400340e201c032412502a940382940f02a00d181c202c42040311000060322138040000c22217403095140c0c00c0000001625441440241402c40800c011300c012030041210503440010104003040c000d402520320050020141e42110fa541c0e180041668840401c2410b10425485016101d1803c600c6000d4503030704901c003c505190401e00080d550740c40c001400844c00d46500c280c02070b141404c0200001410030381e1000c1c8220350703450103400c0d40d46d40103060350103100c2d0808080302c0c0500d1194056522 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 872495764 1250 872494514 872494517
    0x27101502031e1b03220b04290c0f1b12030904050717041103060a111206030f0d02012a2a14030a080c03062103070c1e0504050403 57
    0x2d02910344020078520361055002c0a500f10f0601800d404104007400505156000d00c0b8010000d0b40c031800c1c03850041003a40d0400c4004403405e0100b40070300d10710003260102e04600c80c0300300c0d500300a50454403103260042140f2134043d032151882104070b5180202c1d104e41034800c10344d81125406840c40400840013030300c28511805902c180300310300f1180f500f6080946c0150301814002e07640410380f984618900d6040f942901d50300d540355034003c0e06013010005907038080d4142800f00244403074648041d0480c03240102e8145031070304080102e00155811710103543d17441d880c14115500e4681c801c401030b029090301015041406412071101d100d2001d64081184002d41665070f0f15140e18a080c2a28010021440074109407a1255103140004030080d8000741d0f0841400025900c604020030010543c8500908003504602c06000784010358a40d00b000203001c8542c0d100304e110070035014404600d14040d0600c0544020b080444c0007500da5081c09040607540250b94048901945850602040c0c48050b0340040 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 872497014 1250 872495764 872495797
    0x12003090a1b08011103040c0608010b160c0806011206060f0e0613090807140c0409050c101b11090c1204030e0102160e070e03070509062710150203 65
    0x300041ca803070b1900c0c280d00c07540c4109800025101c2c80c03802d0858020428400080400200f030100348010011004010302c85440c2c8009158100823035244540031fa402031031008450001c03220100252500f00c00050314200040341c2103981d50b2401710031022901070050780c1062910f24007088181605404038160382203030a450425840d420309100300c0064003884031144030340d00c0d01010b0010ba81e40000b0400340d40240004410002c99804040c107000c00e0071901d43c4103a1921804800103200802d07203034000c03581203c003603045c00d1040d0006d0f2410100c0da19519801d0311516036a0040280a003200a11050266800c0c592543e81109842951107000340c0c04030510700700c01c0002c0010f07100c1d031a8483d2070311042c8191003c0c042c2c141a4900c0b46007280e00f240074501c589508000d400c50344182c1c1c090380301404034020054103150001180c1c1000002e00898001c00c2c041c112046407042d0f006182d51100b20104450000349489002420b22126600500700e91f0803070000c0d82d843c840e2000060b40c00c1889410002e1 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 872498264 1250 872497014 872497033
    0x3020604030212030c0f0102031504140601050f13090207050f03040608340306030b06060906070b0916321e1f08041e0c060c02010309060e01200309 65
    0x41004003140340307004058070017000b900720244014400f420100748082c0002d0f8170713414801c650482c40b504060304036000c0ea160001c4031400b105545000354110a080c00c21943e500820114080e01780705280300200544002e1100003a00e86041e4001d0081a0003801502c0c0449800080c55480e841544200800291201f01181458409040c4020400e284010f0b00f5400c074101072010103290351a0b05d907880030940e40e0b1000c009000142c035140e540000e048035501c0ca00718608000403030f80c0c002c48202900e00d030702c5040082c07070405c03082017900410107100c500702c80300c60707601d84d0a21400c03a0000c1144c0c15500a4100c0011038040050b14003640403001480c04032a11300d841041d0100143c645181e65100303103100f1301c40c100039402c1e090040e901205959141d002d80b515040401c03101541612320100000c042d001c0d00d0100302041c1c8003404cd00e83c14a00b00c1c2ca01c02c21400100c02a004803803001e41440d00d0714459031500703a015400305420302040f03042440c05134100b030880421804111980e100c1c40d00b158110 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 872499514 1250 872498264 872498269
    0x1103040b0a051312050702150711062b140103050313060318062d0c14070302072303061501030507020c010912021302040e0708090303040c0e04260d0b0a030206040302 73
    0x844c20281c0c0c5407800078140b013816000100b107004644180d84c402c880002e20841030020003040b0b420440001c1c0e841500e00103d02c01c0f00c0b06103840d000710078102c0c140000c01e003e0b07546000d500210b0b84c605c02006810b00c2c558482c01c10311b4489d40f2100404441d8204900c000030043d000e4002d4010b95440441c1000482c202606c0784005040e81100041005003604c003401c0703001281c03000125020011210008003060b40360001703069043c8c80e0511020121090002500103540050607405850040f0b00102c0a4030003040300c1905007000c030300102c3e41070090070200400c1d044c10460905d2010026038040c007650b102c5541c00c2c2c2e200c400000d03c40d80024403840c014082e003440ca40c2d103603450318405825240e611400c0b0340698106c4c2c015411001e482c00750b41c010f01551035400b038419500b00c10800d001d036103142007956030612003400c9446055800312070711000809000805443d401081d201c80d03e80420480d1928402c80c29034444110400803504d0b0020705002814801840002e0b0b03503002d04007d161038295002c = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 872500764 1250 872499514 872499533
    0x4090f061410060c060225080913020f030606161a0a06051903120c080d02091513060f0c0203011406190612150503101509090308060120011103040b0a0513 68
    0x107d50140b50126001b40d000d0100100c81d80d40c040d004051550321040c0110030450440001000701d440035005001c408020074140b001c40e900100226105680c072000da2030304607201d581002024115000c880e20703a00804200002d01803261400340410040e442e16001040161000c0808541c034881d4400024000903403901080c911803482030a1240c0c4400c5240d5544050b64070405040c545203030041543c00d01030801c8110010394507818601c44d03040105100f0400d210402074448d42080001542000e41200c0c00b542c800c40c0b251b41c014000f40840c10140400411110045e59018014803190a03010100415104800c00303448550303940390380d041b891410b140050301150354000400903034804000f0345d0741c1d0104a082c10216600f13401080b442e120800340d03600e2640551103154914100b00c058000a644400100e500507003d0806402089619865601c0000c91603a849000e40c40c000c0121340600440d00554400d502c104864011543c5070740102064880640300c03400d00000c10b0800c030780054900711 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 872502014 1250 872500764 872500777
    0xf0f0c020418080c060a021e030402010507020a1710020a0903140304080a050f010515010503010905100e2a04080c010f03090501050a0501031511030a0b04090f061410060c0602 77
    0x1800031410b018110300c1c0d40b01c0d02c1c007212030407a450000003070040d25000c41800440c1d40119054400c6091100c40e0501013000d501c2d00c005007241c1e10f000400a400c41e070080040c0c0d0750341d9802400a26640780c94040d0109804400000001c96116120408286584900803248050515595032130054603558910108002886281071140014400411020b1041225000031030088005040c000c01c1c40f008182115406010f5100010315101440751f240d800000b281e045a45507a00003810b0f0350341d003440142038455900101410b1403003805000000e040c400754070312070744252958442c807400e025000540303905c41e6110380e031405d4210030f104100c15030086000b171110104606011030401c90958989003122412504208002ea44000500a10070f249000c2c0800f60142d4030700300b080c840403505121031404010215110991180d403000070b191125000b41185aa2003203036072605044a143c10f00240071031a45201d1030b0030311680003400f850203403c0d090080f503155455680a40419840b100b000e5401031 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 872503264 1250 872502014 872502019
    0x30309090e0304090e0102131505040314012301051302040305070e04080705010e011b17150411030f01031713030201080a06031b030b07110304090209040b0325060f0f0c02 75
    0x203101c00100ca104c0c0303000e0340801039024000180d50b00382c10034840c80240c40540051903010580c0c1c03542900315412038100da050700d07004407030a01800c1c01c85440381c1c0548801000b4610745640104a0191207000b080c40c0c5045c0c0d082110902d001200f103103000022030090344405851640030420400c0303010840c004840e002030088a06078a0082c107900e910b429150400c500c450a070313645102c940c0240c12424800f1160914034079241208144c044105123a56101030b102440449040702045025512540f10103130030a4010400d98481c0313070840940c0510142480240d51140000d101c1c07058902d0114205c806000003802d8440400b8215001190f85420080c01e03000200d61310b00c03000c400700300380c0c0900d550046200c1301e000d4589819481c007190b441c5405021001440003240d00501c2050300030054400b40d800700c500050b1a8424078000070042d09181039a107805005040c0341c00116000c80700e200b204150300c5440010f056079125000c95052102c40c01c2c000000b81c440030341c10b10607845241c40c0100035000 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 872504514 1250 872503264 872503267
    0xd0f021b04090215030f0609070815010203040810200406020a08090112050c0c1501080c0f150a091406071203090f060e0d0201140c03040b0a020408160905060307030309090e03 77
    0x2640c040350042001c3d407804c2c01130020100c20030800080b00000030364801c4041d590800705061101c0040c00c40d90014000a620720141901008664403c005543c010711804049407907007d80da1240380d009112150000706010703c8030081402d602542c1041320225006a80204480200340d1201446504240d001d5410401c008008035a10451405058020009091015500e54080030180d06c0c18090380701d543e16516040740104420340002c40c510381c044405444188402008100042d49065503c40d101d0b56820049801583c0035400f602c0c04c000d41340b0444290b20b0307060340c040c01c002280c0030700d8200400800d81402c9180c80144039400454206104030681403c80d41030b0341e1013505681c1c4200109140e540600010340c038030b0f41c0c24040d02024640c00200c440150812813989121807100501c007600040101000c42c00c0c41e60264105d030020080380040d02c0618500d5403003807003402d41501ca0000c226080030041140c0d441d010a4144c1180d50540700c41e40b1046c0b0740560b00024181003290520103010 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 872505764 1250 872504514 872504531
    0x115020706081909031d0a0311040e0312011502160e0711010b12010c090b03040b130c0e011202120606010e19050603040c0510090e1512030c0f0d0f021b04 68
    0x43e8020707a5404da11913114080c60242d0421a500114801140c03280305202c003010402c0452407001c54980c1010059502040101d84600c03100d142d807060010031005484081c00016401921561000420b039150b801d540880f120100e10b14000380e1030f801181e006a200002003100640140d00325208007040750004100025100c0008490358050b034070b0022165112103056900991040e0120090117904071181d0540c10585c90710441010000c01414001161340250810701a003a08032200500d1010314450b0b4039a19140d05610108164404a0240c6503600341128109004610940b1034041a5a44402160000c0802c036003518142c200552881c40110042150b4503060005e40c03180340640c0300e541c1d0203032a05042c8281402000c6a000800c054200140700401c1d411004613002409219502076041d04540003410654510181c64544e200000e0300c03090348540412554a5985408241c0303425104542c81920294501d994560060b00260a03400d0f4000c0a81c0d030404029402800c00502100d = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 872507014 1250 872505764 872505811
    0x18041104051b0d14060d03020a0f080702091006030f0911010e22060312020c0d080c030f0301120203010501170d0c060219110105070e0f04230c040e011502070608 71
    0x20f012820650425440350b01100b54120840082600880c0a5441d9250101e09880003500d40300d1840c40104039950151a8000384550301080da44143d40042c11400030b03003010482100748030420310440c80800d06003004020400840d209000c0e00383d8100307a403900c018508000440e04000c40025440d44519440280c000302740130101a41c03441707940e0140002d407180c02c60520b9181380000c1030b81d003011035001014240c1c1589a19600303210440d805400f05841d03500d00c107001c9095020703e06400c2c03c001408000050b030058080340c00c04446000750001c104d0b590326866110380340101c081e8000c400f40c0c8901c0c2803004103482110348400ca64010040181000d480703140022800030360320010000516291440030340e202c1d00f03105843d00700742942450801150340001241c0e01d8280441c020b8880c070381d00e1031201c0d4400804104001140d1240101d0b0724240391500400d80075030080d024090107011000000306134503901ca402003d07035985540040a1581c5001002c0b1101030b4010681200210401800c41000 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 872508264 1250 872507014 872507017
    0x40911010e1503070c020a290310030f110418030e0d0c080106030b0106090806060901031e060c03151703090f01140f0304060c020d1e0c0f1118041104051b 68
    0x100039544d5001881c40301d5004004560080b600203205028204030184110b0001c07130741c47c03403c120325002c80c00e86030390740d070507866112b801c9031b5102620010040c50500204210203480031055981101e04203e0a424400c06001242200b40e0040c0442c0c4460b0100c4180d1805c0182c20000901c11450300e0010f5031594000390941d9815442103450000150050044907085451075000d0911a801040149042400104018418400a400131215580b8101009820441050307c103410281c03d001403c450b0300b00400800d0701d520001100e255503200414120810209200c491961038001e46c2088140310802c1900610444010b0510420320080c1401b51070030f401074090b04082014290f200d281c582024025030710070305140d00441d003001c0c1d51020b40b103812103a84100140c20a4011100b14071403402a94011404040030b40a802070300b040600704800042c6400c80300c04142d410400540e807035803003800200e01c1502c004101408507690744d010341c1007951080364400409010b00d200c6120054032702d00309 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 872509514 1250 872508264 872508271
    0x20a0816020612060301180f0b1b0c1e0a020109090b0d05100f140105130507030e011a1008070503012c0411010f020c181504020c060114040911010e1503 67
    0x40040714042213414a420b2194002040750102d4115407080c0d503a0b80c0b26441107143d400244040343c40400b19180415800300100b15a520f450041c0e900e50400440566a118441c01c4036a04c601c60480010f6000780032815007103095042c0c4819920a0030f00c0c11100240640c0c0400755007000070650314801183d1704000006c1004900640016440c0d807024540c5c090300c14044011a801401000401803900c4000b034a1145d88164a0000b0341512400c4040b4090900f0b100741c119650700740780b900981e01040075a010510303142140c04000b5219030850030b0319040e10031036100010900c14170040001c1c01007011a1b0035695007500c6c1c400c451103034414040c0c03c0080266001d036a0000103104513000b03943c02803500b2004542c81d00040140c0031210300040e400c81040b404040064030300102050340c6c3c0302c0000c40399144210042003991640c54840c0c42d99551003003403091000034229450301c01d116003010b104401d0020b402144020030402d090006480c1d9004071b00c0c0301c50704128002c2006055008280c0134500 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 872510764 1250 872509514 872509537
    0x1c020307060903060e03090105030403030e01090212033001120c081f14090316060b090c070c060305040206090f1908070614120114030f0d18060f020a08160206 70
    0x142e40d0441c14910115042d8803042e50340c0c0e90040248500c00da800c007084e80d5001d41e0514000c50000078003426507015080d503c40094011030600541c1d605184088041e049840202410200c810030100043e038103a06034140803c540601e042c018040c051703504001030030a9000b60940004143e40c2c00c07503249450104104429403501043e078000c4501400d01645024490f005400390380781c14820440e41d00e80c810800c03405102d0094041e88000c0040c2900100e032103d0008100120302c0ca001c12a407960741d800048110345100d210900820b0315030086c030801780543e40243c104c60400d404402848600380c02c08508640c4079841d601d44010202c0c81c041e400b009400250080c2c040e191411001602d800c0350000c01014904041c0301011041c500100e99034115100e5840001304200a00301103401c01c0581d20216401c1d0050f20341400340c140e08880d490b01c9180c0454590641166994800c0302c0c4103001800c0400143c000c9003203800481c0b040e00c05488da03840501e01140214a00354002201988007000150 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 872512014 1250 872510764 872510777
    0x1407180f12200102060c090406091d061303020312040314070f05060106030621020604030b041b060f080f06040605030f010905100b090c03041104090b1f0f051c02030706 74
    0x800500d801c48058a4441064050b0400840030000c0d40703d00c3c0050401000780302c00724490403641e0310b40d04140300500c19000e081007496403c0d031180c2d0780702c14034003d2518180300b614003141d02c2006800c0705d0444150590301450030009600f18818541c80098010340c200406403030004800060000100b0450b40324240441030400980713003250a00710140e20001c00e0510f003d50401085e08074002902c511888070000c0d202035905480005c0f92402907070005080041158100001c2000b40e00c080903441c0c515000c402d00040d5030704421120070300e2080d101000543d01001007222520f200d40c1464000400038404105140c42d0300110f8600284034800044580d1298410000c0c440b041c010b0302c0303100700800000e000e201c11319000725100510107000c010b00709000100003018840d41075401e00490000601c288100316072428132840f25041503072100c00d00010120a005401e4044070b5007011110507640c000001031410b0100803006143c1001c0c80780c0742e9090b41c19000180d409100e03c1d800b0305110b40340c02 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 872513264 1250 872512014 872512049
    0x40c15020f0f06150112020c1203011a09010c0f050708061608060621090a0c0f0303121a041107060c09060206090a03020a0206030c07120f0e041407180f 67
    0x59107000b000b8528400d10350440070034030800e44590303642c040b60700400b0308144000410f00543d0070000d105410203001c142c0030720942c50100c40b200c60b00a60481d00000411003020075040004062449406041c4d404259081c080200003000811041c01d0301d80240243c41040365074601c0d150a00e4801ca030300311080c1c402080c070260308076006165203411220588400d8180990000e6000801080304040c11b1541034410014141c0b2404020b841010f5500c4030301000702654403080c00341d00003490301040380464143c42c200b00c101100d0b0f2044408641414140e5440071140409010051403402542000f00604026200100f2694020040403003910799510b401c0c1031800a000b802c006019111081c03e070810100d410100b0b500260041040b40c044407042d903030703480300d0104035068070810400602e1004030310b5903030f101c258001d58000c0c580d01e02525901202c904407400c020480e407042d500d0269150300d4001080c80b8502c12310041c0a86a400340504000a0305c070310089222829030381c0000e007102c1b10480d52 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 872514514 1250 872513264 872513293
    0x61d0f06180f070e0c040807141c1502030709030b1510020f2121070f0903051917130518090c09270114090303060d0b040c1502 56
    0x5406104141c8028015492a1102043c0c030780c2803c3c4500b0f00c5501942000c41c42070140282141c004110035001ca0310010b55481502d0303102031645244034440d0b008140e00c81c488460f5215803a19440d480034602c850070512050548c02904040c0401040084110010002800c5075441900440300c10f01038803054400d8400b0046c800800002c80030443d0441a006054500c00041040c6038480801207001284002d1344400d074030380a00c40301e051154180040e80b40074194031818043c00b0301d000b03076a10082c1c081100015510b554281c40007c0417a4404c020980c101303100850344883d524483d100f01c1181d41c543d2031002c089030304140703c1c0019500c100c03202001203180007020034070144070000406000f443c110042a468903a4100302a02405e40000066404005a50101c4508003a02d074243c02d51410048254020600b00182c0c0d07140078544c0e804541840000403e50f4441c0d58020121010041941e032840c00c0f00c080900219001c10140b240450090761410300b440c803410180e40144000d0607405072 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 872515764 1250 872514514 872514541
    0x10903030209120d020312130c0e0a0e0c0604030303020306030304030c03050f0d2a0f05011d16030b13080d020a110d08010303090b2d0a170f04061d0f06 67
    0x21074091076005541c040c1801d6004003c2d502c7c13281d01c48510094581d00c420180030940c1c40c40400a220b403400f0840401c0d4884014036042c040c069406007000307031040300c0309100c1c2e9503031812003000d5003c0d20601c4200b0005c0d01c250001e5074000300c0501920708044d40ca0348c441510070b015400c2211765030481c00000f409501d04001845842c00f9030718104031010809104000e1101041c1014200351040030300300030a00180d500821260f690100003000030020051480225a804441ca5605802841c806a100f000d1100044081d40d402150204454503507132400400e01662010455210009220340d6010b4905440501081c00164070b4002c62840f541610500b000e40e81070210040c88020801400400e90000519040d02e104451551f40c40f086000058413503502c50041044210034101201901d00c45000074190b0841e440d207400700c8076000064a20504002103618401071480321001401052007504101d44c02000015251401b03c0d2404100e400d0951040e1302c8101540000140086000c0c1d681 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 872517014 1250 872515764 872515789
    0x7150509030f0102341b0f050f0a0b1303050a0c0302040b120c0f030c041505100503040b150d120e090c072319050c031608210c010903030209 62
    0x402180360802c440d941448032140d4005c2d00524510081d000e00380f6620024200a2141e0000c1416488859080344041c0d40140c40c080d096800301000400286403d010840b52403d02c001460402d29a06190b80610030381c2203481480e031240214030f40080851018428001040d00a001011040b82940144010b4420003103095025940305100410310f1400414030090081045074bc0035120200307000081d00e000c24801505030320910702507051902c140d40c4074600c401c482c810780c2e846100c0350244800ba68030b40070407078000d055030051100040c1c0c0810080b0184245d0300004000b80707104449604d814400e0b11400b4020b0740800c01010b41217140303241c4030200c641c0c41498800c0c83e5181c100250340d003000308034110031940e1190f0311549110501351002d104940d00f1011515501c0c4088003c0d04003903036280c0303180700c04034068066038041040c07821301030b2565421344030b040380103043da8001c030260400305808801d80f6500e003002c1031219944003502801110545402580d016032140340d080c1c2004110300e540c4 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 872518264 1250 872517014 872517043
    0x31e021c0f0305060f240f0c0a110d0233180102060a1b05130503030c101103250201141614041203080a02120c070b100513020c0715050903 61
    0x2009501741640e80751b80000d80c40e034408488a900a0000000c80c000c1d010b80c4880e001011400700b101c0a01c0740f800218030380200e0080c8034440c1808000000d20040b6410010080c1d0044201103a14441c203820314001e0b800041d400b00b060b4100e02540000f4503c03500011440419904008414071040d80e040100a070082c4d0b45d90410000300003900351103040c001d00d5020100038000082903d4035103903100f000303140007414040c042d20b5440c007180b8807554640d0302241400740c1d414a80000f010540c26408242d034032803c41001c4004800c0d4280100900800e20951184110b64a5040d002c41122888146a00900113550300d2140711200c0a40680320406523024400c0e0090140801c100080301341984003069600340c140001a07445900cbd10720080e1040d90182200b480490003407150402200005024442c05132044408a4540243c001040c444a110315940041c2e04c0b000183e5190309640144000d0381020100c407449a581e800400b40300403285034140110700040b40c2242c031800c00340445810300c3c1c020f = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 872519514 1250 872518264 872518279
    0x2010c110d030c0504050a08030a081003020a06080606160318050d110603061203221409070513050411091005030f0106030c050903100b040e0703031e021c0f030506 72
    0x59400c0580d0340c0201900e9508041d110710f070940c407440c081e02c1254040c21010702400b10b00c0343c071440c05030344e00c0d80b102030401e0000b5281400604840711942d1040150b80d030041074890340d01d00c0d04208454048001c1d0029520100070450b000300c4c3c0c1c0d00e20506003900c43c403c2c3c4410a407103800d040b8003411011240d100d40e000e0701d01011200001228a54045d10b11802100d4003034036601ca610104941d1640c07100d0385001880002803c001a000900320013030320000c82c009000c40c0c1611001c000005101d403061050b000032803c004290a54099000740c121145000405048030b56038000080c03e40d481841b921b00603441c00906464a030505105c2202c4a1000f828501e1850824048e8920744050501c200f100701607482c8000b442c0c030f501c200115414098014120b404c40c0c40c000980000030009035104500c114074025002201c1c0c03101040ca641180d4050f1105018520070401034a01110030001880847c01041480d040d901c01f08200300e4140c030303443c0c0c0d100107400700d0103840030301102d00180c40184070360f50 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 872520764 1250 872519514 872519537
    0xe160f140904050907081b0f06090102060a05060609030a140f01150303080903120106080703060519090504150203042009011412010e0f0c03010609140402061e120702010c 75
    0x600801c03168100c03410348001405039a16200b090412409400408580c0110b00d00800b900398607201c00804082c040307600b10011030381401080b209100310603466002d0f070040800212007481075845640d000c0360141009190207040000281441c440c1541100c0c0449032455100440300c0401c60742a4403028800200030340080300302c060300005801d110081c10020340c1f8001581003d01072058a0700003008075040107155131102001b07003d00741e00b21007c00001389000070000790362030300e282c1707201c507421030722210703410042c20b080b4000081c010080c01514802d803010b5050000661304d100943c49a80a42d4000e0105c1c4800590a076040c146510789902c291302d481c0041c031040c0007000b02072000301411158580d8a0142845950140070704000000310350042c005004401940480e4185d00108214001c2000d070307480700031000807100610101c1480e02c128100240060804c00d0040c5105c40c0c210b51020b410000f80e03000e80380b0b55400f02502c0d0341106003075000d000074950240202226005c0c142400b01080c074 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 872522014 1250 872520764 872520797
    0x70617040809090718060c050c0315060609040204030b010e041505090706030e0a061d100219030b0303070503070c030c05010c02012c130c140a02250e160f 68
    0x202ca121034820314501e40860240d82c003c1d07a2110092412500c000c040702c0d40c40b00003414400c0f180d0400e440c580140c1c1c0680b417241c94045203401c903d05090b09200e88a803128070038000d1941011000c250001d50820020022a80c3c06c00703014020811480c03402000e2400e840c121200041000c02d041c3c8140c02c0600b80010050085107080c20303182103140028040b00c07407070409031030640c4450000e4000b602e0032007010f000f00c03400c10480803a102130000b11403c0040d0700110004a115845060b900000c00840003801365209400c04002c010006088905100b40b9846007030441c1e01c00401182d038000b00714800c0007001203460110000b01000d0078840d85000c00c940001e083c05030364900d02d22038110001d46002030b98214501845103008094004e80703000031030403c100020315540c001680803a206100000c034402d044d208403880d0122982c0030700f000c0d04a0102d401004860003441440c6240c0f001000f03c0d00c240c07881201445a00d220000840c0da90504401034260500200400108144030051140e1705 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 872523264 1250 872522014 872522017
    0xc2001020406031506090b0a03061d1506040e0f0c040f290406210f020705011416051c020f07050309090a06120b0c041a04030b0f250c050d020706170408 67
    0x507821f00c805203983d40e100b50811002080c0d0340d0050745071424030415169052404001d018440d84820b000f00b8a00c1064408200450003188074824241c00c00000145542410103240c0d6007003d00706400508040c1c03141e08000028115411070901d80c50002406021032500420f100000a40c01914518003070400c10028440851320b41c102520006041c043c2c09003429a5001c40d0007085244800c544030341251428074040c1512088095902046a020400c3c0c0c0d100800009804005a2103403031030440c81c2003000a103c0012020300010b143e0034088283e60044103002441c140f84036002a40e50b540d54041040319628025180d41000c5251510034801c10006030b01c107020b0a81c10000c1041d01f66900301120040b0310903600071140c0340889846401c4074440c5c0b840640309482c03050a102c2c4003070341c920761030b280300340c2e02128260020840c400c90358100c81d240d500d089145500600d0220030715040345c2c032050320300320b00041c6201c016400700c1000c00003254442803003009068003007102d158604041c0c440203840e = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 872524514 1250 872523264 872523269
    0x4030f090311090612032205040605030a030813060c0c150b01120209030f0706080402150a0203030a090203010e060c0a0e030c0609040b0a0906030b01030b01080a150c200102040603150609 82
    0x50b4103c20040f070070350750703801110b503945034800000c1703d581361001810228180d42c20322110310076010307514002c5901c1c68280a0a420348402030000c104203902518103c1707050030090100c2a019009125400100d00c103401058942c0304940c4404481c85400d2420b4801020340d0351300041c00074a4800c807c3d642da80e020314030340d0901030384100c0980c544c66600b00080c05c14105180400c220f1081890006020313400a8807070b445580200e81e1151101c400031111302051050908200042c0c10410000c2c07100340c0240d120001c01d07800900000303040000c00d90417500e0594196007607048400040f9940403a0342e40441c0c0ca410500d002d4014000074031022001c070750280521412030384202e1301c03501c5034541d60b1294290305c0018a680c0d20b0a100040d504c2c03d240415210038001960364555050000c40d81c101c0000c0c0500c00158041c4c100e4045101107890306008154202d542020003400c0280113a07500620b021180c1460300392000140d460b480d107000541111145603046048180d095820450aa0891000c004 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 872525764 1250 872524514 872524519
    0x9020d05040b1f0501180e2d330603041406090a0503030406090614130c05011d0915040c08150a050312090d141b04020c0d03020c0102070803090604030f090311 70
    0x41012004070b020340381c60155040f5202480d4040108248d15002a0507841c01804114416644181d41407501c168210225403201c15900d000342c0c80c6090014035a128810039150048681e81003403074074000341e0f441c1e205513810f40e01180d590404240402051000075003050605006000c50041980e56036142d000040000e462203540d4a0300c04e06101041e0049116404068541c4440745032101c80d80c048118a20015500b0740c010010100b081d5000e8040c0c11201840c10014003d4001d00c44100580c481000b481d440a4417600c1140d480c82d0303103ca000b03090240d040b9813601e00e0079140c0321102c4a40e0800c501a2984500143c07002004152004a040e42c5408280750030250355041600100c2c0d009034074420000c000024a032a032120200010841c103510f038030400f80210318024113004000603402900b00d800c0300c64118851059850307000c1c1d070040440b2801940007504001480e2940047c030f07001280c001e40c986c0c205004003c00c141c3c8c0240900241012828032461190031921110803070150b0900b82070 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 872527014 1250 872525764 872525777
    0x1090302091512070602250b2d09040f020315090916090504030e01020a030905190b030a06030b130b01060f02030c010f06141c020f01050409020d05040b1f0501 70
    0x1088041c0000703050981c100b001d80000760b18140500b0341d681d40e05051007410010b0090440c420828500d141d4100c13030f946171402c0161001414440c4414940d80000401030ba00025942100c5601d0074203a10f0220f6606601c0a941e221101c00b0180400c0d02c0398031040b07401c914030420070415000c80050344420021b005a81f081c0d015034410350910700d041c1c1d01880100900ca5248000030320195103070090b921a900ca0750342c1411600c2210016a900c203060840100841c48041090100c0d051a00c80c80307142805d0503400c0044031f40d54001d044131076442a100c3c0ba4282da2907003424414809018600c03a0070150313554511010340066100d80d1030220b41805490b08110701d82d03460040709031081042e01c40001e40c442c0204542d59481040600030080c0b441240300000c4010210101c0d490104c2d214a55030b03006c60145500000540c2c04c00a403100903000050612205000c0410503425510240101d246900030004030303400c00e070904074004c020090403141419400d021207032580c042170b90b100c02200c00c06c2c01c00c40c = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 872528264 1250 872527014 872527021
    0xf1c050114010e090a1d060c180d020901060305190e030d05010515040506090609220516050d0c0507080711010206010b0c19170d060515040f1a090a060804200109030209 74
    0x4a400d400c3c1001411102e20401e000d100134101e0901c01030181c00e040c24140031400b2705500a000242c1d0b80c3d400f004c1d60010303802004000250094014540c0601c00640400380c000d060404101203d2042020f40b64560000c184016000c2262280b00d01400048402109280202000c0b0300c50b44182c1c000c0d00d0107150082580c00329034948800b03071007101ca001040510700400c0c043d801e410301c1c00d810310303044402410500840c5405001d0151089030364060b83d81c1c5c0785822500c2d0158005442c0030b88410081000400041000c42c3c039100160050b244601c26605280030390200084c03600c5010380003074150180400c04030100c0600020f54580c09105610001101951800e1000321001d40c080c502400000026403040003400d943d1086040d160200e80c800003002c21050405280e025a000b80c0d082a40301000900180c40c111001c15000502c220449240480303440c04148481200d0f030003100801c2e180c47c1400100914160614407030003902c0641c2002d040d40d50002441e0400c0c6100180c00b410740080403 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 872529514 1250 872528264 872528291
    0x11203030b0a050d0605041a0910051f030c080114060f01080423010902011d060306091801090305181504050112090b0903122a0f1c050114010e090a 65
    0xe0350b009040013800565842c601c0d0505001900c000c803821111804861a60504e045008040314099104d500041c030a80301a1540030f801028060302031030302102900d1b500d00202d00b00039600717400f95100340c0001c1c140900d000545429960b503c02c138402072806660421030705445452251100f900d0918201400391580c0c20000d03070103a00b5541c0c9440020030403226a1184005402c903001c100d00c00c0c1e0740c0300c40d0a60001d0302c1c20882540f2118650744203008001017a40b034680b24400d150000300410304032001400880c840340c214ae6100f0800c6010030800b090b103014002660105800d404010b13600b06408500c0840703022010b1199005450606c5480d0120000100c3c0a80c0013246507a4020740c1c00c2d8150070003040b456a02e070000c4908401100c4060002440301100014400303008100301c001000d05c912030603203a0559000030141103c040c400f4030407005400000980103a2031100351900103025414454610a03001c1c49001860504c91000c4070740c800c6d030f103800100a0f4000d10f00c240c00036400c4e142815 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 872530764 1250 872529514 872529529
    0x70f020d0f020d200d020706170f130201050c06130201090b090d06020f04030206040305030d0b1c0602360f0a0602060a0906060e090d12090f03120e1e15011203030b 72
    0x180500714070401c00345c0e800140d000984a002c0d07400d661518030b0b510782400b011500340b08040350750403100f035400340200380c04821020314048214030504045081078211000d0524204040b5100404203100c08030741c6007596081152000548604200189018041c00105560022400f0000c011641c00604030102c110018140c07070203590b004128130780e1b840d030f40e01788070b99260004910380c020319143c000d0056403442c111841c200741c02d000062628031040c050b11801c000f9046034000901c100b1000082407940354803540c01c0c910310700e88420040d8102c904c03141889881c2000d1480c050043d155000184020307500014000d0384281d04079000328000c941031515074041d20107a0f000481d100c180700107000c070202c1d003c916440400300603981d40c80744441001d100c909881081e5000380c0003048201d50000464403840b114100240080700102d02e50b03601d40c0c0c0140c5400e40b4240e5112a100210300741c1402c2c0c8600348620031540a440320b17028403039410500e03002d080d1982000010141030340c0c1d9031241d1940d00e6408 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 872532014 1250 872530764 872530817
    0x304141f0203011409160f0306050a0902070b06010e030a110d02040504152016110a091d0d0207120609051b100f080615040b03070f020d0f020d 63
    0x102415003002a421458080d40080c0210240601580032031901c1c0d0404200c80c5101d0302820440b03141d0032801c25400c0c1c0b090200c60788103038105074407181c000c516525140d10050080c6450800180d4030052410b15010380c10b03026042a04011143e03c440407907139800580e960f03486070004010b00443c03805000095040c40403100094001d801c1c00200030a00482003145085102c10410074000c0c0b4141c404555032144817500c1c0140380000078440740117004205100c0082c1d9520510704c000c00c890010300007910302007056001c20f0b111501c6106049400d9542d0030310704260203a11005001c41e051060010307448d0000360091003500c403003d01e4030000340300303840e00405400b030f030080c00351a000081100a01003512203180b10f58044c2028901c0b82d41d407a4414504113107005080d6481c080261181030400c1702c1c1ca40f81c0301031141c22105c203000118581c01960019401810326861701507601d80554800f9042c074024660407002c0c0085890215001d5402041c2200384040501c2c051640050885042100c40c0046 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 872533264 1250 872532014 872532043
    0x20109030827150709060e03150703090204060305010614040e0a0201111c0801211205130306061e0f140f04061203020f0f0102090f240304030c0c0603060803030414 72
    0x1c0d01500f151482940e8942c000c884542d9040002c6849071801d0390211090941c1c83d070142d0080e05c8444620062120b21a0020401d29000c40c0d081c07601e40000d000c0e10095001518944d640d51390030844100c02d0702065070803480c10303901404034a002a40031500c540c0e8641001e4144480542d040d124100c0510144050403243d00148451800c2800001d08042c400d00503000c00000c03200f00c1c019095040c614078022641d001a03a01d400c21540e0800315995049529000c1e00da80038200044000b0311207014040240c41194030700424100c2040e07407080b50080603813202004080d503401c10700012902001c002c62500090343e5849031245140081801085a640700c02d401c1543d0104000030141d01003800f605010300d50048415444940c48554202c0c81040b03151a40b00e4500810000e070b909040350382c0006070b01e134111265034140400518009079442103c044002a0440e00300340d04100d007985000b00640941e113001c10002e03040014007030f038a10002c0c6c00a404046250502c06500c50700308103989141088 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 872534514 1250 872533264 872533273
    0x309150302120f06010905060313030c030e0a090f1d060a1a0909030c0f071d060a031406070306090c0804030c1407080f1c020a03110705101e020109030827 68
    0x1c03c6541a00d038002e0340d0150000d04100d000050915105e410340e0700441c0400711758000f25042e640e00b41d510307ca42c071104505005110080002c560741d4420035200401c00142e001c543ca01f00d0342c60351002c4444008072403290707090f071070410384000b040001c40592010720714400281c80b075103a42007000442d4140b40c41c103074440d0746181013000b000d4001c03020b460101c1a40089800304014085802c0d2100d0040c0914a01c003500d07d500841c440209650b681d41144000c0c00221105481c3c0d1100303500d002000d00e00c065150700c01400c2c4200e83e9454800e001c0181840a41000b4010040c40001c10a56001e000a010401e1501e500402c0c040d2003003100240c401c89004840103d03540741c070030746d80703803410f036107680c1135074041c0c15074528101c0002d03d50544d80183c01d5000d4058528a65000d0f80ca401d4102031100c2140305e088000f18060b02c40119038a0740403502e840301c0c0c0d00e00ca49010381400300c280380300307034401164100310480303000a400440190300085556911304061100f0810074200c002ca030220203100d0b00c41c = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 872535764 1250 872534514 872534521
    0x3040b0a1808071508062b03050d06120b010905010b030c070318090f0f151a070f0305030a0501140a0324020d200f030c071109071205060409030915030212 68
    0x50f010a40e18581d03140d5180c01c1c0701a84c0e880700300080c150280007401c80c0201c00d80b4104101d503921f0751880c03c055110707050881c00c05030b104a4280856642d500314851102500c80e0385002c1c040404001401031268020520903581400c58400c1c9901000d02100700c0c0903004902201058041c0c4110155212401d03559242d650703aa403503070313001fa1a03180500345509103400d1500741e06004031b0103042900c085060705040c3c4185481050308161010709100109440c0500c0040c2c005031440044080043c000e98889450f0b05041102204a440680c410340c282c002da81040d2441c0d440b06450300040703039003114600055034070507900d8500405009442589040c800a02001c000101c2c0d402441c020b0200a40503403201d805c101b03000358500c921840e80c0c05240703040c000500481c01c21001003803c1c52182144505d49030045012a000601c2541c0010100e0403410301841100164031420707500120888040c4412203403628050000c40c1036005400a11220010354002c682c081d4044130340d84540942002030524 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 872537014 1250 872535764 872535779
    0x31e05070605130323010b0603152e1206050f09190e0a0b010e131a070917030309070603090203100b04060b04090c020105100f0b180607121211030f04140d03061703040b0a180807 78
    0x140300d1340c3c0d041c1c52403401e00e0103b80c50804403690304541501402035000780d1254800e01450044407240001100c0d29001e42c9035018900340f2003090210f00c50100720440c0d50504c0080032096900a021442d13180f4a580080c0200b5154464030149400c01800c00080781c6458100701c8107003034540c005580c140c003070000802130b0390b0001004600c950381c03a00036507030b42c55210345084040d6a24001301940c154817520141800d00c150354028021104000c000080b195603403490000c090b00302c1e50241040b82d80e16118507807000c0d020301900c2e81c00301005003d01c080d1400d0026040601d461406003135600040403403c15801c1c82903507a487c03088280104045d48540c2e5603e0034156081205032250005440700f00040034100c860300510442e40e0900c2072032420f6985505801c82d40c1d4200802c01e95000720583c08095180e8801c0c444034580d40903a80c2d0105e2964107004182084416030200d139100380e4010001081311141d05c20603140710203054541001316000c40303843d200500495406c030200714041d0003800135402 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 872538264 1250 872537014 872537027
    0x3160c05060112020a050303070809060307030e010f0b12010501182c0d0f050324030a02090a0203060a0e01031a060d140601031e05070605130323010b0603152e 70
    0x3180700700c5e01d03c12001d4446003031545078020090001c101410501040700b40d850100081c41e0b0084c4186000555049001141c13400e413400241c58224190340d94000d80c42038108031400070866101c50009104551610a00d280e00b825190b00800800350f58092910740000c00031030380100488464082810300d105040745944480c8140905400700b40101c3c0c44450750340c0a281660310607403451455a401c48c004e46491041400c1845035143c0c140120034001006988501399980076100e001d400584070b2038150b05018007020160407001503034401800400005816144029403484d044912800e592580c02c0401c80014062400400080c225880c0710780d02c41001504904a0707002d104900c0e1a210400340c1d9814884c5203a40c042c01d00d030445142880010300410003844106419606000f640365240c9074603c0f21186085038440744ad10281c00003090041c01d00800c00c8052048400624508002d010f611000c02e2346085d4a018031030041c07182e1107007104800c284c90040103141080e004000a500002c00c0d9 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 872539514 1250 872538264 872538299
    0x6060d020f13090e07240314090601090f02090906060c16080303100909020913080c01180b06151836010b0c0304090e03090a122603160c050601 63
    0x4140751942c84004e10400040013002c880b2040d100302a41c10680300c415040c4010048100240b42e103501d02852400805a8014828121600903210030f50403c10210152030b000308010302c1c0301e0300510000c6035507910442d800360490011101c4540d2032070046041410000040c001c45800d140e02c0c1d10000e64403001000640c81040c12800c1d241029071105030a400300da03071440380650410903082c000390a030104000b15000c00c60140d60440d050010840309a400d4907502035940709505a54160300c2c081100d01d40035250002c0e801c4a48890126507200400d40c0d60048444a07003120b41e00742004155625007491703105142d8040c0b49080d1500b0407801420742c0821581d030075407010b68841d500018401111100381c841450315280558501441e141045002d0440c0451800c6507010403c002c00c4280e071619220320060103901080c080c19a602d003450044018916040010980c41a92255040c109a41200c1d444180811800c206410044c1d0841e60807074500320040c074030302c118000400c1402e800040d0070340 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 872540764 1250 872539514 872539529
    0x50a06090b040b0f01030c05040203060301090b090304050411090f150c120909060f1003020a0e09041a07090312030c0509120601081b0607030c15061e09020c0606060d020f13 76
    0x2e0300d89564100c404113903001d01c00a05407404e00002400645000c2e0011a00800010004a100200c03510b4110065905544940c8150300024041203541064024800d00030740202da954103066101c408a050920300e0b01c28076105400b10f080c061082e42d83c00081e1806c81c521340301118a11080c0c1c07002c440c05070740003103080da01c034209d150000b982900e4403000c06007405401800034201c41409800c10b4019421244036041407185003440b14903240c480d5048079100302c0c060103681c142d091040483c0100504041c1c110410010002418004542c0022018510070860701d4001340d1103118110864081c0220202940d1040d90808200c51010340040c03a0703416170710140d00b50380703032040b0220404038042d17000078403560001424485e0501080c060710300c5c461181d028915400340064110304440446543d504002da85102c40c610f089101e100180c4010b02514414104501c3d01031210041a2384a1000742100e20605000594102c90780c17240c0c06aa500e1200a140c0315100c00c1d2a165010041072240200724 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 872542014 1250 872540764 872540783
    0x40609061106070c030815060720010c080301050d030512041b060203130306200706051b0405010210050a0b06040e0103051203010312030c0201090818010908060c04090504050a06090b04 81
    0x4440240402c0803030045109850320802c880d55642c0550318544010501555156214400103c5449250041c100d2a01c1860700d8422040000d103030b5585000260005030420408654950000f800c02d402c4078156401210543e20502003460308403164414683e60342c001c460310100b4001080040c0040c0c00b0741c2518480107845492300c90381c0c00c0343c0c0c0303004044901711080100780041010030030b80d0703005502d503501411742582d80c0f190400080405134403140084950586c4d0f4000c0001c00d4480401d0101640c113031444251400d0b242c400005d540c2c2c10344000e51202d1a40d07070400710b98582280d501034400d9101c0988007507221a171710300500c5c092401c01d00c01660980190901c11050310b83c95800c40303060380d41c010404040c00b606000b08400808100c0108001e565031030b00107501103a041005065880c5e889c07603110a201c448200010510f448aa21480d407a912080078801c4840e2000151001d464800e900040c050341d40781005441c248112101800c3c0303d1a21a0f01d40074082e03414030f824400c0d800f134440c2e034 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 872543264 1250 872542014 872542037
    0x4060b0a020c0d110d0807150b0907050a03150b1312170d180807030f1805040902030c0402191803050706081302030607050306010e040203150105031b04060906 70
    0x16005110305054a401a0040c0c5501820740c0b070300c41032a92046020303400d0715100d0f6403920041000e6003002e01c0280e482d00c1c00810700070200203403201c18001d031807a0208144028800304001c10b0701040080c040c3c43c01d002000c101d103032507240700c0c3c1d0140720a86144120440ca0340c0c0d581c00b94178103d42c0800060040b0300110f0b0008544407005103c0a40740c0d07640b000e0303a07001d040c034180681802c9401c01c501e040c0c0c86949841c00340407d6040e40320950b01c0d80f40556401ea64414282c42d001d40302c54080341300f4009000b00d1080c04075000200c2a105012164280c1c0c010411008a00c0000d0501d5640722180303510500c0400c182c0c41c0a160094624a40c0c40d4688400a141038410000312001c01c07188402426940078003810b00043d40f04507041d5400110885080c91200c1460b800079040000403144400010b001004002440d83c2c04280c05c1d103403041c15101140b443c1003488000d462154100d0715241445400400f040905030140d03039503c03104800207051070b00c503600c034a80181854014402c0400146011045 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 872544514 1250 872543264 872543279
    0x90310060b0304020d0309090f02090f0405100e0c0706020304060b0102010b03120f0a0903050114041e050a02120f06040f02130e0318010e03030d1401170a03120b0d08090406 76
    0x1444181c58100c15010b0031a0b4459081025888003900d0803400c000c25013100052000342c0b07005641000da410300c4050f0321080a80180f101130b21124021612031410308061042074010b14200200b41c80350340095403400c4d503c006080685225950300240001c1c400000c00c0140700144e441a40e044600b60b00074055a41040c1c02c0645d180a15400c0c3c18440c2c1040015000c0d040800380100010b20307050910340c10150307481e01c946007113031150170039404024114000c0004003ca0030340250395546440c00c80110014494540070703500c8030106002405212242203a8034003c07020030600c1d0700700100d40111011454103103480e07080c40c0942d00c4200c1c081c591614114070062018084d8036080d4418000840c01c21b08801a41174010f034400d0741c018180020000d183c070306074a050000742081d007184100411006042030500000b550140c0c402008002244007111101c0000320b01d60b0204d0f0340503e028880e60381c070340110700c004080c1200c1440d84240c2d0615003804102020001d001c00510880302000703d01d596000 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 872545764 1250 872544514 872544521
    0x4050c031e070905060f2809030605132102010c0e09061c080406180b04030f200607060b010f08010f05060c240603071e0501050d02071205090310 64
    0x2020400700000620401909181c01203080d03200351140352600b0340c01d07039680101c4c80a0340103c41100c0e441c44001407412450142c150038030407082540141d05d40c01885440c004201c0200c5020007002e40d92260045101034065618038020301e600704004824104905c00601c03200e0118000c25405942081c00100496000f440191020782001c4c1400407141e8402042020b84400c05a8400c0d00e40080b803148808251180050400b034850342d1200f40e01c444a0442e6460303901c4681d407042017580d50401c402d1000924000c0c0183e403d55118500d85d0103c110030116161010142c149a5001000031a51800340880f80d00414802e401c280c0705c807100741e5a895011142900700f40180b04041d6640300c01007000d410054000c0686010490954001000c00d0140c102c4817040c039401031850306050020320403a4a41417184400805001030807041190252014000c0840f240c801e00e814043d000c07468031003100054044445166222a542001e99141040901560488820340740030348503015240c41c3c05c41d010b12 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 872547014 1250 872545764 872545771
    0x6140315010f14040905061f0b03010b0f092d040b1e011b0f0f0308090318010c0c0e040b01061202040e2205150a0f0c120c020102041203030b04050c03 66
    0x100307008111420f000411556009015007207401903034544107000404c4c000c0c000c0a008801d121403103412a00442d0840d92100e08d50f8000401c01501003004100c12004002152030f40c80407a00500d455007202d000060181d034411480c08801041c941d00c007084842c64460810500740c04640420040e02d62100b80500f490b2803071002110955240013444e041d6020b000b01200c0081c603c2d1100340000307019a10b1b40401c001e88078044900716681f4005100305070300298260303445401c0000135428219031010803a08240945103e5040c000a59980800e008024403564050034164103a4901400d191600039a007840c24414440000d403409036480c1a00120b000301c0d030403654440306200d007540380c181d0300311441118000041e0841400041b0304000440c2808018040365800c000c45d0340c0f80c41c2002e41003050f1070181c0034601c2010310b88140c145d216600024040b00c041000c0e80c0005000c04030082c268024031503500140c882c0407980640100b09030740343e0480310310940103680038030264813031030810081400240e = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 872548264 1250 872547014 872547029
    0x81207030c02010c0203010b060d060905131a0402010c0b07210b010f120b0a0f080d0f08010311011202030a020703110d0c02010809010b0d06091110050a030f06090614031501 76
    0x41e00c072009036129181075540c29000500009030500f400300010a03e92000c40200d40c0e041d1110401c2105a03e14801c240d84420030a0070085c0c3d6070a0382d92100503002c0c0c02050090301c1341c0c0b10008141503920404041d4101c40c0e1000990200382082d0401070704009060321000900001c0141d030082083c0540101a5541c074180c442d80d0030f4042e101c00644665044590005541c1d55620031844941e071a1a02d01000b0004607a14090f042c0c10084280e00700062102d03660203101d81c900038210645c0c1d002d00542d044a411010f440d100000c1e9000407034034004803d40b13a011803400441488108407040c1e0040c02460304c43c0d210340d0200e00850940a0301c940124004d400800c0c60701c0784c00e00141d40138469040c3e0001c1c441000140a0407002d00285088003056025140c503036444040c1420080410b0341d03920461011682003c1000c0c001000420501c10b10a01d5820160cc13095910810003603504000041c1440d81024012170b62549906049000100c07034944c0f0910a2070000c66030341c0e4400017600d0684140 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 872549514 1250 872548264 872548277
    0xb060f011d0424030209070503060f100203070b040c0609050316090c090e07020601090b190303051c0908030a3806160f0b0105060405030606090a0b10050408120703 72
    0x2060407401d2120001600342d4010b51641c0d542414a2038003560324000d000744083d40d1012506600520007403100c010010400c3c41002c005120450762151000d01d940741084a00c1c1090311440102241180110203008040e01599003d200810004284c418292245941c031403664650781c000f010760b5503960044841000b00c00c0f081c01d10440c09203411850036446282405a1460760300d81c015086554205c81c10360041e0001d000601456095000d2140fa0503800c4031540c1c0988050210940090044d00c00241401400202d10100c080400400c1991405921080100364840d0520013455032003103500d0800c948ca003210400303c0101558442d4810080011540c02900300102c0900e40c44001713002c01279001c001400546920320508444942c41380c428110003504a5a510b04001280010380000348129002c0c0300034425610006011b6a1002c0300305c0b02d1200b16100c1520200007000340c821007981103104540c00309a003540050080080382c0703c59003150351440e444440303000c540c0901c45006000610 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 872550764 1250 872549514 872549537
    0x21070e0603270a050304060f03091e020f06270d030212030c04030b01090b040c050f0a031505090106110609010b010e100e130603020a080d0917120a0c0b060f01 70
    0xa40c0c00245002d20082e0312440c038481600ea520900d0400304140c1141c0941c40000d050101d50740c49043c0c6003002c45142820b000c0719541e80c1d02c0003c1d5541194a8000f82001144080c09554506180343c0900380040c1040b0359490240300e00110038065a091510b009450384000210350601d01d1000038800c2e050f134050600c403412040041c51603400540440d0101c14280008030108545c0f02070700e8020581140005409482d070400d002c1a5460b1040000c28440d040c841304d01c816070214211480a401da10740018140094809158510040d401031904003116100102d80d0f81c0c0c00079503083c20a4844011108903035900c4210a00ba10304140130180021013404580e030090a050300d803040000801e0404444942042005c120404ca80ba842c441865803140710800c00e42c01c1c00c1002d071000e8154040640050741102c00090300d42c116501c00d25040f40071114815040361418088003c0704010000c80659840c41140010400303040708105445021089000c1003292600369125104c011041c0c59a6400b540e = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 872552014 1250 872550764 872550781
    0xa0f030605060d3201050a1413080d090501020c0a030503040312150605030601050d1b0f1b0807020d061103012112080a06031514091212060607020621070e0603 70
    0x2400f03140b038410b200492644c4034111910a000301032161030380400020345c00310070250584d02c2042c040e0808041c40c5000c103617600419402d01c11143c9400d5000408204400a8a031240c024440d10004018500464074001c04265000380203500450199950300d4981c140300b010b01c0d0440d0b40f030142040c0a08240002000b03054003601c042e55100d401410036074144052105e15805441c20206044410004042c80611030307600480306c118585c42924107001c05103001d000c51101076644101c00f41c1034000115141c811540c41c122810007107540050240002d03074554035910740c02e410a014001040c000d44114209984602150969458104d0b1100f04a0340d0708800589400c1c4c1c01400101d0f0a985901001c0086011940c2404c03250700b1040000803405900300080268100152005038140c00c007841e0448001e4418040c2d42541040c01c210340c1640e114100007505a108440c002500140d001c030b840c035080c1004018403200c0e50f0101e602041150343c1c5010807590f191060454680c0b000080c0b01144842 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 872553264 1250 872552014 872552063
    0x120a0c0f0509010c170a030f0e0a0f140703120503010305010f1103040b19020f0c070608070203121e04050f1015030f020604080a0c1505071208060f0a0f030605060d 72
    0x120702603903460000c54424845c5035050b0748141e0b01075001c01d03200c06d40c1640810061045122900003440074020380c0d505541e07a403074103401c011005070650104102200d21034809020440c01154814840f002da0140760038080c00d00c0d0024482943e9039440c25841c410401c4050146901c11003c00e020b40389195200d43d03500000b944064a401040c040c05520703559003004510042484a002c0b44040d03444a040307400e95031500c00541c0018003045140b030244219250000b003a5080c90810544020007a560003101c8590010704400b00803c8a486405100c02d206003c2014100f1484030b00a039980c00c9080455182074403044595001c64900c6a0400c001144401e920482c885200420940c03a059640d404a40f604030314030016a00d8002c084810801010b582c6006262258030b41002400c0c9a0b0130b03140d05128510101040092041d0341d00000c8c0c042d039a565048119010003000e218141e07880354003c00020300603010890310701d13151a0108100303140040000c0c4030303603501400110040d024141c2e0f001c101c = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 872554514 1250 872553264 872553287
    0xd02160e01060809160f1e060c021003090b012c0f06120a02032401090b130515150301080d030203010821120415110a020a120e06120a0c0f050901 64
    0x2580942c0700052140782c2e41c2c000c184001d102c070710441c4200c1c40c10702071925640c1240c87e40d45000040c10920400c880b50304444000d6800750110340d40c480d4019214010f0f009050300c4200100041141d000108941d010750155094204c03c0c1d000c85501c02e200d0300c0007440220030544001d00b00d44185400918180360862882c2c6005c125a000da561003442a40401c0c505009003240d81d6550742512042d0780158820703c2458018050000188481d84200300410342201461010180e4035032140c1c00501d50024a890030960340e00040c00020340e4038801c03035500c070032900700b0300580100e03004000c4030004c064401e000752410780d408075020f02076800703620703004e24100a03184105014180c402d20042c0242204450f03480d110720f004540c070844200b0a05418822101c3d01d0301c00906941d011700c80c1281146d8000745004596030b000c502200130f50500082603801403412994190320802c005080341500140316070b03240c01a2503054042c440b18501c881c095802c03001504910b030000d101846911141e62240710352605 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 872555764 1250 872554514 872554531
    0x20150f0c03030906061f0e01030f0e0f0c01031b12050901060807030807031b0803150a05030d05071403040e07140928060e0307090e0f010e0d02160e010608 68
    0x5440340e0049024150b0700304881c0ca4156030005000c11440b410401507041655000d80340e8807a02e00c07030550b0081c00400300000020b041503995901580b000c0550f602c0401c0303080108040f40c0448581d014180e540e036000030074160010b0f0501452040ea0150181107400c0754080c1d44420805010582c510380003400001e11109003592148000200c0030000c0c8001030146014600460b41c41ba26820040c0610300d074081044c01c0d01e081c1c03100c4100410035050a5a80044240090300c070480340e0072000400c11071081e00500c0c0e140c00342c04c01846038141c00a005080d22031241580c14007140c0c8d100d203020f803030b8081e0f17100c3e0049161154000400080c4561503c3c13480071404078a1a00700014000032070340c0400d031301c1c00f3f1001a00a0b80c40b0900c0d11009400b403100103185070700d0008921003440001c03a84031030061244010458403903410400c0d8000174840c2e04040181700b0003c0050001c004410780c2e0320b8910048242c05030284990046c4489007100301c1c213040e103a00d2958807144d41d1800c842100c007840002c24034607 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 872557014 1250 872555764 872555767
    0x70b0901030e03161211070f150309060f021809010608160903050d08010603050f01050a0b0705190c170309030a0f050a02210d020c151605030406090320150f 69
    0x110a440300140c1121a8010a00e0010200c1005e0000c0d20301404840c000082e035000b07843c200b09284032032100c102a9003c0942c44844d40c407481c4419000340900d22130007000e4505000708100700d02015406001e590140c03010f9a0300100306642400390b03090080c00b401000540707100000b0b00a895490b00010f0402c1c06203081e5401c6070b0b40b6103c040c2414410640c803000a0506c0004009540d494002e054010580c252400c4555250078001080045103200c0d062501c0c40106044090003014040081d144580f10b10b0b07054030519501d02110f120f90180241c02c0c88140e00e08040b04000400010b131006904060020b200005d01601c682511940014003200e2034440e4200300030058940d00c003901550342c400c9580100c2c040032000d1807410401e00169140455004030003048240d03454442191000d105400070a6485041d0301d19000c4242d440b440c007406900c00050001401303580301c80511f0440e03000316241500501205506c5420700c0d94400c2a95000881d040f102411642800003050500c0010101a = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 872558264 1250 872557014 872557027
    0x1050105030c070c0b18041b031a0312041509030f06091e050f12070f140705030714091506120705090a1413050c0f0c0705090c1308070b0901030e03 65
    0x3200803213040d0030a00c4201d501240c01d2440c1c0480030310325403801008841c02e0110710200b03411601e4580c401c078420001c1680b11002c2191301d01c1e201d9010980c00101505840c0c5049080c2078403140b5600620075000c141e000c04580f0000207120b5200030041daa80540c10724003401c500e88031140134181900081d505c0b07013400940c0d4140c4101d00c80701614107a1288000d0b040c28012040004d0900781005c1c075180e25030004002a1001603041c4200c210b615034005020085440c2d028802448c00030107410041d0148103a031000f040c59130707603c0f8849500c0001124010790541d0364070442443c00c2c0710a81e041d81c104005000c1e200300501c1030040c46500c481d480c5002070a2680e0b4100043c030b000e5a41e070200324040c2c905c010709a06410200c60300700c1104e880c20018080340c2072150400d02240319800d801c90940e0404640b0901c440d805201c0c200c000c01000b0202c400600302800c05410551141c500104042d4001000044420000ca9048103e0f081c140c403c905140080c00150082c0000701c8510050703000070082c4 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 872559514 1250 872558264 872558273
    0x6050a050d060e09100c020c0d060e0f1005090304050a12060b04230f0f0402010c08040503030a050909090f0c040b19260c030c0d051606020c010306050607080301050105030c07 77
    0x1618001c3c0b114051603807050421a04182c20689240391941c00700b81002480a40941c001501341e0700000d054032220320400480c01c245005104031a00054503000304e00102d208404000b80c100440c00600c3e200304247e485914090342da0344a144038182d0415a00082000070780390b0f004d07884280307034042d10300421112040340000d005c85030100c1181c5100181004c1c7c01410045141c2610344c03100c0c904030483c0d44d0f820700180e068840e1000502c001d0410140001140810011600340d8004200203000c03241c440c00403400203040c41d08000381c580d01480c0058001520001e002032810b60015401003c0d0860900c0b4030280f00103400b40415058000b680002c903d100e8a56a205800050400310150321047c3c4961301c0884002c041e00e00d4000d665405103504030303215a008950100300c03050071644086524860320302207042507081940c0a0388007100c024002003d5801154070f07110028240d030100700700c1b91580c0c10480607010341407002c0c0243c881400148015400b0300021504210056050b80c2002c1880d40c4 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 872560764 1250 872559514 872559521
    0x5070e0d080c010b040b0d0b1803030903070b07321b01150b04180b0d0f03030902100302041802130f030c05010305010b04150f030e0f1e030903060106050a050d 70
    0x100710340030100011144a069402e00c50800411004c46051000319802e10001d80700740405800a024940020003244121040e00050f828107071803142500e4491401d81015902c1c0d800549007527a1158802c40015840c903c075010078070015a40e04540da0203840d281d9100003100074013420505420308104840c1c1d1406c45841268443c464010700041110403e0b0001d1510349160b503440542d180c0801c0c07000340b116040c0c100c540001c03400c42c10400542c0c104000c0006203200204400039003e9006114100141941600321502c498000e50740645043c496130000c038205d108a201d541000c10b800d80c840031440000d03130010b0140b05500001d0400d060307101d07102500341101c264011a50310085042c208890f50709806518014a1360918040c201761609070742c15103036003180c010141000144010383d00142c1c041ea0042e030b42d0031410012102c001d415092038658403100c9000300c0103010008058001c1d0120000200c0b454210007901510044c2d19190090340c40d50055a10704003445014030210000100610 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 872562014 1250 872560764 872560789
    0x2031e1e061006321209010504020108061c170f1201080c010509100e0111030c0c090c0a0c03050d1112071b26120708041a0601020c010305070e 63
    0x207044241000d084a980082881d40060709104816100c10300d140c1003c0021500c0c00c0d950304080941c19000d01080c4400e1158440802051201105024034a00154041da2199100381c8a1110075181c4104211701e0314091080513442030205143e990005494170540040d50a580307003400d0401080140d21660758004e69444c20490040800400100000700051000403500f820302900d08030fa040003040b40c04010b00c0455050001c104000541640309a480e02c0060869a0a9039295418050001c0c0c85840312800e1600c50712821010525000000d8110b038503191403078643d4408040c65540c292260340001c7c854a0006648883c500d455000400041ca41489420500c150790300d029200a494503000f6140140058003826416000454240710703442d0003600345004440c3d03400707040c03982d0809105488110300d82d00120030034040c6650700046403d0081e445038144440c52608002901c0c3c0c02d05046803100c0c0142e000f0b080040055019520403a000300c660f2801d00400500507000c50189400070 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 872563264 1250 872562014 872562073
    0x92d090607021e0d030506030a121e090b0703080601050c0d0c14030315040e0a0c030c1403060705030a0b120a0c0306050106053603060406091e02031e 66
    0x4404011041d50705000d00d0703924100d2001a00580500d2260311551650b402007208185a65000400c511f50b90420004007200c0d88910f80c101c00140070700c002010100030f540001e60450700c880410310b03218015244982515490b04040342080a2a00e04031025100540f901c1d040c0b16081103070040b407250038091016485000e481d101c2c4401150b2030b11818282c0039549118407a001401070043d00359001d10b02e40d0700f59000b29004108030321811050340c00c0c40b154000c02004444608800802c1000042d4124100c440046d001080341c00c1540915403550307000c442e24800500100005607242083c0d82c0002c020020141c09424010440c2c0821440c7c4609600c00756800ca0080070304200304802401818094030181c50a10b0900f062000700c811404107048010615440942c028080c0c0780304c2c65001110020011708071403850a060806200400b4455001d81740380c0c14655616000d4103151262009050340a8010101c0b8905260044080c040c840c600c03000030b0050103101c00300781d41740c40803060551400 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 872564514 1250 872563264 872563273
    0x30f0b0601090e040206032e03030815040b01020d03020d11032502010216030c021f05030108010e06010b0711030f01020c010c02060109180308040318060306170606092d09 75
    0x34000240031000164001c004440e408030070803005840b00d5055076009200c005660f149800d8019010000d14002c50200d101111a940c00105240c1d00102841c041c1c22040a10a402c45810041c0b0080e980459185030250f0310010302000b92a00c0b903402050340003440c19000a1049400062482603070050311002e40d00349100c601e40c00107015011101444869600085244c24500810890340082c110000750602070415040b9055458882288803020700004601070000b0300102d0240036a0000c3c081c0b800c0341d6207822504040605c0004016060f20303102d105542c14503e072a0394940e06100030040300c0d07400d80140c801d0344074240c2003400608002c0c901c2d200041034a0882c0a00203280c03000591005056900b4080040e82000d140140e40034202d80501d4a004650343d070341015240f2404516144018224101c40003503a44d500d640300e1000d560240f41581301b03480c24010110b942d0482943d245500204c508049003000c603441c2c035111540c80c507600d1024850031760940780000b0101300b1036910485420 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 872565764 1250 872564514 872564521
    0x703050307300503011d04230a060f050f0c040807050405091c030c26010b070305070c120c06170105010509280504060807060203030705160822060e060d050c04030f0b 73
    0x24481c001d403d0310504280f601b40501d481c0d2a484800d48803280401008c80b4400d03849150030900348540340d10581c000c8424070042c4a8040c15000801c0111803543c144074140b03022506000108040702e04442090f4020003c036810041008014030029000c0f02d020b21030302180140c0d010010042e6004019039440c00500b030b20100d174001c0c10800c0280001000c0050095050380e02c4100b801c8411b042d1480e1010040e119556442e00756046d100d01c3c0000b40ca000c654180020702500600107007551144101403280809582e250192001c07064506c9407044940804e00500240d40300700040c000540008100c01c5c142c1e100000c00310f2802c0c00c00700e102019002c03076100500a42c1018080c01e80100f0103040103000c401e240443c000c0d140c0c00041c003c0310400100045520748180b00300b030b00704403454002122590b0b50558607424803400d1009000085410000385001135001c1c025146051a5503019200b1440d1036803490b5014000c010003402412a40030911022012840740640c4803101d510400c80900da40c02d = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 872567014 1250 872565764 872565779
    0x3050607170a02040506040b2101030609053309210d0606080402060d0906020f03010b0703090501080105010f0c0501020f040602070e0a1a0405060a090e01020417070305030730050301 80
    0x40d4024807070b030491801040100066110744044034105c403180180c1d55140c6440c2d42c0645401110000c501e040b40c0e83d007000101c10301015600c51341d40740740f01d8802c950f48a042000001d041102c6440d4003403a000e0061041182040000d42541e40b241e040c00590356a0000054446142070b440d03a5812040c44021860030416512441400f01038030725800c009509252a40c00903010388200c504103002c1c00d4844038071310100f000f80d405403070700c40300f15102058681d078580840c41582c0c1c0159009500184400c8170000d400e5004008140c140c41060751034014050640d8800d6800b09150001210f0030765081000c0c03400011460080c1025000300c1c1c1c060802249032400140a081c4040e000c1da54240c9441058984034918103999400800b060303402003084c0d80c955000130901a1194044c8061600300000c12412030019401070050754003040c006a000391000c5410342d620fa03e0350000600d254001c0001c3c0003c00c0d0b54a40c22091000348070040d103d5507608440c001c0100216061003000f007a8080010302129 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 872568264 1250 872567014 872567057
    0x150609190824220303020d050a051e09250f03030203040314030c0a150e01151d0435040f0f170c0f010509060708070606081506010f0903050607 63
    0x20340340b010450603400c0500e01d4100c064030a6541910400c2c450f092541014000d40542c0d00c0c5000202c0c00b04014071717006540b04080e0104039442c0108107441c9031119840c29840ca841030048032040d005126003003035482a02020843d5100074200782c06150030004000507204502c20207540310340d000e961220f165150050030060848010f44241c1c1090004034a140400140001030f1500701220700c83c0b04240402d58401410342250070307815542044220302d100300100101604940c0892403460711090083c400e00110340c000d5900800c41c02e03588803004240456603015400420110100c404050006080d280980c0c1c480d50000316050b075944001c200031803000281500418100301d54510b5215034200194403500c1019149100e82100d0b000013032664811020350380b880c0b00c060a00c2e690340c1140e003002c0701c0940100c2801c0700d440d81840c00201341d401d0082440c488114040061080380d071110401921501440c0112004102c0d0644000021450070800d8500900e4070b42c5031041c1c001d030226402480e0 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 872569514 1250 872568264 872568313
    0x9180b060105280c051515040207030207171501080109030e010f0f110139031413240e0c091902091207031203141506091908 55
    0x41c0541441041500c0110652003a900075000b01e0340f80104216482c141d403402015403010b40710384610294043d8890400101c240268000345c110b0110541842c10841a881035800003001604181d804004595490080c1c00f2580a4001614100c4006080711078825009910402c0ca40c0c2d100c40103282816080380b0455003001c030a29003441c143c5a5000094641020401c1c03420803c4031320340c0e0352424001c0079400408031504031b070900c4070300d400180a40101090000e09400320b0030803110150400300e00030321441c08c500301180365402a640c0e8401e03000003812403505050320100140c03800c0c1810044449400c10000d0b00004000601042c2c2524a82c500010440643c1c00b40158809002d00c2505484200b0320b07110440d080540e95001c084041404041000403c1d002849014000301c10814041100710b250012560108140341c44090104941d100c00c0d21017404005480c00c01240740d0600a00820490001811010715204c0d103000031800a00c5542c002c80e05030304404501c1608601c000b03d80d041 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 872570764 1250 872569514 872569517
    0x110a0b041a0f0408030103110a0f18060905071b0303090b0f0a0b18160903020604030c0e0f0c12060f19260606090613050901050105130c0c110a09180b0601 68
    0x200b6151079070354640c41d8407060001170b1810149102d6049940c1d00c1101880180091402004025a8414800f041d9098000c6001420790030082e000c500c0d01010311030144204490b941e5075040b105220022050000c3d0b10000350100342e150030140d00400c03412480c240c003a0041003005051441c002d803001045907101c0e003060f44202c403448080051081c00ba060143c10000220700071499020400c0300791829126a80025013040000c6400011f002c42d06807044111140c5d03029810007640e4040f52130406520464021464010034000795640480095042d503220788081d0040d019100e1036000540e0113413060420041030142840d00380315110420540030f00325407041c802020350215580540b80c031058000d1845005410712030000308240c1e00d00c071900300402140b0b10100140d0500c000246c2c06800c0900030075003d2080b21404402090300da220f0400282d84640e5403445c0c203a0103584582c9903200c01c03402c0d554004c11103d800305083c0031500c900c211320030b00150a0300800469140114003070b1802800c850 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 872572014 1250 872570764 872570791
    0x130b070302241012050a031124070e090112060c052224090b031302120303010302031b01080f0601030b1305041511040b09190e1b130501110a0b041a 65
    0x4c00241c0014002410b42e034035040910070448000c0046150081c01042d20240d1000c80e00c4200c110941490880d001e00d4003a654410800f00200c00d02044040030303c1000310581d50f1518150110f2016170060b482d0070308903d442840d201c10b10302011074420044446910603105e007207042190300200284051000e01d48240000d0322194610301526403661482030300200140000003510002428030304d899115802050100c0c8044c3c10b202c0d80d0750b650400d0000b05d010303101d601145280351403d14500b040305030f416503c028030b5560b40100c801003000c0241042c0d06041d140c80810000b40d84450000320100c400100019003441c1c942410f1031000403014072401064900383e10788080404d101c01b21015140007424550740c0310b007010b0210743d540801c043c86007405e28080710041740300802c00d034241c2e000304803101c221403400c21803404071401c610a00e50380844a08800d00d00700a254002c610f03501e0107650044c16a40c9005940d2140ca11a1030100c504171003501e0030803000c292812a107142160092043c5100c071 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 872573264 1250 872572014 872572049
    0x40501150305092d1006030c1a070f060207050c100c1b051819090c03031211031803160b0f0907060c02090c0903011a15130b0703022410 60
    0x142d01000c1c0d000b4111481030300c040102010313000401c40040c4c50316071490304120b1243e40e0305202540e558580500c155007582c0451120030602e081c0140d801ca0f40d044405c8011101450347d540d4000e502c5400c04803028046d000701d090060740e0318a2414034185041e01c070480f80e14078a141c018209130715010180f1108800c09003e010765100c030f408409503d000c0d100c0ca02000d4032070381c12408032040c0490704407000e80d04149000041100e51180c1504513442030700c038000401040b5042030b0550740003034061008a42d0500005601c207180f0301000d030038910042e00750307407810020310070030382d10b4004009090f140209505e09000141038070130003070340c0e2000c446009800080c1c14800c00030f11588103600c001c0d114603803050214001086603801c03291803000c024020404280e01511030405100a907035014412041c42e05505d20040c80f401c1180e13884004420b910401074101911000c039a00042010b07811031085842900d10f018010b4100d81c407034000406000c88038a014509060600295040140c0314401d44401 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 872574514 1250 872573264 872573293
    0x7081504030c0302120705010605010f08060f060a0c0b040f12261b0c011505040902060906031302060403030e033309010e0a0606050a05190b090f04050115030509 71
    0x245030308294180b03010440103001d424124982101c0c03d0061009540c001403040400c00c1c150701c080c0407103078282c90b07401e0343c0d00114605584950341211132581140d06040d91000e6451b01ca40100540c0b1040e080c4a000c2d1030050b2151818200d08441c02c40e0b010141481080902980c0003120121000b07034a409880310b0051206407201c584407a070b031601445182d0b0041600b48081c440c05075201055108a951a428104078190103000d4075099001c881100d0304001c40c140c1070078040c204280ba00a03041c249407182038401d001c041d60004100c02803c41f00904650010394074000144019030190741d0384881501508109801c008107034043c9107000c40152100a060080f402c6030602121040c1d01302c645d2076550445280c0900100c062000c0640241c0c07021a0401181e0b50000040c0d42c000e580102d042c0c0d40342c00c24084000040301300561600b09842c030402c69000814000c004803e0040c05154944441750301090652300700ba04404410080d4100c090100707a130500c510b9034410000c0006014120b80b01a4 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 872575764 1250 872574514 872574553
    0x20301060f050c150732040302010c150615020106090203060d1b0305100e0111040501022119050909060409120e19090b1e03061503100501080f0708 65
    0x10715800344000819000b500300c105000c14074449002d2103140d4441c2c074025074001c2420845000040381389040000031841c04a40720102c07040104104101d514090851f00107490702001c440044039140d402010700104d0f0704180c0620350050040030b040d290441d603510070203800c1d140280c10046000340305000700b1405540700078030060b500360080c619952503506100ca411101900350800f0b0a40d1040140015405500354008600251008001c00040c5c020410807580d038800d5100e00c45c0180d0141401c213240c01d040700114107019500003030750780c41c14614843d0511543c6080300d400010840c00300c1c280480c1c0c204515040c1c4e00880489080002152039900d103981c60169130841000c00041c8514440c440d103807907a030407100f890010520b000300c9550f00016000b44c40b80c015102e0203003000c3c0d485c1071500c14a40459002482c0c004000d401c00340c1d11498140a07600e070f03841000b40e1520030001c804038a41e03424480c8a000c0d20006015004403007502c88480d10708000c503406150b15912907580c0b424912030495 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 872577014 1250 872575764 872575787
    0x70309053f0c01020c2a0a0312032004050114030c1801021c02070e010506070b22050613111005120a020904020c0d090f0e040204051008151006080c07121206030b010e0a02030106 78
    0x540f99827656030300114001c000300a07240c1c1c1d04d61040c0300c0b074035140480351020384215902683d41c0590300c0d20f9200c0010090200342e030040040207081c003142d0031203109a40800301d022410301c106d031304040101120342041580701d8540310140c5c200c0d500034401c1e5105d450b10a8050002501c0c000c0c0b400005540301400b08200034580b40015100001d0440781c613100901c00080150448212901c81c00c0400c501000100020011504002c000600588505081d410811040030b16101e050800d03083c41000c110981000308401a016420402d00742c0d280e440d44040c000d019a02c00042000b1410030304040e00860160308125200000c98200b041142c074214422030b449641039030046041d13142c243d10181d880b0100c1d00701003028059070355840c1c000c8a0926165104803132102031601469902d020a03215000143c1d40480e00341020015030700460700180241c154542c6034500428408009502541198016001121444000f4004220646544a00c03503044a0000c070308619552614201038032070941603 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 872578264 1250 872577014 872577023
    0x90c080a09020f10030b131b020a0c03120905130c03061a0d0b0d2103051e041b0f060c02041b0c0314070b070309053f0c01020c2a0a03 59
    0x65a500000c0d84680c2090503032406c00b6001c0c08001c00000b0741c04005d0f10030a0322030034603c80f1003402c0c2402a40700003000c41a0300d0304a4401d040c66400c1d903c400552080c194078000a1000c01100003c458031403612150f088040200c0000b00300d4030121004003a6002648200000000900d4074541420104200c504103076521000180c2c00f01c5103004a10020000b410240c40907881045043c0414000318280c103034055a680c04022507507414180a20f0441c0780081089541e5034240000c0003d505210105d00c002d03000c03110111741945e00c031503602d040003994004600181c0c0c0142600d08606040c010640c0c5400030410600c903000252000404003046501d002c1c5c1082130056a02146008603000c4070748182d0048440c0450b407802c41409009449404403c5455104801521005000006042550416442c0034803204014001c000c448400d0440743c2080c288001c2040c0f0b4a0460244000c04994003820007030b1060081110900c45180e000024000044c3d9000ca11441c0345c1d6510034401050301d901c0b = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 872579514 1250 872578264 872578279
    0x9060d021e0910020a080322020409050606100504080d1407022133060d051009110301050420010e18070f0206070e04110d091406060406081005180601090c080a09020f 73
    0x740150a1030000004c8d130081e4025103469800c000b80540455000d01c213030825185540c1c0c03030a24a004484074492440fa90156800004000e4642840b407140c1c4503545803030051550900101c2d40010f40d030820a00d40c00000080c00701489003440205101c8078400252000840042500c01d09400c02d110341008010127100074500300090196031071031114540b80e9000070403109454681c011030001065448400e0b14039402d410390f01149403405000e0b80340314591000041078800c42d450500d00d250044042e80c20704ac4031100418001507111802508103801c502861040d00c2e0a04070000b07007074012071030044002c64219408000d669038010381142140e090035035001800c10645161040131f0700075455208805800e080c107400600c01800b008140c91603080c019580d06417110001c1004071500d9105241c400c0d00041140e201d1a201507200ca6403120103041d00c80d404000c0e5401203410000242c20100495907600b42c5d0f102c90507886280c26074071100c2690100000149a000101e2a0002e03c001310b114070315 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 872580764 1250 872579514 872579551
    0x20903100b0a0e0c0309070b0406122703090e06030703030c0f02191814070f0c050a0c0b120919080711061306020c0301020f09060d021e0910020a0803 66
    0x100c0035884001804000e001c03403954101403081079a40c0d1300581c0d20500b94407c4a10101d00c03076850008840443d04191210342c0c007036003401c000501502c40c010354011703e0b4034035000c1800800c0e41c0440e005d06152003036036441401401c1c601000f204110241040b0301070341c405241400041e801042880145801641480c44fc0f034940c400108107004140c0082641100084001421021041d400051480c084424000e0201c000340c440920300c0d084a0300700000d014800c0d12048140203142540703031140910280c0b40703106c560340c0359543c05070b00307aa001000d00d180000398142c40d904001c596642044865028108440711159815004940c0500152000c24001036050400c007103038021200c0b218001d0025038942038043e04000c002c180910446003d03024881901c00c1d80d18043c400c0f1803852881009450910030028140703c0c0e1a0060146410850b074200305109040c0c3c00c96034040c601204499285e0b507120805405c1c05042d84c4003450302c000b5903102c519154001403010007944d0340002c001181c01d50926 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 872582014 1250 872580764 872580769
    0x2e052d0105031b131403060405031c0603081912050124020309040903050405101b1707050a061a011106040b090109020a0f03060507080412031509051f050301020903100b 74
    0xe00d00019514010f0000b6484180003001222804562140d0510750303400001c03409158540d14100d40041041e0420007082400e811052441800d2120034803000640b107499a450034000d0740441542c4201d034004107402c50945503c180d240c0e01800005106001c907500d0000a00032441802e180000d005401404005c42e032842001601c4202e00020701c00d000c200c1c1503080180150b4054040c060003100350b4032000301c10b81d0141c61640410348a450000c0041c4074182c0f50f0000d4007400c10420710221804100c01c2021900421600021030b009020000d07280200e00c20503403005281c118654140882101c4580301c070807000c071721306138400d4100e050070b0307002e50303c0c00c0b802401409503440c002d42c8586603000118602e9181c0e02c29006886c03244108100c079445030141511010000c0790018108008001e038100c200b48690820354a641c00c81d002d00501c40c1d29070159505951084a1070010718214a07440b484400801100343c3c014001500214035102a10b4017081e01c448181050700d5402d9100c03001c14410f078 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 872583264 1250 872582014 872582041
    0x209010c060f05011404150b0702032d010b010903082a0a030809370c1203020a0303150f030f0f020409230606182e052d010503 56
    0xa80c0d21041c1007000b1074504100c2c4009010a008131055201c280b0442410f82c103080c4540010a00c90a42c0e10650b903240423240080d5a12800c03040360035001c2c0040031040000040400c0c0741004480343d0b89003601e1040841107003121801c0d150981001541042000440e441c0c404032100d0340f0010404e02d41c0c4c1c0210801d0608480c00d1700d00c40c075189124000c002c100785030f4440c005c0b5000c0d00350b000540341035100141d01681c041d40e42d03108174074965199800500180c040f0b11901c1040381c0c0300d9658401000c0d643d1601c0340d503841c00785c80c0c29009078105c013079140101681480703400000c85000d4002e0800d20706000c0d40740e07140041400000c0c03580344030b81060014843c0b01c6001d011a0f907401801401900641c0c68503440c05180d02d41c2d915402c02a2041001c03125402055080c49600080e0182c0c00e9a00f01d20000020b10002416440c0c404003030440d0004c444441c00c40c200c450200c0341030b0441c44689400c0a019020010b540380b1203c5141100c002c0c00c1c3c1400008410036100346c24609140c580e00c40408a1011 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 872584514 1250 872583264 872583287
    0x120703200f0327060306180414070e0726070f12150806010f03020d0609030c0c0b0a0e040e0705010509130e01050a0c02030913111c0209100f020d03020901 68
    0xa0300c00030407510345840e1010303c04003402103022501608111054103101240c0403d46640754445d80c090045030300315441c10801541b16015501c03404412401544550504e810780d0814403241611804002d880d5400001c107045c1c0c1c41c2c0c1c5c00c468010055081584810241c0054544000c0044120010305203034800c400c940c035030b000600000c00c2880d121a0414002c19440c1c4107229082c000d140000650942040e01d100880303402808150b101c8800d40c0e200c800810a0840803814001307501c10f08408542c1500040c0080c00d400542a40c1c5c4628102d000b80a080d4542420351045060103c9141201008100c400c2125420300380140c950180000090f6401000c06500c1030b018a07140e00d0071080c0710150072207800344011150070443c61401c0a4100d840c3c0c412044080d40008130418000075019460f40608041c0e800e4004050910724031094254005a44d40082210190081542e5070245007010f1048002039860034440b0300308940c010060740b102d40e42541c2a0a160340820601c0c1c80d0390242c99a01d00 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 872585764 1250 872584514 872584543
    0x62408070e060a0201020f18122e0e0a050a06050a0b01140a030e0d02071503060605120702030c010e0a0b100e01141c0602070302070501111002070f02030307120212070320 75
    0x46500d1702e10700c00030341d0490b0480414484c3e403030074200a000420114403008003e04030903400b00d01120784910304401035292074078011260b8bd200c07425401003c0c14090b80d40740c00d210b500901a0b0500a04056090342c901400400e60b4038509007040050340c0e003000c00c4410a114024001c1d07101d030034804c2c098004110f0100d86024500451080c0380c40c0c030f9400303d00002501c0f2948403413060f00240a4088080303448078082c40004c103004009810700d039104412800d81c000c0040c0304480c03920701c038840384509592114400301c06590080b2500002c003c180380000d0340c0001c091001007691850088240195841841440100c00180c0460540c54aa140300a042c1d09480301a40714030b13072036614298000b27600940099005001341a00480c1c558070540550703111000302001442d201c0c0c4905544402540812422150440e9000600d40162410b001800c0c0290040144403428204020060704100080311480d1090404000c1c41000139041910404420208481c58000c80107800125140c012942c12280 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 872587014 1250 872585764 872585767
    0xc04050402190b030a0501080c0d061805010c05091234030b010626012718050616140a203403020d08030613062408070e060a0201020f 59
    0x20f0258120390055000c1ca1180030100016070780c980c880d40c0c40c1d01c0000c0c010303980034003400c0107a070114010307070015005491840000b1501c40340c070399949400c41e0b1014600c0c130301040780400c544443e481c00c602c41000700d5030414003034403601e40036402100405504d13121408124000404103003404030300048000c00340d81e012800407015611540060100907645618034003507810b0702c204e00154020340300b015040360105150713008500d061210750700302e036107015111003421580c07101c044041c2c040e144403812825000d40003070003045c2405102403a110504040c54020700881000c501c80084140c001c90b01411414a0708250700000c2004855003601c03208509006031140d044003100a0b90004200c01078841d52240b0540441d01d08010a070f8541d446210203580591898003480220354003d00840e40200000d2400ca50621594801c20456625410522100d205440010342d40501901f01d42c00e160030509000c400b0746007814000b401ca4201581490041c5004207034010b040303000b5019644000c01e248c80b180d = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 872588264 1250 872587014 872587019
    0x80a0201050a0e010c02060103061a0a0f0801060f1a1e0d060521070308180a0303020c0312070807030e130c030b090c0a0f0f0207090905010c08180c0405040219 70
    0xa01030300c810b480600d00c0e07928040701104403560511030a9807910701a0051701d0280e1841d2201c2004200840900610104110034020103981b8460500003030110000354041c000d0501041608681c9170b50040c0034800f24601042c0206242d440860315142100524503a03174951820003000b040f02e440c128601039140c00b14002c0b00c003aa154001109460041d140e42c401c06900119a05020b4104490322900e03400000042c4086071028000344280b010200d40200100d8503000412400030b4142d0081e00160012002c0120500e4240403c50f00200000049810401c90781c0f10703602c15100c0c05000405000c0c890a180d05207803038141314030486090070301c0104950100254081c010302103581e1040d11955440000580316008581558210301071561210b416002e080026030f655068148003405502c200c134000940d48441e2300440b140c00780b10b60004108500480c40181030702001034209504501c0d4820303403001030200000c0f80009903008a0300403d1a4450740081029200c50b4251940c00e0010f86001 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 872589514 1250 872588264 872588267
    0xd0204030602090f01230c0109050607020703110102010c05091314010f09060b0c0304050d05030d0c09170f0c011218030801050312070c0b0702012f010e0105012d03080a 74
    0x340007550021360781842440351034401118101c6000703010490039410b00a10340042c80120001e488250301200000038607458580320180740070421640480181c0c01060306108002e01d80060300d440030070a00003885403802c0310364040e10b00c0c014440c580b0300920511070642100e00040c5c0110b43e00203034002c420050303035840340303011681c041c0d40c1c0c0180100d180c01c000b0b0018942d940c0c401140c4d012044074014500f400e00344020056070700755902080c0c503907210610060303101d0301442c40340454101642e290a49141c0c6040e2149400b82170b0195840703101c2d00000070001007602c01003500d6404076024070300301880402000210000304000c140c0500d20304010907284c0308058014410030306a0f50210b0840b00c9030709880b8900d01041c0304401c801410800491300c10088142c441014101c680e10505003a403040b42c444038003102c0030350352681c00c0407070145c40303c00c110300b40d0b50030302c1070459007180c05009002640c101040c1410300c2c46d00301f4000007202d20a409075000d106500711048069075003c6039003030f540c1241020 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 872590764 1250 872589514 872589517
    0x912150903041a0f040e1306050a090201140703090911071401090c1205030f1803060a05043806011112030a05010f2601060f2603030f04080a050d0204030602 69
    0x7400c401d01e090359614810f650001096400032180211100c1c6807900702448560741c0c1c0e5001c0c180d03410741c10f01601070400103010b90165921800304200d00180020f22400010700841520b0b055030a044020001c400120360320140350001e56400100c0410b403542c24420755070b024841c00101038031143d40f1203240204820190466103070b142c0200c0c2400601c5807102200d070240200184010f02552081203190041d410580c0502020300702c0c0b100301c010030147c00001c00d0902108039800740d801c82d641c1040004224680d43c00301c0f51295500c00c0950400040011989903600714514004161103050000c0e6007681310b03100d202003594801c0d0a5818001c2c201c0f113000790341c0c0c209407408009142001c0011407912101001e06d81110080301c1c03106040c030310b001505000031400c034284a11554a078000407507011001490030000701035a0414a5043d042e0401c190030081d421603003403245400400c02d01032151007030b500c40758100e9000925581e54828030141521240700b0f0020070100a80040707400000d00030580d0 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 872592014 1250 872590764 872590769
    0x3210403050f07080d08040309030206031807080c01020a0f0804081203100501021903030c090503300307090b030c071703010801150e15030109150b011e05091215090304 74
    0xc6400306040c400010303807200504d003c1c0c082c03c0c0d031141d10001c819503c41d07102c213034115000e810988a40c0303480c0d4020404950040341c0b013410f20101c00300d00c41180300c020484400103111100c007030f001c4c0c5100b10000030740b0b4809020000c5c003070619001c3d41c0f0007801a81011030b001024041c080300c1c4400c120700040c4249800c115052601e512103440e0024565001064100030304d503000b0990003001d0b00d1507a050700200b203c0f1651804000c1c04001c0801c01f618100100c061b02c900c0c4503014288180d9103c154604206542c013410001c98080c4140450f5907000351040007661161405a03490b9038032401c541c000340c01021405440c1c0c0784008815018034803c5801941a540b45c00001c0c000400717841e4404401001c2885103031345028010000903030341402000241e1603900014008204440380741c80d02401c40140485119100e55a050300d42455030300001660200c4040b0403c6c840d1490301000040c1003401001203250040328500407050340340009018500c004c20040015900c2c42c1088113000d80d40e5080350 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 872593264 1250 872592014 872592023
    0x806331509130516230d110706110414240a020f03190905011716120e012a0509150d0507120e0c091303030b060a0e090609040f02010c0203210403 64
    0x40b200390b0145c1e450038031640005403075907120300c1d251502001000a02011004003600c00c030500c0300301d0002e0514020151012000010507032100c1c00d010056210035100d00c01d803842888102040600e400841405244c038103000c02859460313140d100c10580c1071035030340215040d05020000314000c14881e141c0c116100030000d0340d07804040e20348500040d20314082d880100485504568005108001120748020240d045440c00e0640040c41614010644e48031050280307299440301002b0519002c2005078000310031646001115440c445807016010b0f102c0c26070f00d6401904a40401550910080100d91080000070410803162601038402482441c00b443c0403485c1c2c90400c24040ca02e103100080542c0700c204014800b0907261500403010003644800c1c0800c4060640718505d800944e42c0b80c1011704641486070b1242d50103240c0c00310400c0800c840040a29201e01d0b11141071001040040710b84015907542824014900103a600010323192135203c04140c0c01d00d0350174104085e02501d00340042c1c4200c9124 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 872594514 1250 872593264 872593277
    0xc1b01060906091811060c010e014d0702060703020a05010b030c030c0f0a031209171504020409050114010603150504050705120403090806331509130516 67
    0x40d0704140c0256100c01304084421010081e022001c40c40048042095043c01810700e80307407080d00c50843c1e0947d00c1d20451103d8595540c40043c1005034400303005240803112050040d218010071000b582e000041d400e900b00300400d100320191420184500b00e990058009082540360700d01d03444e0084d0b84500640d070450b015400e040f0240703500d0074001014440c05d00000c02403d60700d4006000d0102544892204581c0801e14090000203c3d11103600d82030400c07007544d64003554a0800101020021001040880030340c000072040842d1070038594819001541200c010070540921b041181c050165908916070400c45440001000c0d50141d200c0e44103e808000c42070356042e40c0318100400c44d401181d02c0804034804100c00c1081072000b00310258407034481d00701040c10548400d02c0d60b1400350111440090481d064400c801610303070900540180d203107a540f485100010490100b00c2d00b49011441d2102110f020405860355902d9100c001120038a41104203c186481d6500307511002d290404030021940 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 872595764 1250 872594514 872594519
    0xc040f0b032407030c02100e07080d02030c06011404090c060305070320070212031e1b0f0706050903190818060a1d1c060504030801080304120b0c1b01060906 69
    0x600601a40c40500c403a418a80350f0740e030340c060580260400040800031401381300c2c8412040200d51089403045017044d40106080c07402c008000340343c48003144000040d580301307103c44240a0000039000c0d040d201c0000b0181c440d0803894001c20f024200101c0c1c0281011f8114402081155040d48101e2060300c0c41e683c14046005560072103400c07042c0e01307802302c01c946034204031080160400e0408504001d0640c030469140c40022034281c16011410720061030301101c0043d44988801107850703101c001324401805003502100e0098625030740c1800b441580180140894980025607050101d0801048420490051007000e4a01010300350b00501c00348280022004581c1ea45d42018001e546e440c500710345400190300b05441c0c4007494504840404c50b48040101203084900d40030244100c1d140744640c074007280500380b03841c0250103120160006e60b0a50b00c144010000d0203c0002148003180d0000710003d500d0311034680001d8140b15a8144140f0ba441c030358070701c2c210790105510060864107414807c211554 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 872597014 1250 872595764 872595793
    0x607030e1b06030f060a08070b09010e0126040c09020f030618010e010902030a110c0607110c01021e010b03120a030510030f080a020f1e0f07080703140c040f0b03 71
    0x190740030074550020428000101c0741080307a04c3c01c5400020041c0303402030390303540d5400c0e507443c003000c82d08a0720544401051400752035801c20307942c529559003400d09501c00b080030b4640408400305c0e011405140407400c4049000c2c0b140c4810b01c000507050074241590354202030042c0207115407090707030f1050144880900c4c090800003000c03415416a104407440888a03482d10425901a400140850320f103a5941c015000800241c48001d180d4900b03048050101450034640250100d0141803441140350040c86015507983c1c0d010400501e01e542c0a800c0203052103081d00028010060f03c090740c0e415100b50034100e080c000c0c0841c05040000e4450303030240007940c1c030384540314083d0090744002454180e0340c0030b48000141c070190140001200d9441110042480b280c80c90349007a08201035003d000c212500c4440c0c25150901411107a005918000c1520030b00d4680f1040d500d9a41e44030140400401341032010580c6c80920450070240300040060003443c0d42250038000802e00544087d100e842050345511500 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 872598264 1250 872597014 872597053
    0xa090b01090b15030c040608100b0403060603020414010e0117030702030610080d21090206120f01082a060a140c1c0807210603020402070b1519150903050607030e 71
    0x85c0b00d8210b0b00c505061a106041d100000064004c43c020034a0590104800002d032020f40001c3d4004c11000c94000c0ca5401880708507240f6000a000e07065400006215903035601144504540349147e001d4003a00943c1c210900314043c041e002903140c0143c40511805100e03041081c0c069480c40015207a8400785040c080e61820004500d2071071401c6091013a24008501d0b03401449a9400901201d2900913580d10b028084c110407180001d034800610014004c01c0000c0142035040320801c5880c11041c0d0585800c442e5000e8620381fa0b0380f1901f0002010701e00940300d00c0d284448000c05c0e65101e9282d2000351071058803503030340e1404c01142004203c80015154030410321a40a145103803220841c80600600c02184c0354a560700c1c03903080380d403142c0340000181c48170310040c20204e01417181c1c2c038400c0c03d2900f5003400d0000c60b10340c0d1134030801000c40342802d400c05a1800d80308490340c02c014440c4070014440c098034083c52552000e03296028000400c000d19030150040d403d0300c0c000205490309883c0300c04500854 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 872599514 1250 872598264 872598271
    0x303041d0c2107030f05070c06060602010b03120f0f070f1506180f02041517010812040e0405100504061a060f22080d0903050c01090509040303050a090b01090b1503 72
    0xb812000358800c124541c00600d55908890345103000b007120700d829018001918401e0720110000340312401c005080c04100d1082101134060f5100a000403010310700060b40c2d44a03507a10a0035500c20002d0026010f94024040351400c400c003e2103941c030b80055003802000e0301400d00c1c0035942c0a80a6804003540e841600c144800ea83e0501c22600140000b110640d006007440162001c0040e400c0001103005201d4101c2801d46600955031040394500e0303182000344400041c2e01c40d503140c0e445098408940c00720300069400317841d40d400705048280d0b0346003482850411a10108000daa28080912007800b8060300a00d0100c1b0340300c400440c080c00910288884c2e031264000b10b001400f801c0c0301001d061070170802481a100c0d100d14414414945400146082003054855400030900340e84080003005000d00003081504402d0034000b01d11440c000100f51400c0005200504040c2c1c0c0304c00040700074146c0d030311110942d03801414240740d0b50303103c000b80c00040110080084c4241c0b80341802c01194680b004c00c4030311 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 872600764 1250 872599514 872599537
    0x5071704121e170a1d010504210f0f11010f0e1003060f090e07061115090102160804080f030c031219020c03120108030c0601031704050303041d0c 64
    0x4071003261224140008400e0082e604480302c1002603010403861070201100004190109640350104003024145864140c00312001040014280030981e0300141624104c60103081034401c0d42d50740c0d003a2920f4085030800001c0010480301c0c411001e101d22418602c03103003803140c07002d800c0d00c801c0b220054401da0100111400042c0400b941c07201103080600e16204451818203002c01da4a880700803c20480310740703821840c81c055441c01d0a01114004020b004000c1000b400d010650341e11008003aa00c0780103c024201d90761200c4000b0801d102d109604803801d1051121070065842154600814164458440c01343e02c2d116080d05040030031008002c41d00e004511000035840d10801c1d0031895841d00c0002c207566a07498041d02c042c40c145119000030020f0400c204051a41c49040c00c54440e500d0006070807005d0aa0310920600202d901c0000d00c0d207064a812407803108400040320748070170091080c0d4010541500001c10300140500800c0081d80b03401114031607449082e943c000d40c000f03140c0078030801800c = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 872602014 1250 872600764 872600789
    0x30c020c03060c18060c03030906011a070803100b0c010b120318100e10030e011401050102031c020d0f0e060a0219080718030f050616020705041806090305071704 71
    0x31100c3e1010300041c00e140c03c0320f601080c8044082c200103400b540041199200b541c00c00420007180d440140681409451481a04844602c94410032819809509001091b003d0001301180a1001d000c00e103400414061804d1651a0020846a030292401042c818081c094120807049041c4000c0181e40c01d00101401003041d82400070308212031842c000d0329800034015403e024910380e07294221585c440c10101d0b00d0104440c1c110f03682060840b004543c1c109009546003006200581c2c2c080111034500c14003d602115011200d440d6400070b2081c0412040704a14040900071150995080030303552142150941d0740390350310f40c407002050b440340b01001c2d4050f000304042400b5150007000e05641108591416108618406400409000580c0c1003500c11490080c800c20400608200ca2984036455200003000c03540b2404020b0340e505000c0c0036540c400c61b20340c2100a02d240780c0015541129411003024480103041d41809019031b409108107454510b01c0502480e00025010102c60440d4608201c01 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 872603264 1250 872602014 872602021
    0x3050730090801020306100e1329060703210621030e04090c03030c0501020d060b18040b0616050a020d110310180f1b0609060e1c08030403210507030c020c0306 70
    0x44a81907008c0b004503610801c0c8485400c038401d80c91081e007125100b1109100b05a030700400c130b02240b001e4a504810305c100b50401c819070010790f20004044411203404062400f1003007080045016011301d0700300b200311031710b1800010520020a001d0b06191402a12542820301000080c4810340307940c070b0005800240c140b10100002840340302c050700d415002d48001801c0050100070391080d02c0075035208031459040071900f80301c5d082200c1001e004d031205c11035042160003411401b00b41c1d50301800f200141014000d8035400309004050110b600c50640c000c01c0b102d005402c2e8944089190030010340300e402449422225030b8901000d00c40c40c3e10348461041241104480e55030303102d6100c10900382c01c840c3c000291703248681d81d485540000010784681d4440130354160401000a002c007031010403040c8130314060742c3d51510035003000d20300d103001ba07030030102c11a80d03980d480c242030365035104420b020380420502100b02c02c4501c145074011405481c0940d418851011700b440304903516581480c20550580010011 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 872604514 1250 872603264 872603267
    0xc0e0d0b060d030908030705152a0c07080a05100e0f150a0b031912030b0603011a0712081e010e06240708031e04030206040305073009080102030610 65
    0xb0440242c8245414001d4035200d011090440c1c104000446030f6a0001071000c030454034848029501042c030a03988140d9031154055074200c4480c6209205405400080031036101100b4046d07980a04002030441d41b684044d8034286607185d00011050380001d1904110800441c400304042d945001c044009003803943c9561316a40b80024050000c00030250b4452201c2101e0300d00340030000703682002c1c1400f02e001122904003110201c0f590940788040510340b0040c1c0c07540d55561030607603041d1070350707808000742082080440007160f22032020003801d01400403001641003544000920701c00e4080c0c0442c1032920400200f08440c655080c014440f140780810001003403800d00c04110440d2560900440d00c43c100d88061008043d07004c000c064a1100000081001050000392000407042001c1034805007440e15480c0251180c0d40940010700300200000d00c002840104440c0c1c1244401039022500500c841500ba00500b0f032075102818040707a810382d030016858006100f17992044001415410031121078110 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 872605764 1250 872604514 872604529
    0x130506010207050d0b0405010608030a200c04061214010207020a06081005041b03051308030105060304080408070e04062f0c100e2109060a0503091f0c0e0d0b06 70
    0x285411482001000602603079120a000d04450141c01c869099080c141421803d4030016080240a68020450390414a43c840080181d1486031444202041c1307055201d107040c2165000100c0e8400d0034100702084c80480340341d000d400288110030300d08045d000c00308a0b0f802c0c2e020b0680041c0d8440a40a810811680a540302c17541c041000c81c007004405803500c0008045900c002c00090840d40415074100300700c1d400d84241d0750481c4030101401036500013a941c2283d6072005000e0741e402040044042000c0081102c266000303040500152441e85440d840d51120f956822181030340c0c40340c2005041d0180c058810320802c030b105185003a5001035002b0170341e0700082d580094407101c03007803185032100201d0240d94810401034100360000340c0181c00000703649940741d289445101006400800004c10540c0d240c104841c2070403544d081040c0c6a4ae900580d5070b041102d000940102d4414a101c1d49a0000b49903025100d10489511425903c08980c018441154119100180450900000f28405242c80007 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 872607014 1250 872605764 872605771
    0xa0809060304150e0c0f090c04290f0a08010608040f02042d0902030706140a0c1a090705211f02130e0109050a050606070f080f0412060f09021305 64
    0x1c10111900440526507000c90301c04804c41c19560f0088190700c3c3c2c551500500c030301c0e60910116040181410a02014140c0b8412403013400302084c160140032481c5c00392590121300903000c0c0b403c41d40d103410341c200c004d51069004084010001d1f200d0400841c500b0300845c41e06010710b03048040c201000703203168280802070212a85035240c807594080c040c40718148034400d403440300303a96a80104100c220380c81418030b8240160410014005911000d0304424000d1040e41d410503010b02d408000071600d400c4c0f021a9607000346100e5500d60783d02d4100802414001030070804c0340c4054480e0018019007440791a43c1d203200f49050b0910307410001c00348540c883c6100e8444069101c5410041c9041e216462100461006600407401081200d0040100031030910580b944003070400b074103100c18078000c40010b140c1d01c1100802480e80c0310341001901440003820540c2c2c43c2900c00c0b01d03516074680c1c6030b0390510858103c815080312810304140000794041c0b01d500601c150142d01a1602203a081d440340f200005e440002c = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 872608264 1250 872607014 872607023
    0xb06040207033e071706060d03031e02040b091e1509181e090105010609060c030915180902121308090405310201050301052106040503090a080a0809060304 68
    0x5062114465000c1c1940a03903842d8001c00400340949001030350b01064201e50360351417945c0c0103001000313155290400214a00307a4076290003e00c80c40448100802e00b0443c2107031300000d52011030f01081c0d0410050040110200c00c880d58170340c0b581c42c00145001081c4032040d4640110443c404001c81c1c40c200030250404540017803c55950390003c0b0704d4980c0c800710440f60001c2002411424200303031062800065085000f01c40244030b158107005000c0e008005500c0303210200407400702c440c4141f510880084014022000d45025001215038000f403c085486105030380c8001c1c0b4400000345940701303100f1600d88420003044001d95030780e440e43c60403e03402d42000036550b0040400580c12103950b07502c41d00d4071511307042400d51480c0c02d04030030020000115031b44e030080e00c0b480400c00038090b030b8004054071304440085403074113005829203100701c00c92040e070b0052200c144503040c1440100030000c0301a240d88072060360b11030502513840424540d40d200d0307110064401305c02004150340c0c0707080241c011030340107004 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 872609514 1250 872608264 872608337
    0x21c02010209062809030210050307120e071703070b2701050a0501210201080417070507030c0501021c140a111501180b03030906210709030b0604020703 67
    0x10b41d000c030f4125400516008a108240302d252404444c07100a80c2d0006015850601c0c029070079540071a0300c2d4100f6408090034000048000340000f0322484040302c000c6c0620704d0601c001d2032407007499940c0340c225010380c9140d129540003030f409412001041d50000f0303400c20000e00d42c41e00c0384c0184600c028110202500340040d02c40500301010001d008280c01045001d0000500350b24202100282c0220080521050305c1404003c4000d40e9000706a90342103178006a04c00d801d02000c0020120611038844010005c1c09500400014480e45503601812100f081e0203a0b1407034101e03119200c030501c10411a050116800b01c5941c60100c00d0100586900206400c0c41060603001c1f4001d0b0303180c615a4920301e40d0380f0508500501410000c00303002c0514081030841485980034000009840c5d01500030702e18000e9102050070b80b42c0b60803052003004190800b00c8643d4044c1466400148644144c0c0015201600d042d008103180e03052600c215010b80f6050b079902c1070720180d03560142108105051609848014 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 872610764 1250 872609514 872609527
    0x15131502070803070b01080601050406080c15091509040b0901061b150609050403110102030606041211061c050f15061c050106021b300106030f031101051303021c020102 74
    0x1410401013181c54000d9140101302c1d80362503101403400505810590085044c540b0800c2010b1000a4403100503108032040c450720f00c1c480c2e00020050041100d4250301c0407880003038840410542b4010940301c0e0040c0e90600608846000384214000284580350000704201c68818030b1a09a81514050724130459840144940c1c40c0d401d202070b0b80c0587c200c0c02e00c0caa41d80c801d0108054001051403114005040250705610f0503100041150007640708942551581c034004600b00130107031035510301000008140c03645a85410031000c800c1ca4460b405012498900004596840181c0388428440c3c2c44542140e400b00c1505801d120b019046210054002203005002d5072440d43c0274052280030340803503070042013061811407204000214480c1094012104812406072404040c07031183c03026600070141c0e11801c00703816450790040502e948081d0014040c5400ca07810940e110312001114226a0300901131601e0384a100c03442c074500c041008000d40e121442a40e0350211b48244549040c5050000505190 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 872612014 1250 872610764 872610779
    0xd05010f06090c18030b0a02090111030a02010902091e04060b032a130203060901030201180306020d05010f0b0306030604140a05060c0c061617060f1305061513150207 73
    0x10349030b421041980d611500403081c1158001241800458850210f130465072039602c0d2410108809400001440d400080011a69014449621051210500b2240d40d0709240754024001c002c0c001c003c80c4909944004161410022080f480404143d54140d080a03101ea582d02802400c1100856826024200500010070411400c400288040329401c07141d00341540c041242d1440c4206185000034414000e1092640355411501c1c1920b80c20b0030900200c3c140307a000400b120700e10b98002440107000042c415202011900144d0484600b115148603003030719401034102d1800b04551054142d130010b400500424403440c480f0804280d018103660b100030064a13038030f0030320b40122400d0002d00c00024100c50685e0b400c01056510404095140c042154580700042c800540032186003940790030040800d1541ea10441c20b09140080201400d010408034000480584000c580f00d5114402c8003042030040003d00c001c0f11101444400440e24160400c400030086d40c0408a05138214403800c400802c100 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 872613264 1250 872612014 872612021
    0xa050d02131503050105041107030206010e0a0207050706180b2502060c0d0203130509010e010e15060703030b030705040605060904110d0c08010e100b0711130606260105030c0d05010f 80
    0x142c41955000c18598140004d1000707551911105801c010f00400000c07020980c041001410740f044000c0c941c81546415001c01c000c0c1c01646005040e42c080e10f000002d0701904107003248510501c604a511106a07107805071070301070051a000c0d40e000119078070186001c000c4c00c01c4100240c0d10040c51242041060b1180e03600d0094440406409a070001540d0b148014a440e001c1c0c3c000c0c0b60803202c1107400d60410131140c152400601c29400e001210001080412002c480380f80582c0c1000ba0511303464005505000340581140500c0354002d004a000228403801c05005410035180064040c91a04040e09d040c0130003020040d05241c2001c1051001c4986102c9a001d400041e00c15941c6041031541040348d80c140011001c2d045106120525030200701c0c03140c014094481c407607008441c00031310320707038030b01c04213508070785140d51880144c2c0741c14004185a608500c20303429a1055040d101e032004504007120400e20028001c2583c99480b0800b040c210f80b40101284e03080b80c0c42600082088407642c0851420b5 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 872614514 1250 872613264 872613299
    0x2120313062009041b0207060c26070210030606140a03061a070c08030309100b0d02090705030907061b0b0c04180903030e1902100c050f011508030a050d0213 69
    0x8600000440c2c0c9058034017801030030440c0b4980c0440c1c11410b00c180901940d1080c541c41b6000070b10000d8240503052002104505609c01254148061184410864104a0b074082c140480c4291046110094014070a1280b4030988013151192442c03070510520717800564000d5200142010344955003c51902443d51000080102808100751140010301d4003a62010a80e0400302043c1c0c03050041141a1900154030803854604450019950100e08081200a140d924019401552100900c07041c0e50344080254420250b4800361104692141000c542498081c0c5d181402c0d48085060900441c101b1001c140c0c00441e1101041e1500ea9904000c40300342c11001060814241d469512405268140c06004401181c0b040036149031242400312070407882c02c03c4c1020780070b10100007100c03c6442c02054400c100d01d40101c00c480001055110a9019000e0000c901d881e1004510000076489000429941d140f00c45403201400e0001c00f00c40c46009400c11010701c2d0701d201e1500c50001c1c180c0b1884034681072 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 872615764 1250 872614514 872614571
    0x8070b030403021203042006090d0f03110f060103060f021c0e1915090c050616110f06122a0a1701140607020d06020412050601060212031306 62
    0x100c0346040c0c18040e003040100e04544602010070000c00000440001d0080d10380e090034440c0880da494240045604c50040c0f06403940c00c841c01001c40c0c0103001064160100e0b82d442a0784a0702080c212808181c4c0743c8030a045007080b950720400040c0001402a04951040c420020006080c540702d51100c0c01e204d801c1d0407640d5403c4d5030740d1401c62200501804060409224100014000605584d036485441d04a0b51040120b560300d0b015242000300d000b2500c002480c0044c107458031341c40d0280140380c6900c0740380d400301e0713072099000d480303411600303041c001307120814801440030b41803840c1c6181400890340001d100f950654559850b0034410070416a01100d082600d541d013039203680d000b10002d000145005421600d8103e41001080710300810f85000d2005001583d469840e1001c1c1c1c80070912000018900500706800842d001c2101180c032485400001d009104851a40c4da036000d05a844042400440851a008100041c02d041402005600303c510134180050044c20401c00c070300740c0603503905000c00b = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 872617014 1250 872615764 872615767
    0x60e2109130c051e040b040b0703090b0417280308101a030a180809040e150916060512010504180c090203070e0f0916050c07060804030305070503090d081008070b 71
    0x2c44070014801c00c100c2900000c0c00117103000d04200c0c45020b640075511441202060010b071060400d44260f003840000d00c81416200d8840341c80f5100041943d6200e4401c4400f44504a001c820780c2207401214040d81c14243d070301055180300303a1002c41c3c40090082c9030319426006814000b5080740d0001c0305081d0384022100250320ba080070042d41d808c0d6403d0003e190f014420f6044100041601101110039040c411503002500ba0700e20719045043c2001800508411510001003281c1003c5c0400ea100c0081186400000030350341b40c050540b290f004008400b010f03090724200500c0941450f40c040d440304131202d944840c103111190354110364a03019401101085401005010b000c5030803000850b07203200c04498189441a141e00481d07a001c100a01603524111140000744540b806001120707240003600c416280080d0311100040c01602041d28101e000910b0000025122841041507a0207580b210024006031240880100c604850103051810714020040000441460410420f4001c0c8010511a07 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 872618264 1250 872617014 872617027
    0x8041205190f140a02030c04200d0209041104031a04030c06020c0f010e070605120c09120703150e03090d02011107120c1e1e150309060e2109130c05 65
    0x1003803901007082c010f8400e03800903084d03000607900410514140e4005840005540c1e884080d12880a942c000c205007502d00000b84a501280140d0010700e41d00009035014484401c0e0180807a5891055220203403005504081c07100c007405101080301c2d0028000e1501004005403a140d0358102ea2010b4205c407526440601c0001d140078007802000d001d0030602e4050800103182030005460ba1245080d0b440f4070030720700d400144004c2c5070070b03041c0c62050102030617842506140e4100e544c2c0d0f50306180002d480240c03100d24560700381403960180115400801c4069030410f091403051141c40e4003d1007040741444500041d60441b01000c111900040c00b1604400e82d01c050303e1b0902000c15044c0f07420001034180707030b0304d52840031a81c7d40c0240c2d000c8503d2207103c580064040c021000022401d0303003160071280a104000b0074040d07455081180c4250050f601044020a100c000a5541ea010b8070001110300200a40803170362040e02c005019004000781072000c1b240104950081298141c10150300490000f1511 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 872619514 1250 872618264 872618273
    0x1b030207150507350c0309010e07050604031509060f0218040e15091603111201060501080601030f0b030a14190c1809050609011d010908041205190f 65
    0x82694080040401a40c10720400007408440742c01960044d07003c2c1c14081c00f82d9288084401003050007002007561440c1407100d4618a1980299801200e0b50f0900185901c5003502084107412648010700030f51500b460360740d030700314059200200c03100d500380d5455204d4003280301401a803062113856580180d403a80ca07007683c03800002030304c40c8281c012890f0014042c3c001000180c4d071b1103c2e0400c0d80102e12282c0d2002070f111301d0001c0d0244150020140c0d4080003042040c072200900700e030f0408592903101c2d844400d07481800c032800ca12804d40007841c1c0e81e0204130154001d0344030110042000102044c0d41c0e030709002003071030a0742d4043c040355000040825140c5084c000e002a400b5224503400901c101c0d00152a502e0751401d550181d4813000c6103060a20003518070340e5000c500b43c40e900005272022407500c100d131140200b01584035078010900c44025400d044006220303600116602180c02c604050400d0911312095006100413607840c0710300d0724034042003040c511000018501c203081250030118075240c0f = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 872620764 1250 872619514 872619533
    0x60106090f051e13150b031b03061c08090a0608070207030311030c1f110f1c0b04090605060312130b0702040605031204210b0417190507050105090606100509041b030207 74
    0x9201c00000d0050010f09023480004261450075248265180c0c1c480b113002894043c85d41c10030200802003141d030b05003040600f80280c804e0130000c0b65000b040607030304c20058681c01012501000160095403080c00024020f081d5000c0340c0e4000780440307040108000d62189444072140c80718848021880c021403612500e030107101e444a61500a403404c0c024042c405002d079000394089011440d426603884500c2560682c00b071515104004c006104410b402e040150040106964660103406540242c42c0074021610440b880c1c032488c00840c9030010b18101d01c200c56504030203070403644252107800020f49543c0400c01303900b0214021040d1035449213060030415005845c080c0f0400a89941101100450a80220680d0240d0880c8421170b44802d01914940203104484158661700300014416918030761007009040308a00c548000c000703a0715140d001c196a075408a9040b81c3c006002c0c44014200c130310480c05408503039405000442c03075005080128103405012a01100000d601041d40001e0114078003 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 872622014 1250 872620764 872620769
    0x1050901061a070512190e011b170d0507050d060915052e02030711030102030603251d04030e0a05010509010c05070e0c0c060106090f051e1315 63
    0x8100281c5440d960075030000b0000b0300e05052620100b5080c0602c0f00c14082d5440101c50000c0c09a6201040e00315038843c150400503480020300201118003035940220030103070b904000d03c4c18402003035903140d654030710148054102c0c086200c030a1200900014075801154050a29070311000c0d1a0303240342c0d10702c0c02251060741c0540001814060020305200d105e00c01003065400c1551408040c00010308001c0022040286840c01c07c03880040400b0010340c04400f5004541c41089440303a5a8280800c05080c3e0106540c040d40c5a0804000340156002490b000e510402e0029800000c05035501042c100142003050142a060b4501e070405c020141c0c000388030f1030342d0b48040769600f64460410300024024056140c850f4140008012800148001004000024505005614003624040303c4010103500002118215032150070000700d06140240c1084080e41c04070000e071765035585043c0401003100c040458a03100190181c54110042e150391618080150f100340c0b0116204220505551240c3c50a5 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 872623264 1250 872622014 872622031
    0x1080f06010506030f07031515030b01111203130f11180708070e0a12081e07050d0e06070b07020f0f010c1b06020c03032508330a0e090105 61
    0x30001070219640380400c0d00d0300080f002d00640510398442000794010302e40b160964070303a6820f024001a015401c02c4140c111003600b82c1e400d0007400c41f04c1c4019214001d4905022440e6040120030326125803c00d4055580a10f0300d10340c01c00908010f403500260708003507481c16036031400051084e42d4070303003406482c8035a1a49000c1040304079140480e00104005ca002d03125030300b0032102054049895031154800c0c80540305c015034003e03020b04603140105e0903a02ca5410401020200c0d20100d00112041050f04c0c100364114000d01100300610700121a84c102c100e945642c0440c06103c80070204007100f641503c2042550020205169242c401a107040291100b5981c1607040c2622281c0143d4449000c0100e4820381c150051031800d01d281c0366001c0d000b084060002c520021017042041c02038860410503c0010305411490700d0f483e000304444504013155000c5000d940828030b4031aa80d6605080e440d00c0400c41160784000c213450000a00801103503110a41c490445000c2c428103260030f101d02600036011 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 872624514 1250 872623264 872623273
    0xa020a08130e070f0518060d0c1d0406030215030c0732030405030d0509030f192109140f0306012d05030a030c050c0a061e0f091503021c0501080f 64
    0x4c002c0d00034a984100c0c003403184440310000703103c490b5480308000e4442c07a140e251018400c180c10440010120809186c85985004401540b0715039070400c0c5c451002500d801900c2c030f1084403851001b038261503001801020300078104020175401700d029001ca0b5402c07244040c0c00300c011303030042c403c40c00748000661413200241d4000700402c11060381c1c0020310160800003030420946920100001900f801c004400b656041d005030410f101138400351805008034076200360320412001446407010021010a0400e075800300b5401078060243c401c4403610402c000c8802000279003001201404203081140a0f44851144289a4048082400e205003801050800c01d086c50125030b25001c0020307641d60b014000a000e1060811901061080911841d485240081d0841c80001c0d40c0302c02c01002c1004801c1c0c04401030000c1c800f4125540d209107070604c0e060116a40da0111581001c140c10188425a02110700340b550030080e40d28034100400a441c12552880340c00681589495a0503044c804041c5c03105140b90003 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 872625764 1250 872624514 872624537
    0xe01090b090c09040b060706090c05030d020102180906121005060f0618150d0603051f0e070b1305030601180e1f02070c051305040312021c020a020a08130e07 69
    0x1200503102030280444020408005d82404240240306200b0064051810324040009026100c0f040d28202c131400d404681041440e0b0030704a08074080d69803610102c0e071401541c04520300d0034010203a0030000082401007000e800700509450201103090310740d202600c85040009900e400102c1115004064460301e10744000d8460a403281417481020034491891110091001c003a94001e03038258250000c000c00403282c407410400c0c0d0322103000c081c42d41c54544070f0a2080b0507940b240590501001d5010050030790390f0078000051003d400284d40403041701c2034008001030b5542e00b003000600a041ca81115403a101101503000d05544a010032850598403e000d02d0380300c981d0b180d00c442c0616040910040e12030f011850140740f02825684030b00d601c800b504025034100c003803940c04680220f01c65101c040e220140280301c40f050307004440041160b4001a280482d81c0841078004244800075032050390108003007562540c0c02030b04040c1c840c11303c041e0b54840a0148070130303000c0b0f41500110f4904005903a0341c03 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 872627014 1250 872625764 872625781
    0xc0607020609212b020d0510031212020d06090501080d080709031119090b10260910020a1e05090603190603080307020309032503080a090803040e01090b09 68
    0x10700101110070041c00005100410b80d050641004400a0318801a000134840c00e0050380a5005054401621032400000ca0904d00001d0741c000c0490b640300041c000c0345107900d03005a543d000ba414148103425020030580480c03040611440c8041c00e0142c900040c1941401041031904680c1c4a40c442408140400c0c40b11a0b0340040129003185e5108400c40c0040c400500814000b807004000c1c40105030700d2002c0441c400364142c00c07080800005441c42d814000850720116014051580304032907250859000c82ca000d50190300c4a0391142c407201c100d4500b031100c0c0f03c9000403071380980a081c001840b445801c01c000e003645025015a4950707880c00508142c00c44c400119140b0000e04989a0809002c080d421411925001720b401140c10194654481c030303055901075242c0e8001c6400d14800d0141c000e0000e811940340ca00c0d042c556450400002c030309030131540d0b110f58590104007443d09000d2803850008070408c0410090020f4076912117148019450321070201c00340e4aa040d2550f00c10551802080403e0 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 872628264 1250 872627014 872627053
    0x905031603260610050c01110318011517030702091501120608070902070312050a021809160f020718230403140d02040b030f04030206090307030c0303050601140c0607020609 76
    0x11113aa407410b540416080e070701481840c9081005500704040d80065010350405580708400c28070307074100c0828a405241d0700700d6000040014204c400340d0010b000100700039000c070035100307494006c4920b081101d8001848560040360b40003404161140300b0403555a0040410000980d240c0c018442c16007090b0641d42c4494407030081107000d6601280b100181440b03200015084c3d51000005c00c01400c01401d480065440510100c04100080060051509290003618070800f00c89c1c00702d1001401c2c020040303c80402803a080c1003148502c0d00045524810241142c181807058100040d0030096036404050403411108013410801c0d510b01017201103a0807007140c160311940ca0009503030321540d107080000240a16006040c6003034010081264104004484c280a01e0003a000c03103203180c2c1c0c1d17850650750b00c0c482d13080000c00003030561800b000000d020390005a0000d5050401c8051031096184c200e182c0e42220344004440d60161301800a1560140102a0080050809050210541d03064000034 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 872629514 1250 872628264 872628271
    0xe0d050c090a0207150603260f030a11180102060f04050c012102040b180d020604030602070807080c0c0f0603010b1b0c0409051c0305060f06090301090503160326 71
    0x1085000000750181c0c02c1541102c2100303a00c000300017524242c441e0400000c01c0a400200c0d081e0382020905a810041e0340305500b08a06504400d61804c05095403103e180d0300090102510140c1311420702511158501c0500740900741035500b101964042e400080c548000601900500040b030b005102c04120003083c0454501020b0822034001c03964034000400701c00134141da03800c07000c0c404103020443c05c1d5407000a025402c4a580c10506000b040340070021502c400c020000d5018004100400005206030081c0800c036004102e00341c14107206071200075440c1d0041c04a000150086143c0c0ca01610b400320102d0106030051314054210b40c100781d1180000d10580d48050150300b940500800500340402007030800c1ca41c09072060104609502e89166180800ba00311105141c201c80c800058034400d109143c816079000b0000120101c04809002260f0302c8120000d805540b00c0000c82c0110304100700500981501910052180910342070060440e50520012050441c1071580003040e6606a00b00c0c0e80c0 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 872630764 1250 872629514 872629519
    0x40309091a21070b092b020603010303030f0e0105161d0307030302210c0c010c050a0f110f060c060f0c040e09010f05070e1005030712020d0c0e0d050c 66
    0x22100440390070440c000805603940c40d0b20202000003280c44082c9481040b0400804104940da010740740e100f090103038050401400e0f080300542d00c0b0b007003003000007001601803044102807040c43c2e000c003034010a6007a03200741c205502080e19032401e078810290030312500c2144080c04008020908107400c403031880380c1c00512810200024a403052010013920746407113030070000041c101c49950b03603285006511003010314806861115070841c1246188510411107050040740000740100054150040d1030045032414152400c2c41000c10240002e50482900d10a03d4021310101025005c50410417000142030f42405000e0f0100340211aa0030f0800a8900e030440d15100e06600965600b402c071019500139640503d07811180501072080c40e1a06511890790300c468500207020658a030501903524000016440b500a201c070014900c5051040003d5900f044451400c508415410509042a43c00410a42c480b6540e10003846555580040c01074040b0384080d06c1d0384001101c281c440f41e44490301d01009a0 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 872632014 1250 872630764 872630771
    0xf090a0501020613020f0415091b020a0b070f0e1207090608010209011209051c08010e070503090d080a0f020706240e0a090503090d05010b122e06033804030909 70
    0x14280c5e1384c80c1c00111030142c0304c000d407500c241d90780c089e2003018024025441042d2264050700307070021840403a50003452908200c0070600c0d9202c4c40000c481c0544808014403c010400021403090703540c02510310981c0c4044030043c1121410a5103a2040300c085a200c4101c1341e00c10460b0039940e0360048908000d103140b8100c002808211418014149588110480480146000d45064646e044880c15050f94044c08003070b4040d680340d90b000d030341c81d02c81651140c2d071940c01009501e101b14403440f400b03640051201c0d00400d220410080100c20fa80000308121038050302e03110204c04516a40d90300a110440b030103590702075280342c4210100c030014003070400080c03561980654000c2c0310040040b10360008000c2c041544803811402c000e40240350118060348110300e40c02803d0b03500325002480b0441881c038411642020640524401d5403d07034040d95000d02192250000000714240c020032400fa00780c0410003140d0180f442c0240d0503001c628801d04c0701e6440c860000c1c0310100c1c1c0e00110366000c1e00d80196001 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 872633264 1250 872632014 872632039
    0xe250207031b0f1221050d0b0a0816091b17040809130605040c110615010c05010f0b030d0c03020601120f0c080706031514150f0f090a050102061302 65
    0x6114141c681d00900c0c440010980b0009518585648036a0340c517000b1840d00c0031044000070340385400c0020002d0180081c100b40b15203001034815512048141c00700410a801d0a41d5805e0218200640d0101860005c0c1205004100116144c0105c91102400d41c1000114000c00c180240002c1d545080203e0803000c1040014204266042114a00c0c68001c1c498038dc00b83c55000b40c903018103982d0207010b000381d06058003411103d00409400c0620585a0b0152205540701201c141401004140c00c6c2d04010f240301d400390106000784156909580b9070309012410b4103205052614014401c3c0741c42c0100030101ca0032801082c2d0106600b41940c01d41c1c11910000074450420a803101750142c0c0262030746507a001c0004503d540010365601315151a01c00340040300000075400c18443c001d04c103010404031010f2410400b0320340001110b50030703180c5a06050030040b960524142a420003040301d4410f50340007406200d1441c108015600801c004d200904692030501c44e100041305a10074000e004512117402c4 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 872634514 1250 872633264 872633303
    0x1b0e0703020906120103053f0714010f06050a08010b014b0801120b010308161208100b130b07170c011a0a0303020c0114160f021201020304051207050a0605010e25020703 74
    0xac28a2080c4130000780003201040c0d540a00400b1544a814822031100000103000341d0180115114000705854008032640600004111017501d95400c80ca110340300b0b43c0c8014400120903900d410b1400c1ca9103190740d0f0a090071009810b02c41c06070000c54041e04010703429800a1600c5618606495004803d5601e0f18180704818040700c00b0130700020b0031a01c0c01001510104d6005100d02d03c41e03010b503c086c4014958680205129100b211940c0004080c4600b0500c1603d020360f0051500902c903185845503c41c800da65105030fa08146005509651982514803803030343c0307045400701034131002c850441c01c05107541d03800396440e1307028600b9505000c804034600b07e0811071001600c520140001d6015540344e194940000d11a03012202240b04102a000038030390190144241d07841954800002c00d4001c0507031401c2482500001e1302101c0b18403400d803803a0b0001c0c00d1805500c0c02064003001c28030542c01c11011580220310b14243c00042c1c1c02034904480c3c0126030003c1d0090440340c2007600d0380b40010380001c0 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 872635764 1250 872634514 872634533
    0x51b031023010605030403031b0507020411130f0603050105041e091104050108030406020142050310060512011a010e0402190c1b0e0703020906120103053f07 69
    0x1da8031101c00c450000003034410307080340056125034400d50b010080b00c100b0761140042941699030143c0091070a001400050400d503111510401c00441d5450620940d10040c03800039449400411025008a0301006400e8040c0503890140104075400d0095031819200c4400c0021110b592000c0f0b1a255070800c030030711000401a40c005038000c0c4c800d00082da101c4403429a294044c1c400c50380190710700801404c0703140c964031481555002c954502200030525101500c3c028243d00c07550b01607160303008000030b4640d800b00280105890078580105100303240c4820880300304422240080c4503410600981030b0f030724910060203065442424012a16120300b40420024014000c24160040c2034005007944203810600f00000903100b980314010000030300d105402c0e2140340784202c554002c07644010540b003070b0090f0090305405601402003401c1c907141c492500410700081c0d00949841c0c0141c4504c1c0c446820755104405840d1102e41c100121880c2520b18000010080b10484034601c0d0120307d41c3c041011401 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 872637014 1250 872635764 872635811
    0x108070c17030a020712020f2b0e01020f0a030f0f0e031c030b120a0b101503020714010203161b0c1202030c031506010206010f2409050307030609051b0310 68
    0x70003040146c04e514030040e5480a80c1780018072103100e4441007180c2002c4a40d254120122540902843c40303519480903218075100607290750540c00b0701c5040500c612810041c2d0000a40030766580c2c0d180b8840301c03030b000d4040003412481004004c0c0780d809d480717076640f40010380341d8412000b078022400b4041320100803001048900400c980c4651602080c0800d0b10300081c1743c52165000702080c48058484c1c081202030700443c0c1c8200904281550708441c0210700a0780902010303401012205070100400c8401030880e4012160818248440c005000c04558000100811014000c07040c0b1100729007600d034066170100c81d105440f80c0c050994150021524140702c0340140300c4002e005c44003210185a04000f070000304452141c0184642e0000240b980300d00c0390084100c0d9003c1c0007498000444904d80b400928402c0b0b03641081c40050300b40001d1545040000c0c6005500400001400f80340520b0321501741100b58444000d036107030900c0c40d90515540803036045070b24289040c000800c200301e1098004d0302c2c403818 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 872638264 1250 872637014 872637023
    0xa0203041a2d1b0105040b010e090a0b130b071706060f0403060906020c01051608092107240c02101b1206031211010e06100b1b16050108070c17030a0207 67
    0xc03068060180d070540005011b244241a9600326030b8071086e4128007194100c1c1c44520781e92004044202085400e9100d039007100710802061038143d12078030342c0b01c2c0c078030b209a51420014001c41c2000f003031600b04480d400d8000070100d035100d00d440d20010710100303107018900000c0e0100b6a541c2a10b0304001c001c0d811030b20140003000c028031051400004040303182d44807407085408a502800010720f005004a54504001d104940c1c4a2800c148071150a007140c0000c1c0341155007401d01003401120500d41d001c8000070000b00a004204001c07000707402401d04c1001c8110b211003e043c0740040e403101c0c40d0050f05580007d2603182c982a9040c0041d00036010b4041d50307101030403444c107000b500030f22694480620790344004080001d00010781781409250791030034102e40643c05155000b905215425021009110604072611602c0f078406804004038102040d058441c1c000030782041d010089035070043c80041e4002c507030b803c102e50703074000c0ea499020440780e1040c20f9141d807210010000d0720f081e00750b50654030036070b803c03 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 872639514 1250 872638264 872638297
    0x7030308150f030a060e25060f030906050f0105100c080904020a020a0605041a0c070b1524070b07051306030c0309060c08060f0406080c04021e0a0203041a2d 69
    0x2d82c14070000806c0c0750071101e02140690b240c2c21000d610901200c280701c1d01c5d600c164880d15403604c0001c0303c8981070251490101500c50210f2400714045015007401035400c3c4444071465454a4200300c940d00f1307000585014044501029004940300741c00f603d49001003a600035944000041d001c80c206025220000c1219240109110510010200c1c1d2142d45070321035861300040e25117505002003805200c0000304903c441100244601c0aa1601d030820890040e0880311103e44480e00d81003540f04070455200c0b2042c0204820741482035148082c0d0300000c260406500d001045091210741c81c0050081105158036540316460072840b950000500a130001400c11a54403d040020305100059603020300c00c2a80101181140ca094410182190498001081038071840f0b001c0c400a904442c01e88009d4010410f664084d00591500802034840c695000d59076850401c40200c42040c507414440381c2000d010300c8604003600052311100c0350f000d69840384280280304009254042d00c505400701821001 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 872640764 1250 872639514 872639533
    0xd032909061903120e0a0e0a0b040605150306040c0e0d080a050d020a0f021506010903021e28120314030a0609020d0204180504080304080c1c0f02010e07030308150f03 73
    0x440e100c42c0c46646009640d6a8555082d1703608018a503401400303106220324100c00450344102c2c4503130211004031b10180c808280d0644d6140000c000d0324800c200c102076a2000010003501d440d051084003d03c042e54105400b2054005020440c1440540002450000700085240d20301d0300402c240c55042d8850030f019540c980391804010709048292642d04054460514030b03c8900300106c09031882480182d58805140303285400b0003440340c070642c444105580103081c40c00c03141d880b180e000802002002500000c11025442c07914241207440d40400480c90308144806c00280d402034080e02100708050001c3d80301d403a100071035030080000340c1c03210264038800070303020340704c908247c010b442121040325241004165080c0c100c41603c01c200c4000f040e01400b0400100002d81d864040d00d00700440700704a808844410070a030003040015541030011501c1041d000c03903070580c24055600c521254002500e4024610b51b0040d1214002809041c00c18900000e004080d0b01da035640b02d00da05d10000c0440b1081c1c503 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 872642014 1250 872640764 872640773
    0x1509151005030609070e070c0305091c0218040b0a09022e0f0201110f0a020f010908030a1a0d0201030509010e0a06060303080603071203030b0a170d032909061903 71
    0x40d9520995002c0e000709070000e43d0405000c10f601c0201d070034500c4150410f641d611000c0300c0f200301c103850803401d00c030051040300596240c1540d10100c4044002003030941c0b4510b801040300b8070a004080426401c0d5140401000800c50312042e03400095010005c6a00032044c8001106174100320030241024104100200502814800b43c4448030341503119100904030b945822400e0b44c4885682000e41d010820410301d440c8909002801500042e20503224104689416a403d42e944042c0941c0c0e102008424840080700500c248002d203500b0301950443c4044480209480c0c0c161007401074141a82d80c0c0000706054020342180f021010140c068502017a43e900c0c081004200c02d0100354006040180014060f04000030039806642c00d500364042c01201c2a5011000790110380d14041c0c2080c40000000350040114011008140308400604071301c0c64110030080844030f101d080125020340501040704281c64100301a064298161851085c03640c80e01c000c110250424054040c48200d540800410310 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 872643264 1250 872642014 872642041
    0x15060d0506011b032304080f0a0309050406140405090304050a170706080417070501060e0a200906040504112b0608030a090905090c04020c01090201031508150915 71
    0x1a0303026210000116040c10030700004100f22003000b80414680c651204406440f0613402680c0c02102101a02d0603480341181820000b103800c610125902c104d40d4034013010b07001042c080107001c080d40d003001003a1030305100c265405920f54440b40030b40e5032040419000300d018000c88010380700190070f1214142d500c0840c41c0d034164151040480e079019504010469900c500c4406004582145c0d01429952101c0c5900240341e214050403982903603200070000d40c00e00804e801d6481001c0814000039855101800011074030442710415035512001c22040140d5078518003600c068800503240000c0c2200103040e40125803150101864600301e40f03025401c0145100e4981c00d0030505105011300585d03039203a8202c2c0d920b01a1408000105907584400d20000c94164002035101d000f16040f50101340c1184082002c990115140003146c5e51608090030955816002c1d85440020350a0524000d601e400002c548881601141c0c500c11140d500200304070400030412031544060348005401d030740c10000f031441d108 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 872644514 1250 872643264 872643271
    0x3020a120215010e010f0303141909080f150a020904110d0501080f010c0f1b0c0b04140a03080d090c0e090303040b0a1503020114040e09070509011205070e15060d05 72
    0x1007038180c4008030b03004c0c400860090413680c008035050020f03030856400703413402032110340406085070040c41194010070081c1a200d6902c1c4041d290780204604000d046400c01190140d000e200398080c2004400045059010613444440e401c40140c5441c003400c0054090510b0310742c50708160b41d01048222510600d580124101d5003030700c00702d5428660000b125403e9441e18201c2001040c059043c541071580200a5a000c0c1461070b021420341da0f41542e104440b0310701d40d8200b007180d0301d0086014001117a10f0a0017190481c801c4034028030692856841c0d841c14451041c90040568464404604202030442c00002405000d01381e0704062402843e2650380360022101035031144043e0000c12380c2c405c42407240d4048116410011800c50341183c00540341c292072011040503036002080000350b1082c1c1e03100594000c0762550040e200741ea2900d030800131808030682040320a441c03103806400014000103500c1c0b007140e1447d54002c2d010754480b0340015540c1500314a5907000100021413071801d4085900441c803 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 872645764 1250 872644514 872644543
    0x906010f060809060c030c07060c030e0d03060b0418020c0a110a051c060b01020c0d151416080603011509020d0c05210c0d06262803020a1202 62
    0x100c695503581203405100c162000082604464049481d000c00710000b5684400501103242c0f40181c6940c5003411a015040c060001913928209010351030310074400780070050803d1400344a1f00d41041c0122019114174465881010101e0b02511800300240d0141d507040300c1c064096075000300007402c200407141301112000d846042d5182002c1240d1a00244c40b40003040000c1c3c8008040400b075480c1001029406405410b6100300b4041c05699034494450b4900c080c403c810002041880b548140192100b00160002803074100040004010301c50600700c00c50b401601d84042651194400b02c0d0050000c00f449a102c424440808079140401b5001480307051500700041080d9101190100c420340500c1400501e0301c080c180380f100600400da081c05400176500700358286899040c811040072100c5543c08030000c07011251084034100c0c500340070308040440d81c0c80502902052050f947d102d0b1f820120300e900b6840382c00942d080c2814420000e100c80513511039214000c842d02c404c0003958030b240100324980c = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 872647014 1250 872645764 872645789
    0xc160b130603020f09010c02030f1002070c05060405090c07032a2109170c0405090c1302160f050309030708062211150f0a03140a0e071e0905090601 65
    0x3654500c81e100316040c0900c1c0181c5103017000c1421004581a4140031010390303052044400c400d883d580c003800400d07008440900010303a1600c0d2440c00c820060780d684d2040e0311445060000300040d498400b68507034446d420392030380c3c2d58402241c902560300049103012020f01d860911404c1602030003142c0340a16440c06901060300036900c81c01e03078980300310340101c5600c0045c150300d03000c00c03d143c1d064201002c6102d800f0117481c40181a10042000c490b4100c40b02e021550106001801d141004100000d022200104c15890400d08a008641145014600800c20b040340404142481001e00035a242c0007001002c0e40da0302543c8100040c0d840c841030321031000708402c4680722440c000044009164960780910300e08809030b00b01c41000700d041082280660615420400141514501c400034040d4008603100000e2032804e00d2030003082010014580d14030a0302d891550818042e00091080031a04000320001c40003210381d00341074007124030b98051801ca03400d0005114884401064940c180d0322010042c4 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 872648264 1250 872647014 872647019
    0x50d020d08060d11091b0d0b040c08010609031209081006080d260c040f0602010e011514040b1c0302011a030d090b0901090312050702091506040b0c160b13 68
    0x11900581e6a0340050100c1c202010b04d80301c3c4d00b0400d070081c1c2d009090140703002c104091400004c1c00f030342c40001c004034160b03560f0b45100410b00e0540304601141d501c40c50807802070360510f000504412080e010240454000c0e000f1024403c1c40707405504041c1c040c16080c0d90340b640d840034419001c2c04240c0662009405485040c00480d072040280e810303140000b06078003140b010a00d0500d0310085000d4120b40c050602040041070030503407001058010003041c2d0002800c1009119170741e00f100e0300040407980d040d1800b03008000e40113680204030510300003100c000030000d41c40800500514222411000003004000c91041450b80640c000c42000c2c035082001b409102c0c0702c80802d5110703900c60079500d01142902c4800d119407240c4034042c0202400605044002585075143c5480340300400c4211000a100042e824085040602c0361340c1d00550441c0703007180c18130040400076850f8000d0b806211600c403404180c1210200041000e5040c080c200100200420b44406450600754881303810740382c00304c0f10b08100 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 872649514 1250 872648264 872648269
    0x8090c0907021f06030b10140114180f1e010e0603060102060417070506270a030206060d0609020d0609050d02030c0d300606030c08160c0f050d020d0806 67
    0xe101c0c89565000d06041c10346040041c00c441c140b034440d0041250380d07850101c0050410040d40b40181c0a40098103185854401218480401d0000003030401124100d10300c584a401800d4680c1d0f10700c1c880380348008440c480e000c074004030504a4060307480544180b610803181c2d2000710382c09800c2c10a0360340301c0c84001c0e810b090000034407003650505c1c01a8003450000740429406607004203070038032035030b4103d1900c400758903000d10380b00b4165803105888880d10400307000303280003a03650036030850707110040c1103a2034888d10302070745515004001c030b40104140c41981c000c200e21580841643d50340103150920805c000d00300600102106c400450321445501c1580010030700020036036002070600340092581c91b0f041d460032038101d0040d0013142413507120b9000b486569130040c01d04541440c12180006202032500900905454820038000c0a012043c000c0c008119841204241c0d81c4005040541480a0a1409a500e0765003890050035a000326810917906903404561224207200c0380d556904540c451004 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 872650764 1250 872649514 872649529
    0x403021f1505040b060d0c0c05030c0106051011060c0306032d01051b040909081c0c09170c04020f120103120801090b03061609050a08150703140a1104030c0608090c 72
    0x24441e038404018403041b03519a000d44c00035008403583c3d2401040e01001a0b480620756003010b05101e0480e512040c00344500d0034200c603051080011482c0246213400b1102003180c54080190005a8042e0700000080d1692030070404c05e8141e8080c01640103000d41c002d440d07094038100060107000b407542001c0110310104441030b00d130050314291141d694541442e141c1044d00511410104603a07800f400d10010380080214183c131505904451400b04980301c094100402d00030180e082180c1069040d0142005141c00040e0000040e100f0b0300c1c01a6540c00c0c012130104203002d9403c06140d134900301c900110070042c110485581440300c540740c40a859885030107c80aa990613001250140d0000c800603441c0030325504030446142c0c2e18140041d03a2910f480110f412602c10750040d41090744440e2120411402401075150b01c60182d01d02000016400010f1959041d4081d00a4135001d4031a50314040c1d0020301421140155446402000c0c0c0e103584600107402d107a400c56520509000c0c10303145000d681011403 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 872652014 1250 872650764 872650781
    0x90219020d022e02030f0405070503060c070f0503070f05030a09050a03031e1808010911041b050d020d140103120908061f08100516020d080a050403021f150504 70
    0x20050700b00003008000300c2c5806039078480c00301c43c400c0004901041026030381c80194090100910600082c3c60242000ba00c0d081e2190b100078040d61003002082208010541900c200c43d610115008940c81c090070100c1ca0342c0a180b80c00341034004110703519820443c0010051030250540e031a21042c0680d114104180e81c042c901c40900400c500c0000325020701050b0102c0b0640920070f0414141c06a803018210500d00c02d5600003100aa540f00c803d1024020f0381c800341e03401c00704100c13424054221104035028502d004d04800109000d0301013801403490080760161410941400c2e400c2020446041c07440c03031014001e100039035030710f038000400c4450903104420400684500000900160321034018092441c82d8500c00c08841d01040071020814904c00d110b81c6143d90031080700410b02d4100028400d038030401d0b01a0300415584071414004410b600400030343d070b01600200303000860303030344134201a410007610707804401205a071115410084d40c1203510840708403849040290907503031160244812039120706c = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 872653264 1250 872652014 872652017
    0x12070302060d0e1f05010603140405070620010513110d200109030c29190f030902030d0906020601092705160b0309010c050a0c02090603010e0304090219020d 69
    0xc00c244075110009802c07003c0a010b040084505210300d8080d604000403090400a20058548004106c0a0782c140550140091040e9250596040c00d5541c40e94903d030701d01c40c4c2010b02040064004107040007000301d0310b07210002402801549412406e401e041040d001c0121607441c0d0311202840181412500810310726889108100342c00300480c221248218440c2c0914108401034001100103607510f01260003c06050a44080e40c1041c0d921403242102e0354101e12014070000e1024500c000415481c0c04c104c100c20342003004000000031803c5000d4110303d10301941601c1000200f009540d0312a641400b03d45680c0d09458150740c82e443c145043d640d0760040860400000034010110451085054200c141706034110369164003000c040002c0e00c1c00301c0d03000c001241c00200401660f5082805400142c0c64589030191030500044c04c00303440306409e0b40001e8010303941200050039a1300c095001d04600740285045075180d0303680d0220303000a90301c1801865183c0340d00c03540c0408003070300016240c8100c0030b89 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 872654514 1250 872653264 872653267
    0x6050708011212030e070504020f13050607051b0f04051911030105010e060c160e180106230d1709010e04050105010f0c110d1104050601091415040b030a020301051207030206 76
    0x3c0d04101c014264203d003500e440d00441c200050190b60b148001e102800341c450f040d0307450b01ea09680300290000d4560165009850400c80c1c180040c20126064001005540881c14050b0012011440340b14950005581083ca060188115204034205030210b12800305028403402400e913090a1040c0002c2c452580400c0745081c1e803424618040d0040c0400016400c110340c9031140c071450812440310f140e07011544203030181040c0803012050024080d182900c03a0020b010980c40c0211683c41020000910b030451040c41400680940d916206002c5d1030760005641c1500300340f6814000e0700c0e54400d500c03150100300c0c00e03450400030f406c0500403917040315816100c00c221140030b454140c1e140360800704201c03069085090320400c41d40e94200000b01c007600460414101003034502c21303c012100b01501241c141300c0103080400000c80700f00c0c00042e0f15142602c84400705810314415526600580d004250404800710801060700101d6020b141201c02c11243c2401c120111034901d51102600d000c0a03400100 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 872655764 1250 872654514 872654543
    0x305010f0207121823030304030c2103120b0f0301060801051801110315060c190c06030e060402060c0f100905010b0105250f0f2f0a032d060507080112 66
    0x5c2d0040308110620b4201e10901440c404000000d05560143c0c00450316402c40340414000d5041d000e40107810030014058040120780c1a44010b003402485006030000c06459904851050b04d40390880140020041c009210040d2a045032078003920302212050110b200701090700c0c49481c4140122616080032a5a0501e103840e001c1428442c04205140796820a80400211048143c200070500304111807170364000d004179980c5861004403041358014000c0604003000f11520030808030344140c00c00e40c11210150303201480d40c1c603141030004541d41c0e10b0050113000715800d09146181c01c00d10f50b040c429030080011100110043d6030600510007045205020705400d4034000c81107640305180e5a002d00400b0310103070083d5840d03002c10505100c0131280b5058200040b2036407412000c0300351501d6001c4c0203403100c0c071044130080780d8012903520000e00f040728020031101c124580e021099000c2c51252212a090001310300b80000039003003d99440000501501c00081c640d075060044450140d8410100307000c404 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 872657014 1250 872655764 872655779
    0xb0c07060e030109031b06020f040f060e0d121116080120030c1c06031202010b1320070606081c0f05040e0a0507020c06210906060907180305010f02071218 68
    0x10400c90202c2c2d1f169402c118152626017100301030001000700c0c00340342003440e007000360003040200014400d80c02142e81020040024103141c4400360024100c0ca80f02802e40c0004040c0780c90b0001008140807990344608011030103241c1900a9007155610100c0710300340030101600814544000c41c9c00d88040c0c5024041c1400803e48202d081706031800c0440003103521070712a102c1da4140400342000401507950741c1140e40c42401d0411000802e4000c00004124494046242d84034801101e91441d140c110300017903120401019a1241c0082c01494080314202c1080c094a2591404000c00a9003c02c40c0d002d0719003107552240e001c460a41e48640441c084a440e03404050300600006401d000550180d003001c88000e4441c2000342070341020761100c00d1544000340c1000d01c503100000d41501c5403030f0000410000039407034180700c058111100385849050382d0901c0000101c1c2e1010741e04000c3c095402c0410340c9a01440725005400c5140c01108039886a10340d5540a032021103041841004180702c0d00b400300701d4071 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 872658264 1250 872657014 872657057
    0x30c050108072304030308060901030210050a0c05060f011a03011202100c050105070e04060602010501030b15031501030503031b0304030e0f040f0603050609120c0c04150b0c07060e03010903 83
    0x29078a4200203c41503080c4441d4486450600c003400120300001c80d0810900d42e000c02d032290410002d6071480ba02e5410740c0c01046110f5aa10107020030b01030f0010380c00f00750a00c1590703040c3d9016004420f0f5000c504120080801c805002e1040c2d104c000c2d8000c2d60000104100c0b000c40f4121810440002200360495080c4024201d81464940038031100f0031491010500030301400340b25528542d17940110012000810084648035009641160325100044c000106801c2d0b0490300580c100d640c003882e605007040002c1c9040d41201e0944c6e1051041c1000208004000001d58022005411000d40a0320213031540c041600003210040c00207402035145c2903040c02e140500203a20180900042000c51194003004e0a03a174143d40203e4103a441002000303c0c030b41041c0580641d512030f07090210302d08001903c0b134640e05c0a401039214821507070303594080405407410329079000602e1443e402d181c80350724409041b42c98100a00c2103070046641510300c003403a0318041c8a91168554151600300d03600010301c100c40240c = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 872659514 1250 872658264 872658271
    0x10902010e06032e0b180307060e06040e0606040503030403320d0c170c150a022d041a03040303050105010503071d030f07030c1802070f0213090b1e0c04030c050108 72
    0x52254410000ca900001c3c1d20042151079858030024032121903803421f141c60500981e124204210030f601102c1c800f030f641e5004a83c100c82090b45010219111100000c045114903841a03606210001d000010005000030500702583c8141031420300c0d45400820350080002d03403002d515682c01074004500071500811841100f18080c0c02c024000d4500c449210b4055440b6100f400401e034000c0540c0120441c560754199400620f13014158240100c1d981da08240f55503502048815010b108203001c24028001d0589004141402404400f9000b13150404000d61056809030002414031001140d154081e00449001c1c0c0b0003903540c440c10b000300a91500302010304141c0c00703903d170041c40c40c1c802c5000710030440c3c6c00c040d44c0100902141c55280582d103104a0302c0304500528034600500ca440d010460311120304100c9501610305803420740010070850018020444020700a15148050110559400000a45c1201040c01202c0207807100c5542c6140d030300451100400301d100d0080c0c06e000039486130065580 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 872660764 1250 872659514 872659591
    0xb06040903110d090f080d0507080a0c0f08032505030703020a0306030c0b12180327040f060f050306101202030307050a1b050105120109051b0408010902010e0603 71
    0x10814442c066042c11014407518000078002c0c103090203441c600f030380c4c214010101e150092080c1100fa0102078154060310782c018041c42004203114070701c3e500495104240d06e07488461450790a800345012a03030ba420544034440c0f00b40300540b40c00350414007601c4e04840009503450b0303107086903940001207000c1c3d1f100444150415898210010000b0340c82d00e002000360146410f030549030310b1008246c2110f48002012017020000c019138800c41c1e036401004980c45c0301c0da01400c0111883c400c400000a204d44024010380181ca00416844801d440d0751015041c0d500c0c0c254100040d9503180205a0b80719401c0d144034494080c0034508001c4214a420041c1c00b40784040c1c140d03400e02d58a61034580c103040011209945540301c5030041880781416454450260400f400c2c82d9090a000400c1c00e0f1003054140518104a5074860100340c04c144525407901c1d41c1242e108010380d036552103118060284c52508001c13400314400c08194001840e01801340e070311a803106101040808a10040c441d0000304a180420 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 872661870 1106 872660764 872660777
    0xb0a030c0303180b1b06060307271b02010b0a050607210302090d0c051504152102070506040506090d090b0306210703030e0604030b06040903 62
    0x241642e0305440e1028075480c508002500600e000c2e0481480a6808a40c11a01c213400b5446000030401310301c140c60003a200c0038240b580c0d5440038060400b224140462002e0f030141c1102c0307000c00301104010041001d002d0b1402d180074051080069600503510f90319041d07918140b000d14580101070540e0300f9850030742603407500c0158414081400301100c004401943d40c051082c0c040d1410442c00800d0801450000e00d8030341c5040100740f140c240100710848651a00701c102d18187c80480300031030b54200460f000000204c42481c41511403002c8440c1c030340d204c44104d10103031000d08652803141e40202418249400c08900c3e11400404010130350744680c0c81d00c0c40541d4807140c504100c940c6d00000340d48940312a030006100000c103c040c04410985400000d90304140000c0840407a4000d449126a030300070346060040382d10a500000d01080060004590030341403940c4203008160007442c101 = true := by decide +kernel

theorem cover : BRFrame.Cov 872482014 872661870 := by
  have h0 := BRFrame.cov_init 872482014
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 872482014 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 872482014 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 872482014 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 872482014 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 872482014 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 872482014 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 872482014 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 872482014 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 872482014 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 872482014 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 872482014 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 872482014 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 872482014 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 872482014 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 872482014 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 872482014 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 872482014 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 872482014 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 872482014 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 872482014 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 872482014 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 872482014 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 872482014 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 872482014 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 872482014 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 872482014 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 872482014 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 872482014 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 872482014 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 872482014 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 872482014 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 872482014 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 872482014 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 872482014 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 872482014 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 872482014 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 872482014 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 872482014 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 872482014 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 872482014 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 872482014 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 872482014 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 872482014 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 872482014 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 872482014 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 872482014 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 872482014 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 872482014 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 872482014 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 872482014 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 872482014 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 872482014 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 872482014 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 872482014 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 872482014 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 872482014 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 872482014 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 872482014 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 872482014 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 872482014 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 872482014 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 872482014 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 872482014 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 872482014 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 872482014 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 872482014 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 872482014 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 872482014 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 872482014 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 872482014 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 872482014 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 872482014 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 872482014 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 872482014 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 872482014 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 872482014 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 872482014 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 872482014 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 872482014 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 872482014 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 872482014 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 872482014 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 872482014 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 872482014 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 872482014 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 872482014 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 872482014 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 872482014 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 872482014 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 872482014 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 872482014 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 872482014 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 872482014 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 872482014 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 872482014 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 872482014 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 872482014 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 872482014 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 872482014 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 872482014 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 872482014 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 872482014 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 872482014 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 872482014 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 872482014 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 872482014 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 872482014 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 872482014 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 872482014 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 872482014 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 872482014 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 872482014 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 872482014 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 872482014 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 872482014 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 872482014 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 872482014 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 872482014 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 872482014 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 872482014 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 872482014 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 872482014 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 872482014 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 872482014 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 872482014 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 872482014 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 872482014 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 872482014 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 872482014 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 872482014 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 872482014 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 872482014 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 872482014 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 872482014 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 872482014 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 872482014 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 872482014 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 872482014 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 872482014 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 872482014 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 872482014 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 872482014 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 872482014 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 872482014 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 872482014 ≤ n) (h2 : n < 872661870) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
