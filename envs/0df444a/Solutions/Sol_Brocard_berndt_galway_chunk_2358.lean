-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_2358
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T06:28:29.066978+00:00
-- url     : https://prove2.me/submissions/09d0d8e4-25ca-4824-b865-ca3b12f3eb0e

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 423920863 ≤ n < 424100719 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 423922113 1250 423920863 423920921
    0xc0e04020906102f190507081902010f0203070f121418010c05030d020415030c020c03070b03070903082d0a0e0d0f15061505091302090301021204030210 67
    0x3500318080d02d070600690710130101000403d11424061a040d405407401c08410b84d440240c0180002e07001d042280c2c22a5150003869444110409050100615400000c001035010310368400c403101641c0103507030034078299450301c100441c9248011074100700c150755444038258000080c484441143c0c09220308203411420300040208510103283d040c030a0b82082041040420400c440c0c0074100d8420640d01c490352000c0740c1d141102c1c03e44800000c40d0502c0c81500ba02d80c80040c408010800060080002070f14101c040714a50f440030b0080c90810414800200105082d03100800240000c5854a001903040c00d02c0e0080360041d00c24400401041004014821588100265003a02d8101d420282580f0f007440d01884444582900034409041c0c4000380c3c81304015030303011400b00e80e8084854002c24105040440d81e500c101001d00394055011203030001240045d901130482c200e000341c0014648680110010410881200c00b180117910080030000c80807814040d0304111317240042c13070b54a01c1c0094000 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 423923363 1250 423922113 423922127
    0x40905090f0d090605030a050c190302090a0501212a02070f0e04024912081909110a080303011d0f0703180b010f0e010f0e04031404030c0e0402090610 66
    0x115403116440b00d021840e8110027904a9000c41c20180c1030400d80f042d20000940650030418030300f4400c2c0c22203030f0001120350041e00c6041042440300342d02949102c01c07207a07241c0100703503001142490800c4402d0398003030394080d8903001c0400503043e0010903d00c2d2911070a048100070f507401c070580c008107143c180b200503100c0d84800c3d41c00c6031414008241380c0a401c580f40510044854444200d404a2103080300ea0f442c201440e890007074000c0c84884100030b10041c2c02d8401d0700c8203584c2041d03028542c8151002e0b09103a64811136403a40304808a01c5000190000283c07050079582000342c190304008010820781080d84036620192011440035807491402c002c200780c05400050175202419124a5030000315090080b000715940c0d40310074000241d58440583c98410794070340c0a0300f8003004441002168011080481303404039a992020003804e03550710b95007211881d040c0700c1c24840e9401e0600c4003000268002c0c10303d501038100c030322035043d1510b07150040040845004c0c100390b0203105400103010303e03140d000d00 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 423924613 1250 423923363 423923371
    0xe0a08030403020c0603010905010e070806010915020a0602040603140a060e042406060e041107051b0121050601031a0f0402030c1303050303070908071503050c040905090f0d09060503 80
    0x642a1a9901ca04003a82401001c040d0b10b039014000000100d101507166000b84c1c141c030103440400003a0350341c0c801e042e20b807202c2c1500c205021406560342006840201e00360890140c0c4944182c03091841255107000c11f0340c02641004011a403100010700c281e504102103c1e0b4054043d40f01408040e14200c00c0b00c1c08544c0181018107010b050114070303940700c0001000802d82c6080590304000b002e0781c8800040111030700301c115510a034244152003460101390020713603440c04c1d04540600b4030010003204401030443e0300e40c0f00c1030520130002690034800ca03244520744550b0101800110b103502d0500c00050489510aa03143e1050554190840280d21104c0320700a0044040d940143d1f6600d41c00c003034000340c1c010582c00385188148034001004208001c0061809146280c603442459501c90312000e40f070b012140592101b0580030414440d40a00c81c1c2c000c01e03000703903110061524194483d148141a07800488160249034080103215201140822125040202078030b00002c4050400000422030312001e0 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 423925863 1250 423924613 423924623
    0xb011a0307050f0d2a030c0306030203062703161208090d080703060b070305070204060e3102091614090a03150608070e041205090f1903050d030f0605040e0a 69
    0x4c101c1c2c0f66010303059031240340380349911100c5450207030501280a48003400c5c145058002402d1400c20b451050280c0218420f6990040c040c0c00995606603034043c1c0614050704911594809100d540b900e03520500003010141e840c8140e8160300300803810040302c6241a00c0039041000f06500030420b0307811010a0311001c2c2c1026241040704c0e611182070890103840c558000c1c000d05000050380c14105500f000040040c641b084e281444100e603940c803000c41c80001100c0038007500790811049600f6031101001c0f10801081c141c0d0900c00000c035500030400c01d00d811510382034001c902442c250b109603004910074120354035001c00c00d45012030310404960712441e80c0c40000d01d031081c03120310100400c0d0141c00c0080079010410403245060b85e6400000c44686054805681e692440c40e40808218414000c482c0040c0b805000300851442010a0015810614450042b85150103001000060051080c00c1e509641d6540208000002c060200129422540141e20813031a00150000d0a0710200322055016000 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 423927113 1250 423925863 423925867
    0x10b19030b0a030b1e061801030308180303010e0114040b030d050a02010207050d0e0a08030f030705090f03010e03130603060509060d1a04080a090902131a0d090b011a0307050f 77
    0x200780415049101c039003004207802a81c004010140c500000c1300307071310000030840d20016500c03100c0c140160105c5a0686090301c00e82c007030040c004a40114000ea403c5100000d00100d540e114040c10b6044d0341082e08101031040d140c400400100e041010000ea210004440420004244100103542d900b01580c0070802c0c00800b05100d11036034000e505903200c1c01e0304a0305640001015001c020a00881743c042030744142c1c0010404980e90000006071090300e505ca80403a481c545410805030340b55048503502c00c0d404414000e0008040d1404e0080c50990b100c00d10046840e080410003180d1441101d400c11020180307804010890340d592142c0003504139406a03903075040210541825204a403142c2c801c0d02440307074080c1c240b004102074007006000d00216551801380303007900d548450099115040b0400d651203040a0140a803004034902c403101e4119070b01d5020b29060307032050004144d8004a605680500c503141c010030052000c03c1d54500c02c0030034800c106141d0318144801031700d24069907000071307410400 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 423928363 1250 423927113 423927131
    0x60501050f2d03060103140609060907050103110f0a0c03270b070201030e1203010911090607021908070e0406050601050403120c3e0f0a0501031802040203090a030206010b1903 77
    0xd540c02c00800b000c0080c054400b13940c2c40f8240406a4102c09682c10410f108242c001501c8c0300b004540e082c090102030b400741070410300c1e0000441c0540b00540045c0c01e8158100459000c000076000140540c850340e8031600100306907801c02621a121074400c00c0700e661854441000796044102d2b41000b0f4803007000480e902c0b180b080c00104c3c002c05860142412510800c00004410340001010f181200e607100c605010600c04090002c40b9801043c200e01e400070700c00e1000c0001898841c0d21907100581d560b0044050319079840b1030a190081d1a84071200038081e80041c0030900c003141c042c8a911840c00e0078220700d0f00b881c40e83ca15400e46007500030041005540c1082e2070070028690080c1d02e00702071304c031803000e440f6000c007076489100001444203e0040d4075100b8a0f840900b01011a000a14030003031024525516060056015081c03181d0411840c14040301c035000181c0e1244040d502610340c120041c16013905603c3d02924101040e002032407444000e11283e10300c00100a00f42d0300041c400d00c0d02145e0310032 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 423929613 1250 423928363 423928429
    0xc09180f0e01021209010c021c08040201030908040b1c0b09010b18211501030209011502010e062505091c020402072a0506030105090a05250804060501050f 68
    0x34224451601c0354000201003130407408004409000d44901c1d00208481c0d03842d540141d0340c681c4500c1d9040700f400b9424050b0301d01740740a900784d16801401030401051045940c0c2d01d0344130307690082d0803d00806401080380c0303c00a01300202812542c0b6004000c00901c65498001030904005216550701c0000c0010291a003107090360341c0b8a1044400f51106190905440c094985c0120122882400340300f8030040d0302c1501003208106040704d030054607a0085900700307a00d0f032013180c0100030300c00103541d2110b00c074810b403080400003244200c1c03214000d103501c201000000d02c5500001920181006014003405686a50b50582c0030441d0001e4000510765003071610215010b4020108040c1136000e004010b8400440303800d5000603110300400c05c16000c2c40d198001c01c0b48a020030b004441e0803000032000201e10a01c41d0f40065040500d904800001c41815088090005c2148131300c0d9001071100824041082002c1c02440e0250404950201c2c1d451036540220f0b142d8012464519464005012040c21050b = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 423930863 1250 423929613 423929621
    0xd05012a02031809130b090102030f06100804020402131d010503071707120f05031305040c1d0609010201090c03050d080f04031d0109050a03050c1c0302150615040602100c09180f 78
    0x181d03200300d901c012847c040d85014001e4104544003e00d00c2001c1c0005016450001071102c00e0341280d803108100360701d95400f03100080d045071000300481003440c030300400c00340752450003c11912001200000c2c19070418041c5428001c2551181076040b00030400c0c00407019004c900e55003962341d9651440c040100c00c3c18601e00e50455060060a940000544030340344000700c503090f800341d407415102408400c2e00d40c88202c40c01c402c000103408010510300744084035481c0400080c05404014070000c82c00400c80e80b122548041690b00840c0c0603441413030940700040d080b441041d8049150415a01c06262070b0711701a00b140c0e6880102c030051101c2d00040c40c260381c0a000001e004d0040580209c2e103082d10f034900030740d80382c010080c1c007885240c8100c20282d01c0c1c50b2949400036a03a6040d809404403250200440445010242006074040c3d03041100442500210029000800c01513000f001030a00d0414514100d0381104289c80400c46402c1d01841103840da40e910701341d08018800c0005980c21949207510042c = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 423932113 1250 423930863 423930901
    0xa05040e0a0509120a020a060209060409020a110f070609090e0f0304081513240209040903051b0c09182b02070603051303030b0d05012a02031809 64
    0x102080d18188540c0d0072050b4031140c4188401c0301103402801d20a41c500704640140036108005900c80003a4900007070031a0050103d00303c0c050075180c2410380b5082e4a00598000d1409080011091400d409440c00100720f410644808075016040c070b1420510000c1c2090024000d00400c95100d80f40d540300360b101004036134846400302060b030340c132551214102a100c404c40100c000302450303a0004208041c1d03c460803203000c0b681c1305580c48555404101d6180e003480c0e1024038000030aa00340480303c69a02c3d0781c05201405440b82d903070b40b991104207600c2d501ca80d2802100d400d4240c1d20011840842c1d03210300108a0300910b00000e1514121008102e0303900d045100556001d0fa00400c10120080d86855000c042d070540f0303180c003510040c2d510340354210100c40e41207442008a110390041180801d000744c1c8000a840006404c0c810145d580e62149401c1d107080368000c8440f030b0042404103111190030ba407001024030351440030f1844c00c0c1c822880c1d003000c03140e0340803814800c140d0f42000c540300e80e0384d0000e02254 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 423933363 1250 423932113 423932129
    0xc0c070801020f03040308100e0408031905091006060908100e120a08060a1d071121030106032d02070f1b0602190201020c09070203090d0308060901050409020d0f1e0501230106080c0a0504 82
    0x4510700740c000346807143100d09030554085c542004008540d90f130042040000341c0da6444014031040c88040e01e090054000808408554015450b0b07031107036213102c80d0050594501c03c1e10340300e441d0304184013440504402c3c2c3d4012850003114008030700d8915204401d4540010702031518002c00a41480103900349400200300311280d92181950101c40101000914101d4005441c104a04070501c0f14004c00107041e88405071195070120080c260302c810a80c06098028094208030801a9140da64510746807410181614040000c880400c0311a50402c960300700600005040680304540f41c0c0007035a19405000158840e4080200090b40c0510800a86a91403401031402c000c141160a000c0c200f5041034940b24001c2c43c0003000407905007803030300980d0621a4060150200d0030a9511620420030502004840f9419600d81701c01707655064440440f4600d0060000150400540341c0e4001010f40b072a002440718000a001000215000003503030f503010451b412041d5a4805003081150680b04903081040 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 423934613 1250 423933363 423933371
    0x1410020c040e2814010b2101110d020d051005062b0c0c03020d0f17060d0804170717121b03040905060306070809060c0c070801020f03040308100e04080319 68
    0x2102c040383e0780c03180455000750f8208482d40f0003514400d0980d01680042c581005004501c1c110400c680b0b410006000512000000c00c022503182004144d0302c05298003c0c2c06402003607284191240d407150700e80046429000f001084c0c81c01c2d002c07441d04c3c064000c050400f52021b00780f03080c02c0500c040c141000b03180255401c1181940c911030142c1006082c3d881580144101b400342c042890003042046001000341d182d4400728882e20420142c112070040416030000043c882401c0043e52005c0a00003030501d0140740529120803010f110316000140d807000300e040d038000d0031107080c0e400702048100010005103115965200300001a10f40400d180000c84000c4c440010005410081503202c0c600841040701a00d0030b0b0388907000200d075034050a85452a25401103404244c6d8101400000c02042140c0c0d82501d03070042c0d40c3c48215089070045599250a01d40010801080560100303403954000d044d2440f4807a16400c20026221010000b4002001c02d0000404600c40d091001c107941c0607407900f074102740 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 423935863 1250 423934613 423934663
    0x70f0513030c0e07020303090318030c0a080d03200405090c041a09010e030d090510020f0a060203010e090a05060a05180607020f24040b1312091410020c040e 69
    0x9008410b40c4548030b262140200411305492011003100e0142404c0c500039800c280840d18811410601c2807813156041c032421200280544501c910103000f0800b920280907441604070f4050259030f099480054140010000f404582e0036100c00c3d641615000e5820b014145c0d140c2400440c0c0344210741042005504c480740c00440d0394150f00080c180c10400b81c0c0c40c0b8001d001114141a51460030000e400c01050341188244514100711700003404500702881259480f80e80d001503181800607042e41945c91540020050080341d41191540b50031000b5080184086c01d402e89800d83c50b400080d0209440da074403040819414001030318461098008241503584906060034041d5607843c400000420900460800e5082c00b05640305e2030354504101055054240d030360360b4904403100310003031070503942d4018865160003149500311403e074001a140c07940d85410f803d00301d481071203035200c0004502c600281c0104031001c1d50301203a60a0241c4003642c004c50011240090903003845040c110380030310403000e40244 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 423937113 1250 423935863 423935873
    0xe10050909030c0d050f03040b0a0204090e030d0c0206190507140a17060927100501030f03090b0310140a03050105091f020304030c0f06060e2517070f051303 69
    0xa0940007030300c004130784054070101c0e030548003401500c040705016041400085c2c0466103594004d40e000302116001450f1a8035041e0b2101111902025111103030701c04210020340d4582841036681103069400184050f10b032a4120201408103454940340caa510b86003c908401e00414180c1000c03520303090300d15180c000168009252200c400100890031a04401203403076814461801d034091400e504184440c401512440d041440c2c80000d058035511038140135001c040d03014402d19010303620404a1391400242d60400914255880d00050f0f00d0000c10824803980317104d81c0500f2001c840d80800c02d155090b1501c400580450001e0340050050750804003040038280002c81d50b180702c0c1c074442d840100e0819401756400128001106c1c02000b191409150304081030200b0064486180300f44408105551110090080c00c20180c40504079144495070a1101011801c074031040010185003412541902c3d45481d402100050320441c2407018940d000d4084511440c01c640d0610912100d2100083c1d9030702e09 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 423938363 1250 423937113 423937117
    0x12011d131b12110409031b1505040614070314040b04020d12020c03010f06080d0e06040305070303020d0e0d021f090e0903221421101d0106050a0e1005090903 69
    0x2080350b4043c56011800d10364a07051148080c95501680e032030741d118001c040c0120080034140d10698104c4d03031241c002900302c030103400307002e202d280308007808118030307044a90000011002602020505003404d8060110645900c88140d20079000724440c241c03501c03140041140d0060b440c00292051f40104064070700c00c1e030000780040510200b40c0c020050070665154460407207183d030145042540140342e084080512600e0758040303105000700f1303107441c095403a0340b22450032405a2048016030880c0d228185465000304806c0031009040e00e61018661184d80020101c2c414001d0f0101c00491110001c40d80d00d00c03a52805025049842003d25a0300b071940d41144c3d02c1d040281c80c60011507819100d58000c034004194041201c461f601e4100b050440d0b0400c000380e1503140c0300c88840580808000c07500c80d40381080144032000c6c11302c0e00041c141c00207845d01c000b10410485021400c1c0e040200c03c20054454210880444443e40503402c060f0b21550780282045034035602c01c0d039000e168401840250100440 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 423939613 1250 423938363 423938399
    0x90d050106060f020c1e0a080d020a02030c1507060c03110c1e01020a02030d0209061c0c18050a060804020f0405010602100606180302130b03060c12011d131b 69
    0xd5043d20b02c40040401ca039a035a40068a540142202ca0029001040038080c50309000c00105102c6c1c0f03144d00d6600a510b0b02141142d0107005a010021038019800d05000040b9980070598a403000801140300789000c9104100c0c00418040d91850b01c4040c003407181c0c1c001e60b0314904c0c140d091540d8501c11258684e4441d40710501c40d00d044250048900403110500c00c60303120701034540145081540340342220000750021140150480801c00c121048820350380d4041b4031001240d880011070103d00000181081600b200c82c0b411404109404d000582c0c8400a4000322400c6280c00205552588049940306d40c001c640103401ca0704102c004034500e60085111040414042020030a05980300c800300e46000309020007910382414000c0900243c2000d80341c3d40d143d2901018041001041900441c4ca8810100e034600849400420741c1900f4032002e00845006050030401d14000c84825411031200d140c0c041c219031114100c07144042c0800c50540c104200c0c070445c036a0f40e000704036500d43c0031040b4065420 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 423940863 1250 423939613 423939617
    0x1061a1e070b180f0109210f0e0418050307080702100c0209161e090f0801020910030b13050f0601030e0d0e010f05092707080c030a11090d05010606 65
    0x208a060300c61800080da5103141d040a05844542c4030300c89a030102290a190080440c0204000b10315104424020f0211480c42081805a854000040080c58a00c5080c503103041003c0a5070120507030740c1c415080c2c02c1140c1c2c126400120308040d0740c000c805110100400500901000c1008024040500c0c050b0603030030300035124980720b10f0010038110f030240f0184100a40c010990390114003001601c00f84081e81c8021030030100815501070700f03404c9000f20b06800e00381c00690250030620031600d414040600a000c1c0c00029400c000403800000c114018048a42d802c046d95200301e480b043d0355100c81100340204081e0f0400107400c042e0311f00c510741ca404664030b902180c2045004140313030400007090700c10600d280d03840f082c7d0281d031100111400c4944c041e00e0341c1006028000b1109a0341c455107954403114040741d400011440e091070f81c45400300d001700044184440031042084154030101281e600c05076003200018200da07120740843c454061900d140703401c034050f0301d511410170405501000030b8034216 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 423942113 1250 423940863 423940897
    0x105010608010515040b0a1116050a05041104140604150305040219150c060f060602100606050a0c031202250c0905060f060304050f06040b100603060b0a080901061a 72
    0x920180700d0380351440c4803a00710304541000201b04110300003010b00320a80ba01e280c8404000c4a4000f40340c0340003894081c8861206909104019038585500013200504003640c05004003a48807200c03440ba40681e02c0740c02c208018810102000b603441104613006041c00301c60040010400481c020b00404003101c08900a100c5282202e00c1025541d503041c044074101080065203504010341100c0c07144030000c0071200309407601c240d40c900074000e0003102d0107842c02c0d0340180300f075030600690407003a108940e008500b40310301048010742003540548a010001c0d0142011803001500b002e2010091003000500903088500b1441c2540b0700203e00306080f0b6490103604480d24140c1c490ba00c1d40d0440c3c4043d1380c030b254020952202e86007d401c01002840e03101d80100700350760035107039840a111305001c4211000c503100180c510401c500c206981504002411315882d040191908000c827643e41c40c821440d6541c107000000c0002480300300250851800f03004141c10b00864004030001c00e09a94011540c200187c0d070745 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 423943363 1250 423942113 423942119
    0x7050c010b03031303030e130c0f080c070c0614070611041d10170a05030406031b0305040b0f0405010e160609090b0a0302060304141207060e2427010501060801 70
    0x400070581d2500814590301552941c550b940076543c47d000b100015030000c023440c0700e0304220b0010b84180d1079180015101d850710305a40c4d09008050800003810008460000c0c081c003c0441c40d156401c0042d503081e403c0183c40075240d9045660903006096000b0207039030401400700c0e400c411000203001150818512512400413900400e030960408039448403205903c0035040296900140e0080003070f50215098a803024081c4c0c6a803030440d441904843c01294485a0031501c0f01c0340011001980c07905454204030505041c0d07290100100003505494115543c8004142404800e40c045480741c84e5800444481200310902180c0d400d10030b120708000f0559204c03000943d12024003070b00c0002c0000400b40500541103900700100343c0c10103030080c5d0301546c95059000403040204480d48203800c0441070705840d03c02c2e40c41c0140036101000300e044441d0700a00049509242c104000c1212104010003404803640d4108401c001300c060411040401c01ca40d40040d18600010761200e41613503016a1102d07056030b2 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 423944613 1250 423943363 423943369
    0x1902010b0f2d010c0501060e180303090d08150909100e1603020d06110d0915090510051b071a01062c0604030803041b06020f03040501110f0607050c010b 67
    0x84041003020650800d00d8244110740314802c1d081c400160305040041a1501907126182140c90726000a49560000c0c070512810038407081d0404040707403c44008616510f0201107494548401e020341500b4032003604c000c1108407581c0c444001c994640a40049240d01d0b0440382c03555640c202120004146140180151f282403001c12800c0785070301c4001c29141503502d15404d00005503a581e0043d200240e030303120f1440803008c0d0341c001058000c000f15004203054044d410454070780e41d00c1840e00503c0343c0c40c2601c40000246c0104200700020840840040c46580705184614030100c2c2c0c08610714202c200040e0f610801c5921005030442e01c854500000103a03072126001c1d2080b051820304140c100e007001c0b0107094504507030340c0d0308840c809000d0812402c207a03480d03840000e00e030000c2d2011550500b44103000c801c440d407203466010040c13010384001d01803448403910980c1c891103580101410440700309580f200818042004060144079402295000e10705803000800a4008622040155003040c44c4040f0b40d00d = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 423945863 1250 423944613 423944629
    0xb120402180406051e060a0e0c1312051005040c0308090d060c0f0801050d03090509182d0d0e0409050a02090a0b0306250806131b0207051206010902030603031902010b0f 74
    0xb00000e01040306080c1881d0358800902390003094000c85031010841500e184040220a00041100040d4100810854600700b41402020303400114858505020032002c1407015240c842220b4007d46c0190703031020031201140310020110030242c54942418424801141e0101c0d805604051a690ba400346c0d903203031070421128500f103690290009080200134402131514400094004d007420300740b040c8a0140380e40103410851100420950070070715840b048196549490824102000d20000d4640c226000c0780c05046441100c4400c0c5c0550796401c03009040110801945001c650010a100001d1030724072084c2016080700116503000780212408668a004801d4a81040074103030580034000ea003226804036030b4120005c0c06a03502210580080400503c02c0c0310300032000d1038030031078a2403000680b80c010745442d032070340e1100c1e00030908901912070b45d48010420f14195a88410050799a450b4030f000649507004900d1101020744860003000804c03601540507518201065551804a10681040102c84 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 423947113 1250 423945863 423945871
    0xc030a26091018030c0605070c0e13030311070602130f05061608030a060b07030207060305091906090c0506181003090323040b0d06050301150b120402180406051e 71
    0x4110b2001d081040d03030240d4520050140c400300030809903542d0342c03204801c1c003a80340d114001090307000409030309218042c11244013078a4200d644850f030703040c0380701d403050340c0040e400307015007015030f00c0809142c6c2070207010840d0545070b0461819902c400b504000050418518440e03a11041e022480010383c074108a4151015680c021408040c045580d81300d4403010740c401403001c03840716074036070b808a84103410001500310640254010304001e410010041d04461002d40603540310b622a1012540d0342540f60480c0c40030a51142e40420300c2030552034403000340ba00d9500055881400840c12030002d8000c0711003aa0100d40481d407034110a8402c2d8020b5081740d858039005400142041d14001000103046425210300350a104803a10303041c1e807034018000b560003141c4403a151640300c00c000c0015190900980d0080e00140c080c0e01c2625242c21000005403251005c45d500c0580f03140000350a540d10004074190003a4a0100f0308421700d001e00d07001b001007000320f605420722007448100158031650030540b507100d = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 423948363 1250 423947113 423947119
    0x3050402011413030206030903120109200d0209030321150105030f1306020a050a18060819020c010204030c081015091e06031101020d0206040b0604020c0c030a2609 72
    0x4a0245040e0080354480e120600f20308200c8040000141c070707604002d501c6007610502943e2144a070b49540b914100060b400a42124288000001801003051080c010003490360310782d6507655080501d4038080d001d200b44465040c040402c1c600341046500000a0016202d1040080c0d250740703241002c0542c0352030b800e549000a40c1440002d0001011365401d0743c2001c13850260440e0b07a40c05544c0c890680e4030490801001034004102a0010b54205003030604814461044640309810f2030002801243d00806c03111090072154445140e604103581101c5100c072403640299a215101d082c42201d2a1080c418880305104002c0041c058002510800180c0140301626058240c50110520b0281540c551080c000f030f8510008001444080c0c41410002d40c440d0740203001d200b003100d0001e070800c4440300c4a4000c1d0f400603820040040c103610050303075010808071001a20b8180a8204a140500c04c00106425100d0041400280080000501e6240d20a59489180d0450070300f0800c5680c0610203030307150 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 423949613 1250 423948363 423948377
    0x905150f0d1a1009080d1706040b0d0503030c07030e0303160303020901022508070617040f0804080a0b01170307020a0306110f070809010807050405010f0f23190305040201 75
    0x30820302a0040c101901c40c0c02c1d04104001071007400540c5082d060400070020800041c01000509000e220702001c4d1012810124032492809054000382c440090410344071301d0381d421952540707664469210010341d130080b08a0703442c0c0c0740500c8407141303550100304254082a0355080341105481c00104445500171013002c7e0355804aa6a5815000394000000f094158002e030800310700c0200c1700d11b00c1a84000307441c0c00e1a120245c03905401c14181b80035a00980700304200c50429140c0c29040d241440c0d04160701002d06c81d580240c6050085041c01540c010340181d01a80c40c061003400420041907050f030342000c01c242a101780b00d80c1000e50320f00c966100250080c4c00350b00e0802c0070911076800111915400c100c1b151a19802c04007401e40c59016100403240c0c1c04002c100d08041d0f591100440b40d01c034100c0d042451a0504000000c1c04403000383d1a00410002d400729849411132103842e40c01360034848060006000c0f4541141c42401e80c1020208018802d00508011540c51003400303614025901038403113907 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 423950863 1250 423949613 423949627
    0xc030c0a03030c0f03032702151608070c031202010905070e012603071202100501050901050d0204051504051008100627060f091e090c141f0905150f 65
    0xb081340781c0d2541501407642c0c81600101ca10108120303c41060b010148125070b1000610400251481c006030000649400307000c0821560044d60301c4089003134101c1002500e40e80c0c81d2410100340c111036003005150504a04011717100740d80542010380c1651003101564078481e00c8002e60030000f0024403500c0d484030841412425211601e00810040e41c20388420b83c2c3c541000c0761550340210480b2801c500061b0b000b0304003044403450903c02e4a02604013211460501d5161100280c00e5058149001e88203035982d8001c41c2000010044040588101410601c118501051150081d100b42d10036100c42d0f00a2009004e10900d043c800d5100b030b1402c86040120046600b04400c100070441402c14094035581c102c0420319088028a0500910414402059030008501c10801c4005007030242031000e801c011016001651060340c5409541088080446071411030340000d0b0345c505100111161100002c640c2d54401d03500c410030303105440c400d031512806200c6003550180648551741d1001881d035800d1100e8 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 423952113 1250 423950863 423950873
    0x31d1e0405090a0210230403050601080d02010e0a06020a0e040f0f1a031015120503030a1d060606130f1403010506060307301401051005070201020303220b01080c030c0a03030c 77
    0x54441a40da041b0304005240c0e00442e03a416403044d00181c806600c00c40040144640400c010000000d491000303100041c1009620f5a03076040c4100e00404440c0c0218240076568403a10b1109080c0700010b1080c031441d603001c070215004222003812407200c04e04040152140040140c4202c1e103c40025004180645504110720700506000e41002803000c07000d0400240a4500c0b01d20392403541c0210080c43e035a003481c0b030580b000c07181e01080c00d62a540f2201c4028418882c080f500790b50141003070700c2e015524540d002509081c10490b810161540c0351b8210702040842c0d5006050f114150141d00800064460404201650000320b40940000c3c03808a4021403038000e50100301007440602d5441c01e400040c01c4548015551a14038803521052000010442c1e458001b050741e4001c0070f103080013854806540c00007926131200800d580c414070210f248080c3c8661043d4460554140c000c088000a543c440c0012030700c03800d010b1813061003881890485019490308480080840e903060b19145c0c10042d0651321 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 423953363 1250 423952113 423952127
    0x2090411060c06100f050909100e071205010515060301030c03140312010824011a03090703020303040807062616021c050406110c0607031d1e0405090a0210 68
    0x80e190016001e201c051034007101003001c2e070301624020340f80b005502d0818219004130043c1d40d1100748035a4403c8140685c81e58040303205503072030112000c0425615040c400e5140340070b00702c0d0302c42014020440240030501c5010350181380140c00200d403011a105050b410020075010038003001c3c1c440c180d8268100300052480c884508000c6008007503a00b014412000800c0b8410264000070745d60f0801d0182c00004842c56001040c05c50700725030039440f0b5505058aa64030b0340164071503441c071000e0020100f030040001300708a000940e4024100d96413285c03102e08458584000e0f1040d00041005c121065000160034040e600205501d051102020f64950000c800f100c6a00f017080010f6004020b43d0304d111611031842c1c512098115218165243d207003080c01131181505080160440d0010310102055690302c004503030302d4641520b8551100748540181c1c510306100c5030403040d400125001142d0b00315104c10400e00b111003040313404010607a105120b0948490403041c00940c0501a03022440b407460150032 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 423954613 1250 423953363 423953393
    0x10e010c0f081204060506151902071a19090305030d0207081201080102041409090d0806030304090c0801090605060903070b0f09031009060518030301030609060209100c05010507020a020904 83
    0x4689500d401585481505900003140f0801e0704118004000c1840980c0c001c05030482c90940d090207003903000b400c101d1118099003102c5151000c00c04c00c03400e102d80c400c00c401d001400b8484580306840b1080711034402540d214a80401811800078603201a403030040607010101c81c0c1205c05149403007000c845010080d402803a0132a01d003082485155505c01d18001b242d80a0b2005000042c0c3d95400c100c9100c0c451031018001611456015041004400c000324044e140d501302401c202d40241c0710000003a0541c00f81da04810032540c60581c1c0071000c10341c810f401a040380e03010501007010740c0d1183c09021182c07050b110342540681c840074003041400c030014003c101d0b0110500e001d50500a002e070000c0e04105040000c103014980f036103001014030103140325564010a940c1c580e512001c41c10140b658490005100141280c4c6d0f8132030b407003401d005040d011206003100003012000c409441c108080c110764440481a0f40c1c0c0c0d0f10b450000f0b240680000b411071103150300144107235641d0741d0715907541c141818864 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 423955863 1250 423954613 423954623
    0x1c090b160f06061a0405210a0f0614010906060f0e03190503070b0a06050901030f0503090901031a0702030322110d20031906050403031401060c060b040605010e010c 72
    0x4406002044004100914240c4240b40c0443c826140266589102c1100c600c00e00c00c25004110421465454140c0480c103094204103048112491400c2541407501444001e826a842c558113070701040280c3c0e0010784403075240c0c600d142084c0d0301d03030628008481860003244d0110b49444002c0f08164040c201c1603084030750081c220b4a041030389151010401005400c21511a840030440c0c0080028080c5015801031041d642000240e16000000c0c140b00810320000c0c00300d10000c0180b01c1404018070845501d00e0014141380d0055940703150180501c1d07611102c20119601d0000826411840402200c1c042e40484d00120030800030311450394442501d444080f503840700d60300c064010326110340c0d24a1558500a011103801042c6030300c3c0c816079030020300b6001403103608041c2a64065480322281c4c1c0001d580c00c031900042d41d64491809a00414542800d910074080a40000a01582c48558519083d100b24410701c54030351141c0c01d1009403402409528045101d448d590240f5501c10051840018007407 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 423957113 1250 423955863 423955897
    0x913021b0709060b0a1b0212160918030806010807031523031b131506050a1404080d08040f05070e09071a0406030e1009030306050406120308160504090e06010303021c090b 75
    0x1200164035084c440f1008269803400000c00700440c600d5482540210b0700720189100c5001c00b4cd81e0000e05803040104058180091840480c1d1003501c6030f440545000428008103940d0727a00c826a814007490402101c8684d011100460a400e040110750f40456520070528201c4060201d010000c5107a03000502d110b015503110307100585151b4224404d8020050b503100c803940d030704080000508090440054980f8441e08000400c446180051503000c0704c1358a1615603040d44807450600c1e50305400c4c04002c0d080748108480403801d585074200d86405121100115032010342c0c1c6030029800f01c5e69002c000800340c0804d020400c9503500942145182013048415202107003020400b50044859102d41580080c1d6684ca040c041401c0c90b11500c800307015008000301c80d00d0b0196500502c0c50000600c440d14041412441d00440c03805141a5005008074a5041c003116030500c810707030340d580c600b40700c243c0c01880380042d0011201035950100c0500e42c8241d50300001e05090001203c403552010351100661142 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 423958363 1250 423957113 423957139
    0x10c060501090e151501052503020714030703110d050304080f0601090c030204080327040c081f06020607111c02060a050c0c030913021b0709060b0a1b02 67
    0x503031054901030100c48600081c02c0c400030301e440d4035140d8441070005880c02140d00748031540b83c00e002c8800c1086001d103013240d95401000000451208001c014119014842010340d08154010425206413000c66003030781001d054134000c05a0f514854807020740791911404c0801941d061695104517002c0c010011a40b81c030f660b401c052864514003084460550f04039000600c080312040c040c4030040302480c5020741c246401c01c050746442c0c2c802c8003d00b419826a5510310f004190f41c0100c001210f01c0000c20400292500e0305000e00f0180c022240303080d40c1d03011554000301040b60300124100341c400c194024205070780c8103641980c0c5002c800c81302086901c6000c1e9004411070700d40d8883c02c82100c140d80600003d042245100c810740d8400703820551189000d1140b941c1180c800425a22840030482d43c080e0711004001c00c200003441344080e01c0c100031900d42100341c3c1e030384000102c0c441100e8002d00100141030381c0d00a00d600c24000e010000f40040c1e6609065075045080c00c51800d610f40c001040b00c0440c880d = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 423959613 1250 423958363 423958373
    0x10080a2f0f092706010f08070509030a140f0c040c20070305031612020604080a03110909010b04030c06090b030a050a0e0a0b011d04050303071b0c061d01030b09040204020306010c 78
    0x1d11000b886910031030b20980d803020351122901c0f80e5004503080c01c10a0484038141006098403a00400207400c1140200f1341958554041004844a582212072462032031384220b503242d102e080a400b48107881c4a81e0800015074186445400f01b08441540d81d400e0740001091101451060301c905420944528407000c004140c0c02d0000301045074030060041e11481c4c56240072414501420440025504500c041101042103901211202003003403a001445040031801014540a0741c820141c115681c04000b00d030386401e107402841624020007480035582d5a81c2000c03240085036005281c01510188082080005150031a0b50018503e51001c1007071070104142c1403070f003240f004042d5680710303002d401002040c0074200c81341500e80641410703031880d00d815100c0d1981c0b403101918110030804030182d5006c21508841e41003820607030000900e07451954070741d40100203210b02014406007088820b00402650302910464094010140c0001101d0380e46408000c001d42000301110705121030f40d003100c1d0001e1 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 423960863 1250 423959613 423959629
    0xb07030908031305010e090709140d05070f080f061b070f0803040327080a0b060102190614010e010302010c020d05010f02040914090102032e0510080a2f0f09 69
    0x1015030051034102807070a030005004505001c00b25000e4a01c7e8800d12400d03a6102ca020420340d10031560200c0d105079200c2c007086d8928090700303000e04030b40240b41380458410f55403100030301162804000c54410030344140006440f00419101b4505800b4000740034265161950060014580140d1a228141aa603101d011055100f280d040300040c0c0d5418410306070400c401e81c1c00051424801055000b0b03410710b81601d5a42142c0307000030f420882d078980012100d030b00c2002004030141d0380c505d410b945803c29260035006401000c00d5031092007140f90010510304084424641240d40503550b444143c400c41e002d00c03c0845003031800f50360f10b54890b610450a40710b107000420040c20100c800140001810503020714100001d0200388072640100103019403481c0000c004c00c0441143c11131a0071016001da60704445006a40c801078100200c4050303101c485400a070b001c2d1040c40d5489040c04141402c180b101548203a42115003100b000b0207184418600d1a40b02607c401703441d2005852030300c2d058500145c100 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 423962113 1250 423960863 423960877
    0x91508040219240203030112080906091804120206060f1002010e030307020f150402061209010e06310203120c0c03100903022401060806010e0414160c08040b0703090803 74
    0x400031202580100d0f800c5980d200f00003a0340e61010318219414090300c014105641c6d42c0282c4002e5021400d1030103030303070b80340b0889094000060104100702540000e0800c00d1400300d0341038403600c003c24101896180045002841948014005c002440803101000f012492100d241411590384245642107541d08000441c0a100e43c0e80052441030982d410382e510307102c00c45050001404011082c0001030322458160f034502c84e500c1801d41041c0d900d80c2049070042c000c41c0307001002c512980b000e001a0a0100917a0086985031902400104c45800c0e900034100e0180c2800a415500982111860b0140320015204c1100d41d0420f0724040c41d00c00340080d20b0131080001520106075102580000c054040007a0041c5451a402d2213031309100c2040c251450140512411050181d624005601b80e88519202c000d0000c5c002c004100c2d10440d01c0b120350b0742c3c02c4119031483c0303000200440c1c0440203001d50b10003400298045d040e50318081c104510608142c100001c11820710a480102050400090003d0016 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 423963363 1250 423962113 423962129
    0x80403020109140c030d02070b0409091407060c0b181b1804080c0c030708100b01121b09140607120c050a080d05071119020a090e0705040c091508040219 67
    0xf084940703138100b41c106202030341058155484094200310040526007600c0440e50382880005401019050644090031403031074000032801076010104901f500140c0381c00d46103005402540311941c0d85442c120704220001c903007034420713480350f0a0307000a0014490b074940020030103402582103400086c0300004280040d0340c100c484020224126100010411060815a03412401405650303d40419a901c075801c004020754051b032204510382487e4002c0540401c0d2590654040001c28030010700c5050821039a0300380340000c0c00000380020381c480c600350403507200c00c00240340a152034960380c0ea038a00d02c4451038608040c00103224140303001ca0400e120b10b01515004048480d900c0c00f52840307000032140000c0511041c403000800c070494600740040c0d102030700980030302c2c008500320160001407200e080550012001c1741c10181031800300e000114001c0125002901d0a01c910400f20381d06468256480c012003c500d10740c95100150940308086183d0400e001030030710a000844101d240c0b00e90940d98001c108 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 423964613 1250 423963363 423963373
    0x3f24040e010b030d020105040f0305071a0a0c08010b2703071d07020721081b030d0204090b0603060f060a111b01020d0216061d030105010801060e010902130608040302010914 76
    0x80d035050611a800c4c0710b601c644000c11552030166158441c00c0e0385058050100440803034032a08006241d022258551a43c03070001601d86865000704000d04009001100012524000000c0b0031108909a410000308030b203081516103c000d040000c101c2011032500e43c140b01c1c084c0c2c0080c0342c107409596085000805107c0c0c0000d8a00004080d02c0e01d8110b0713001c042c1102140c94841144907203010803601280d0300c40d010396a01c225003083c040d008846007070f041680c3d00000801e810081010790003071044403141407041c0a041c0f514010400c1d01e00088602603044818400024103a2074140300510102144d030900c2d5005460740c001c1e10707140040f2602d600b01d103070300d0481020310f066804009040300d41505100800ba441e182280c110342140c0300d4030031002404514448084000c0006581b20005e11014000b0403843d80d4581c0d04502030000c5118800002062000108590035a030003190400c07040d000c0110615071420f001185e00c214024001d508555840400c1d40005101d082c400c0103c14105000744 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 423965863 1250 423964613 423964631
    0x2130501081902010f0f110607020d0e041e0b012a06140915090c04050405030d110a08190b0d0b0619081b030a083f24040e01 55
    0x1031a081890340504242000b034071540c0300507a40410f00c1e021405003441d10190420b145281030303c81285420707824106025003007c00200c603600041010081002c1d685480600c07a4500a0000f00e401107140c0b02281d00c141c1c103030410a0000d60708540b900c520189403d42c00f0450050b521000c2004013450042200d0003800008284119405402a881840008c0d0403135030a2044c23a4a0340e58007460041d0150280650015100550501032020700c0c2e00e01034020f01c100c0c5010300c0c0407500c80e4890740c840107009103802e00c541c02060404040c1d4501d441d040d25980105e880f20480900100900d031100c1041c540c0b01c1e03071010102d4407800c5040c40902d100e900100c2ca28200042040001d2801c80b10180ca6074a0301e500400ca19540003c000c00c040c688008113011202c4d122010030b003010842e09001d46500b800041d061542480c42414041c0b1144000d1813000004409030000104080094081c0c1442084400b04102d050070080c024040b25031000c1d41503121007907902240a4403040366549500e65501c010300 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 423967113 1250 423965863 423965879
    0x40c1413080c04050f040f06020c0a0609020415060207030b25020606040f11090409060b0a080a03090f0b0d020306030a1704031e03020307170403060504210305010e01060c020d02130501 81
    0x2c048030400c4030180035600c1c2c41803111460000051002d03001122840c2d68005000e407560482d08842140410758441e030143c0c0c1440009003111220403070141c1c0c0f802c0d1141584940e2202418140d5406601600590340b440c0c55044503004094080441240d8403181d0390030001030802964207190b000d40140c501303850a04104803c88403200300481d2642d0410b4100004001c2c04011100e0071003084400241d09000e40c00c2003401011040e00c480e80000c0303214404248036500040c89020a40710f075690a840c40c1c2c950000c14044072041c400c100e41ca2805108644000401d0f401559100b103000e011501d040c006503e4100011000b90784000401000290600520034800e100391074103041441c0300b444095880d94025628440c4900142048903640e0000440b0301d0081e04071401903402020501c02406e090400f141410b114841d10304400e00c3c10140c000d070340e502a014480c12908401c0f24281c5030380c81c0c103209507050480424102d030721201030300c1c8070001030b99401040150b072031481800040640c10001e00d = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 423968363 1250 423967113 423967123
    0xe011d03031204050d0201090302210f030f190b0d0321051005010201060512030a080429010e18060105060d0609050c070201020d020a1101120209130f1a0f040c141308 73
    0x4817011a41800344100200c1d80004007904a4034600c000ca4450341904840c1c00d599000741001043e100c84000140004030701c00c22030b0103000d06e00480507640a810740e451000201d070080003104d500078200300c0044001c640a0b0945942a01030600d004031003110031001d410890390f01b25a200f000d840c400d82c007481380d943d09104101c06800141c4800c11840e04501c0f0f440d50340c4c010114007404000302640000d0800519003041c6c9140301c241c034020004545242010044600e0901400c600418904001010400c01c0c100d00215960460043c2c0f0700c690030b103020b001e0b980c0d03c92a951200d0301e440755000038038020248140d51080041d41203054072080c05100090600e940d01c00700380c0840d400503003c1c078003003180c50081d5080e0f1a400d0a0441800c00740403603000180c0aa43d6110342e100344095821510025244c010607000c2d16242c204100f64040201d04400d407492524816030071900c0c000121240b03080aa1000601e02c001e0305092440584103070040540d54841d54400c45076100c900420403880b01c5c1049 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 423969613 1250 423968363 423968383
    0x9060121030203031503010902031501080d1d0d14030d2a05180a150c060f060602070506161403040603050c0f070602070c08010623090103030e011d0303120405 70
    0x540c85080c5614029a0381c00b0181c440294007403040f84584d4165002d501040242d54050260384403a0890241011002802d20951a00703001303185030400707042c3c801e00185403c94540c1c1400000c18440030240301a10028001c03c80318580700500200a031081080982820684500041003a010000d81000b41e0001455880e0300811901341001c039142d0408242e5400e50071210703240c0c00120024000852950711a0721000c809407030452104441c84c1d1020029803501e009007070511406c0c40c501d40000840e2614401c0d8001604903540500c010700e011001059005c000c6e0005009441c1340c0c5e01c0b80400320409030500405903100140c100002034141c020300f40e00100310120726051048088116459105080c1d0080240c1d500058400400100c405010043d041270402007114540750300100c9844041000e0000045920301c0f12214140307001140c2c18140ca030b0603520010f0b01009000103591944051241480c03544203901000e846840810117001c24440d034004051940c2003d0410a0500d40580 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 423970863 1250 423969613 423969659
    0x1801140703020c1513150810050a180b032d010203090c0f01170106020106140312070f0c03080d140a0c02062a03010807030c060219080d090605090601 66
    0x200c0040d01007500807440c20303030441d03065030420f01c8584d0741580c0c0c48842c86410030000e0359801444010485002d18045100c009003d9120341c43e483d20303072200c4040d441e0030f54420030394485010782c070030306c00c802441a01111901c1e0101004c03402c1c0707c5110000341000c0c0b02820b46103401c1d030010100040030103818480c803100030403c8000c40c42c6081c064600e41d05c504400b043c0c2d5005d00520f1f00351a6060340b0402c2c0b990178070030f03034040600410350711050000c0c064a071604c80e15040252050032202940b401140c0c262201c038005680c0b910701006030351030000e0021420010399148050000001c00700f00c4000080811a90741c110028204a080030414003916016201865243c508031009245030b40001d2043d40001c100754200e25621900e41010302000c05028440021000100000540a00c00503442e801d9900c0303418001501620754104981d102445140302c0c15011b442144400860401c0c002001001c07520800800c813400642c44800980c0c8042d503980e0302c1584030400401c42c440d9401921274002c1101d03 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 423972113 1250 423970863 423970867
    0x70c0e04080307030b06190801140402180409170c0307030801091a010309050102131d070e060d24030b0f060f061b0c0d240506060a03020309070b180114 67
    0x641c6030740c9194040109407005256071800b0583c0c80d45d84001c01d44404074072940f42da40d4940c50804004003035100a01c1402004090034a443c107a51500b8001e490201c40340d0044d82424548890811010700600d55085d120300040314142e80d0351184c00780c010702d078128840c0021651101d040c5001440700b04140e20003a81c2c103162a003120f1081c8181d5103650f4a444003464085680c840c2400d040740248150440620045102c032030015213100003031142c0141001070120400345580f5410700b9210f01310008403da600003001c208144800d5002e9106c0000303590320b103000104c00c01341480f00381c4c408540c03500181c41042e200e104200203011401e080991004081d14030302c00f501911000b26070640a82704211030800400558003c0c03040c02080021804040180509008000307030420503200d038007110320000b904036005030f04d840036001030080b14002c0001405441c07402d40b5004089000703400145c21070950740210381c3c0004414100e07801800c444403118169559140c1e0300d4002510100820356408030b05c0d241 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 423973363 1250 423972113 423972121
    0x601060c03050d022115130b09011e080d0e2701122d05061513091506091e0515041107240507020f0a1103071703070c0e 53
    0x2100d002c3d162070500c1018050784445d02900142190260501c002c443c24080301e041059544040340221461035044d1a048501c000c4000004150ba104280403030300329610b840104203001007640c2c2d0300c00b0158090070300d20f03d0b1910350441e86d0a06c15004000c1c00040c40e28a01481d45150604890002c40081480184c03803080042260040c2d810500c00c510f240350100e8262800d02040c3c850164904201d600c54485102c04001e51028006484006444078410070380010100c0c0c640140c1d260320034000410140080c04d2034031501e0050400b03080201e820350700c0e200007c00403007901d020750809030000c0c02c00829012400704001d01d20b1140030001100e0681010140281111040e41501c06024192000300750b40c10000640742040c880d400005001543e4640072103403244020072100128100b0000078040c0c2d890311603003203a075020039074980e02c1240c0180c00d0440000c0d103168001c6030710b4080130b0141c40e10301b596808000f02402c1d50003003800b000e800004454040020004140c2e002e000d04010810725820 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 423974613 1250 423973363 423973367
    0xe03030703090501300203071119083103210e0609030a08070c0f3005071a0c010b010819200309100e010e0d03051b07140601060c03 58
    0x1d20f119860601c1902c075189018840031511205002c80b2000e0f83c98042492035038000020740c0308480b030000090700112040004400422410740c001c80217051100c218003a921908080c1c0e0180303280ea8400100030364204549010b03002a80c0c0091210750b0701415080c51800c100b03212007006c0d4204240d610b50b2800e1030742d03581c0c0c01c503410300403030403040d0307544c588074070b1802c2c0441d14050026501401403d0041001410440440024001d5604007042080d12668800040d0101319401407078420140c003131100c0149207e0103189180310a0300030703c221070134a55501501c1041107031804030504480c5002a100320903110034040d055500d02e0a1a105040e450945403038081e0343c528a0300088000c1e01c0301d44c040c540c81c20300c001580c1c0c6020589003aa43d2030500104c815941c2d902e02203414030035410000424070348a4184102d8a1980070359000c0c1410400d001800c5008000081c0b6100044244d28500c100c182214005003d2152151a00c031000154440c601d528061050b4046e20410030350744032550000b0307 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 423975863 1250 423974613 423974627
    0x702100813151103091f0203010f0314070f12050715020601051314070f030f200a030f1d1c020706050f0735070f03080603150f06010e03030703 63
    0x6078108030480d0032084402d501c44040c020350001c140c0040d1011040c8081240701003900c105880448100d0740d04244100504010b0740000d00c9941a03036070500400f04045022241c07000140c025a5050710b11464507414901c3c000c2c036a40c1c000c0741d5620206440c0c0820000c0c00c0081078058510f640c110800c3d9000404003e69403181406841d0213055840140d18840100e9044a18910710704004802c440c0b0f06804010049a00007000c100040e00341140038584040c0391060b9034081c0140140404a00f0140c070508143ea03111007694001c043c0e0b607040c00c241d0100035101d401d00713003071803031250580d0015000902881d00c2d03081d20465821800c142e0101032041e40024480c01100d446040079910b481040d041c40c000360060328409010a10a10440304542113600040139411020704040c407502c8c0d80c0004000103501803004018038040b0124280d00120b801000b005510000c010304442000b8280c0c01c800b8001a415520f0b401e986403100103000480da005903034220b00a1003600194108031030380d10020160 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 423977113 1250 423975863 423975901
    0x203090f241308061f090506010804020f030a0602040308040e01051017100503100c020708010e07030b1f0308031608070c0f02010e030703080d0e16091a1507021008 72
    0x12000095001030404040b00c0000051100b1010f44007203280920442440b100d900c202c096645004103400302c0c01ca02c00d4420315005c1e61041e0750320740032640c0c3d80d0300340504c00c6403a0144c141d041c4200c1040e100084c10a00003000954480c0780030307039140ca01d8210300c0e01c820201a08440d104a5019412022a9501280a81141c541240040a20303102d001c0603181e9000305e80c1086416000d00d02807059582d440c1e0300503c0b038800c2d4035801c841c1840d54070580b5900f2624280107420f5150031031101000401c0c542c60903175401c80009180c0d550084180501071b000c00600c1e600c100c2d040380b0084104200d070722650005080c079441604101e0301c80e141580f0003c100143c031210003007503070032414106425a4810b610f440c0310580003408aa002c1c035241d0401801c1508984100d00342c040c02d0400d5503031782ca000880c00c0c9074010541825170107910301701004480549800c03105c126100f2140c46211907035581d210b0341115011140790181b03580d000540107115848180100d80c00601102405200e40ca005112324080c103 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 423978363 1250 423977113 423977179
    0x12040308040c090c0503040b01080c06090d110904050a051507090b0a120e10051501090b1606020a080109181104091103010504050d172a1201060203090f 67
    0x2103075885103000700350b01c90030341c00c08145180b41504125030660000000c41c0a00e000d103815441681e44d81c8145a0f8034400040d240b070300701e00140002c800c1800d01050b82102c1c0740c420300420482d0130300c0c0c030003060380c1e81821030b0190340a038060f036200414014180300c003070592400180425424a0000c0e0098010002440380c8c80d5070440008540a0b164414001d280c4400650b8405010345001100201d903542c00c0c044804581a29090110303440c8000d0061840e2146010384400424516100c00400c941c1c1002108400c1d1030075441c0c4510001e015440100a0070386980c8500c565941448152802c9406c11604030716400c01c40507060010450445201c450031f02c045a01140e00c038a42c1c40d107d291850031042c125010760808050204100c00400c143c20b101180390786242424803003490b400720b03c600a40d01c801c2c100646082d040700c3c000403070090070303008040c202403145403613131855000d403000209a00000c01a000443c003201a4500b40103804100e0720121132960042d40b120002c8000c0c20610012010 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 423979613 1250 423978363 423978377
    0x1020d1202070b0c09130b030d0c020307031703040c12020d0618140102070b0702120301060c020d08130e0a1505090703090b01080c101b0b0714180f06120403 69
    0x41084103640450304030582c450b0941d80c99040c1806915039540000c21290700c50440185201c10451541c45050a0740a00500402072481c0041c415036038680d0f0103d05981600900102101181080d0340d0b802060051868103542d0786441e003002c1c240001030f0f401080580c5086800c0c1e602503503039001804c200320303005036000802840444901c0c11240100d48010b0a40c00060301d9003034004010b5000e45289401585060200c4e9101a81280c540700782030200c00c09010f0500051000c0c80c403803d4040c241e14405031890a03202610f031034211940c0c0020704142d0341441420f009200b00e403139800320140c0020b110107041c0b09810702c04201d4109010035006450003210b05400050741c082c8240c00c040940d81d0030662010440d40c40e1040380d07031201480003565010300440d45211003124812881483c04240e80ca500f2003402401e60703241412008003500c2c03081004185052900d0103114540105903500340201030710f00904911003400100302540210034414141880764440c401c0c5070ba800554440e40c0340c42d01ca0 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 423980863 1250 423979613 423979637
    0x1051809160305030903010c030c08010e270105070216180b060d090b040b0601090b190c08030117190b16020709050a0b1c0305041e170d090f0501020d 66
    0x510707090402641c01c0c441180d440000050000200040c8481c4600713400038808a40d00010a5044e205000c294400081d0f01200400002d01aa40350340e400000100b00d55081f00300e114441c80300c5000502c103c012030b95583c014004216010403c60202960b07610361104024a0705035044103030350b6080500f0300c0c699150910507000341d5440f801c4507005c44c500d480070096622541002a98440c04460841c0c024901c2c40c0800e41c1903005142940440e0001210700741340c010503805e49546400154154805d000761007072081c0008058001031030280030741c032600701400300c0c0443c00c1a1409400305006c0303640034880c00c0f071000407880140d90390754021102c070343c00103181442c070408a10b841d005a0001d10030030710303200510601030b000c2e8001d03101d00780c0100e03101c043c0c3c030034841104020032400403c01004184100b004100076541840c5003880c4540402070084805d91307035284070084102c0c1d08692005a0403080031130350b02035045030200707014100100d040440e15040c540080d5403040b494000600b0301c04501000 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 423982113 1250 423980863 423980881
    0x1020d0f0e010212030f180f07031103030d05041b09090c032603090c010f0e0a061407020406030501091403040f0e060d1a07020706021501051c1a04030215010518 71
    0x4d69144a51111907a40d02d44141e210000000540d00e4200600070b0f40d4040020500000315010a03038491382c0544442441e55603403502e5103106010064060000f480b6403500f00880f4401d4034440d40c01601072002100401044070402d6005030850000c00d440c00c2c08150100300700c581e4490543c1d0740144114071840700c0301410009180f19000d140000c800010400880240204080500391401e0700c0f03140c4509400003041e1034065007448030503040707010040300f00091845900e0200e442c0a565820314030f0444103070007140c04e9130201e0304280c40c00c1e0345450708002041550302c000401450140d02440c141070400c5645100c1c8843c500c1032001014400022130100ea5544601c1c01c0c40540c45204195510349510300302030503080455080015005252b80002c0280c00401c0080c0c1007003241e14000b05681c01c1004001c0850141c03003920099442000a00d00052103490f102c02159418151382d501d40d15240c50000c1c5068411000368028010f400e004001c2074903a060100940c1d51403c081640c82c0d52380c1810 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 423983363 1250 423982113 423982123
    0x10c0914060702090a0b0109060f0f120b0406061d0612040b0402061209150603032b020904020c2506080103030c1a07051c1505010f0e100504080c01020d0f0e0102 71
    0x41c0d0312007914424040170b000c45520490031240203032100010a0307641ca009441c2c4440c41c084101c00f00781c034180e000a41030711455000100d6903403c00001407000d000c6000c181125003076007041c0c0104011010411b060180b0354000454160211803942c6001d60401800d05c41c003401900003042c0208020126003150b4901c0240e802210380e0300440c00d110b02e418508030303680c4e01320780500381010b00ea10300215140e41004002c41c3e02083c0707000380c0305200680481152480c24400e02c1c543d194a40e0a00a4621a940c0d0380020403103100503a00504407041500012295030700c06541c0c0c104883d84140081003441d0b00600c80c90704580d09420012050741050914009901c1143c0010519020643c10011641e40001c0601483c04103450500034506c81c1c44040d50485084c09030403098000031300c0040003d0f611a050001d43c81e501032428411a0b0740507400b03d5602000c1003c0700002c2800070409001c10300041210015240e002d20041c1402105050042c0801c1c21517400030007001158010b1040907402001 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 423984613 1250 423983363 423983377
    0x2070e040c1206050f070f020615030705040903051905040509010b0906070f0c230904020f060c0d020a1104020304030c1506030b04080903070f0b1c06090e0f0c03010c091406 76
    0x60700b0146100e81c80e00c0390041104503800d510114144010400e000e1251407001400c0341150000c0019440b00b280451071001130882b1150315118004002c101500d40b80955040188a81c036201d407116152a141150549044100c00c03c001c1d0a0008000c10781e1244111411603521107080c03695161000081049e0f482002000b800e079101d550903400820807086a841d0850f00400b21580041c0ba51101c02c440484800b2041540705011202190240c50541400c62014600030940c0d40380844911210b4280041e01d025a005a013015800e2030030b01601000c440c0003c01e08460442c81d6103031070707540501202100c1001409150f844580000e4112650740140003540d00030f00051400d141a2078040005e5000d91081c0c0c1c0a40a02500080e8421362030840c01c05441c11580094202107080b006240307a4100c580317103009400c1d1035800008205202e4418450200021f1024051001465a0092400c4e0308240900c0c0a80c1c03414501c41c4002d42d10245050603078220742c40340307503200c690100000c0035401040 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 423985863 1250 423984613 423984629
    0x10e0606040305012a301404060c020c04111b030c0111031503070b0d020a0203042403060f060e060c0a120903051606050d0507090f170105010806010602070e040c 71
    0x703500100d40117000750507100c1400e01c0d944403852040050001c440d000f4403040c11003914845422540404107003808003101d170702c4851000181c0045000c02c0780c801090169001c4c0c0303955a407148032204090b41407005211034101580c00740030001e148914003600e40324104900c50182c110340000082c520302801141d28000c0204000d010102071000701000aa00540d0442c0c40b00c090700c0402e41c01820b020584108480391040040d0501b10b0390010b41c0003a511084900302140010040440c5104149480c09880843e0740c00b0704c501c00c01e50110150171111590800b5401c460a448100000d55119412040080c0c007650841d4440c100702a06038038046948000600e00c40c00100d10b10105544803003e04201c7e030103041225448901c02178540c0000350346004120010b42c04100c0c840501b1200d07000f10307400544030301e883c90302560f807001c0c3c5021815084e00a0b80c2808410005c5c03106100c424010706015004500c0600004d5141c010040e6844002d40b00c0e08810410301d100117400c1c030401c1440000100f800d1 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 423987113 1250 423985863 423985871
    0x81c0c0201200d02060907060203040e0a020405090a0c0323130311030c030a0f030b09040605090a15150f0b07020d15050c04030308091f1505040212040201080903070803010e060604030501 82
    0x34035103183c1c40b10400195034005100c0e01c800164400000540d6200311426078014524190238181703440e40b0000c0c0204030100b03694080000003118ec45103081030f0302c01d03c07403000001900c0c60b04440040070780361081440e840d1344420341884440341051482007a0050503003060702c01c0c180014034003034405002500781a0700501000c2040203040c81c001c001405812030b035a9034110031a00d0b25405600711106c00c0760f503a0700400a41c000500045142c1d003c5a000b0312480e0480d81c1080d0b0301d5841c24110f6149000d4030200f6078443c14414034002c15200c080000d080c80902ea0144c49041800000c1070340580d50001e48511100c032141800e2042d84041c0311001109404188070900c1d120700f400e20154002d12080700020b07001c2001808021001c510032402e580c3d070403010303090f2840703116049001c0c0000c011420503045a0404c001010b50b2280300401045805400d58007203881c050001400319803000704440010380081142c4400901817104982c155810038900d405151600c502050180c000ca0704028840e6280c = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 423988363 1250 423987113 423987167
    0x1021609140c130e10120c030227060d02240705120a081902041806080d03060806070f02010902090103060e0601050111030406030911090f0907081c0c0201 68
    0x20340e400120301c0c0205041d0a40880d11140100c1c191442044282142014520814440c00c0c000d644401d0b040211280c600846944440e41c4034002d81c1d081100720707403001c0d44035020011814440a59841d10700404c0c441c0030807910700311180342955070040455108801003042c1c0c0046654640204114403c0f03412828880075002c030481d041d82d4014282070301c241c424225070000340352404d8111486002650380341c1d101030302e8840440ca09040d0300318001d0842d0f44c09000c04079244032618240c0051030040100861010720b040f072a1800c00d9000b0030103608060400200f804580d900051240d0061542c0ca040e04460030405000c074010004550000e6205c00d131000004203200040e0410749071414507000743d9180366607403001510034117160440d803111500144010007030903000f540401c02050144480e160114401000201032850841e502c01c500d0001e801885000903007000501c0c040c14804000b411881c4141011101a6000050a50030000307484000c0c811640709041541448901090b191413105d5 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 423989613 1250 423988363 423988379
    0x61a0a081012120201050a0207021e01170c210115120b100807020f010c0e040e010612030314072109021c080306040e07030b0c0901020f1002030601030f020304021806010216 76
    0xc883c090400660800c0041080e038015072084401142d40140701d001d2826403640200c4003103010b48405411b015403040611006540050403a11984d128440c003545e0740c40c160030200700d6000b107454801c04800c1c490010700598944103002042010340b81000310341c41e1202401a00902084085160800d2034130790800c000c99001542c0a00401b9103400362250040300c503082ca8201c0341d0000090780050b005810703007800790a1a45c040e000c1c507a16000003280c140c1d220010014008801e000450001c6ea44030a2520307194411300506401803440d00d042204d440c864400c104c2200f000b410f90140203952100300d1011561106801085150668140c0c0e10b045075070300b041072558108503100c038011030130444003221410000c55110143c03688140030000c04c0d12151040c0e04141c1040280d81c0c150311410003d00c0500070200a4101c05003040000980d480c9030080004081e14080140401898014030620005a45201a44d40311a80f408039001c095911100100d141119901c080c24241c550740c0d101141d040 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 423990863 1250 423989613 423989633
    0xa0804060f030e15040320120d110a210209030a030e0a08120d05040c03170301061704030203090f0301021b0106030611070c120807060606050d061a0a081012 69
    0xc80d29440c01c1010080403100162039401c1d0862849004c1c481400040000c1d002c0d0143e040d02894041910300c11403642020585040c44541d04600e08003004500c1506500c3c07580188807019a42c203412500b01010684040c2145048000c442c810b05442c4448440c0c00c040ca5043c1c80150000504465003c2070070306002d41600210845580121080040802e0140c030001761100c401c14201c0003646000e01401441d001001c02510071240d0707064181f40080481d01c110303031020482254240321580c1e5450060094080f11080700302091000c80b103420480030039000310581d000540140d9290602100070b000090092080c0f6282d600024131420281c0c1d007040b01540401d00b030300d03c500010000385050b074004038542d016800006108008090003030082403100c0c600e0209071785c42040c8403424441550f68420a864281e00480c00107035000c54801003c9031140240e000502c0207964a01881802190200441c03181e000c020b01400091000711b04c0c641c0c2120380381d000070118001380c500c04005620f051480d003 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 423992113 1250 423990863 423990887
    0x503060f09152406040f0b0c0c03070308030901060815010302090423010e1533150a021b06030109020a050c010e010b0a090b09060d110909071a03040c0b03090a080406 73
    0x204010f00541004c004482c10345601e0900c0c41c10030b07844d1103c03070341c01c9901c40b00394003215004d40400310a0b5503c003004024080d40c0304000d81e544914010800c2030849100d0340c40b02c2015449103a49075890380380c1d1030056066a806541c1c562086d50b8609000d98800b8503204440110441d003504061503d40650100d101050400d0580da0303000d4000d503030010300c2601a111326403621100302c901d41c1d0390124400321140401201c010305510340d10303c0c0d001402404549441c002d8901c00040c015141a50611145800c016461044000c80c804131002c510140414010001c40c190b0006072083d0700d038007075400d850803452800300038803280064024041c064146109050302030401c0d01c0c80415003030358600400c0001440904010126603540b000c00c0f140700204081919010f103502804651038072501b203605d1041d520a002070540500e000c3d203071510303d0b510807a80c181811040c0140070014143c106403400311604003002e9612515200115403c02810900080190200060010300290403100c1c1100ca = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 423993363 1250 423992113 423992161
    0x90806060420090102030c010e0a0219150c051c02071502070506031303170709090605121b0103090213021207080108101112090a030f03090b0a150b04030605070f05040311090c0409060b0405030d090503060f0915 92
    0x5a2100d000f01030341d5457181402401d0b4011000d00004a04000c00c808841140d4007900d130003115025180d540f510001c500360b0340040041c0e04c000b01402021118005e6100400054442080f4050203c00c80c0740c68010000b40303240e18800c8040c02d1011a80320f034000c007d403c1d0b00203100340c03200f0010094182c001d521440c0c01c4a500b41c0c6140c0001d05080c0074508440c1228502006041d00c846410b144c00004c01e40304965881400b414058004a4088880c101d481404914001c0a0a14072410040e02d4842200321001c2050700b4401c640c8001740113060b44581100171081c02103071003d240c82a205008015800600c3d00320f5000c9000410320140b41c2120703016141d191914021410b40d12001c9959204074000070704904001e00c0354004c0340c20103800144d4061020300c1180c3c20903803107800e21816141c4962001e9181c03d030105080c01289402d1180c000008018140080d0007894500441d803940b1004000740400800040050030382c1e0410322201020107051040317a4124a4000b1480482030401085000 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 423994613 1250 423993363 423993389
    0xa140c061204021306050d030f0201110a03020c010f0239011b08090601030b0f0a090c0f1409010e0105060706020c030406090806060420090102030c010e0a0219150c051c0207 76
    0x13640182510840b41581d03400303050403005040e2510292030302c450340d900c1e04045640e2213030340b2480d0740545000f4100d80c5a16a5015079a03218580c1030601b5509102c040c024098410400101403400342e140e02904c50b034482d1607c041020064440901841484131562115402c0c01c041958145881c041c1e403200250513280c625003a01e0711301c1481e9458009010041886c9183d0011940134540600900c1d844980a4004542404160740e622011704080d1722a02080c1e035844014030010000b4001001c06000c141c0c0c50130495031401641c40e81604041c46201d004041c005524010b00849404403050990010116903445070b6410340105640181c0c0700b6004103000d540040fa295240034003409600005001500d10769914403449144581d00019005055210400040080e44000e0240d2101d00d45240d02801e141202d50041c030501944040c03155400106003107041c407031f54048038030014142d0618541f030741380c600c02da03d4114905664200c0c00c2005160001a146c1c5480d80040c048042c1c50304184540 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 423995863 1250 423994613 423994639
    0x130305060c0703020d0c110a0f06030624080c1303210c150e0307020d0803060102011b0504030b0a060b0c010b010f0f0e0f030102040e090328020a140c06120402 70
    0x41c0d26010b40c0400070f0044e0070184000d000d2a1003402d4501c58280607000007200d07244120002041e05100d580011131103441c4a00410181e0303058403030000141380740d0404543c0f8188007245400c40710b24507401c8106005041011480030101d000aa910403647c1850a030403d584a003800807904124075540c1101c1e480c50341d1810103241c480c8065000070790b40000a440c2c402d042000541c090300d200624014140b0040c000000917981e8001d14088007402078500643d2801c004000a01790340360141c0744486401c0c1100c1040c03a459001e4100e0b4100c80d005580b034411a05c4851007100580b00e26400014811404108070b1003200c010f600c90080e01c0000d894051084440d01c10035941ca2000e41c00744030109100b4612030b0070a08001d1003101c3d001300000d000510b440d4940b403500030042c0b816642d800e041e5001140d01c12100c60080d420b2a9444c5441c010300c1840009603000942d115010940200381103110b1102c07000d240b10030040c100b80b50300e005115603118800c600300b2901c84d800c02c0b18241c1c41080c03030240003 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 423997113 1250 423995863 423995881
    0x140d0b0d20011b110f03030f03040606050904050a0b0a180803160801080c060d0209031c020c01050316050c0c100e01030b04090503070f050c0409030903032709090501060b13030506 79
    0x1211520b0580141140815013a103a004402e0b41000807190031004110852a440e50144002c001004107908425101d050904000c01164115046135000c2c82201c420b01c004594001003820b04940c1c0b01d0705000c081e65030f1606000151141000212218002445010411003901c0145109010149910003844921074086a00f54000e101c1c0000c55000401c0d10034507401d2800003080b40b00300545001d0315052064000c28a41042840000c10195480c0424924503a060208003000042442c1660030350078244180800074011743c183c40f0900c02d00040d4503002c00c07028029200004030080c100b032254004140054846d0006804840c006441c100c1401c203140307018844c8402582d0403100850803e01141d80d400707006500c03c5010b80d040c0c07050641ca1001940c56009401c8818469650b0b205402d140d0324000e08201c8040380b10f0880040d0814203800c40010304190041115500c01010038680c0351410f0090050007240c0100805050014440c801d0a195007a030504403441141210102d42c1c0720456 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 423998363 1250 423997113 423997127
    0xc030605092e18080d0605031009122105090d09061403010308030709080f150906070e091b040e06010e100e06070c09140702010615140d0b0d2001 64
    0x2041d0000000c41c5140c18095143c1d800f01c50720031800c01d03120201020380d44801c14140c020110a9400c80d88802060001d030401f800515009201030740e0503c08582c02d903941c8040e4002e609000c004001c0c084000c46103018251b03499200701a2500c108001078100071000c283c55940b14061280072500c9420001805480307080c4203a42450f1000140742540d007182e49142c607580c0003521940802ca82c041000ca01ea040c1400003058051030700000708428a1441d481c41c001000c014441c6005400103801c00c030000e83c008010391a1500300302d40ca1040341e07803100c400c07400f15900e0001e400d640040c04900414080c280c000e034240140c400740c0b10a180c84440e2001c12400d51604d01c41c3d4000a00c00416016040c10050094000030744280c02020f80591120804011038440302daa04031141d0b101c5041c0184650280f00e03440107000d081d007a00c000e20400f041c000e0002c4000d0580304024040000e0038108400d05540f0041481170014042544449282030103002c3c20580e144444250305d0b0901059265802042 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 423999613 1250 423998363 423998413
    0x609060c081518150a0b03060109050a2103031e05040c080303040c090906060b0c06070915050909060d02190305105103110301020a08220c03060509 65
    0x100300001c580006840044594003d031134400800c840d14030741c0d10140e98191000d8013800340c5040c080d44a25081000401d81c8400c1e038411030141c0f100704010322546c980307100f100380e1341e80c0c2c10900e481c0d0300001072030100c2c010f0040b02004800400c0700030b100c22844003681c010601403130003014040000c1c0e8403500c550b0340341d102c01d6034010004401c210040107000c110b03403c80450540582d01c00100140e0b0f40980900d194440010f602064120740e041144143d04540c0810142c1410481b034200c110807464083d009100f0b051015120f403542c080000c44590ba40341c1010203407075001d800c0d05400f05240203102d0b01640940022181c07030183c0f4501c08000800b40c4a9103a50411300c49180390f420304d01083c58a00e48440c10010a2080d080e450414603000030b10491401d03240f0401d10503202c180c0345051940400d100405000d11a034010006049404e81c03040380190414200180d82c401a90010020769158003e880014070903240204000b0500055074400c0b81701c1c1200809480c80c0e0540501c2070105d4400c009 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 424000863 1250 423999613 423999619
    0x114090102030307080711011a10020a020105030a0207140f0609150609010509072705010f08010806040b0c040305010606021e0d0c14030c03040f060201110708031506070609060c0815 80
    0x3c40080c0407144250f0720650000c505050a800810300014102e0a58000781d02c03040582c0e40c8086241c605040000b2101e8610380184040d142030007441d40004c081e440041d003c045003076004206c4800b03000020140d540b050900108843c01c0600003400c640e241c8904030340803142402502c895100c1084001c0c5a135200e14401400c0c41c840b682844200f052500d0041d240070208030941500075101c41d52000c2c08180c1c45801038415000615000004002e41c4040e80104100403e40c001044107481c000740341030b0880c0e40505038450596980c0c4510000780203a920150880d824a800016104c0d008228460000c222001d00000c0c0381c007008034107070f44090038002540040d001c105c0ca80c000c81c49110b407015a456103039085e00d01d40804c42c1d03c141c2c03558000307810041050245032820040103409102d02c4045002d034044143c1400205d44402185000051002e100b103403001d12400700c0c40e0b4981040f40c0440b50f004e441040713402d8103414180f000700643e803120f6011542d0b1102061625030805461082c2e45001 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 424002113 1250 424000863 424000867
    0x6040b0a0e0403030c0c060c1701120503190201140403120f1b031e0c1214010506030c181c060506151602040b0d050a0c050103020406090e1b0f0702011409010203 71
    0x3503603013140101a941c03018010004003200000000e182ca000b41c2a40007200d940d01c0d52504206c8900049001041e40283c00c01009500388400003640841910316203c1440180086560496400c0c0e024001f0000c1030b960301207003003081004042d00310441509001c06840f08000c1c00a1101000b81100c02e07404404203001048030551044034400c1d040045a25030010640096003100c5001c2400d032907004200c54041200b01903402010002e1344181c1d4501700a1802c2a0200d524180c00305525100207004000c1c5854000713071088442d10400c00c0c012005001400202e240c800198802d614000401422a0780e2030401020a4003850b01c001c41110050a040d0318034034042000344480c06581d0341007c103e0300952a01106400c03680c8030301980d543c070b9000c2c1c40940854509450604000c85040c1c00050502d8070603c018419654021003e01c29990700c10b4114046841d440c0120300520186003140388008000500000100100c401810314103100380c07141280c02d1425142142e550080782015030043e881 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 424003363 1250 424002113 424002121
    0x1211030a09180f0f0c170610361d06030613140a03051b010c0503040201030f0e01060b041d0c030c160b090601050913021e0a091406040b0a0e 62
    0x24407101c2d148050441d21000842c0c0407143c48080581e141c518080003010354075180d003e10b00b07801036201c414982442030f40024038940340b0005404030040c0340c0c070070741040a00b07a40c600e00700c0f0341350401c50000820800c0003402c0c0d12401c2035608030401c1c00c1c00b1301d10310184002800b041401884100e64000c0700c1c002d0140405030345001014040c00b008280c19100344410205070308601c0001e0140c0e1b0501402076444540d200d603040e9002e03c130104c41c1080810700307a2508040019007548041034a41041e824a80418603d81c5083c400c006001c800c90b1490700795191503000241e140301c14004104962a1100c05000c680420600c250441e00844035800300800410010f4040e10384900145441001000a0070541c2d949881d0203070340e0081201e1008955002c031b8014015880d250300700769400003150300788104c038922541c00700d294203d5018a440781715007c2d64060031540e50300030f1948041e14a90104014035400b480d01d503041c0d485c003a00c450b40681d140c660010ba507410510700b514162851184403002e02e8903 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 424004613 1250 424003363 424003379
    0xf050d0b0c0a020c040608060105180f06060a2a0606150203040b07020307031a041106040302030a020d02032401030b010503010e0304140a03020904080903010e011829041211030a09 79
    0x2221502c0141103000302143d554040da594480c0201901d01c1600401f5a50b05000a010300c0300c5003441803820410320341007009035801d004000c07039a0080041e90740350788074103000c90207680340700320590500c8842c1502407591020246041d00c80170064021001032000a540e0808030040d4861800e10b000160010403051002000d01801400d04601c0542124000c503502c1e1140600b0001e0940410440b141c00760610091001c11a0049940603080711741d01c0c5410700c2c50340082e944003400c4900034043d111649201040d5502405042040c507061540da090100900d00030340c0410109002c2251003101100022440e400c0520a801c403600710200214589828810940c40505903907552650140c0c81000120041e1249176883d40203030301c604100c54551040004040c2960050303003d80307020340e02d4880c0668880c1448130b0859040d5401030114449070301e080200503c0071001421072780c002501902440200440803462210400315a41c440e882c086030361750130f240c032131040c8806840041c40300a03003404900c0c = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 424005863 1250 424004613 424004617
    0x120b070810121a1317090f120a05010c0c03021504030503070503040606270506191e0305250e0f040308070c12050a0201150503070308090d05160f050d0b0c 68
    0x80c0036140000780c0c01020380b8414200c50080710401072044c5800258000c10203800300021800d0001d5202d90706150707281c000315440340558407049110b0400342185d10068031051050105180e0020003e002d10400d0f004040c015003800801100144113007105032003501241000384e8003403589a62900d103141c03120801150141c001400a0b20303210f03940d00c1300040054080f5030b0719030b03002d04a0134002031034085180d60108641c40142030a004040c0c80003440071a03084025040252190b240703100140e00c0c10305444800304a40c60704014405c0c400d035400f070285042c1600c5007400c0607028044c00d003c1592502c501001c60300302514603210000f554400b080c0041d02803c101c540c440e009282a40e5907070325075210030410682000c41c184c080364001400250407542800381032501239901110480c1c0758030b802c000c250303104220b02c00034200c000085101101e41c1c0d52821a60300058000085550030000740303702c600426003038854400c4060202d400010542400070b410180c242c0c01400080350f503034649a0041c655 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 424007113 1250 424005863 424005899
    0xd021b0a0b04062a052a010206010603020d06050306130611071101031d0d120606090f090207110603041a2409040201120f15270209010c020901120b070810 68
    0x407411380001c060202e943c184544a034280130300f00034081483c200000840d5480000c44c20021a103d5018201e00c80c0d03000145075044806034640113a03181c1c40c43c0492802840c41d504400d926004084c103210f15101100e00f083c0111340a420100030a122004544c0e081c0c1c0700e9140028040d0350096a03641e420b40c000c0d80110008442a055045401034005006090050b14803c9502107a50025003404005041c8074030b02c081c00b02ea0400100403401c0080d800340a0240d0312481c0041900000c40800f0801c580090410a00020b42030300d031a03080ca40350905000d002c1c1d500c00e550b8504400005032100c0d904030030000802e419030000006201c03a0006004c15010014000c2c0d041c0071003100c66006045c2588a0a102c0789446000050003851075400d1000390800c950021412222070019110304030742c11203087e200c0c014501c00041e552700003080160b03074882c0b4600d4040d600c840310400014204202c2407100c0302592040401051980d2540b800313031800b0320240c0d030b110b034080ca04080a1044d02c0c2005054840 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 424008363 1250 424007113 424007147
    0x50702031915090f05010b030f15150405010312031107150f06080f1506030a050d20030d0e010c030e0303070c05121b10061508040303020c0d021b0a0b0406 68
    0x2400035202d04050314040c0404a034286074180d544002e0110a125912030340608030050700c0d0b03440507034080c1c41d514851103020500c00700720100416400c1039042900031107064041c2c020300c543d40e940d091071500030360351b01482c501003401d140308d001200d1000000c50307002d150311044003081145174020740380050801642c0251890b680d01004100c503802088000548900c04004007020080d0040d0103400850181485019900c880c170302e0b400240c0040345842445c106071400e11040c04482031201444a044180f00a15020010b000300c49040700380c000000114068009200c12405880106c040750f14202d0080c50940080c004600564403641c0000160341c000d204950b1103030624641882254031a0031004079070740545018500e04801805202000b50503c40c08004152901c1048029030074072040110411004200060406002b03605880b4114600130444c1c0501e0008000a03540d50143c403070240500303003003503d601071034070703108241030140d81c503c00d00181000c2c075010341a55550107010900403 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 424009613 1250 424008363 424008383
    0x630041506261501090605031506280b0d02180303090a060f0909020c0307050c090708220807060609050c0a050d020306060403141f050105013002040b18010507020319 73
    0x10b003520540c3c81d01800c030040002607074514010802d4603001c06440b00b60340061010040090f656a0450744006000310902c1d541c1d40703207407040328089040b42c003504001c8a078140403d0202042007540d016000c100340001030072044450007010143c1d02d00903484030a0b84582007081c140300180c80b820484816001a09120840d191070348043c1c0c0580c4c2280d04805060380c00400c116041c000200303d040c40517503065604060038141250020a0140c0041c00030418015004900c8203102d20391340e5440c0ba581e0000031450722040c2a00e0060054180ba1185140c071600f800f001c1803a01000900b25003a80103151102440d26840c4102d06010b500000e00859114070b0521002002c15880c240c100c1200c80950041e00b50710b0480c1d03a411090015066039440c0640c5807030010300c17003030b60031a5154018502288680e00140308003855030b031038041c0c004840742d0350038004900000c0ca0001d041c05443c0d20740d400004030181c1303403070711b40115003d004100300607502d64000350074000424094080e17040c1090282c66062 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 424010863 1250 424009613 424009633
    0x12060601030f1d0c04060b030705030f0702030f0c0105060a0506030c0403260f04030c090203040804060c2f0a15020c010809010f050708010e06030604030e063004150626 74
    0x55549012200f41501d5130410f41d0100d41a2406108000142401c940c105045080c1000700030603e006c010407ca81c2072030320001184a06000300309644a0b419059080c603030364529100482d010701025a2254000d0a26803800f0643e40b81c11001d507803051031003040c84c2d805c0074510b4580c217203900d0041601d07207504102c180303040c0c1850386190001c1c02c0c440d00002005613075920314944514101e202d9405450154818010702001650000031502280e00d5442d01500d03031702c0d25040800c150443c603040b0030001e072044510310300581341d41c00b0b407221902c50803184100c0d22642d4407856030000c41c00302c855000682040400e6909907008071041500044043c0000a06100d40c0851a04544003513030090040f41014004000314032102d41010341c890400e4000d450345042c95a00a082034460000c05031083d0008078020140a050582214040c0643c8080c13041d84041e400000304840b5080d2416a0740c031011000522074851103008820450321560b070915052020305200d0f050f40368070a001b01d1828001c841e541 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 424012113 1250 424010863 424010891
    0x90a0b090f22230604140307020d080711040501080d03060506031e040c080a05060604050a0b010c08090612010902040618030c12030507060f1e060509150609060c06090c12060601030f 80
    0x1142415003d80014034850525040110762046818a018000c0e4810024103005865031040200fa030360348410700540b81c04081c82c05402e550360781d410a540061900c0000140c60301c000444d64602011a00d04002581d00c410601c13080d403000f01d80d14010000c40c41da002030100240440d95900601500c401e140c0c01d911404140d05020040400703443c15402081403282900d824400c0075000240c2d464204100c80d41c14001034501640c2c8174001d4a028408104480da0342c03203900445e2800e90780c6c0014040b943d81c407080c02c08000e40043c000c04000505c42c231107007181125092106019203401c14040d08041c4d14102e041c010450b4500c200f02d04010040c042880050310b5805900d080102120000c911102000c9044464103600c04501d14a241010020401c54540c64003e54100000803103621000b514900418298800d5100c2c4035001341000403807000c08800845d855002d0001802a80c07103048941003004280416a40249425000407003c80c3c1e43c0d601946c0f0071940100e120b80c001c1000e124a90303030 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 424013363 1250 424012113 424012163
    0x1303051b1f020301151b11031006090203010305160b0f0715140403120218010347031f020706091211060f150d0302010902090a0b090f22 60
    0x800c1c50098020005100121041203a44d00c580389034a40303e0780c41803104c09178000b030b0a49614040c0c01960811120320303484e10244408100840b0f001c0c410300030705590f40d0300500294424442074500313002c4d00c180c1e100506030440c00c480c02c58004202860400350030701c0c9a00c2a503444282d00710380c0d6074580d800300c103003c1c5054042c1c160300d0141c58900a010749070500b4044c240448a001c1500303054070421908e00300313503411440c014807500300b80380c009600914805003540310070b43c0035458003c40c004628400d110200c01145141c0c2d000e800445140d92207003240c2419611425034001c145030000d07420414107074100310707400b60000c54026200802ca0f005140ca814102050a03045074000400640415103070500401c801a005148032101e03949515100c400c0d42d001c540303400511842800c11400032800c0c10f200350051800c1540081104095082428042e0020304c0380361401c60040b00410700081d21802140e0b18184140540040c0900441c0481220b1600d0785c0420000c0b11203801943c03805c201c070702035129 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 424014613 1250 424013363 424013413
    0x601050a0822060f0c18090903140c03090109091806092306090d0804020d030f09152607020a0b0c0412060b040516020a030f050c06090c091303051b 65
    0x1000554400850010826a03060f10054818080060040f0034241d00b80074061003105c1064400040d200400d142c00c507a1071310920b0405000090205041c2f90260010000341403100c026210226440d5444440c502030314004600c0344c5c4d003501284035000200b4125000705a2451080d444880413107507400700f0301032610080715030b03800d5940142e00300b00d03200364204038510b8800380905140105141960006182c0501c4030001410041188654004940a88900000303084002086012030161040080c503c0d201a561007001c01c0b81c0c44e0002c4d10341e014a00c0500d0150800c2d40c00f40441c070284d80c0b100401184c0107881d030070360000100800a010380c4043c43e005480b600c0b8090100359141400d04200076920041c040d8411440e014800c4124990001410b60200360b042c1400f4002460074002558980075a060014042c06003800f080f00c071613004100d001c03031054221b03540300c07164403004e201a4142d03008410040c0441e000f04080060030b03103903400d050b0200016400703d0394910889602000c81c404000 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 424015863 1250 424014613 424014623
    0x705030a0c0e0d060e01112b090b0f06011707050910091a03010315020a02070e0c1e09100306060509040e01090516030b060103050402010c03121d1f02030601050a0822 73
    0x40181000c0c85c42070085100404840d01c4850410005d08c01d401800d2041011070010001d1180f1110740703143d0982c00880c003961b000000b200c25032800324803100010344100c03030240c00140e010041c8010340f0303c0040c0d054050714603542d85d17a0070701a4078018000101113050903101808919400010940811800d1303055041145290b00c2d1a03500d107141c29007500805006902c045070040c401195919400180c01088424100d0328404036103c001e072425151213108100654600500740c071058413001d2500901c895032044d41d0100d0750003000c0b0310840c21a80d0501800c0b000074020000d5410300d1a01da0010040061201c0001030103181540e64545888040150720000c0c203c40c1d44100203000c199190254401001c0c242448245410303400281410070301e0f08002e00f4411220070183e4594683d80c01030340310a0403414107c242000c0f200c3d60329070340d40340403200754494080c44070f907107110070170500940b4098034040e103d150502003d40710544050400411a2a848000c1050b40050540c110170901d94140a8 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 424017113 1250 424015863 424015871
    0x327140a14010e0c06091c030c06090b0712090308010b070c0e0702071d09030f1c0603150b0409050703020120010f0911040b0904140f0102030a050a0b090705030a0c0e0d06 75
    0x110f03100c14188460010310a01c1038100b1300002103030340c49101c10200d031440d144243c14850341c494941078452040c07140c2c015060503c1c01c00031400308240541824080c460f10303160084a546404941400d07150201c00080000321034100410801c1c0b292805014164410041e22002980f61082040144000ca0711a001680403c1007013069000041c4840d0700f4001c042d00c2000640350440b0229503d100701d4401c001442c000050070700b40290107a12505504c010000306202203956410030454002c06c4200001034140fa0080380209460035100f900c17000307940107002c0c1214504d181c005566801030748010004000040c0c000c440786520a2164000d12881c180b00041c500605080542d000303a03091960342d001d40d2030a0210711180d0354071441d0035800390740070107211641821a52980d0034200c1e001c080c1100c82d0300100038020304102c580c20070b9201c2c03904e102e410081c0007654401c00201e00b40955100b004035034100301245800902d031300b0191105105007801e042002d14200031420115156074259800e03603032 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 424018363 1250 424017113 424017131
    0x3020a02030f16121403011e08011410050a03110622060c15050f04111f1e0c0201052d0a080910111b0705120d0327140a1401 55
    0x12100030b0344644440d05c0c0081884c3c15103c81c0040603c010300400b000515003102c401500c008024814001e050340f41d0091100c01c5501c030344000c0d00710007034982101010043c41c0105050800000704d82c212a00090b81000741c49448062045a50001500c211803201c0d0a01440201c1400c2c1500d01c01400e0981c2e4000c4c00807a58181001d0829061901d11401030030b250502404450b520001c50b0420f42052503100074000000010f0030010341e2051f04c40b01c0c8240e1101503010b00350041090084202c20000c1c0b680207100304d020840740e90008001c000c0c0860000d010a0020728001000d00344a04514018200b840001005285c1c01d43c00c040401000140d0030701c10001d102c41c060100c8a03100000160500444419000e40449070040503107041e003c1d0302d107099410224008019600090070301500580010240140d01030301e80c00307100300d074501090806c551000010600a64180c2c4011844240172034440300e03559551801e4812041010140300b500168000700c0c1d840a40e641501007400d00021382c0d040 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 424019613 1250 424018363 424018373
    0x5220605030417090a051002011e0b0a0911030711010b0411070515010308090424030c03020102070e010614030a020d0c05040503070806010803030a05060d051c0905190603020a02030f16 81
    0xb1210f081c50340d07000062142c002c41e5240c2a200009603003044400481742d040c8000c08070300520707440010300d80012030180300b0051161242d000da10b06074416208001815100d60210301614800b50001c01200313400c00004102d01d100d010000704402c1c000d00049003080910000070103a0305d061440c032803103960003d803e404202c070400c0010303040001002040c074a5891915082202c0c022405135a0040c0e8940f16001c480c0d00100110104010b202200340d0031154803418602103954050104038050311540f8008500000a801c413907040b610b696440f90128803003100c1414154001404141aa0f5001d1041480404450007100c070303114002d40e513040c0ca4510307250805140c41102d0380003c850360020b400502c41c143c0c0100c01c40c0c0d841010709030301003001e88400d00464100b2010440c00307021b9003d04400c0602c01d4003000c00b5048407078083c2c1e40d50307440c49498100f08a49c00b000c1d1a0302100d925000241004070301d0003a0050441d23034001d80181d90a2204a20311000036600840d6038214200c0c510101400b048 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 424020863 1250 424019613 424019633
    0x51e03031e04030e09070201020d0911090c0f0d0c0509040c0e101b06020714060c040602010510120f151112010b0c0334030206070801061b03052206050304 68
    0x40da007803030050641059240503000041c2d411001d0302a1058400007036940d8001d40444803440f40ba80e0341000075900c9400c281c600300e400e842401d440391040c1000b00b2558035608003521010815040782d5880c22071078680c0b91006048001d102800d011301880351100a5032544244802044c15442d0403002442c01d004000ca0401d02e10098010300824004038402c034401e031000310054540c00325005036a0b40e120304000c0115500303082c803440700b846000104451080c0356000b4100321a482c1c0c0080c4059103c0d082d0700400480d4901500b58000c80c21071003100401c13510040c404102d4068010a20124007803001001625102c7c000381794041c07400100d000643c0c252100f010300402e01040c5043c10030b2083c40c222903d0344161032070040780750921200710340e10712410814500070303450046125000c5050b0f0b16010b5102c0c841140c141c008203842e90000140c16004449040c2500000d00c0d1664102c0d039165004c3d01e0981041d6448001006901c1c141c801603061107030000d014002c1902c4003902d924207443c01c5c551403 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 424022113 1250 424020863 424020901
    0x209010e0102011850011103040b1e180708010b06041701020408030d1a03060105030d0f02030c15010f060e030705060313150b120f1009051e0303 64
    0x681c50100803241c10040030400d03444d121752200c00048050a4400c02102c0e00d12401d0720030036040940f40d001c61030161805408003401c200c1c11007050b008080c1c09005801c07601544e80000d5018004c00c0010006a681800140c0c00080280d1503003251045808002621300100c07a40e0b00114182c4805014203003040000c0c400601d41640284041c90005020a41ca80140d1140d83d03008400e09601c3c0c65408400c0d0107940151000d5812a9140c40c0d1303040d41100a00300d9031490003400d02506d980c0c1085828080346031070603030b90042d0092108000509040321010694800c078030460000b44546c60200205019440340e5141c10303081070b0215410030100100c4040340c2d601680c18010310301840c138860784002c254001151421078005449507030b100700c4251000d152200003440300000714400314058000b540200285201511140c0d05d10200e1904542d07610a195021105030b4081407c1c0c11880c0702941000780054407407003e44820082c0001401c0800000301d188801350340001c820082448420750041c105 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 424023363 1250 424022113 424022117
    0x3032a1b090e07050103020c07120809041b0e0609031207062a0e0d020f0d151d0307020904210302091c02100c230f0c010e0306070807020106030602030a0209010e01 72
    0x7a80840c00702c419954103681c4185414180c001c00c2410b402d42040c060040280400355001e20780a00c2c9203800c0001c3d41c40255043c2c0302d42e242c00e0030088044001c2030f824030300341003503140d04609024203020840d864010003036007a1f1510030030402484000c00c4a02401819200300400320b96980070904030b52403194502c0c501d000401c00030788012000d80d0300c01060034a40d00152840c15509506002040e028011070861907002154402c610040082c41040c03042d55480f0b901003007060100159907062040c0b508a050801d6038014405070016103461091076070800d10522038040a440b030030720103440348460b25540c0f0010030303401b00f04d0200f00d00300303032100f42e00c1c41028600c000c4521020b03034005840054103e4000c4100720003100510100095601c036184100d070748862003503030104140c4045550342800310280406000b1414512103c0d402801d1003600194001c0c0079041075500c409044800740c0c401404181190740301d180010200c0c0480c8019405581800b0025a071003a1410015100740c12468071981 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 424024613 1250 424023363 424023371
    0x10503060601171906081b1009030809120618010b24090d0c0f0911030c090d1b09050612060714070c0306020a0c0311010c05030103032a1b09 62
    0x1655a070300150400d071550700c940f00c4007001e0300d90448549645a1641d20004860b2400b070b008103074410001001e850503110503e0080481c3c0c0d0318000c0c8000c080d5200d13600c401003201d00d40b080c0009802c81002d000d0514000d007141c90b403502006803081c5055010307201403045c0b9080d422810007845082c0281c0c1040001680e02549140d10b194007900c21102e820410307180e0280c00b040c5e0b888141c3d60005000155500702a002c0a4036032107606800403951984503000003c1c0c90007950304501008482075a00c0b910340c044549040100d000c1c140107a00c03e00c104220b54200010747e1030341c42e0b1709040c001c1c0406401f03102000101c6140c1941031004d503885008002c9010ba00180810112540c0211480b501d04403440f81152202d15a10704103c2c4210300d500020030aa001080200180b170381720040c03099082c0203681e40c2803050700512505080b036001b000349c440095010001840400d0003020301c461064248010521150540d40307200300036225440048444043c20f0070349021080c50308440708050107207940c00b00 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 424025863 1250 424024613 424024621
    0x1302070b07050a030b0a03080d0b010c05100c2114090616031107020405090319050f0406030b13020c0c010315050108011e1503060306060e040b0a15080d110601050306 73
    0x1440c000001007010080000020f0500c880074481d402034242c41030050046244251a032a00401d55000801a040520716040c01c015241d072003107a00c040324640080103440070590b500d601c00042c1802d03a454000344a1003107030510401d4a42806052082c2000c13000280794413480c3c06c0f1140a8078082c0085c6550b5001e0b0041c400f01d01c883e5200000100010304001803500c14034058403010780110b1300d020358858903100420170581ca003c00104540c3c4415151000702141c00b010540d418010001408490901071106020080c002d80c0540c401c2800104840c0c10506034400c480705aa20a42c0c00241581000d030724440d10703507014064191500302c44c403c03810089081900090452038148155400100840c614402000c600880e507000362680d1641c1000b00b40403442c5c0078020b0b0085110403109146003400005650700142183c600640e440080c904090f00c80030300c07400c05032140b402e1420000301036841c0002d180800300304901320b15a080d15983c100303002c01c14046041441c140e11050190300820100 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 424027113 1250 424025863 424025873
    0x103051c03060b0306121c1e090b04060e0f040207140705040513060908090d1b150f0c03030b030f0a110d02030a1209091107061b080c0a03021e040302130207 69
    0x20381d61203c0c0a0319a140141070443c07606203080d1f07000b540c810014070314001c49110a82e012039840d8001259403c445a9507100030411180f101e4148900d0101c070609100034051644503120364008054014600e1014880880c0040c04a0740901401c9424030f0038410003040004003440010020402120200322510300510740102039440c1c00002402c05603203086560422400009540400c000a071030801421540d213400641d02c038051113000c4030030900301000580d00002c0d40441400c0d486540e00e904204103c80801d07680d41c4041c5008900381501e44084030420f46040250f1003141c04aa0010840840c45050140d2000f02c5032050a0250a00503454005030b01c0004212100070740c006004d4402140208040310300003000c0d00b00500035403d00c0c0c407940e283d500e03c3c2d0282c001140281030030064140c5280c0307405180e08140301040049042d120000c1d03a901c5918000d80400001c908001d4034000a41c01180c00301c0140180d44c60100034003003001d00542c20248018041640884000c43c40c080481d150 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 424028363 1250 424027113 424027117
    0xd170702011a06070602040b031305100b06070b09030d0c05030a1a0a12210e0108060303130b130f2d060219020604030204180b0a060608010911120103051c03060b 71
    0x20043c060140001c1c124100000d90341118004e0889210264407801c01c10769000641c0354404081d40d8510500103000c40c0c80804d8803a070641807200500e0346161692964440c00c800f00014498101d0340003d111502da10801401002036885680e690590342c3d00d004518031044498000340c060410358800500d0007203444416040058400368805500380d42864689400c0804203030b540894004403200e82c2c1e581254220401001c83c41091300c61041c05d550321000c1c55134034010f00d0aaa94521104002003000340e81101c0200800d40c0740f00484c155054480513403407040c00c226400031090b030300f00d01001941e8005801b000702146804800c84202e0501e0250000d60781e00c0a0300c2c01d4541c1c1e80c4440390b072a0440d40ca010031100110341c013034001c0c4007101410406500c0016031342015a00004414006422030786280b0881007615000d441d101c4059080411002c0103281c041c1c4d102d0309100040000404131507140c0d103a18000c61040008000110207100740c0340b104141c0180c160245401c0075828008800076000b = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 424029613 1250 424028363 424028411
    0x105030106291305060a0e040b04020304050a020f030309030a05160b07031d0102010213120c0b0a0f111005090304090f0b0a060c06140c090306100e0c1b0d17070201 72
    0xb942074441e034640014454080d0a81e0009034080030000c1c1100c0c542d6005190a50b000400301d0b01044403115200a00003a48421580180290414002840185098210f4000892014044a041c0803030131000c02e01d0310400304010b8440d030b40944e0711207450712401714150016101d00c0f0720f918180750705540c1c0a0728038210f40c000b62071180b5003049041c580f81d100b58181c0d400180c075810b24500303041e03545401e1010b50200f1101500c0341840b064012400d5100d82c1d04844412074540d0b03402c4519101c0c18401c59007201e04122003040d40c00313171048038031002c1c50500800e800b440803003014555407031501903120304641c0c01030b841e0f4070000e0510101d041c942c0e0b101142801242d0044c00d200128462502e030071001480c41404402e0507a440009005082e00140007526140e032040e021140e164503482c41c1555034510a1003490306203004030300003842d481d0805010702250000f03000c4501c4014414221141080500c5111000007004142080040500781c000d4a8005080c0d0000b00700030920003248c0d200d0741c01000 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 424030863 1250 424029613 424029689
    0x121e02030601030209190c11010e1b010e010c0b010609150201150e0408070507090b030114040507121a1e0f04030c020108070207230a050a0b1e0702180105030106 71
    0x200c002a117891a401c603003541c806d2107203010003028001c03090280408010300c0c0c0040ca035620300700e44542c0010002400c59000f0b070f4204030780c0d100000701c00011288104505030150400c0035544520000400035003410780a03089a481d0707441418100840c0c940142c01c462109411a8100001090301681da144403901340ca40e890030702e1095a540c1d0408640c1c608c12004010624407030305c2d80001e11460343e5440300030701c817908500034040c20302d840066100c0c0740c00968003c2c28982058004020140c4c0150f4054102841588100700b000e440d08027130325214604407078000c1c8018441d100720f80c0c469103000c14103a01640500403080741d400c0640303004250701659000203040c0500e90001c601464000c210840041400c080c14240040c005401801c401410426403401740b40c2016001c5214038084d49110196139068030313040c0c2025800c2c2ca000c0c0480c5660021542420000c00c1034001588800d8030940b43c0200041c068512545882d0034103084481c658040c8e800b05203140b6003c0358483c8100321000c0181421 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 424032113 1250 424030863 424030879
    0x1b080609010b180d080d051005100e040903030e0a030504142209140d05090a060806090c1804022a01021c0203041b060f18030f0602031906121e020306010302 69
    0x1c83c0205120700802540604a81300c0440e031241340040c140c020902c1400000d075100d504554400502a446146600701e2021a602d0300700d2140c00e051030741c02864030394000d00e004110f92007541130250622819072410742c002840000c0502c4a102000200105c0d05011789001600803580c020368203020201c00072440480e074545000c0002d009a02c000440d40e501c029040e030b251000090006001035006484542c01811100d01c001202801020954031500016104440c3d55440400b480030a2380300d2407400c002d0501110180c02a0f803a244060801c8a004030b02c0d06078000c2d042a80c0e040c1c11103565140022681c010030040d8800c045049262081707040c40c10000da01c0781c0b500d10346540a0b44003100c41c20a0605003080004a040d07004081c0c00c1145038503100c00f41c5040c180890860000e565000c05020405a0050400001d40e09d50045502c89030030b00a4405046004010106540041e845200440101080300c1c0500440031401c1e00940550103100d8a1a00240e000c2501da50341413001a04c030ba110 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 424033363 1250 424032113 424032157
    0xa23061003090206040801020d18020315041b0e060102100b011202090a030807080918061c081306050a1202070b010e0615070b150f13020901020307061b080609010b 72
    0x10b90000d180040c0d0080c01242c8881d10f4101c102c2c000c0d040001c2a001140c00c1400041420380f40451998002d078001d0060848100161a41000d29901401c11990316880d81054023402541c002d0080182c03110764000000e41c10020002481c210041008446191800c10101060b0303030030030780605100d0720545026881e240c85030b00040c5120b00d84d0344042c112000018a1004000f2160028020b4000844803015461111920382c0e0701c0341c604a60641e005142d08010703241e070f58003048016841c10311800c07510341b51000c0c590360905c40488d298007203408200089212814240c10040e030401c004041281103003820b0030750f204d8180100c0d0600c0f0700d00040d80c451020880548dd6600380c100115949c0b03050b1a0365140c1031610b0491410115401160410a0780c0c1c180c8031464410207030b00312184000d003500400c0e0303290920140290310103007100c1e0540c8000c00001000554500600d980018041d02100c2d809074403010241032920018a40c1d0703c640102001404074000c1c4405540c030041500c690343c035407040 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 424034613 1250 424033363 424033367
    0x30f0206090c010806061b060615041a181c0303110c03040312050f030f09060f010302090a0f061509090516140913050108010b03010e01050603250f030b0a230610 71
    0x442d4640e2049600c2c0c0c030040e005624480008c00502404007940c82c01823170049200d030520b46000314000c0d04000c45820f100344aa5552010180104146d48403000c2d00f01d80c2d404000130355041d803443c0074104250041420b2801d041d09031080052104842200324900b21004641d180c81e4400c500004040c0700d50355110440c000c0c4a1700c15643c0000f403003004c066480c03c0042d0100044141250716454611420001400503103424040c28101e0354041c248400c130f81c86d0040414040c2030711412541031240e503228000343c1840407944400765403009440e80b0101e00d0401441c4020b581c00288441d400070302d12000125100d9200c00141000312500da10581c83d00c17002c5000a840e00c1030700d080392003018202800400c0094065000d11000a0210008c005050099a4542c00d071340341100d0042e0700d900900013079460032244405c24031014105c50848001180c8500626034030080d15007041c0d41101c1141c2c2080080002c40c400d40200c11390032240800c00e0741c16104810140e91009108900841a150448070014 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 424035863 1250 424034613 424034617
    0x1b0f0302060f12011205100c080114040b09070e01110c030607050a120515010221090d03020106090c0206100e2401020a060603050c0a0b070206090103020f0f0403050a030f0206090c01080606 83
    0x50b4500d0f41e00100d5a645a04200c0c00001c0c61041d5110b0150740307881ca290445e03620601d0203160103602c8071152a0319001801401100503070302d13035800ca40c980102801540c0d40ca0a098414100c03030b00c40038022441080010548805190000703016400860200150341d00080c4d100c1d80f2007a00d10300565101030700c1d1021101582c2410b10001c905d03007002c0074008008030f0006200c3c9454800c0e401c84a800b4404921804280707ca0410950396880400c112061414800f401000c414020700001c0340c2c543d42c030441a407c4078206c04500005070030840c10b00c40071a940b26404c0d0001c0c070f56120302018508108108c58280500d101c1022140b100801c00710102da402800006015500404200540b582e28142a034841500e443c1880c85202c07541c02c04250080b000050b40d60307480d005860a4240081c6e400103400035030040d06481e05014051110319241d1800c1401070000c1d500c140090100d00a54bc03801034003214020031400c0542d0003a10410690050008404039003076824a000c201988030003000c50b60074 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 424037113 1250 424035863 424035877
    0x2101060305030d11030708010302132310052b0f14070f0501020a03020a020603060409020a08010f060e060904123b03010209010215040816030201091b0f0302060f 71
    0x5508052000050041c04809401c0d0b08001d09402e1160f40c80e26004054a880111400700124005800610150074010351031560980c0e06000014000351183e1850303101061021500010340c00c8400b04070b81d68407849000c40017810300742c6001ea0018485410800d403194550190303411036800503010710a01422400d910113698012a200e02010302202140d5111000350041c1008810354071400202d81d4400164100b190b60968054040b0100305d80c00c2000c0c0d90b0000d004540d0041e1903203854000b5035150102000209114000050111619503101003a05e039142e00200d03040d441d032802c00c0380c030b501d6401d40d0a52069020084000030700341e01c5400d5551003841d04100d03c0b0181031048850100704d40d540301c0704141030201c50321005004034000300360a1f4801c0d0618240145c0003c0b108403250740351707240c000b50810310555903907003040d010f03012690800840c0c1c081900142c0d100c481030003d200100c80862040c0000d004028880b50401d8469107070b440061100038042d4070005031000d50701011600b99400c03 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 424038363 1250 424037113 424037179
    0xc150b120a060c090b0706050c1306210603031b021f02071406040303020715030207080a1d090c0405060a110601170d0915050307030b03060106050d1103010311 70
    0x2a100408400c0d90300d9900c400c00302c446a1500c4610711071140078a0081084404010215141050a80d1040d000c0e020107041e00d1b1406205100c0541e000440e10500070281000744d440a0380010170030340e4811481400035a2102083c50141c00380702003640040041e00c20b500d0340c0c1040925120910200e1401410102c00b075100d0300c0481c070640d0202e0360209060044036100341e4009a040040f80c2008400d00c52031000602503807020307104004404c1580300c40c000c0d001050600500b085890b0b169246a58400740c8448001001b20300442d013100c0c00c2070380c04400020260380122561401e01082c2c80107104034050248075001c089519103101e4400e415140307450b9000e105403206542c0d60a41d6490314440710080348178902820906501e01849844d5400454075800c001c803c0c500301c080410f40d010b0748041c00c490200741d11001c206445031000c001039402070900e662a656945c0c40220030200720b030300324411880038003000c100400101d2000d2201c002c1600c0202d07031454224460206284105c2001d94170400 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 424039613 1250 424038363 424038379
    0x7120b042322061107152903060412020f0307080a1101200d0626070b18010f050408030304030f08070e011d120f0f01051503210f04140a0e070c150b 65
    0xf55003000b0f900315041e05503840464610100c0507840c1031f80c0404807154216003640c8804002800700c0d0314a04401152101d03801507542200320351764098110340c4a04000d80d03850b100000c040401070352019a00f4215a03400b4003c0140b110070242c80c21404c40d03544401310340c1c4000032603211700c240c515601c000d0050604040d407101541407058609218003a03a461811140654100001d014007100103d0f81810010140b40203010103207401940d128043c02c07240d0042080900c404a8200340410040d0b001700d010f5181d2520000101d40020480c1c0f100501d10001c00a60134582021079070410443d980b040110441400c0c46c03440e03000819001c041003c0000307090b1060107000c0850440c0482d0701002452420005c0c8903a07039035114403205000c110b505640d019402400c10441c0c40101d242d13941b0025804a15091034007440705141c0c091f81d0015001510740a2602d40c002e0707101e00c0d0240d03840c40245070403c0f6014103071410204c0a01000c40d040400342841c91440c1041c41031030f02946c4101d4204000504510b = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 424040863 1250 424039613 424039643
    0x120e04090c05090f0402010816020a0807030203070501150f09110708070b100b04050a0b0c0a02030106062d081605040f0e010617010b0307120b042322061107 69
    0x80d074104240c8203030740c0035020703620200356038440d00c0c0036462240c1e4040e1184901074403000401300a4550038020b01c02140250f0210400044080e030040112a000b5402562544020700300142143c2c1400d1f26a00070aa85a60400102a80c00454803c0b01c403140b80020344154200c0421880380f06558009296034000508041008080900d06016207200320f80c1c0000c0391b488840c040040d1040d03005082c0c1c420300c0c4c0c2c03200300709011030400100015040d21058400c40000e03907011078203681c510341240b0041030081c020808031030802c00d000300c10b21a803044144690a07074100701408404010f860141100800c1603406062400740c02220010315202d132036110003070b80d81c400f0165010002e019280009843c407856410b0540c5022100b81625030880d40d00d4074585404005640c0402d4580c00d02600d1a2240441c04080d951445407280d1540e06c9110109501490154416491401016201c1d000381c40c50b00320b0702400e81d0201c0642505c1d0b0204e0006041030715901c91140c1c0d4000e64030010400c0d0f4040c1c2e01c00c = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 424042113 1250 424040863 424040873
    0x1608010501060206090105041e031809020c10050f01060809031605010605120102070c0b13090e010b03160608011a0c031b07060c02011742090112120e0409 68
    0x158100c0382941e098802944170000d034a801c0e184180d402038240003600c04254035101600348030348140c901c20700f032038002c0d80d00100c012601501da03944400103195000c10b07103400c0a00c0900a40710b07480003030b1500300306602c0d0510612108940600481d410851020300144d20258108121034600aa2019003200303240b140c1740803800f901850044c54042d40d0713401080c042c070304814021303a540c1940c0300d44400c50440c1801302c910711342e402c46551172300c2e0100440400100050540301d6440403020110000c900001102c0600d807a0401c0c1000e00c0c080154034080030001540e100320381e1419500c09040750304000600b0080e1201a0040b41c0e04407056010008581c250b10b00f440c0f800740401d8400505540b007159075a001507032400b4111030084c2c00f00b04070301c080c0c00d204607070030340031b82e0b030100414074440c003080c00c6035400740d9503c80d40bd484012170031131951442e982c42c28002c040044581c000c80e040c20666050000a4081030a00d5100410100c106030501e4000e41c02848007c42e201c80c080c10411401d804c505203 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 424043363 1250 424042113 424042121
    0x90f03120d110406020303150406051201050f010527060301090803090a030f05030910110712020a060501121109040212190201030e0105132603072c09060f0102160801 73
    0x80150325034a0b1101c8180a014030100380c03011030301250040d50031641c03100101d03d00c6078031005030990710503170b2034802040c2543c4080101000c12040c0f000040c261801c240140110340301a0012441400203440524072142001e080807480d014914605100e40c4851001c03d01600009000400b0418048100062602c00103600c514a030300a640b400d000c407105120079a6648030684550388542c01000000b0341d028415008506507009410350945031000702d0722041c08803055045443d0047e00201c514400340102400b4881c09810aa044410300d80003d9440f0054082503400e014002c0c0071400c00a41955200708c0d80d010007986031001d4a1364000721090030030715031422501c1280841e1908018840c407420500c9214444d510641c0008400c0d855a02d40c604030702048910320003141032030522119210307408405940501011b844094100340300d000c2c100c11782d50790034410100c06180f0811000c1940d840a44594110300c1c00d442050180c0c001000407820480d207105509030b460050780d80060050b205502c = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 424044613 1250 424043363 424043377
    0x60a0b0c150c121501050417070503010606020601170c01020604110f09040303050702010c170c070f06060b04090b040c090911040b070f0201020708060f160e0405090a0309060e011202090f0312 84
    0xc00110940c0c1341c90300c0c09105503952140c280012002c1c041441041e10181d052150054500200d500312969a00085d003500c3d0746402441c0140c001900401c000032a03044030444a40d49900071384004110361000035591540100054199100d8406062064076208215105070001400b000711900e014240a000307030100343c50110040d8a00100614650f22440403020003074000d008120442d02c0d400f00341140c640080206841d00140e142e10480040c0715445518014902d10a13450349651901e556082142c4424851500407030800316502c51883e44004070b107040d10f81c49c00c030003d07030406103021001c03160145030000850300100003044010320000c2200c0400c824400d908885d005511104181d0702c400d070682c0d8400341700b070450700401c4112085840700000c0313607502d203025511085000300181c00c1d18019552500390360000400070040c990300c02141000313021a410312685030b00d6940c00007818981d40c0d0440516165000c01e0480e0785070341e403c0403801684001002c546030810070807040300440d40031003 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 424045863 1250 424044613 424044637
    0x220e070c080d0204122a03170702030c03060a0504110a06050a1d0a060305010302151c0216020405040803090115140423040b1005010e101107080613050c0405060a0b0c150c 75
    0xf00444920900c901520066a900480700401e00c020084400c446800600700ac913458003605d8030211040c0c03001c104061052102c1400842c16007400e08015082e60300c03540700c2d240181c00c200c000303000c0150003030100c80c11105c440c80d00e4113414180d100d103185600e000000b5684c0c4000400310004040341c0c103030007540c1668000c980d0041c00d41c2600c014281e0a116000c46407025003007035481c2c04090b0010350f0103046282a08022010b074654190f00080413180116800c66070b40202100b44540d160003481007000d42c15491040300c0d103c1d8145400c00401e8924800c05902c2113846500001c08a030a10903110004061081b42080b207090a1130011464041143d10200c1c00c100305600080941c8581c800b0903441c903019014404070500301800f00e070305800c0d02100ca5505c0c0f056100c00a030300c45041141910503464003540d002840c1151400c0c504040d01803030a14030807814002844071943e210341c510703801c0710f6154503010f9450f03a030517140d241002504507051640050070003c03c81c41e251548020101d0380c40c01 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 424047113 1250 424045863 424045913
    0x120608031308070e040f0f080f0304030f030c1b02040e01020c3703030506030a0f03030b01030b040e0709020a02070803030a230f010306180503220e070c080d020412 72
    0x100b0649544000c10300c514180129204040740103d000d070211100d03494044c611601140d8019201c541c020b5100a50740101964000304000600d80d1240401e6400055440d0500084018110091554500110010001549001080856403503600c0041c4107481540299202c84d03221503030540307a8103080b400702403120071403c03440039074209052860b80d01c580050b1103034020560345d2011001010010000e41d01442541042d80c0407900c07100d07245210034820755001c030311448a000010103592444200e00d009504080110040c8240403a901c5c040d80e030144001619a04225400c925020095010b40c03968003001081c030a05426541244416400d40c4800e03200c0300e10b40c0e410890035108101c82540340a09848014000141c0c83e40201400303007042440f1209102c042c0d1500c0382594804101c0e900f15a105525410ac40c2c04c021002500601c0311265240305880c0054000c0d18050440c0c4d001002c40c10b000074034004c1001c16038196005070841e003003c40000c541074580806914604003044416001c8 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 424048363 1250 424047113 424047119
    0xc23010809060705161509060f090201021002031f0806010503061005060712030f02180301110c030d0b04060b1c110301050105040b070503090d0b0109050601050702100e011206080313 80
    0x1805014000d15030072000301600e654002d0f003203d00ea000408809101c15161180b8004203854417106030080c400702c40005a921410f150100458030b8a107440e407119420f110b41480540c1e00481c031405074024032103015070744c3d81d210714400c903d404100c407018a10705035020000c0f034210800102c4d0b80c1070700e0080d000c07504942c80e254800340d42c0c40614820306a021600f040128009013641255020300c200500b00450303072240b6141100260303000b420071030600225101d03c0014600d4240101c084c4404003030a0f142c90202e004402940724429246044143e40d02e0b04640720813a00ca41d44860300415519052544135042504117100c0f1001d61403401941e281000514003541031703c007042764103c0d50140c41c1d031850309140c521041200c1e0400fa10079107081c0002d00c202e14041c1c6812401e035640d11721480044403a903040c1130414080343c0e0b0143c5007504105003071084000503200c1c40300841c204101c500340b0301c18000d11200100c17200c52007180031401c102d0034a8400142c01400001400d14040184241c2c96807030b403 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 424049613 1250 424048363 424048367
    0xa050a0314061023010210023001080a030c050f030f07050606090c2704060f0602070b030709090218031b101806050903100e0313170c06030a090c2301 66
    0xf940b401000c404040d80c031041400b1842c0400030000810301030050351010401800350310101d0700300c20b025907040c0b868850f0410f1003803902c0307204860900422940c00d034103504000c249651141d511400030103001300c1481002c180401040900d04540c00501240d079903a1a05c0000d044a8104c0242100d0701c0c800c0101283c01482c164040611810300310312642d0030403040c44520128007500703800c00c541c402400200340707005454070f014660152840007610129649451002860400c1c02d510144900c1c40034014070100d542d01040350350417035003007640141e1500e0b44842c3d0741c1c0c03003450b4915607190726100308410942e55151800c00c80c042000700701e42c19064044044805d5440c0000001810655513200906000e4540140080d0465000182c100c50000381c80160500880f01104142c00c55a80b003c240403204054040c80c1c075002c0d11040024610000c0704812150b0b40f000c8100d00750384114004000250b03e03810130751004c01c1c403a8010611010180d81c0b220402c0d030000c0880030a030a054004004402154 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 424050863 1250 424049613 424049641
    0x70819050414040902151c09080a090b03070e1e0907080a0501050406030b061c02060a050715090f0b1504060f030c0806060108040b100b071b0911090d020a050a031406 73
    0x70b801a215051b014100340c0008103903030280105400390b41105004508424441c49000341c268452051a1340e103d0700a0005440200140d01010031420100101b01403250b0042207010700103400c6c2d481c58001444003d0004d629010800d64035002001d0303a00300807c1c00e503c000d0300303800382400c1c0c0001c00c0300e6603d5006100c1501c50600002d421640c120012030010309044200203001c0e0401e0b0011b45146115030f00291031540700b5007000c40080c4010500c84140158a585010650b58001302000500a01d0350784540c40e0b200c40c403002e0720844032200092850360503059286040310005004009035901e92850900d01740c9140001e980d601004c06008c5101d0400007442405240161210010344da81c0f6540c1d40c440c3d4400904090403c841d4a100152010450b000b40c11300b9032255070918441d0b51100003422503c05143d12111103282014404156032051404a801d001c4041e24941c6607004107001003544402da590085400a44030b50000041c00301d003074001c040e11041c90041d81c000741c55100242043c2 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 424052113 1250 424050863 424050881
    0x2070506070803060d080403030f081311221503050c19030b07090e0a06090c08010e1f08101506050705070b160f03020c010e01180b07081905041404 65
    0x11500c10004040420b15400185512100007881107034a02c4140d0754074a40f43d0442e0b441240410450120301c11203e0304802c1c40c0f40e02c00382100f0703828181e10080d1118030000d480360303050600481d130170342890403541c03448180194907180c590300600c0408910a0300103400c00d01403105503924000e1421210141c030300345203a03018205110007000085401c54540d8a11410b02914000621079074400000b94900030744510f82c42184cd00070f001401500e410840c0313054803400d100307242c200943c0070b0045c4054004541000e40001c1000315110070364a048111089552103130700081075900c600b40350a200d810b0340340c10520301e40302030f400300801c5180d54030340699580c010204028415048040c0c184120a51000582140743c0b41305800e503000c00c0b00d81c584d030340641100401507005800014002590f540c1000081c0c102e002e0038a81104240070740454031410641078001c28907036aa0009120b81800110000c0c1e562038941d010399034401c0c9a2007940588030b03034003500c903600b4403242082d03401e800c81c030703103489801c0003 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 424053363 1250 424052113 424052119
    0x6070f0f0e0306150607060c090f050102030910110f15070e011803080d1409060604060506090603040b1f08070503010b1203090906013b06070c17012a0e01020705 71
    0x1168070703402d0b4a602a0b00d04d0051298010500348150320208620303008140c0b059a840d00d8941c1070071b0802070001c500004903000f850640d407042121108540752080824030280840c585680b0348440c03c882c82d0b00304040360a1748800c9220703200c04503403500407200109002d4202a2a85000e0303020000066440d003114410581c0c000c00300d80c0381000031a001400403e840010114005111311140d28520415031040d200d5038226030100040000c282820300c20500542400c0302c0290811346d800001520511004100400398068040460154044a040803080800144103031000c00e4071858026682c1d01d152241c00d20940c03c0148046013814482d5200d890040340348040d628024001c41804070041000d0b1407035042040309407440c000005100841c4081040c4c0d4484401509030540c028201c806201d1911813107108200000400510404e01c200d04640c090540140180e40311070b02c1c2c50060126191078106190301042500041a0140001c03071122626190140c101451400490b56003059000c0d441d0 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 424054613 1250 424053363 424053373
    0xe1213080706080a0e33090105063f03030703060605040b19090302040c030204030b061c0f06020706020a170901060311061e0c012306010c080309010e06070f0f0e03 72
    0x13000d1146030812903109078074108880c02d03840040308240401c00794085249101805c00801202d01e00340040003604412890020311040c01d040001980c041718002c0002c01c2010780500d003003a0b0440b88118100d40da40480e6458910489026132207407079500458446000038030700080498402e010b01d0a03101550f003070100d041d00700480703107500c00380c502d11404044090240c4018000016a106e01401803040d941d95009a02c403460b42c50003021240024240b11310074000c5208181c00c40e11440c800c481e100b604040524401402d40c107155000f40300d010b101030403050000603902000c2d074000d0179501c00340b1301411104081d13560b0966134034221031507030000410a4900d48808090b51411308003400c10a07004542044188410301501d0846a114002c0003269075120f100c2ca9001c203035540c810580024220304403a00c00d25203040003c042004400b00180300f40780c08030201e1342c02002540301000c585180b40880d00d00b81089200a8042049150314000180d200005504100d00c6902803035230a14001e00146 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 424055863 1250 424054613 424054621
    0x301170a0809270a021312050d08070512090a0327050405061504140306010b1306120603061e1112040f0f0506070e030c01080403050702090a0e121308070608 69
    0x2000d0f540034401041e044001454081d80c201070003c020303901442c6122801039446468469480000070740c0c2d40500201d00062441c0c0011500c0411f158081071641d280a152035665100306840c14041c180c00030748443c0d504400c1000500d000070b5003a18180c06912540310b02e640c0811240c07040f41410003524410408404104081d04051700b000350000001081c00c0307030740d4a48981150054000351303c070300100e075110b000c500c180d42400c0c8445400350001016981c80c00103149200c2c411960180b040c1c00400103600c541030020801d80c0c2c02070001c1c40e4068030038403100e200314400311050314500360b1039914580340030b0589880083c024125100302913401d60a0003580d4982d2603420901d0044802503d40c5588150104002401404a01d101d40686d07100c5500c48051401810702d01b0102d0341c81c0505000c0030100340004a50030a096076012a811074803404e05956100e001d1014040412100d040c2c1e110300c1e444818240c0541000d040c0c0741c011440031001140d80c0311035650b5610841c0c4510408601e01300041 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 424057113 1250 424055863 424055869
    0xc0c010627090c08030d060f0608060a06081909110109050604050f01050903010e03040f143a080c010c0810120b0a23010e09070f060c020f030109080301170a0809 71
    0x2410005000c3d0000009070b41e41c5030040c60a651040945044c0c4a50392002800310310003600f1a1006000b141c9004844e9144c818040f4144480030300608080c01070420010b840b006400d0300092807034003107034000e100c0d00e80c080c40e0140465800010756408694030920224840c2014130698044620040443d107440c81030b040150390540c0300342d030000d4265480d07802c04e0703125800c100018002005134011400c00e10740303040b1080c01c0000d40540e80501c80c100c2c0180903640e5941001401884205d668041c0b201c1d032030340c5091400c01e00f03105800149003460125144104034410f5001254044040e00c81c00c00e59070b81c814407030681180c540503800e40b24401c0c0803a480464524803503558004030100c4002000300f0041000900281c05088420040c02e600005011500c0c0200c2d070aa0402a2342000386030745824003403111600101030054108015440d8900010340d80d4407004090700580c003400070000340c00c003810140641c3e0b009000e1a814070a802420000c18100010303c0580aa0820071030b41c2030541c14010 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 424058363 1250 424057113 424057121
    0x712081009200c070602101506080c07120806031e1510030b010b1b01050f0c090a0b03090610050607030507020913200306090a0b1f0b030c0c010627 65
    0xd81048020403a081018400b4410010201490f00b0700080807140d151040c02482c10a042d0b202c070741418141b840110f02c02010024020941e2002d0405001c580d4404402c44840e004030704020f0003001c0545c182c4151507400c0180d40e4000da02c00d5041c4c0300c854001030500710380b59000c04500d10305984a15244a100401050072940018000200041c0541c1c1d98a442d400c0c1d41c801e0304456208003001990901070b940c560700d1100440c8448000344082c0c505030b4070700b5440d180c0003484040040000070744e02616945a1420b200035155481d551504ca0030056009643e0700380869208842c001040c00114462038005c0c02c2d03c0c040d07039060352942c2c07404100e542407107e01880900040e1500c044041250300040ca4905d8104a4458901e08a5814101c410403d4038100d009042140b1540288001d50041400e5441866001c2c500c2403c4045170400c04141c034212803070580c043da0f0000000300600030038104400c001c1640115240091100545840b050504582c050381c0c000e1041d07003061045c030720020b11500 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 424059613 1250 424058363 424058381
    0xb0a0206150f030d080105031b0306040330061a0f0a050a03140f04030801050901050117130507030b090d05090906040f06030501020301060302040f090603032a080706020712081009 79
    0x30340d14010b0240c0082464042c040e1001000f0548800040c040340c2000c00294510031032a02c4d420300ea410030f51010a8544d0401307000941004400215000c102c40c0c604244c039200080c05004514a482c00300d4524020320581c0207141c144101c0c0d518141082880d081075074400b0010740c221628140c1d185000b42d4080d880b0000f61018140c071004540c400303041c0d24042c80d11510b503519001859103480c0c500100324220580007240f24828040c014080c42e60720401640424111351281601604c4842d01e030284d041009100501900c269280801005100c8401d0350083c1d2642d0101d80c405544030138103991600070181d103180c02003402c80008039285401d4000142d40c029456000500ca81c80380c50305400c1ea0f20980100c000b103500080c081006040c102004030090800c4902001854110355005005580103c512002d10040512000c640c801c00c460800642d0352050056035a0206490120f000e03401802040d54584e45200c2d1440510b405403004e00d20404030603922044e880c0c100244500180b054113 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 424060863 1250 424059613 424059619
    0xb0a0b24032d1e07091809020105070c031a07020a03021b040905070e011404020304020d0303021c0915050f040201090905190618180f0224070b0106090b0a020615 71
    0x3a01084200c00d82c5100381c0c3c041c0342c0040144800c4030310903c0c000003401c0302416850400001413410410a18542c0e0070b1042e2110320000801c0002c01030004840038021894003a10704644040f00204201c18071514404039030213080409800d07070f036040301a6200c0c60358240190141c0c00140c001c1614148880110646400080c80001c15184d2500d40c0d0740380406640140301600841700060084501c3e4a61203041c80500305c40640c9103150550110b03000820544000703041c15004105a00508641340c0160070081c48a001008140503030b08060515040c08028045420302c1c01e00403507546000001841d10464040c0c40d080e1007245003040380340083c200140342100304400748510100c10034603402020000c2c43c95485403040e00000715124030884401c1c0c0305c05603440140e01c503da400a9500c14400d1611074044032008000d211031034000c070041c2a030340c4240c0c12290001a9a004100c3c1010545040c0d40340e80d500c000850340c51740541c024503c0740c03e03000d00c05a444000040c4100c504210004000030010f = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 424062113 1250 424060863 424060921
    0x807030f0e0607020c03120d02130302130603020a09060e07110102090a031401050c28090f23010201020c03070809031212010608060a03020a090903020a0b0a0b2403 72
    0x404100d604448101c40011800d070000c2c8144600d9941c1002044a4540102d02500e003141c25919281080e20880b201200f042d5000b1443c402d02013032641026001310b4014020860401004500030010040c0780012031044c001070b500070508410034460076007540d01c2d5a03442400c58803440c9080e0303400d00420096002a43d02044000440d80390f4102d14401144035030301c851520159025403d0035034030f004141d50f070b13620020b00ca580e288071003500c242c00c91420001604100c01507106000c4410305944e801407041c5440c45080050f100d01d0840c41900d801d80c0303810015041c103103400012401c2c0e2041d4490741a4581c020300c01100410001001050001e200030300302c0311034000c075680308040754001088003240c80c14201d004010181d00301d41d00355800b030011200005135a095500041c00710556000d002007495035546400c0030036001300964034540f500035800a165181801d1100c010b800c4500016026203070381c0030501c0740c4019542d101003203032003041001421903552100002e410710421030032002e410b0704 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 424063363 1250 424062113 424062131
    0x5010810260c030d0e0105070807050105010608040201111b120c09070e091302010507080d1d1633022503021008040302100e0c031006061b12080703 65
    0x94030001c215941c99490401078034000003010607040441000b810750194000340500c1d040c4070342c492645d00f140082424299201c03101400c1103a8a4090070740002e2941d860900040740315900304400d10f1040b0310036170307a500c800961509040e4489001004200e00144d071480b04442c549001c072540c01030760a414080350116032101e00004c46020050301d1010108602d501544000d04100c1c0c9405d0b07110006000d42d003944205980028440d11440401800c481c3d0080b0740801c40301c0e416081004a5150201011084028100c4158586a03802c60050608003d14000188070380141d042900ca02e1880484002d251007810780c6000c2084a000200110b01440004508210341040001f034200d5141c1c0660b684541980b061180c0d0600e8283c12400f8070625004110001e50700192414a1500741e050125503080c000d41060b10340900c0c00855076050082c1142010ba40000703a0105044401ca07542e032001e102a003103400c008001c10380e00007500280a8440b11854940680b01036908554030749400106411 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 424064613 1250 424063363 424063379
    0x5340602160308090613060510080a03020c040515010c080d0e030307030b1806130b03210309190503071202070b0705150606030709140607050601080303090105150a05010810 76
    0xc406022560340300d0724079a0640a255000c0c0d5440c1e88404501e0081000c3d04040740c0e058840b03004154020191500c600019090040b0120018001c05065044640c0c0b0605441c000e500c4403907000c0103c1c0928582000036101200e801e2541c07000300c078103071901c0340c504059450740420346c0c0c02400324403403050f00d485405078810001c10003948141199980009c80110003410004040605d019035000c00407400c0c08d208840c2c0d00d08c160985200030345c2c0c500054002019010a00300300c80d41000043c4401540021002c05913618011842a02c0030000d0302e0245181030661070018030070290180069000b440080002409204640300b00b018600403156801e59800c540b00817580090003c0321141c04c005001d0342c56418442e8104e4100204898141c20b51415040c01440d030085c6200e4201254251075070b6100c907484100c2201d60654120003a02d00035a160080d090752070f4400c0d41c01d86519842c10002601001c1949200c10034980020207451115151100454060134080c016640c08102c1c08030000d00e0341 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 424065863 1250 424064613 424064617
    0x230604032a060305070806060d060503061302040b041503020603151011010b01231e2113050a14010b0d150b0f0f06160515010f050105340602 62
    0x91003441c2500c616003080010035102280c5030340150245402c020074401140d40050482e580940150380064403041107103248405021160320564143c010300d0103102204060300300010010740207550501005408005100c02c03611503486012050038610400d00051078850001c58000405c5141c0360840030101c000140101e00c8510b0801c0421620b14031a41307580b8081c022024649d4090a05005440c40780580d520461a0807551300d40c51400028030a001c48228890b0440660000d10855220030342604540040c56205440001090301580010800ca07a80e41140d9442580a4058520301c03945640340b0301e540d580b0024440c465500c074400b101145d224441c04a201ca40500c48100c4280c484035004011240425002c0d4040c01c9503d01c44442910342d841c8850042c2019289160b076960680100c040f024402103009042d80906600540b070607524180d520b050b60440c2c41002c0c41c107540d81c0015202d500c6200c0f114128090080440210130500c1c6800c2c8501164400c0114400f0b807a070303a200812a = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 424067113 1250 424065863 424065893
    0xe0a0b01080a06050a021c020904110d02040816031a1e0403031e02070203031c14010306050105090601030c080636011404060803040b1303120809100623060403 70
    0x80d0b100140c41c2060001c04c0c05090341000010740b0840c5030010281c0340070b05010b034500400304055000100380c0c82a49859200c4c85c0c440b2480141961a6003688030f0751006507000b8030801c100f40c804d20000325455543e0042290440780d0000c0b4044041c50042c480801030b0b40001d082100400200006a030014244085203220b94803d5900044694982e07613828001c0303140c8011410410b1040c032803000140c4001044980d4a0041400307947c1d02c85020003c007000e0400000b07003182c2c0d07500703403400042001060b41044e4180c440031140071256a070b40d02d0045080700c180100140014102c4004030307883c0d043c50001000d00365140c13500d15001000b0050b072400310306c0c40e418040c900900000b004000ca983c401c807180b0715194007207405100c0f0074540b245007940c0e40100c2c001c0419264001401140c40708a40c0a000011a0310118802c11840081700141c43d040c01103aa00099001d500710190b695200c5125200684801a500c40007401850784904543c619400c801600312504020100100320303402081402 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 424068363 1250 424067113 424067129
    0x20c0303040f0f020a0816090e0d081b0a09030c080c0607080a021e0f06011706071d0a06030e0d08040b010b070206070f0605160f14030406140c0307030e0c030d030e0a0b01 75
    0x30444000e87e1500d000b00484d80030040709840c01020b0a94440c02048012026031103141c43c000c0707921007042c4031000c8041e800704805a43c2c80040c01c080280d410400701000c40380105000032100360344131a4151500c4281d200c042d8001400c001c00c40004460320044d000b40c03c41c3d841110062030210302c6640c5000340181d12651360340d00440e410540c900c0304020f46070141008600080002079255a8503903513100140c01203040c80680e0030240b000c100060301c0c40625410044c04a000556103c80240040c490b090000307076240102051520414099807409001d55445445c01200760301c2c180304000b0a0304200c0040f6445003003040980c1c0481c4481024203e0107026410010380f504104d0040407020b50409403032014000004506c00c1c5042e0062480120701d0782d2003d515a9903651458100c004204441580001407450010b100318281480055407054010b900c04004a003401c1c0c184035074a02e0880030645e815484a4001802c00d13100c6d4015110a50071641180c030024810750322030354031000c00d82103805 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 424069613 1250 424068363 424068373
    0xf080c010c050c09101e1d07140d060e090102090307031b03080c0115081f0504030c0209070e030c011103190309050303090f160e04030f0504170c13020c0303040f0f020a08 75
    0x34900e9030110302d5041c10f59902000d854940030242c290001c11018450700e114080000923503a41c05403e1259030b07080c208107070135070719450080c074400100311714040c20602c4002c0600141b61640d05108482c0c071030300020001c041c91880c555400c403150381d5008165103111146c010000004401301c0160622458070340010600000c444488142008140e1000995521487d080404101114071048010b5042c0b00c001c12150390713506080e1180c542d0381500a401c41d140504100ca4594404101c0e44c0505080701591a040c2c0010011905004e015400c842d05804c01c0148003102c2030800c0707640b01d50070381504000c601040103440e11400c41c1c10440304a10b0300e4115070301c000503000f010310141c825111900d4032134026604080110305040c4000300000e09021243c20749480550155068400401c03800b94001c4400d001c4104140d02c1e10724922a40e4003403c0b10001961459201d4000d484103858a60019410b5503510303100d9114081410406450322001c4268a2015881d101c85220181c231019000302 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 424070863 1250 424069613 424069619
    0x17090c0a0303020f1b0d0602030408070f06021209030306130e010f0c0206041104110d1d0d02150a0203160810050405010924030201020c1528090f080c010c050c0910 72
    0x2800c217030300b8035000d24046003800c1e0f030b8090a40d0399090740d00005401640058036903449183c45031051148101c0540451603000380c460070803070541c008044d0740d1210f020b485519201c0d090020313905c0c0015585c080c0c5c80503003c8940d6160302c0266010181c80300c280c10002c6480c1c2e205000c800c0440b4507800c003c3d40103030000810441031024080303007003c003030b0b0007900c01700311206040d00b01c04058050304680181264a80c601001d100001000034002c01500d03001341c620b028010000a95614010095141840d184000050f95040c06100741d03032258800d40203080030305000f00000c4070511002040a80030303082d002000300c2c1d240c989104040c00b074000e984c00010000b054150000049000300c00041c03c07000300790001e20060760701186c030980002050b100308006013141406007106029800c0c01814a50404440390321200c18540300078007000860310750b9007640742c4a01c5d103001109424010315806620165400080d5413150404069041c0900b003034421007a0000c0c00188080400c1c1c1d0503a1448005031414 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 424072113 1250 424070863 424070893
    0x1f0302150a090608040c09090201051c051e060d020f0102030f27040e0a080f091309060e070e070f0306171c0201020c07050609030c03061e070e0117090c0a030302 71
    0x501822213810118a6403405035107007000300403980200071400b0380b030b1100d0108590046e81034130707502071001400d403651030100c00d1440000d10045a0084001440100d54204507100e104040d014080c00303844075507000840c1e024451a1012200444d0440c4004c10803880031051910251000821121083d210100d005403070400d40c90445108900ca185410328603207a4a100040401c82c4c16440f89205882d000901c80c01120750288805d12900448104c000c481c8811040d4803541e10981314400407c109480840000d944000c41c1c09104001a4a480401d2101c0d001c0e404609400c0d1840c90003186071078880c002c0680c01003120811018642c000c0f8548030380f00c0030424444503440405d100850504c40f04240660352140e081c8162401500d0000d40d9544540302400701c0c404101001c1c0440d409810042c41a1105010a9030240b01a007492030100d59181e108400180e54114142e50300e150001240b80040f0080d20080c02514140c8076680b04100f15460341d14648008501075009044546030305594 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 424073363 1250 424072113 424072127
    0xa0807061a010f210b060f0301030b07050705030301030f0f150c0f05030915060f04052e0b07060c11010e1f0509071e08010617010b030706081f0302150a 67
    0x1060602508483c20200d543c3c1c0100c0804101c2049042103600e0103440d1820801030030f940d06001e8119030002018007810840400441c100e0784903a6480d0b416a80d40e410488642c05200300062a40d0070800040002c10031501034030402c107024506a0400040300e40e10203848004503c1c1c00802151201d81d940b01040e0898000a03c1d109207041c86d034a946415140316481d090805a41e0302c6500c3c661001c00c082d03885802451840f104060804c002038140070740c04c4040180445807500c4038003040c0d44000c0d200c225103007071001100d103015001e60900520341d80b148003400244100034100181180c65105440c0301f40100170700d05184501900c000e0a401c000e640c2d0540300c03004c01041e0903060a0522271f910f80000b50b40422504110305042c6140758507000000458025807007506158280b1001083c0060084054680c081011000b0083c01d8044c4040c144c98000a10812000c01c048900291400082800140d1400c40c0040e00c03480160716540020310900c0c0744004040004408900d040030281c00c280 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 424074613 1250 424073363 424073411
    0x20d091a0903090d03020c06041d07020a1101260103060204081203010e0105100207030503040803030a061502120306210f010c0908060130030c060501061b11030a080706 74
    0x303042102031400c4224140d0301c0c4140c00325680121401030301c240901d80300f0302142c040c0c0c44004103801e40e600d944803003900c60b0003254087c01035100c0c0c0400c00f00d0001800041d0003103549038802e100c03625003c042c20041d204100d416041c003040901c01003185900c1d01d01144282e0181d072041400607101c60070201c02501e000801c0c900280759a030b01b04010300585580c035600ca0304540040f201401d181946030000c03403c2420560008219101c00700300443c42c800084007551180c55032aa0801c40c4544d110380380c0c104404030081c04405604600385210110350380704025980420090700100403081042800040540e0303c440b00815070b0002c00b1003040c100000c0c061180101400e29144c44154140030304142c80b042c06201c0d6800d40100d0700400b00303040244921000c0700f071480450440070311140d42000307080c02300051403c44565180c00000b040f494040d4109080310603091240400c141030640c0d801062060300c2d81c0c20755151099948001c0011780040003400d03018819000410654501500c42d0007045039a1 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 424075863 1250 424074613 424074653
    0x302180a0b06040b0d110f04080703030807080c091009050a0f031505062107030b1501020f031801030e0115030312050105010503070503040807140304091505150405120c04020d09 78
    0x1004015032400e813810745692820b100e00000d0b0403060001c1030780440c4a2441c0b1f0210712100454002550031001c1084401c90b80a5102c550141d40c42c2501150001802c03100d6085418003031140d00032500303040f500700c50000795030b0400109450b1102c0004c1d0403881c1d15401000d460071076550520802c135151440010100681c1000d2000f401d1210004a1000002d034007100181940881c540080c4003c202010095811000c0c7d0401402c05154400d01cbd94038038000c01c1e0161103200600301114100100320307400461081000c0c206070f07203454011009007403040401c42c0c0d039648400140443d04038048134030f0300541c802d49451107400c0040c10f209003a243c0503070100341400024000c000100390004101ca89c0158400c0c2a60740d101c400b8508000c803408000720500d440d21010401180100095002c00d0b03401610900030703140255503408101c2c01001c5011200c0f007019041c401089141001280e01c1042d91480d402c0d11603514081e00450101c1c0c0000c480c43c00c4150712507015200340f0103a4001100366420303070 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 424077113 1250 424075863 424075867
    0xf0a030b150a050a03060e0f07020f0d020d0c020d0b100f120209010302280803032a120907080f0c0112020717031801020706020a0e0901060801060302130302180a0b06 73
    0x902841c60900400c00c4038020321a00095950300c20784640c0c4144041c00c03180c1494101810301c0c0a079081c02c00b00440c1d500c0058452003d55650070040001c2c0360b0130800c456401040c0c0801076210031101c0900e8110103c0c1c003d80c01000000000b03800d01b1031184100741020701031700418580311071b00e15280300310350043d04c681641000e040c015031101d0b01c1c0e69056a40656122004102d0b4840c40c8014a40010b420348400d2a4a0008034883d10040020344c040c600d08400032043c00702d44c13000401d1a400b51028002c1b6640200068642d8005060784254850314500a0701c00e00ca0380d03038002c1c42c14001548011401ca03004070311090529a0800c03444c00380d50580074001c50612103c0d41d100b2020880042c003801603404040001070f0007424081c101060160300000a540b0307050340e461f004020350014104040071445c1d28240120b81d040440d09507040b9480c40e03540645a9190810990095120b03645940000c00d000a0100260f00d84200440035040b45141c000070615000000404948510000390306c00d41c42 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 424078363 1250 424077113 424077139
    0x305010b090f04120c1a10060905030c0315040c0e07020606010f0806010234030605010f09090807030e0f15030f09120403031b06050103050a050d020a020a0e1b0f0a030b 74
    0x208044013215410000c000580318100b00050b481d100e800344400c48901c0c41009008600314041400310360041d250400150349070001c064485c0c514403402d6406620100784105849411110070341c200d40100d01001c059901c562520750101012503049015030702c20400d20a0b0b65030b01640b000c98404403850803044a06192000039110420302c94081172111a00401ca220141c03002203480700d420f1070504640e1035075a20b00d800700182c8024494600200c2c0d840e180022104030600807000c81c1c940c4011114905031555406230f0f001c80203020500d42014644040c55103546480650000750b00481e80ca8036160320700422400301d8403030b0040910700303da08281056004c42e2405400e0380d05495160400d030380b41d00d041622048200201304030141100c2d06200c000014044049000c01c2424001d10980d0010500d841c0160323a01c884503070000f90011740491081103031120900500b03811180c12000c00c5803400c0c8040c010030302500001c51420b400c0500003072008009415204600081c0700c00e980340380a80003 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 424079613 1250 424078363 424078373
    0x11505090a0506030403092103110309060a05030406090204020d0b0f04090302100c120606030c1d09060f03011e0b0111061e10090e010213090506030d20070305010b090f04 75
    0x402d105081c014903010000c142054002c01c98400a010301000180845c4030680003840040c41c1480d05401181110701c03540203c403400b000b22503803518090900d5140180034401203072181d200600079114036903218030b8040140e039180010051003120010104440300000100002c0d5039211041500c038920b03040140700080c0d0080782e0203000045d104000200b458101400b0364510300b81c191001c80c0c41345030140200308603400d5030044a00c3c241c196118494440c15140c4010071040302c64060303900003401e81c000f54085c0352228064904034401390002c80d0410520281944003048000080400c43d12000400d01c0d40d64000305040411394642d00400c440e040c417442da4140601803c500900728504500014100110034020f03000412081c0420850303804030b0901300307000350040011113031603000080000541841c1ca000380f03401000e00402070030440c5040d18040d5105080c0c00030b090145406402d03000d158050900c1400700440c09a0004180c050703010f000c00c60700c0301006100044070341c415020b02000ca9 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 424080863 1250 424079613 424079629
    0x50a2a0c03030b0319050307230a0210050403060c0801050906030c010c02101404030b1b25060b060d050105030d030c05040608041109011412030a0c111207030b01150509 74
    0x907800d400c0020344400b140011a05040b0708491000105194000c034104200001008140f8035002d240c001c410307611201c4203035811480c2d4021511b0300754040c50521003d131030030b4017246506081c1c0741009171925560ba0340740c83c117a6000d001e40304042070034500100411300303001702c0b080d5001000302e016042d11201c00e40060004001c08c0d202900441030403100305415800b480400122000c8564102c1e1034541e03c0c54107101b0300ca01162071103054607542d045141d5448002c0d00703071029a51405002504519800d01054400d0924401520381641b5241d14000030b072124001000180c22071900400e0660601c803d151a110051103080700701482c0125108049521205a17420b658640c0b030900a0341c0c60b03601303103d0080b45442c2e02e0f0300d40c021420000015100b200554154903110107503050100101c203583d45540768091003000710045003203a221140041c2103560009442240101030341c0b182e00722009a40c0c501100342d00300301d07462a00c0000510035507082842e40709003181c607460464a0202d4010200f4402 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 424082113 1250 424080863 424080887
    0x7080304060309020a17061014100c05010f1a01080f1b030a0f050705040302040506030f0d03020f07060c0c051006030f03080408092e0801030c050d0203030409050a2a 73
    0x95030f10030101c0215500c00501500804840302295044440490b40c540c0381c40c0706640403030210014145c0041c0b0403150800144000000070100c0015a080d82c0090711401000142200d2075580e4000d0320480c0041c0d4410400004140c0031310041700e44d5814009400e40364003420f4403503001d003800f040110341101070700041581e100042c2c80c6501c07500d0f12a00e046c06070095907054070801e0304160401a04035030002c0038004581c000c440c284440d40b10f00051680b50080d1001000c07a5400450040554900940041c40042c01c0803010130300d400505d4613040120740d09030038030200007155028100180441041540581d004182040003100e1441e91441003144880100070180000d483c00941404034500073354445038000b602c000c08500e00c58181e00d061800740d10301d600e24a1360301700a600380a8461088031381603990010404000ea4105402c00c40da40b075811346c040b41c2c548000c01c40860350381d05a0040074000c240c15000420088103000580141c0c1c0f119590100081c0c0d20f0180c3c640c82190300241c40070360 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 424083363 1250 424082113 424082117
    0x5090406020a110106090209040b220c0c023006070507020118120605010315090807060b060f040605120114031009140a030507150e0d26010603020a0f020708030406 72
    0x59502e516600340e400800780200c264240d442c0c240700081d065029001002d0201c1c080301c0c10011007002c0010011220f151003800290b400c0c007106010520160b56020300650a401d00f04800c1d514225800980d07203842030700e940400458208c0300758100300c100d1a450002c2030f004001610b2640340124000380a4005d203207000c0e0401c460400307038503800c0d20000400c402810320b9103150181c01c0c0082c01c0c640c001d494288400c403034285d40d0b1492160710021602c0350890b060b5000f103040d46407002d541c071660054440c484060f07a210030304020101001e9034500040c4014402a2541903c420769004500001c00c4140e001400154005031070480f00c0e9004201d40d06510001240007482d241710b4207041170300a101c061010094420340340c05405043d004000350212511928a26081450104850060b075140b482d4110321648151a01d01c1405d000c3c54460000d0110510150403400b0915400b5039825000c1c0c0c0200086580040d42c02425a4825402c080c901628001081e010f03141c41d080c15030781e11441c855201 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 424084613 1250 424083363 424083367
    0x70614030708040c0911070203060604020310171e0d030c09030f14070b0a0e03070f030c0b0a1214150a0803041502010b040509033103121115071202040509040602 71
    0x401c02c0020344e2900c0c081c0400f40000c01c4034100d02ea2003540e00d07034040b40090b03103c0d104100c00540c03d4274244c02200e20400b01042000e0b80c040c9030402c0b45501c603170725411850702d6010b04007042c8440c06244060201052405c00103003000504c859000e02240c1c2e140d0301d240c081100251090010801c0032040c81d40740755205955501a00e41d0414507400c0c02070725000841c0c1003000081c52490554003050002c1254400c40a84250b81c0d82c1e501003040f43c500c03030b100040c80d4007202103007045203803400805040d0b24411420409840d054218501c8100c0b6800500950907000c0e050500840d50715040e0001d0030070070151491602142802840e80e07581c002e502c1104801c1601321110707182680700390800b22114002400600c0300381001400d180d1280c01500e18100d030210060000e42c901d10ba050079024484002c019040301d09825a11180e1441c0035004002c0705110f000c0c02c5402c60403c0c00c0000050301e1002a8800c5068140290010050903880541c0c0c5902d600600061096607903090009403c9584610016 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 424085863 1250 424084613 424084621
    0x9020f09041b2621031b040e041110021b0105090603010f15020304030305040b0f0c030c1e15011202010201110315011404150309060e011d070614030708 67
    0x6482040e10440b07060b98064407100c0001d000303844070395220001e02904840c19911402104031030381d48010320445401d0210110711200c02c510004021a0052500c09036140c0c01c0d01c5108003c50b596011340d00640d05525580200424803010f5010111702d100200e40740c004590035010000c0d590920b0604001c00c00344907200d402c032540e0081e41110004000a000685c0300d40e9580151740401101d803091507200b801e0036681c950317064804021a015641d05446590404d418940d00d4440307500900140c1c14600400c12140c484040204050b0180c1e172070450003050ba0000d45040c0c05030202d28558000794691002c2c100c81d401008072802e00341558401000b02000c0381c01030004074050031a4001c110191400013044c400030305118040c40381c4940082e280e056204503250108407480c820742c0f00310500c0d408041c40305c1690300d1180e00300c81c4125010b10008a1602200308046084070040c980185071090000300c8404800010311aa10041003e4101001c1c01d40751003010b24003500c00140843c081000c404002 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 424087113 1250 424085863 424085873
    0x10020a1d010318060e010506090c040b0a0c02060f030412033e03090a05060f191a0307080d0905040216080a0201061e0314010509101a090703020702100309020f0904 72
    0x640e54481482e00c00b800f40250358144803000f4a01341c4410390b155400c0c04001129403c0a0310300901602c00c030540340e4034181c038010500200340c001c034001c5010000e00c2100700015035112030160201385058825180c0d68101850001c09060700780b8418030074181403501e0a0101c0d9100c0d40d400034140e07600d400d00c1c0005442003010251300510302080400e01c0101000307001080e140042c084010900c198101c132000c5d1200101416503000450310710040840f900030b1145102c2250308900c00c01100741021516140180c0b0000e4100340581c1c102c003040754464a50000d94941c40900315004103400d80d411454582000c104540c19480c098014080700c3c0002020079480d4800d500c043d000305640c1500790303154521080c06500300702c0ca80c03109680e1411172075403444400106118143c045c100311401080d41d8007400090202600320110041030110348043d011000b43c4441c1c81e841d2041c0140c1d50f00607901e004520400080d40024030244041601c0c0083c041c00580700c0707400007280c118046840303420651b2a4901 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 424088363 1250 424087113 424087121
    0x91a07023007050a14010501050901080118060c0509090c090123032206090503030109050a0b031f140a02030115020607051e09040c0201330306020c030417070810020a1d0103 76
    0x402040e141002e80b030171340d1440042d4090b50503118201c4681106913640c4441609a0318002807940780441da400315840012843e0740082203440a9041c010300f80142d280000d107501108894a1110f00400103420f10190307440714001660428603e0034140c0041d2000300340007540401003c02101a82c034038000c511416004c52203040c401d40c00501031000740401d140c46a12a0802c0c421038280a00303200c0440d2800285005007000c2190140003450640800e8005101a07071131024807060013a9105d222540030300003440020b00c5146003410159895250000720f00c242405a00407004541092040c0007160348d00004481e2020002c2c11692451090030f41c21480303502c06e56a10960151504145484403030b019000050284401095070019001e49001070301c080c0d600326041802441032000920002da403a6001c0d100e1004414120b0307081a841e03000001045880c0c100c190046c0d07001e40010000340b2420880700500b0144054107500380418680007030402c8650700c20302417000780c40c003800013056407080c0e00c = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 424089613 1250 424088363 424088383
    0xb0303070c03140c150403020328020f0f040903030912050c061306230f0108030f09040e0f010504140714010e0409051f060f0b0a081306091a0702300705 67
    0x10035460820345d02205040d69101e032100724000d0265000c003104146000400ca03400f0b060303106103081c042d03400742d082008400d082c680d5141c2c803142072031a4450540f00c0c4e206083c00e0a2107500c000030460b10754102182c410541a10304030810000b0000801000008034480350003107461100200389005078500b8002a00768600702900b400350b0004644052141095414001e1f80042074a803032598071050b500343c89201d07002c1000110007013080418290b0500c0e81c041d4415090880a540703403424090300c4282510390540b004c0d00c5d5840307564800c5030300745010b1040700014030400e0130185007800e42c1c00c0064071700c0c24241c05c0c075841581d5481003c024000c0c2400f0070007280c0c000007030042e0b405c603000f40200b0003031800d4040d800304604c1440000c2001d0781c480d400c690143c01c15840f002141c0d81c600c0101081e6000d1010103c50840d00d0300c9000c40000c80c41c015078170b41c990204900320118646800b0080c5404400700249205901540a402805080850100c440d40380c1200c407d44d0307200e031030920340d140c040225 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 424090863 1250 424089613 424089619
    0x905100618090c08161103180a09020f070203060c090319020409051c0306120c0504050c0f0313030f0305040218150306090106090b012c13140a0b0303070c03140c 71
    0x3030b645000d941d0b0280b031a45c400c10b10309082c60800400d840c070480b200141c3c801050410f5004000481c3c0c02d0980014082d14804001e1120984a07244c0d4808000d82c0c10000c00080c40c2800451180114901440500d82c00710088188506201540001a94625041e1094182d00712044238220a5450b40c0e08a0f8180302d4004041b1454801c00b1000c0911104c6c2440c1000b00203441c1410100f140007030522212039051300b294184103d10f00f00002c100003800060070003081b00c0010000140c1003d04040918441e60804030040703840441d50034041d1106000490010425240070304120050381c038007071111900341180c6500015603071800b07082181c16000f4080c4650501c69007040214010341504800305543c401101849000c14a5005603261400c6000c065510007400c0d19981c0076180c000c06590002c40e0041030030380108005a010412036014508503030f00d21500f1020815243c20311f0040804440d000c0e0011860621152550a49104070b4040100003481a50300c3d40c2e5851400c01c80c81102003002 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 424092113 1250 424090863 424090871
    0x30f13080f13080c030102072001090807080607031506020a03030914010603141c09060c0206040509040813061d0603130c0e1501020c1807031413020a090510061809 72
    0x900c2d40b03441d034603d1240c90890304c10043e482c0450300701030003612407165002c0c40001c0591441d005403071100c03050040080c1001024840003800c3c1604100d12380080032080d000d80315900306080002c0940d070209040c0a880708144108010300c0d5400145850f106401d80340000304009a4941404c01c0749210110f444250300340306c00401440010858010020583c83c01c442020303000c0d8440f5028000d440c00314130042002d50000b000300d54010100c10456601c0201510319058968002641a4100348c50941e88204041900d0110402080910020b4000c0381000c08910614803003840001001152440c0900b50200206101712100031030000441c2d400903242e030b14540c880207022003c02048074803203079030098045586125400424018098100a8001c00b01017506a4140040010244c040e1042554800c541b107516203803008614052034a0a40c03482c4502090300400250112035007104031454949800d0043c68400d09044208031880c0f42402c0982000d0592450765100700c941c4404805410 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 424093363 1250 424092113 424092127
    0x50f120708150a0b03060402011b151b0804050c01052802030a020d0e06030f090c101e05031015050c06040305030f0f100e0a0e0304030c0905010b030f13080f 69
    0x40071900c0081c1d4080c50b1500c44507070f036038031000c401030303801090304030b50540c03c01c1d030100b00554403a40041c40310b813105a40007400c607146583ca14400d05407450b51400070307a81e22201c004a099460114019080c482d2030144400d003003a03200d050b10b866403968001e050017000518642c01031014400440c50309800c54940100514683e00030f9240c1d4880c02c1c071103006003e00034004203454041c000020300c0d104050402c03411551202418a16420060014a11449000b6103d509650340d0142260307162620303a202c01400d04485200600d00c0d01555907003043c404144100f0500d112407d45040c100c49040030b0780404007040b030708151403d00c95002010543e010b110304100134503400c000114024150f011541d000b80d5900a0380c11200b101c142c409841c64520108104000600803007111b8200d600d00c00006001010318200c00d15503409948112402c106107841003001c1350441c82098014010049081d1a524120304040d450440040c005091b080510909a0522007154280d0320050103d01c00f899840113 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 424094613 1250 424093363 424093379
    0x70806090c1804080706090807050d120f0c2a0f08030f01090501123c0c0501030b060a08090c06030f060a0b0a0e0f1c0c0905010f030309050f1207 64
    0x202074031001d40901030820b0010a0388201100203031090780c1200007981002d4690ba500030145c030b03010400b650094014841304d404520207000e4069441d030562540d402c41c0c241c0080041c160b41450462582152500f144805803540110030107801060704003400601c6034000b1480c00840170700040190501c0354a14007001046504c10086002d00441b15a5015070b80e40c035a8220709441090092003600042d800241c0000b9040d0031042c3e805600791817001c15616070081440006150b0000c1145580c410a8081d01c01e002100c0c1560f0040d140070328061007040061404100f0520031020b01d40d08101102e000138a0410052080101d0f40c0c2c401450980e4905040d817590b001d6050a4079054840d2b10780c280002403d20444c0211200300d040d0f9200c0074544e01050301040b020000140040345c00901c02c06051208114103400040058442c160182c0446c2c10072002804484c4140c20100c4c44241130300003400480c0e006002003040360780031524000c80b060141d02041d108010140c2e003800c80d20800c200400d083c5 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 424095863 1250 424094613 424094623
    0x9150e03100e060907050d0f0303020c120c10050105040b0a06050a0315030809121609020c070302120106061d030304090513061b0216240c050a0f111009051207080609 73
    0x41204d084485180c1c8070810800d0044c25210018600c1c2c04070301304000081d0083e0050a040c0358040306031180c51150300561800e07036000c3c1c200300b04680c1050700205581c440a00c82c1c140074010956080040844c03c4000c100e5451850213902c0601c0800f01e90003c0d007522275003056401501d02024070265aa680c6800c224a0b040141320b103124a103c0d0103a021b00340310000d45c0c040c0b2001c1982036190b415187c42c0014000b540500e5444031203015581010015848406044040195440002400918200b002001151000b1151840800c0c1d80d2400845036400070542d022361346c514000180303039210500d41030b00c211008030004040c142042c250007200703e80b225000b0381d0343c0303101d400799a69000b01c071500041e8001c803400f841810251407940340e1820588206010b000001c0c0e0305141003034000e1526070903c2e281514208071080103100d10701c04204044601d0706500c2c000705550f50b0001c1302d6420006840c00c03c25002d41405041d030b118500a003035000700074010050150302d00340c604c0707030610f0fa41c8940c030341d = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 424097113 1250 424095863 424095871
    0x11040518311419060209040b15190f270e040b09010605121011040b040f18020901050d20070b01050a05062809030204021809060109150e03100e06 64
    0x1a50b2200ba42e180e00241c0440e190300a56424041e10502e08466035446009400c80d071000341d0441c0d0f598910305150f8458800e561203610800d084103803520824100e5000d070120802e001000c20081500708810181c00600400c6e40070700003404c0540121a054031402108215406a608a80d1b06002e100500c101c206085010708001d200900945880b101030102c594480c184840980e480b26642c0615240541d102c1e611405440004c1d519299903100005100c1d00710313402050035506922820400c401c80d11031704490401003101c080d8141813500740007a041e40942c1d005041000c1c0c42c0d890300300201940101c01400713229540d030910786944042c10200b1001c90700f40581030041c2242140420700c0d00d000030545200c500b680c401e0410380c0b050140445248580c3c1042a4140310080340040700503583d500190840d5040c1d004051102c00c00b80c0e0401c0710050024000c5414800044814414000920080c500c0704003907080120a913012070001ca40382800084c0070400b9189040022800d07113402041441c01 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 424098363 1250 424097113 424097123
    0x9120d14010905070e0108040c05061b01050a0b061b010e0f0706030501080a050d0f091d040605130b16050c07090b030f0601060e010813051501091104051831 69
    0x2641e0380b60a180c408851007a600c01010954400508456601c0342c00000c2c2d005225060381c0986980c2c4801003401c03600b00503401180786110300c0038045208024462682d000740e2900060065903110b0001c900070b4402d00300105448104410740802c044401d401564100707e807441200c406544803041a07480c6e90043c010440024141000002d05004c0040e500035400d4002e0098410140c5900c8290368802020030380c00180000c01d940012035070203039980102013520040549105241500d420011a00001d080601c0022025a0840404c01080d2002d40c01a0905003607641c0c40207140701a2440c0c0150407400c011031107440310101e0046a10f42125030700c05010340031214005100903850392168000d01404000980c41c03501e080f255032060001641011340c042a070f0b843d041c0c13030f910751908051886260442c491240c3d0010003154500f0701c00e00d811032208500160030942042e000030340e00c024262101e510000d00c440407400200048440603a518902c0082e18440c9a038072000c00c0c8405a8400305a403 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 424099613 1250 424098363 424098401
    0x3210a0606020f0c0f1915030c080907030303050a020909040f061b080609060d050f1b0103090803040f080c0d0f0e040603030c1b0915080d0212030103060509120d 71
    0xc0c1d03041c00011100400701107480a419000002818003503940c0c0c0202d171441e40102e10070302e140000600080716038040c0c500140c40084c22662000083c05030744211049000b04901c1c0307020481e4000c0007003440c0d02542c4d8140340101c0c450711100801000307800341903441580160a08180800c2164813008542c541c0e22a00086c0b0080304100c1001d424580b6a40e09078002c034100c1d10028102e46002c80744070b84c2c8084014a84a00c680d460344806280400c591041d164a9214188078143d424110101c07004155092805001d2a21141c0d60480355000191008003d00307502c1c400c0004001740d01c0c09650003d070440302200c52011852030010442e1100035003501c0414038142d011003890516014110540350151101c00d600580c42e40d501c1c42d1a50f0360400d11070344401c09c07480411030940b10300403000302c1030021103407880c243e00380f4940c1418504c606002c5070a5500c10800100020002c5007501c0c1140e4001000142580d00d0302000da050003000c04841002e500300040c51030400d4076540c498100781c400108014 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 424100719 1106 424099613 424099619
    0x12060f0b011b15020d0f051b0d0b12030a0507030801060810050f031c090e010b2506020708030a0f0f11250c1d090610030f0503210a06 59
    0xc001c0c03540350940c1014141d001d005040d0003841150001c023a031052602d02400d00d100383d003a0083d8294503503101120707580e650020b82c03850144d10000d8075901c3c0c941c203500601680c002001140400d00c07075070000c41e4080c450503515124840c0905801d15160800040040a0f0602c05246905200700c030500401d8035800005551050866203030340300c191741805200a009941604113241001c02403140341603d0003c403c13480800c01201192602c299180d08010f4080e1007060310141c030503000002803045e11000396010b1440d4030480d0a00300211000042da000560745014440070744904c06008080300520304411410004c40d0b00ea201c64480300d00b40e6903102c403113a2144d012200300a04000b021901300214048241c1c07280322309019000c0c901d00911176100328000c5000140c4605040300e2804104042001202c0c1c6414100790390081c1c1d41240300080501131800c440514440741890380c00 = true := by decide +kernel

theorem cover : BRFrame.Cov 423920863 424100719 := by
  have h0 := BRFrame.cov_init 423920863
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 423920863 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 423920863 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 423920863 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 423920863 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 423920863 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 423920863 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 423920863 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 423920863 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 423920863 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 423920863 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 423920863 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 423920863 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 423920863 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 423920863 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 423920863 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 423920863 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 423920863 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 423920863 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 423920863 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 423920863 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 423920863 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 423920863 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 423920863 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 423920863 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 423920863 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 423920863 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 423920863 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 423920863 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 423920863 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 423920863 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 423920863 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 423920863 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 423920863 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 423920863 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 423920863 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 423920863 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 423920863 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 423920863 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 423920863 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 423920863 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 423920863 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 423920863 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 423920863 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 423920863 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 423920863 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 423920863 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 423920863 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 423920863 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 423920863 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 423920863 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 423920863 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 423920863 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 423920863 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 423920863 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 423920863 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 423920863 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 423920863 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 423920863 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 423920863 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 423920863 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 423920863 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 423920863 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 423920863 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 423920863 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 423920863 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 423920863 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 423920863 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 423920863 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 423920863 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 423920863 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 423920863 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 423920863 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 423920863 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 423920863 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 423920863 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 423920863 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 423920863 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 423920863 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 423920863 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 423920863 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 423920863 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 423920863 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 423920863 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 423920863 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 423920863 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 423920863 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 423920863 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 423920863 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 423920863 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 423920863 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 423920863 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 423920863 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 423920863 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 423920863 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 423920863 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 423920863 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 423920863 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 423920863 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 423920863 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 423920863 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 423920863 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 423920863 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 423920863 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 423920863 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 423920863 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 423920863 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 423920863 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 423920863 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 423920863 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 423920863 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 423920863 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 423920863 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 423920863 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 423920863 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 423920863 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 423920863 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 423920863 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 423920863 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 423920863 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 423920863 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 423920863 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 423920863 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 423920863 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 423920863 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 423920863 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 423920863 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 423920863 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 423920863 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 423920863 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 423920863 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 423920863 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 423920863 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 423920863 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 423920863 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 423920863 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 423920863 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 423920863 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 423920863 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 423920863 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 423920863 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 423920863 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 423920863 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 423920863 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 423920863 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 423920863 ≤ n) (h2 : n < 424100719) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
