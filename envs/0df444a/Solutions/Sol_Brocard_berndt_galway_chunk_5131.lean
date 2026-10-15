-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_5131
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T14:51:17.501249+00:00
-- url     : https://prove2.me/submissions/2f463059-35f9-4582-ba8c-dc7392588867

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 922661870 ≤ n < 922841726 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 922663120 1250 922661870 922661881
    0xb04060911031509040206070b060118080a1b0605090d170f0301090c03151203020f0102030a14070e0d060504030e03070807170a02091b040e090303060f010314040204110c0708030909 80
    0x1440130500482c2c0140c80c46e4903004440d150182c0c59003001d08400d04000105201400c10100c59907188050031802d005400c2c41c01c0b013400c04032481c0107909160342d0f80c2c0c940c0d95030800403d60010202c070000c40c8290380405001c0084d08150480100311404086010400140c034480b00c010400294141c52029404210884200008804031000c00054082031031514106101c00c9a1581c50f0401d114031910444215520856103142039030003e40d0245000364072100f4800e802205603460580c020140c1c41e20012802c040070002c1d041450544000d0039565444010805042c8918460032003c4800f1b01124080e42d40c0b040c41656404091144c00c2c03036040088059070190070080b958521042c4c0091590102e41c03214004184010720080c14081e51800400002032240340f01d01100d03202e4110440615102d1522000307210203608103c0c0202d0405103010003a40c13240b0a90155150004d070113850019070000006041000c51140c4401040580725801000078440d200100038001400306031100c16094980 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 922664370 1250 922663120 922663129
    0xb04050f070e0915060c1b060316050904090f0b09160f0b0c0307020a030309030215270a172506120506031504150c1b060b040609110315 60
    0x256400380001c0c0b00700d868410286030000000740c02c92034240c00039007140390900008000740e00104424019400090b41410455610440b044214400b9585149985040501110340c420340032552400d001000c40c1c1c50659407500c3d40070101040d4004000b90245c0329908100b00d4600e421a0101c0d81d9101c0d041c0e0500f07029010040640880c0e52a5000b104614140980c056a5030040f090a000f548014400c00c4051381d1002c4822004500175114111030f0341c111300601502266142c80104028020440c40040e00c034000d0100c90700910300b50600346504154000507080001641c0301c2000b14500c4688034644a90214400d4600074039401d800900742100d10030354810011510445020034410318404000d68080d07080b10794000c00045c141c5403900042468801701d0002560203507592a0721682c840c3c40e0241030300c03480040080354200b20819002d0390500c00946c84000800610725512400d103050fa1b84c42da030b0070403400391031491401c3c450001201c991041d6a0001c83d01c0154003240b09405080c0b5092 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 922665620 1250 922664370 922664401
    0x30405100204150c060b0405130606050f01050301090e150903040f12050705010c08040b07060e0d020c0913021f051c06080303180309030a141515090903120a0b0405 72
    0x400304544903109503c8030b02030b40d50040d10030301a5001620317910340702c01d0366a81e1710a040c40f4510900c0326044043c4682801800c5503402d40120340200c1698501c20790b1683c112040ea811200189130120394030280600d100c1c200849403c810413943c03140c00500c6102c09011000d001550351611050b01980c1d41c55541030010609640007403c150405a801d0049510030350b19580c4490280c01e1180c84e240d641d0711003948a5110010a444131591094403100c800000d100c00341c00303422248000c198030541000000d02c00d2a0241203c0b441d00841d685036011519800b00c084984d184094105042d035030040310241c665031043c405103401907002c502c405099080d41c0306850035548031030029415541c440042c0e00c10440302150310401c4d40300911511000d030394100725010400e0300c90059580e050720365560141c900899062080c0b4400c20207010004510300b550742ca101503104c02c0343d08820b5a01d91a005d10f0031480340a4075256501403010400c003007601c55400c900e00514040e5001c100c030743c0e82c050071050b1128 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 922666870 1250 922665620 922665629
    0x30e0304120b13120206010f050405040b0a020a1103030f01050f010512010603020901050c16090608010c140a09050307060804121119080421020a0807050310090f17030405100204 78
    0x1981001e00802044032010456402220520442e85010103070f100d0348441c100915050006900c80c02c014054202290f03480710040505a40510080c1007503500c03108441c0c1c008192020140c0d010034041406441500321081030f05940c0c060365a24146580a01c42848090203007a0081482d07000c6581d265224a086a80d01ca046149043d0142d007030240440107980881805810040c0610610074400010301044a46031300c011b902445192415844c2000e45265074480c0c07005903d04158041d0054104410005070242d8080f07260341c6041403581135424032401e8100301e40601c01c10401040311a04031280f00e00950107102403010181444c402229141c00580c10094580c1007080c0300807002e00c031140160b1503c0d1151b126a410aa01c0300742154100819003400c03060302001030510300c02c1d420600070b88406800c60b030010b420300604250102c1d540301001c0400381405551003c182d000d05c5404504d0340c8125074010381c8104440304c440340e4a11580c00c10340d010b513032038000c400b4408401e0703815100700c80449 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 922668120 1250 922666870 922666889
    0x6130506070804080904020406120507050f07060b042c010e0a0c03031b06020c10061a09130b03010609020901030c090f050d11270c1e0c2407030e0304 66
    0x1d81d50200101c4420001a10856191a0500404d880c070381d0786001500c040c1100c0c0d902d00045905404003c02038403005803a59090040130881259a003c4040444000a03001000882c502d0a0100450001d012070030039081c10310144100003505c044104220401c9003941d0000303000c00c1e03228282d2030f51520903480000704800d460303010420000e402000740f1034982080c40b60420000390305440b070070143d80c0701c50035400c0c11717401084421410246522400c00645480b840035807400c40c2020b6455454412004018440d46240c15420090556904809000302000d402840807030398810005000c0c1d004400c0c13a0340400e0808a44181c06032040d42080c040b207217500e0b042b0700c07660f15140902c04607040416003690540780208801c050364450641c0443ca15a0000e1401c02c10f0342c0c5270380030340c2c09081c000d0943e41c560341c0d0400400c003c80c1c1150481c040104c4801800c2640c52070350704403c3c0d1400000141041c0c6d02e80200b4410b613a020040e0481920801040c2c070180310801e4803130806034130f038800c50042030140c = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 922669370 1250 922668120 922668133
    0x60123040501120902281d071809020c15010509060f12030c250803030708160302120403030e060a09210903050601172e050601141605061305 62
    0x120340c4240180f1840030b483c500006a0740b21360350049075001d4000680c0c0400c0c0440304c50051441d48002c41404000e14414005a50424040d100c45024080250419042001c3c0c2110414241035400214000f010051811551854009242c0780c90700aa00b07010340a1208142c000545814100b40b042d2017250020001c401255600c020061a80c0d00307084e219280c0d00c8184806031065030301700000101c4c139600a0703001c00424010310a10f9901c8070745410000d8941c20034003c0c040e0103500421710070b8104c440420307400075180004d9401c90007802000146418680100306000901d9019800428002a081c0550301e82e076407101400000d071540c40e0350040c0f00800348003030900c500d5180002e4010340b4110f80307003004085070b4a880e50fa00c0d10030700703030460b01080c8902c8107124000d14082080700500c181001c40c8603003c141046601040c000080c2e072010410740c648000448036882280342c542c0300303405403a400d51140d6401d000590910340c04942169039202d40e00103d158400d900c9480005103500000a002 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 922670620 1250 922669370 922669379
    0x313061101270308150a06051b240603032107090e2403010212010b1206090c0307050a03060b0c010f050c0f1903090204110304060513020a270e030306012304 69
    0x28510b4008192200d4081740e90030841c126074421a01c00001c09041e030719241c54144403019102440c030002190000d5500405217002c004c0341f40c8041c49401b00d10041683c1e840c0d501c010100e41180f00380d031841d481244120170184111f24940b4202405101a40d0711100c401b6202d0b864070424680a59851100210942e100c2c1c002241d60000c0c0c991409029001604245071038015004500c0203801c02c500120021510342042d16210724103650103c02202c000465080882c603140e0903100152200e003c00500181700040c0d50300a8000324000d0110f071007213581e100b9500f044240240b482060348821182440c0101d64a50070310010744a075078039552074240c50200e00180d06206800c0f182202002e06072103a0000f4050b036994481d840b5080c0000c49402d540f40742c286060b50031160010021928040312808440c0540c072000fa841d401e8643c0510301c5040d00c0700d40301c1c0306024072440c50140c2d0369442c24021503405413500800914001c400a0302c60500015004401d20245140c000312641c26030020b000802 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 922671870 1250 922670620 922670627
    0xc0108191505100207230609040911031f0c0905060a180e01090504020f03030307020a060209181305070f03080d0203041509140c030d0e040b0303130611012703 70
    0xd001e01d00c0a61252446580d800400d400040281000b405a0030005c401c00c4481560342d001c56030011004071503ca040100e50000b0b0150041c52070503030069907203003070b5041080f084d02d401042e9800020202d4031042105481214410300c0201a12869030034071020426650140501000307a50f4014159801c0021054084882ea981480d0007403074008078450008034284a00350135406807400140c042041d24250050009116110441d107000354000c104010b4011350200301c90316015804400540d99003201c06c0000c0491070444200c413074107141c540901411580c0411444002c501c504191001507641b0010300c81d071900300303210240c4150300800100c0048015a4025503026208055401711a0b020b10400021240396a50480340700c1c4152031090003042d8108600c060b8200e04400401305a2102e520080a0307030200c3c900140116100c203c0035850765001d00c00d64807900d0480b00c002e0380080d0b44007801170000385504c512407019441c2003d0503032805900303519084c0b1004402c40808000d0300d541d8049 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 922673120 1250 922671870 922671881
    0x30106050121140a0e1b030d03091b140a05030105060102060c0717040b09010e03030418090507080d0203030a061505120a09080a210501030f03080916170c010819 71
    0x4005551a0a1040d0300040e020250380510b844a40018460b0178403a480c070310340801c80040c004900e01c0070010380c5d940d95000900e610384d88264071740030a00768198940f5880c11044558000c4c028200c0352004510f6007004902005410030850f07d040d0780581d41c200381400c032075040d240d05e40141c001c88001600b0f6900032008181c0d0900c945014405074080800c0d9401c650031541000701c00c0c000004d11400c2c00d40e4440c81003400041e0032070145282915000d0007540405581d000308006a4031040000c080c4201448000010f08080d4151000148101d00003034803644111692896940b40c4074021841c0a18005a1034a440c0941c80b49441c0401c21074000b00b940d000141505081511050810000b42102000d440604c01e07540794016845644010a030003540240c0000841030b14050040001c94414200e505102da0103007090112600e51200441c1400c400130b01284c4145542200056400108050107038588280c00546041088860046541c050141d5000c4060078144003c4880c000099121 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 922674370 1250 922673120 922673177
    0x41203090b13031712010b07050114090d110c0a0308042402060c091903082106030703030c05070308070f02040605100e12030903121207050a05031909050a050f0c0301060501 76
    0xf482c0c01c0c581045c503610760414090304141038a520106800c0c003040404d00558581036640101c4200e14034104c0c0304903a0740e042c0300b0b8105040118220a118801d0014002d40440e0b000240c240d982c01a100d0810340100d602621500c016011202c0118442a5100300d032458440d03c7c0b940500745948071219150100c1d04000e250303a501008241d03503086891155800540190f10800989450701c40202d9681d111442030b12150135010465000c0100c03942d4041200820b8070f07403608005449400d5810300d00d103040030342d400003041000006040d006002e807411422403098070845003070010585500c18044d03450080c182c9407002c102d103100708000fa8030300540403001e520700b19003c0380d086c200c0920003e840d00c845040d00c8100c80d5400540002c280006910441d4004864208240750112002d4018030a1000410040c4c0d244c034100801d08101c1540e40100b84000d8205c8100c8491100c1800d0141d01c42c0d03008449084c0c80e116070f4900390018101800390408841c0141c44901c0318403012a20700c0b4044096248 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 922675620 1250 922674370 922674413
    0x90112021306051f030510060512150d0312060504021215030f0a0602130b070818031009050606210714060c010c0f080604141906050303041203090b1303 67
    0x20042102d03102c07208400d6000100f113035440c03403124805802a00722070001e0174401c510031880c1000d101340b42d00182268901c0156150740346060b034030b10111407030441041c09a01c0d44a0f80100c051003d0651281d83e60b00e041c800c4e50410401c5990703440c10081284500794440302ca0100b03490000300004410248143c8002e80541a01d51482d00740070701a04000d00d40034201c5240c0c2e4041b42c0011201c00c4e01d01440040d204801c44a441d041c491b44800c1c40354010012200740600d00c160300d10721603480a014405016401c0780080c40503a405107425611044101c40040c007855100b49810101d00c6014840c6c003011062034082c0065030305100b0b1008002055825498004104100b80312000d002440781c0200325025940301000614050401028000e001d0170442c419424480c2c036201170003503a10040d40260104072002a0600384e0440507000c0c201980c08554903000116001801e940c200c1d00080110b07100f943c4414045480300090301c0c160003409032091a444401e00c0900001d11000c50f0000c4100d02c005 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 922676870 1250 922675620 922675631
    0x81c0c03030e0726010203010501020c09070c0804091d0105100501030903090f0e040b0a0e100b3706020312060f1503010f14030f1f091b0302010e0901120213 69
    0xc480780f40c0411684141191107008103601c4010269103501c0342c0803007500d0025031a5514000000350358103000c1410511038125000802d04603030040213070b51601d980c40100d650715290380e01e82910040012a80303451250b000e1031003400342201c0600c1134602c41d5003613040101c031441c00c1c800110004d0200b0401103051103540c00000c1200c10002440f04002c041301c4052480607d05442d16105015010704842c14460901c04084a144c00110320301d031340c82110384c100040003642d4000040d52140005200c0f00c18848904c0c80d1008035410b041034103410800700b01d60201182c1c1d070f48012662440350008114901c072541000c10f4071840c00c0e030008205513100910005584030f042030499526402a403000e200410224001c01030b010b6005c442a001d0901140600300708440072031b0440c0c8643c1c10700c3c80149000203104c0c102c001d00b0740942c07158078003541200001d9003003140c11a10f100324a1050105234041f4412158194541c40c0040196040c1c0b0400482c086050500e6130174403103000400803100040c1500c82 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 922678120 1250 922676870 922676891
    0x22080d0b04020c0102090111190f0f02042a09080303040605060f1f08061f0806032404050f06010b16030c1a041109060d0803130501051807081c0c0303 66
    0x90025180f03001d1103c2c001641d400c00f4400240145084a181c00d085401840000200c204900c42d64080c4a400c80002a14110245400d01d040388049030025441480c040304911034800d102a18604041e0b0300c80c6801011048040c10f1390768001503c80d0040c00e90081002030b001400c103400c803c4d0001d030064a00b9420700107a10018a242c03075801407001c402408403010700e0000d5801605a0f40044054550200b003030350440c440c1c8560f404000441040c010003801088040c1c40070021402c92045002c1510044640b0684000440c01c06030340540d4144038040312a174100c80d0101c3c410307049030740d56031600d071400d0b651011358000b1840c0c0407403c0c0e00307000c0d92811500c00300742486044001410411410080782c60540b40080003407074103143d003e00980841c4100445512030004800245030400d581c42d8695031081d0131070072088207050004150f03508020500590410007080c441c1d8022a0720141c0d8507064850702040e0340c522400c0703402c0281034a181c0200304480e0140140a08040c0a450041942d0182 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 922679370 1250 922678120 922678129
    0x9060901110a02030a050d0e0f1f020c090a091106161205040b030f010e16050409090602040302060f031e13080901050c010c090503070f0f17030d06090b040522080d0b 73
    0x10504140d804e608020707c01301d0100d510200c0e400840100711103220300e8586030404129145485c0200501e00d00d200e180142c1f66500800001760880801010704a06181c8401c8607006004890400c541d50a40f45501c1c501603d80300c825903034840c03003600e03122203000c0d000d4507809080c0c1c090300b130000103200c4100004036034a504400110301c100c0784481340d6001c0e54503100b200515888011b10300c4000c0020700340215100c42d0300408803411140c00c80004100c40c010b60400000030f104560000703500c4107001800d400d406418402843c410801c0410582c040840c5440818840034112103010300c070040c602102c0001000500900740c021018500a400c180c0003400c040e084910040403100840c0c1d01150804c801d01d42081040c0150100030300030f42d0064039014841e81002c2c114000c5140c1c0e0501903e1200c0c1013441001914000c192a200a00c0740355940c1034024003c4c652001d0040c0110706007400207041c0741b44802848145c040040340310f0100c4c0c04c251211880761f00551242d0407404c0e19103040710000d548 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 922680620 1250 922679370 922679383
    0x518060a020301231503091609050a1404080306040f0b1e0307050411040e250c020418030507150e0a050601091b050d0c0e0918010c0509060901110a0203 67
    0x4200040ea0303541001c440c295084e1a10000b5001003c0f04100b04055854040401590440180e8000c0c6c40c0d850700c0c08101d0802c0d10012110a851039034840015110219810950041008103001c001d28626062401e41281040b1000b9010a0301040440c00d1400c0c182e00003404516041c9001826100c0640000c0008088080c5220051005016400a0326081c400326000b880101d40c10003174400020072881c000d00a6120303042c08142030200041c3c8000407101d00781000d01e402700c00104401a000005040003241c001d069024500d440120302c88a100b221296030b41c503415031070b80c504007040d0307958030324140c41c0108181c40401d407035545089a8001c10840380c8542352148010300350300c6d810100c4480c102d40254843c030603031910214030001c0c840d4101d0102c0c2c4440500340800320722601d038a00c0a69034406403403c8950060341c5002001010800807220030014000c40c0c0080c40318403ca0301045409000d00040c050744514100b0414907950b000350302c01e40001c003006054446200c2641c0000c0e08121 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 922681870 1250 922680620 922680631
    0x2210f040816090515010c110303130807062102070f060e150a200d02070c23150a180306180c0f03030906030903020c190f0603020319051806 62
    0xa200110405a100707920b50124080d200b0040c00308414607005500340c03141c00781c0c000c03142d040c0800c40c0c01850500c000b50007040592000a41140d65801d21019030f041c1602240c440c540d09401001380c00b141c480c0c452111039a0310243c080b100030219134211200c6000750b100d028122140d400e04090600054458010081c1e030410340005056051881042c42030020801444007030018a01800c610042c6c80e5582e084201c01c0e40c0780b10792603c50111101c0c0388007e21070154054039001c0b0305080010706480801c01d03000c401c0810020020205010410301054250394100800000310a0100b1911580314aa09000003c402c0540031a1690382e0f880380b40c00c03140058416200d440017100c0d0042072142c41c030b0380900107280d01d182102030185151401000b042060160000f09501c4203610b8050520820010502c04002019094002416840d0f03102d0300f0101c5c0315510803a000c0050000342a40a0f00c2030f284140500102c450020140f03030141e0000b440000c14440000104a8040241c4030b020840b0a2240 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 922683120 1250 922681870 922681873
    0x304092c0f0a30110c040509030a080712050907050f0402180609040605120c010314010e0703050604022b0c020f190c1a030402090a0606021b010905060708070b0108030a02210f0408 79
    0x340210800d405c0840600506000d64101030512800380800000c0b103160b54410302d44030075503898a82e0102c41340c0c400000d81c03002a50803c1c0501140a40200d9100c00700c8100310b07680059010b0a07000d0106031302031140040c4441070385a1010006082c82c1004241516004000060711921440010071800b00d0504648103030340b00007005011942c06106040f429005078603260107c1d8074007401c10708080e400401800401d6114008680280c8840d01071302c0c0b20840c1114055240002c00d003040080340050706060b20640c0c1400041c2181500108150960007022806080c000d0901c201a10054103140011600400780c03010012750520380616035a000700c140c4005c20744e0703410306004206001502400400301245402e40030402240c002030540c4e003a107034104424162000410069602c80b020fa81325a411602c005000010400000000c00169100d445800e91698844003040d41e40c1c041c241e50b400245e800151401d50141000c00d2107040c0756000d102c11440d04090600340342d03c507003003540120101e = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 922684370 1250 922683120 922683137
    0xf0312010905011208031306090f060b10081302060304050f071e0501080c1c150603290108070809010b0a0b0c15060f040e0304092c0f0a30 61
    0x10030a2034041c0320300512051a10421044c1c568403580040d01c0040d04403545c1171400c3c20240d04000d01904003d401941100040400d0400381c2001e0010300141c01c1030920a500409414580c54000c0507030390300070020180b043e0181c000c00c0d424005035601c041d10648203480f400c801c40c00140001c229400c0a00b810040042c44098159804000b990050304401d0500c00c0101c01c200f06601680180e50300c0c07665458503c2060040201407030014241c3c0c80e84c12014a40980000c500d01e40c041d000848502041d00c140441c480c400310a0b91094401c8042c6540012800c40200307442900c5901000c0c1c1011841000148041c2c50310300240c960030f61039224811031000410701c002c03050014083d0180640c40071003007041c40d00d03001001443c18034402032407034851551462046042001041a51301500408000f0028100b83e00060b9082003841d0110901c051080c14480482640204101070f518142c803000342030b524000ea039585046c611680c141d040303242c40c00c0d2034802d206c0407103600d400e000800c0c3d460741c003076 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 922685620 1250 922684370 922684379
    0x1020d0e0a030f0923062812020403201201060602070f06030e060703020f0409050c0d050c0406020604030c11102307020d06051e04140c120c01030e0f031201 69
    0x40310040c40c040b00380058028208140d81002d0100f1030f1080b10517480c4010380313610344002035150180d50000c4506141c541e450205c2208100300305114418251a1100024501001d0308140c0c0f00345c3c04020a00180d964164550141030529030511610092400c26280362044142d4211002d0703600003401030744040b10400140480400b104041c259510303087c03010f001c1039410b80d0364613640507040004050b80002c504a0f040300c50340c1664040c0600d8030b018004d0703061035540e041c210b400495002d02c07842d1429000c10300c4485001d04407400c0301d0094010f4001941d4a480540c0c0c40351402d441528800340e509440c0c2c12580e5140581174117581c1d191211301c1101c0f5900c001494028400010188400d420400c500160b40c40c04040b11800d40e111801140c2a59000d070340321900c5c00030354a100540c000c0c0b881403000b000440c00304040c10340a890100c400095480381000f118244942c1c03035010680240b0620318140d44a0b4009040325102c003812555180d00b41c101e040e10390351015481c0078002007000e0042c030 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 922686870 1250 922685620 922685627
    0x507080c0303041b03021f030609020c01060f0902030105031b03010b0d03200105011a0f0c0d09080f07120602070302150a0e010e0c0a0b030a0908040b0705010c0309050c01030e01020d0e0a03 83
    0xb0300c4d0340d94440402c0010f03421a800f20b109800c4900c15135120003d4a07004a403401d00c25006a00680844c080964507540c1c1100d00c240640094015002090801b01c00031880d4401c510aa82c101c1c1e00c01001040035030070503450b0b21103592280d40c00c00d8143d501e4139504403c40d10392208140d0080d1180d5512008407400300c1c0400004080810314203680cbe4184401048841c1020910564000c48000c080c0c0c0e0320004031444051500c1100d40d1140c035801101900c1031642d0304481e103a002c940c7d44134113890300301410703144690b100e45260083c1141c80e80050b55200c0440c1c8541c0c09484013901c81d00440c1e51800741011341180c40304040310b610007200e486000654030350300300b0f01841090700303103240c01424032180c1040025131050b1030340144c0c42001004400290f20b54440c0d003040c103425800882d09540e4946442c1100019482684145c0d003e41c2086030000d1941c0c0b0078410311300b125030404080c0a0300c40303c020044024117000199034200b59004c2c08400383c02e03d25031040c00488895a002490109554613020b0b = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 922688120 1250 922686870 922686893
    0xf0a03021e150c040e060d051b06070c060801080721060209040e01050f0a180b130516080d1d03071413020d0902010201110c100507091e0519030816030507080c030304 73
    0x407802802c009045c7e8001547c00030b0540460341c1c0c0410002e1144c0d1601d00460601d00403c1e0025080d283d81081c0010090342000c603e9041c0c43c1d4407416a0111911903807181882c05c100070030f030302446850f90a05c03030100b010790303016241800f0000e001049551495414a00303441c0c0503200c0182100c1d100080c0f04012107a44514404500c0c0060400c12507045900c0700f05981d04003d2403000041841011641040401c1c0840c3c42158079030b581c51211a51030715a442e5452912050780700c00702c0d010041c4071503540c52940c2d1810100346d0041c010b00045007010724048401e00400075080d000221001088035550450010b0b14071800071810001c1c440c40940002400d4a0790714550081c20042001070701c03141c900c081390030030000e201c0040200303840c5c50740f01048564000c1d56001d83c010940001041c3c1c64110301e2040c0100312081100d84824840c40c2c0b180300300c4090014800106087c104000d04040e02c0d14901c02410f09501034204941020500d484041c4a68000f00501039140c00c00401c20040040c1c00c80b20 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 922689370 1250 922688120 922688131
    0xe0a180c03060f030c03080c0f100203040b01050913031d13140a110d09151a010801053a0f2a120605190c020d020f0a03021e150c040e 59
    0x50f500b241d2a503111203850840c1804040c2104c40c00040700342d400c0808001208210880d1400c07108014940b5024100079002641d00b162815506000001c940c645240070502907031140306040d072400116074050380c0e46000911400b0012611840341285540c5802c1c2001050b507440f0004120031134a01c100c4583c102c07004020007a42441c0014140d2580d4503030058480f0b203d5802400030341c54500d0b0600e14840748809401d1010720741840000010070112114101e5851004c0c1c841050380c1e40c17114104104840c07505226101c020060110350b460b80c0403410312072503450f80304503c044601c0d021f480d000c0c0c08040b0440f056599250940410a0490107001c82c20000c000520341d8000701c030709240301d140f80b41442c00e03005000d90741c03036401141202c082a106200c42601c20a000c0001001c10b102c00380d00c8003649142503000d801148100d115690f8081400c1d4071040c2e055000d800301c4800f9191003221700c0e00b491445109881106c0382103041a600c11000c0f80940c42200e500c07619a07181c0901d412140400808 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 922690620 1250 922689370 922689389
    0x5031b03120a08061504050d0c050906010806060a0c11060307020303040512090303070204091e05061519091808040b0d0501080c010f12272a060e0a180c0306 69
    0x105000c025031100055801240c101c400701217425040c1c440300418040c50b0001544074008a0b03001b002c00c2403100702c103002c0f10801d507403c2000c5d59698006403542d04044401a400c000304000542d5401d00ca00c0c0d04180c01c92060703e00303141004520300030504903001161141e01580c4004280b0040c44020045080203105028400745005404804291203001c0e41200a020b15265032001c41004402070f40d000c401080d08149600040d62400c1681e0b45101c20b8a482810a01e640400c0720281454400c41000c40c424024510f8198501410319005041c1005401410300704e10441b40c0c0058810b00080c0014200c51407419100d0064040d400211841070f809240705038410642c4c107200c0c2e40c2042d10114200078605124508003403091085004d0310180405480d002e0340840e030b84040c48032b0040e40c1e1200e24051040049003104008840b118003030340c90481c0b0705080d8400b0040084600c80c52500441e00b001a02c4010711540d1400c0188a0070b14090108251903120000c0c06c2e25958940702d1400201040c45 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 922691870 1250 922690620 922690627
    0x8070b060a0315050a0f0e0d0806010e09040b060105070f030302040e010b0703121e090c0816080318010311030a0e060a02130b160503030903040612020a080a0f0605031b0312 76
    0xe5403958148940301c3c100ea0450740f5840001c0c1440400da00030300303241284000030321001c02840c4079580c6501d00814040e003c10780441c042003042d403003030032100c0d50288081c01c5140951a292a5001c6c40600141800e0400c00100300d940c00007280c0441d4076278041d119441c003684031820020701c280d0580d01600b040702c0d4845c0c14050200829440001411425480d45000541401c8183c0a0084500000000301d8080c14401c40380d0402c048802e8a10131202c0140030f40f4a080c07010304c1304408102d40c910880a0310392090100185d280d2450f51104081340c2e050400161788010a100000c403074204803000d21140b9035a0041484e07040c420302c03146038401001c1350704600d844240684000081854000d50220440c04921030b10000000f03407000d00c4407504502125180c0c0303840d0707404c13030b0741d0b54004d00038540000c00032a05548076104500a85403907130a0742d1201c20b40395480307601060080641584039403a4030f4840000061340c0d28148818044500540c0003030310565006070501d480d042801641040150081 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 922693120 1250 922691870 922691873
    0x516050703030c0c1d040204090f050d0f0e03120a1115040809040e0a03081614040e1b070803070522060201021809150603042a09110703080103020105030901140408070b060a03 77
    0x1440e0030355020742d04948c001042003040c2004406800103090051180c0b041082083c001c3c1d4001301100030741100c95480d00311300740c1c9450900d07443c1c030b50020b43d00b82005d400340603030300105016041d006084040101207440c0c0c5006490209240c40d010b031015602c90400141810b00c40c10180a040c0c0c00c031085400601400e1002d503001491914018005140b03500003520101301e151143e01050107510444e002184c40303544800307218540107001d440000d5101c02c1041804000403200703096070510b58200c0134643c113550b5546025a03441d8400e86000c5483d10f038811441e1000a46035030100040c2420b540016200c540301154030070300c002111000c6208261007810402c100000209941601606542640d100c0c0c0f550328010010380111072100049040e000e14014403801310207007184c1203a0920600b808407030f000135840c00c0a4070031014090002207a240060001d540141c5c02181c0081d0b50000004840908114509038400c2c00e560440300c04400203265000d204015040380c0d081842200c9405160303246 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 922694370 1250 922693120 922693169
    0xe1302031e070c05060c030108060f190f06091505040c051312080c0d08040507090c08061e03030c07090542040903021608010209060a0516050703030c0c 67
    0x40080c515881810034001461452150404040d4960301008882c011b04005018105d6a0401d0144210721700c0b50300005140e8480c00881b950207044420444012240d03a00071002c0a030584849000780962a0003001454111758403609841c81c650340c0748035243d10304000411091700c03a020500010090305000c5044480c0400301d204048034007440100105000c145400c1c030840c003401c203a44500c3d000751807203aa001c9070840b010b14821481642551003071a01e07580c0180031585d40c0c07071035880000c262400007029401c1c640b901c2c1905c02c20340504041d4030315013200041d02d540c0c80b2084148441d002010100003640c0b0501175036420240039034071200700404880b0351031490958031941c11180e005001c1c80002102e906038184c0002c0e02e002d00140070928903400c01a42d94003821141c1c03240519840e0001404003018402d50741c002200500162034079040c0075088840342c201c1c00c149038115000c90201d0001500070807130f400007988251200070b070000c2d203407e1510160340030382d0020300307030001050900c8a031201 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 922695620 1250 922694370 922694401
    0x9210e0d1202150720100915180803041e05010f0b2b02060a0903020402030408030402330913051513090f0206220801020318070509340e130203 63
    0x480004801740864840e0585406c0111400088861500c00c1c001d00340031440c524030000380c440d003006000d00c50741001000341d8452022009442c4a03003c2c00410005068000c9840c401c003060045508503118030f881b454210384094035440c0c0910381c0c41041810605060000380e2000c03056140c1801c002e6070703400c52551001340401c4002d01c5074a0004490300c426008c0e44204028580283c411500d0b0714003442c20f02c00702e074000d4030160301c241e140794461140c1c02400310100420040e004502450890500b006285030340002c6001c9034418012100440e102c1c05512503184207500584903030020445610074400d00003200c00c2d1400b211402d140080c004101d0440800011039070507600bc43c0e44a94100340c168646200340d440e03801720701c0038910006500d0415000340d03016148589085000c541d804000720341e103042501c00c29800044490014400040403000c107815144411070402c403960ba9030340c161001c00301d41120880401c0010b106021103091058400745010b078000b000b14914146800344200004 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 922696870 1250 922695620 922695647
    0xc071a031602030c15070909021603050a02030705060f0f0f01081221090d090f031a07170c13090626011107031d030109210e0d12021507 60
    0x1d01d011415480c98420801c0341e4410b020203094941c00107640f04011420344003030341c0140c0081c65440c1d000c1414005031080b24101000b61099124810b0a95015941500410040c0b8190300083c4940d101280303007806014420449500c100215203044901c01e511070001800045c0d00c1c258040040c41120707400124a28410440b00a854803080501103450404000d0340d44036801000c02014000c0800c800109044110400d4803022100c640314151207040c4c0c0c00c40e20010304840c5242b014102d0210b54100b0780e5801c02c525240c24107110140e80360280c40c1520558403100500f00004610401250401c03c142c05005052410b000917403034514002c10840f950981e12078170440c2c03074511480041096021815607465002881e468100d00e0801402110700da180f00015030301048146042c0d840c040c450003210340e45c00b2440d42207200c0b0711400c09080242248840b03081c0b00303042c03040031f03402d0b81c030b030720400c04c2143c461111101a0080204001d0070248000c062400034440c1406011301c003900241d10301d0105 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 922698120 1250 922696870 922696891
    0x30603030d1a0a14120f0c04112503080c0301060e0f01020f07080c011409030628051303020c01020105010f23060706060e011202090a1806110c071a03 66
    0x2406508031a200042c0070818652121103000002200c4d0030841690154150803500301c40144945e007400c645505941c0c4840000d41c1080140110a03e4280e0040700055581c40c00300e401c0181c1564444140d464907071845076000d03400c4004904040c2e02c01610f6a020303118101250465240843c00350642002015042c07140c04042801c032807d904c01c001c41054030400c0000c03511120f94414865840c0c14041130031074001005246d00c2040c140120003112500600030b001400107a6409001c610943c0390240075413070b0369110304280704140544d0b01405e40034104014445605070803624002c0e10700200c1c103003800e040d6410b0000400843e503910503520700715028460051103100484100d00160070040b22107c1d408280400c0880501c45150b11510079550754213000139050f622801c82580440480d58000d5000e41c0340310000d21520055001072001c00003040c400082e003a1140c1d681c40a0740c6910010382518030020922440113a81089444010103400c5002458201c0300c4107003030a14440200004800e = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 922699370 1250 922698120 922698131
    0x103020705030c070e1e1504091a0901270c0302012f0d02150f060d020a0503010f2405030c0d050c13050a0501090204050102190c05060d0f060b030603030d 68
    0x92041c00c1c41100e8100203840c05807400aa11000c0c1e13190540001e40700e00c43c02e18400c3e000300300014a0600354070300440b030880020049214400811026081c9000b04442203600306100c03425034002c1c040200d0240d03518a0000c0713074800d042d001c0700380d0310444403c0c103004200364085a0760100714004101410b0720740a2030080f1440380729001c54000405021002e456440840c06552800302c40403c0807c4011001d03401d4800c01d403038081c0c0d83c0050440a03610454241007110106a4234588140b061808510140c10094482d650300e0000c0d08580100c9030394443c040d1a00280403d07034a0a40c1d1010201030680d60809450342003c001c44e81e1843c101e281240150456424035050100c00c0109546456000388182110540c0411542c05840160b074250005402d000010802102038002e03201602c01c1030340201000b003143d00b01c41400c3e03d0807101c103554400500c14003041548422005000c440d504000c0030030031144c29550710040781c40ca94000d002c920014800d21000b560040115a1300c00400781c404541c = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 922700620 1250 922699370 922699373
    0xb06182e0507021302190f0309120c050c1e1309020a12060e190f0c0806072c0a0302090702010e100f0b03060105010f12020d0603030201020421050c01030207 69
    0x410030009400541148103a032051140650280062851520a13aa407040001c54040036100740d000e051b060544088039044c4040c101c81c41440001e201815501d4042407902040c0ca4041903031008440309400038145840c990203010081040021410b0160744242c1c100203044444c07040300102c1d590702807207004070705a00c14070820310783c00c1100507540003014000b201341d0f80c9101801408002c00111007040c14070651640c2e9013800f0405c41040300c0160b1a11038801d1041c0d54801c02140c1ca024101e03440001c0d80d00c0840ca580d004c0042e54410002ca80352902c18240100010700ee181c0c04200048124442d400801503a40741ea00034002120390585101e6072a4581100990144c110040c00038090f1141110031000c00001b41c0080a03032840c490010000603028030300b8951101401d0040780c4c045a00301c13581001c003900c1054400c00c5144407403401401c000201d108002694901d0380250010b0390086000e10000d21f905640342c482e0440e007000210100b030036954a540303840d40e2203000d40c103042d0301103102d00 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 922701870 1250 922700620 922700659
    0x206071d06220f031e080d05010b090a0902091f12180605060301020306010c140a02031603110d200a0905090714040c0909091112030405040b0618 64
    0x52420300007001c80b601c4603040409080244400c01c02219651008100022500744003a104000d8035080002c90404800f695500020001c0e03551007112485410410702c5402e03e410720500d8003030400c8065155541075481d081082283d042e030401d00743c1520401072102245d0714201100c3d5a16000882c00c0581401c0c89403d0304c1c203000c10414207044070b080428080361310a03101d0004800c1842200104a40d44952017854200e0004481640c013060500946501142c007a0800f001c00c0f50800701191030100166011a007081100c4411181d160081c000c1071042254000c07401000c04c0c1c0541d0106010101c0f91225420324103008070045165400f0743c2d128540b41c45030007415000c0d022000092009050500d03225a5501131803142150300da0036511003c500d450715000d442d0124000baa14040c1140c10520508001e0400e040c0460709a0003001526660382c43c3c0d0102e1003050842840070703644441c40c110030f10080d11511040907224550401c0a10301d08008801c003500b805c0810b45180d0013030006400482e = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 922703120 1250 922701870 922701917
    0x170403020a05100606020706030606080f180a0503071e03090306020304170703170606041a250308090c0306061f0908010e01020715090507151421070f020607 69
    0x6041c07400740c00c0411486000715040481110317903d500315141d03036135104001c6084654a0245400156010b0003050000038001d14081d0045040700d0610300b9210703642041d17403521966990880c0c6540000c11a4030602a0710f80720300c031640c00c400e40c10000001c1c0c59500144070b03c0090100400d82c030340c0480410140030328840c681030080341d08001b1584c0d504840c00d01900701e000a90a0a00308048100002c030641480802c0e64100c0b040d204d001209400e02e841400321680100480d030410f0b50000f602c0346010f00c00310641402a50298a0b10300390303402c240446034204081380882d00d010f40d201d541031185541702c07400d13901c42190402c644000e41c1000c03890110b880c1c40c5075a206822940c201000584500010b42c02032544d0b41c403e000e0340c02119058030021003620316115026201f90816032003040381e0030f031610011120503c136242000c000345500b00001c0080d00502c0b00c0e041a40300460300c5038000340388103403025045900c5e402c0c0601c4290441100960f164070090000342003120382d40280d6403104003030158 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 922704370 1250 922703120 922703123
    0x307080910091505030f150303030705092d03070911030c0a180801290a0b0a0c0b15040e1902010f090f0b12060d0507030605151918020901170403020a 66
    0x9110620f0010349004005400c01e9610340c0c6000c00e0b4030041010038045e40c0d0b2412842402034051400c555522009803215004031604c160071820f20b0082d900008840b801c441e890651f2740344c600440d451300f6010315281c07007187e8120340c494528121152640030451420b43e9409010161b9140c3c1d82d88450030f08444408541010050030600c4071408206403406400141c0c0841c21411046640f004204080c103603840050308050b00001c60b0b1071b09004804083c002081407070b4150078200700151031503648400c2c1820031a0601c0f025044540d1031811460180a07587d1400e0740080200040200151000301c406d03100c000c0281030040c400700500040d40181c205030000c0c1001181010340980e62010301081d94002114003104882e00000241c803450514603880e4040c1d0050001c0c80c4250460703441100030940604641300c0b060724507801e0300e45603459218141d04003548a6180010038940302d1140750b07608440340c4a8503418010f01c406000d590f8495010b12082403100302003030b523a4865082c1a420b18020400 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 922705620 1250 922704370 922704389
    0x5030f0c01020d0c03080c032208120a27060b040207030207030c051504091104030f050f0d110c04050c28170f13141903030e030708091009 61
    0x1184100400810106880d031000e03029140300d0021180101d414000c1000001d02141800e00031602c10095100519030118400d90400d442d20103003122074440004e00402251080e10010b900e140007000c00032142c0d00840c203a2020700c018031070210820074100040350a41c40e1a1a624840018880d540e005100002c0c005001150313140b0990400940ba110240019559004454000141814070406150307010319031080d82c43c101801c000f4903001801d4030400002030600c0a20010010031210400c1c110f420303124600800d0751032000ca2015050642852140045c807102c1d540c040810500810300c10f4400354100c0e40007a983d5501820800d0500400a507412000804111031150f5009021100b03491000c035141c0083d40996203051625100342240c40e00380001010340882c0c600d29038455a0400365105480302c130002201200a649400b4111245148101c400b000640034035815100d89500c2d0295a4081c46c94080c2c0f41e00c0c2c06131148155080c05000c0d0300000b0b81e03400d6040c440c007843c2c1d0282c0300200c0c = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 922706870 1250 922705620 922705633
    0x90b1c390b0d111309050907030b0c161b170d120e0a0b0103080403020909030a09090b1c060c0e0d050d0f120e0714120c09060d0b09010e120a0503060411040503 70
    0x1040d900c610481c5c0aaa10388a2603d00410441040000c484003140d500c00c2d8099000ea60300c1060798101d81103240d2071480f004590740c020000684541e00d560140b490001500202481e142143c150000301aa21000b40d800003090038a07103030b074449008107003d60324610101d503980f40030304c0d070510704030701c1c0240a80030000b050000700030441030000600c12240222000503040e1038400c940781d22442a0f03070f0414089050700c1c10800a2440a400194502100504910701c80c0340880f24101495241541201e2669640e60181c07010b07078104c0c11840c401e40c01580d03550314581c85555019a540d040c0341c1c522082c4041d00000403551032041e40800807110031403c00f8400001072099081d42c0742038070301800c0d0030444074601c03d14107810400d50f0380c040c0d01e8008005203850f0340c40c10f05000341da55002e081690450707000590200800c1c205155a40182c52440000a044060785c007018201000351580640d000c03000c10100c0c04017940001901d410007002c5400041c80001c00520361a640301382e034440c0b90940a0f0a = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 922708120 1250 922706870 922706887
    0x50606060f0d051e010f210609020904030c1211210c0d0e0906041404170c1e120f120604060906140117060604090b1c390b0d11 56
    0x3039959504c44013030001c02d0000c1d80d0b21140c60036210700c01030141c40000c2c840c02c18900c03074544650fa070440145000310030018170b00409401181100400310303003d40c04102410389003002c1140a0881c02051101c52804200c191408015592600806442e811030b1f4008008041c1d08800000d0482e2081800301040f00d0030903104060152910305c00c110304503c07800092002504a0400d4050030303803114403082e50304201c0e80d680e82d6518801d68480c005c11b5030040050015105c55141080002d8581030b44208400040036a94100d528101c14050340c01c4091505012029142c61010244c91392209a0b5404102c195640f501081c02880f0075803220680314184000003500c542600c1c0c0c03807104400c081c1e888810441c10301d003011910800c180d031151d820000401c001c2001114a41c40b1100d45040100000c03100c403132a10401d050342a60700000e03036046c0312440a0501c101000c6150504440c0c510301005481c0750041189202c0304a41e104844248100203242c491140c4d1561000350340056902c0829240c0190 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 922709370 1250 922708120 922708141
    0xf07080d05090f09390403140a0206040f05030601210b13020306190b0a05011d01110102070309061101060e06010c061409030c010e010203010803030406021c1112060d050606060f0d05 80
    0x2203a4225142c044845298084a41d6208600001d40100c0b0340c091710b82031071548c4248078070b150f0f680d001d1480d01840e20a880182d0300c44000b80010250907919207207050901041509140301a400780100035036181800d40c2d03040b03480c2c000c0e151031038015640000756034450b40e100030748110708a0000d5043c0034030001c000d0000400c2d00725582c0400842003c000c0b510070401403003c0c4000d42c0c000d075030115007440404044481920414080c406d07041c03601000750035504940b00d0980c2c0100750101c0c00b00e000300600703201c0c1c01d42c44181014040c45000091180c603160010450803080301074107050402c003004050109202d81604440441059048161094902480d0650300c0c1c0d0800c0c04902055420301810300301959050080d09d051b291490301a504d91780b0b881d030b1024000e45c044181c82003201c660314540080041d05100c0c0f03181c0102020b00d520740d1401c05040d00b00745614014130303980c4141260501070010840001d05164014002d0b140903689003240da0203100c840c0211020740d083d1a083c4010004100301 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 922710620 1250 922709370 922709401
    0x8010c1205061210020d1116110d0f0f031407060603020f030106030c0909050705130207060f0e190813080f0715021c120504140f07080d05090f09 64
    0x8030040d0030030a0361100c030108881c6002e481c107a00000d600c0006107940d013502c9680200015980000001140c043c1c000d200712054000c80038100881d01d080041006000c003c030341d006070801d011500c0f42d0800205946140703076480108405031051400580d0102003601814116030380b85080d202aa4880005242510142101d0b01080740240d005202c5071070141014002c0405403548200041e200a04000c150300c018115142c003034070280300b05040014640c9810001c0200d00034568009a912031b01400c02070180d411f80803c465200740340c012151802c2201203072450002e8800040080d0b0020541441c200078000c6450304449000c840800245025002031102d000c02401c000f581c1500c0d0392a0320b02c1401c1c03c03400450320013503080740e142c1c8010183c41d52682040c41c1158102aa00f030213400e401c403421544d00b00c0302243d135401d000407284503a4500f00301709003068440c100100541812301d1b03203143d210784030001c1404c01e0010100395001c0554076130b43c43c240300301c1001c0c011034000e103001c00306a0b40001 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 922711870 1250 922710620 922710647
    0x1180905180d09091e020406270b0d09020a03060e010207110303070b070804051002160311060c1605011103151c1a0c0d05070905040b0f0a05040c050408010c 69
    0x1442401505400400400c1c1a810b00955855202140746000f045002400005508400112102400c0f40c52006a440034101034483d0341c0d902510380b0008003120789190200300c800b00480410703020400014480108480032400d13446070100f0b005415101181d00b400c4180c100800c02800c013580c0130000501540a024064000c10b0414a01030715541455240e109c2d040300907140442071000201c4941c014a50f01760000d214004580c0101c0800341c05a00300d8025082c0403400d21a01070b1148103066000e5140b580300e41e00c0501a1041c2c0c03e0521400880d48900200082c0281d1283c42078010311500398048050800d40c50900d0b80da0f8a0b140c1a4109426070f521002442206a0900b03000920400e801d01c6491039400002a0b40b1001019104202d004004088090780c0700204501c00d03a0784540d0241c64000e00054891074019400e140402040c0c071600d0361120300038110152a0041a0703140c0090f0002c54100351000101c004925008a500d885980c100b030b210340d801d11850701c031502c3e404bd00408079407 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 922713120 1250 922711870 922711891
    0x40603020f1e032d010e0618070903150c08010e0a091b17160b03310b0a1107080d0905062d0105090f070e190e06010f1b0201180905 58
    0x12000100d0441d03500050719491413102c08182c014003640700408801c58200900800ca0440c40d1900c120310b01050b0310171030f83c02000841100040081201410800c1e1050400540c01e02480340b24520043c120201481030f030304401490000300e050b5090a6001c500c0f025000114410184241000c806600f040c1c0d1040c2d4060514415915030b001e00042400000c40384d0b035a003405000e510f0111510700703540001d06641004100800d4406c092002c1e400510000070324a5045240e0000600b000c4181140003017051007a10705210b42c1c80c0341496100c084406440c1e112124a85036505007100300000c212042006040e84100c0081c04400e420095043c0c2c4561120706c0028002030015526401d100d00c28806d42e80c0108911001c070304c500080e5103550368040f03000c0c40c01083c0d0714030340f200140c09803603482c07a805101c0c1002c2d00d00341708a040c40b1030f041d0f61000f42030a040d0058401e202c001803202010180c3c01c007050394500310101c11a03101c0c194840d28000300d118281505500ca03145180240f10554540011 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 922714370 1250 922713120 922713151
    0x7030306170d02150c0904060303020c0103050c09030c150f04080703110d2d02150a18060206040b0c04090f0c0e0406140f030a0b040b06190b040603020f1e03 69
    0xc0c20001e0701400b4000d40e03a01808140c0318440440f0001a0090a43d020781d807010302030300301c4584a901c01c01d0300540c0030364010100824144005006c5803c080c051545c040c1c1c041001c140203440c0019a54000300050b180201c0a40d040d01c1c0b1400300b4000ca16219020307600c00100000d1003500081c04209881c0941542620955580308000c2103001c3d11a00a01402480007275411046c070b0708103002280244a200702000760381550000b40002180c00d100001c5000c007150345c500255200d681d898807408001441e071013450410364003a40d100e800400041008048100098101421000342d40051644107400d00000f84403ca00a001d405080303844070004041c0c1207000000c0c5803600408048814880d55283e8401c3c00390140710306081d8808070301e0307054460441c0090006a02421862299004112110043c00c1c007008205203c40120707455100b200c0951401d20409100000b203034100e40349410b00695030010007015000b10301414003c0c00e040f900e04280c9256008030b0000451248480d015800705 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 922715620 1250 922714370 922714409
    0x41a120105070e040b0d0606030c21020a0b090604150206070f02010506010801030201030c03180f02040b011d01030203060a0e100315180b10030804080708010609020c0c090414010207030306 83
    0x700c0304100c82e420005040c0e2000084903042c143e00104240001074490381c4902c40c0d0740c9039101aa03402c2e43c030440355141280401c125084d042d003965001c3c240b65034144282e424403500050300748240e6000f098050080000c00c01066520038003154000e0003620020071091241c5140a500d0301c804a580034041031440c000352039503d01c10701c200c0d81f01d080145c50b21446642541c004400400264102c80c041c143c3d20f1065001540050a10a200034440c6840c0100e010191051006a0ba0074842140c14028080041000820000c85158112000380390060704c071380d0b0305800288914441d501600407004043d0038009810034020054058a00881c0c0000c0c031603030f450410398111240310860720358031004812524000340385100c095030060104400402d803140c50b91100442d580c401e5216500c10b60080303000304941c003400e000d004000c22444904604010341300460365140d0310610300c22072003801d010b0300040421181c170512030046c50300c0d10001c5444d9100b52801800505450003407843d049101c01c914007 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 922716870 1250 922715620 922715623
    0x1a430306061e11070806180a0b01290a0e0315011401110705030f070f09090803040206130e070c1109070507121407240608121602041a12 60
    0x445405650740b0740c0740e119407005122030028948410381008042200116051420820761018103041ca02901c0035041c03d01e140c0703c030513020307404a5160740c1014444101041007550351038111400c09143d804400c091ba80360f8a000c00d002c4040074008000840d00c0921244c0c8410b110324408401d0b01160584000e111500d241c005091041c900901500c00401103254414100603280c00c40900840d82d062340c0328400241007044030764805400b9408140e042040040341443c0f034000703260028040100481303030340324414240f10042c80640240030004104110701607000d542c0009000420040c0414245110020144c0303100c501c0c1554004145041d440241c0b4203084298010300302921034614000103a035402d8564550102c07c00180042e450074402c10822000c004c000182c8a00c1c0680002c01c2c024168541e0740d421034411680f04d03494141c0c14011400c000641d010000f4510401d40d46031554510042e0114150920003904103080402c03406000400d002c88843e02c500468005a00c00c24650809 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 922718120 1250 922716870 922716881
    0xe040e03030c07080c012d0c1d01171f0e0609042a0e0a061203090501120b1816020a03050a080612011a090705071a4303 53
    0x4000035001040441d0107241d800700148503040c030a0069038182a40540c50900b10340ca070342c0780a0003000980800111074468010b4800d818a0f440c4400c204104134041300a0024002a187c5210020746880810f2980c0c010001000c3c50714070006610501c1c50014425010380b072003503807900d042c44070f84035000c0303402440000070034400d0343c0140c4400200d07540c0d0340b5000c11320b0300940460854a82c411a00c00007944002c0e8200340079101c81d0100d505a800c0c44607541044510a500108045806c1004140069801100c12046600900e00480d64038128042840101401d001880c0d0007207069541c018070405d80f04026201e507841e44c845e6122540351140503622200b03681c80050001c0c0d402c10170b0011160080545981200f006030148225030403410710b03d82150702c20310803800d101c45504004074480c682100078030391080003490701c03604101c800c5d41c8000c0d80004507111600850421400101c031091005482c0d00040240410217210010003198441c01a4085e0b081c0d40c07981a0025403403030f80314002e0141 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 922719370 1250 922718120 922718141
    0x62a090310050408040b0301080a02031b010509012f0c0f0603010b0403080d1407170601050901021e0a02190e0a0506090a02070201030b0910050306010801060f1a0f07030e010e04 78
    0x7408012109078400c0004000c010400c0350000300901c00840e072000311101550290040c3e80c000d200e2078190340101840c01901501d1101001d61000c2010256680b00050300e01e0758400382400c141115800400b802c81c203992460300c9010030b41c103003001401140001a4107000c0d007001d440003003804400a0912030035101c2401181d5569504200410003d54040010040000c111000144c01d00680c0526254658280e400303d000480f1140c0400c840900009450781110013402c0c4581381c0b21003480040e40700c03410200e4840000000480142901005001010038580e00400c203803d0741603c48146890420780e400b42c4840e50324013400099080b1034500c40c8a0040600520540c420f5890b0b40640c000f962200d84100c0c10503484e55000750a603116000c42034001c883c0150707001000ca061400b8145401e00503480900e040e03040100400c1440c5422001d6000c4ea06459800e088110204a200c8680e1062495441402000180c003406050303028100c07001c0d428090381c442d01440300e40d00801054a801698 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 922720620 1250 922719370 922719373
    0x330e0909010e30070809030c040603050c04020a11030a05030708010f291209030c0c0405041a04080f03070905120a1a07200c1005040609030b070908062a0903 69
    0x151407080980501d4082c40d41040d010401035000c540f40944801c075000010125030801c03020840140d140380a210404074502c050310b041281d185940c85031580d803440e41c084540201e0303000443e10300d00c230301c240d450020150110307044a640e01d01422004189920842e0880b0016035403a0011900b05c80440d003200032103403104038030820350202040c4c510401014000e0541104410170100c2840040001101d214000580c007664941001f03011752410100a412518851032424040200180240d2606407424820403400c4000703940b94500524103100f02c5002c2d490b121004800c010903554005140402c0c0c0e03405075011054200c00301d030b04ca50b0791658440e0042c009c0380d00c0c483c00e0301014042d03007241d58082254600104600540041c1351005003162504075026001340a1154190400c410341d061850300394a46a880c00c1c2c90140d000b0a10b41641c00002c2c50f0854150105401b04d1140d4884000740c0256410f5500c031341018102c503040f82c545a2209983d120001d40c44080e5000303d01d05940b0150809030 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 922721870 1250 922720620 922720633
    0x24090123030a020d1b02010e0106060311070f020402121330110106120503090f0d02091305010b090708100807140418050a050d08060d0309330e0909010e 67
    0x241000b02a40020f44540e101995811166640000c207404015040205400004050084940181c295041c5030098010b060600205e2061100100304842d482d07504200c4403d041c010340d00c0042d01034440c854201d00141c82450a101483c003020a4100b5024890329180344a940f03001c19500c00c078001c505140304600c00801c90341c50010f0041800f4a809040302c000064000e4035000c0013807040c40c49040070307586030b80b0100b1001000d003480c0540d008006d00440302440040b8460303000490340b80005003018903200680903020701300542500080a6074100514110040c030340b03020002e20401003201c04a141404191001622130000709503001920000b03145420350100000506c00a8024075100b400d10380100501840405d0052001080d03030341c03003400501440b1155000041c15100c010b0030192280c0c10301940e0340002034000700c0e030000b2140740d0041d00383c5c030454444540b01c1450700801042101142d009a01400e50b9000e030b45d50a00040c00c648550b040d0721140c0519088035102200c000d0b040e0300c0071 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 922723120 1250 922721870 922721881
    0xf01060e04060213080f0a05070f051c1b12020319031b0201021002040e0f0c09030615010507020406062106080a030e130c0513090b0904112409012303 66
    0x1a0000d040180d85626030b1300080e81d86200c018038202064010400c95004415540e082040c14403004005000d50329840f86400e0070000020081d40180c0d21030f45002c15600c910f00700f04001c541c030081200f4401c603041038145541d00d141000b0020328540407842806994069842148034496144007960196240001c603041c000c0c10706510402054143e055110742480c6465040c200d0009202506d107e01652205007072030201401400b0020b001d8a445c60010701407521aa1400200310383e0042c41c041c82c01c5240404040180c4d01c0d07200d6180040d40040c101000402c10700d0f000f120080281d01d0344011030040419130351804013182c1300c0740038084080d085a081007001c43e118880720200100010505410101d906841c41c0031900c2402c442404210040784105048043c1e16805004110140b805c0c40a0301c81900028408040100006c1000d0389660916545440307603489881319400d02d100020000d200080c0e1284244c0010071018005805541c1040030001058000340300c02c0c100501d43c40c01d40c1c403038 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 922724370 1250 922723120 922723133
    0x72105100305120c0606122802100315060513051005120405070806070804080d0507050d060e040b0a06030c0311010c020901290f0714010e15090f01060e04 68
    0x80c00c00401481042000700100d5414004400785403440802c550391904001071207400c0c10301c0101040e2042048080701c3d1400c12011424200b1055800508000c204492510700700d801605503000e03410a903981c07010100160190320545041c00c6004400400742d03520041216944251015040c0d409800c1e00100900e08000d1800c03418000075007001c41c1030a1000101c040b00e03120486098039180d0040404001e8000148900f0703170026903a141400c480e00e0203450f05d4100f44200c20102d4115955400080d0815100390162040070200010a00049075100c8450340040400d942c00da80c4440e034040031500c01e5a007482901c044030743c4038502e988407910b59144c424081c00c0929096062248810002c0300694604254038040c04050340c28401050010003d0740300c0b10100941015000010032001401d03841100554081590002c407a004a54519003402c1c0075080b02e05c1301048a10075a49404d811400c0c03121524410b0030840d0888015003440e5800c0c50981c0d901c0c6c03003040400c5600d10045000b1840 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 922725620 1250 922724370 922724381
    0x40f05090604020714070612150e091f0b010905040b0907231603080601081512150901091407060f080406020c0f1609111b07080703030c0b0721 63
    0x70018401070414240d92605514241070300902c2c145030300034100c180070380c81d046030342074403541180c0204124004000d5800140f0310418000c001890404000240b6417840400c0650b0100c94150f60400403414190403030005003011103c0300d8089004458081014203280c49082c0a1040082c481d0446441c0c1140503150f0fa240001c90f68200c2d070075081c285421039039210003071001c03800c860404603550620b800c000f41001d02c084c003150f0400c50381d003040c40071745256282401e140c040b007146e0303402c00e0180d0032040b28500107203416940140804081080036500040d8407003000140540c4020342140207041045485010500540c80800c0e80043c1006c0120f200399040380d409880307213000528003645c42844501c0c1544051410724103600003043c0302090820a61403200074010b11200340294485a1850758150081c441c0140c204155509801004a02003002100070804e40003907a07072003038407410001c00a45c29820190b5050ba1600c01113a0414440c600402041080780320b24000072004d508484041d01 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 922726870 1250 922725620 922725631
    0xd0c020d0b22120306120209010312050913060602072702031815060f0307050105030a0b0d0b19060e0114040c050405060a03020d0c0c030815010c0b040f03020111040f0509 75
    0x14035042e48800c51519012620300741500490070b000d18812880d034018150341540d0001240d90000c00003034001626800315440c1940d0b03100d121419808501182142c0501483c2c0310203034460030f42014000d070480c490f40310740259805a400d1b100304d151034041040007140b03098441c09802c00044c40c4001d04e00300340c3e8055074018640041d100c211100c4240380528224032810440006086001400300528191b0103854801c20140c01a000481c035110001e0050f000c000c05104205455a24401441c0c0e00d030b82520012076404103c24909060102581d102c4100d29151b007155580303000e401140054100103424100c031a0b000a1030451451801807001410b501c1c03050300203025051102040564540015100d0000e15a030010388911141204406030b5007a00850310030b00c11010f58601c04030754031200144c0d00c0390a891110858000d110012100790702d8078140948144018410b03c410403682c0c1140343c500c540264001d0140380f141412802c013500c01d5210340c40c856490000e00b0003441c200310158682c000c = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 922728120 1250 922726870 922726891
    0xe06220b03030d0c030f0f0e0c061303020406080a1205071106130b0316030b060c032d04090e0f0607020717010f090c1505120604020306031e0c030d0c020d0b 69
    0x10076110004025107001500001c0031a84030229011045218407c01009100725501800122050380035107403038821420085000b400009022800c00c100c810241c1d005660152081000f150340e41a03140d20b0f002110003c0703444800e02000c0100c024410425210b80d9900041c0d10100c02c0c052408000b841e5010b128100c00c80c030078008002070210404009103100e11000c0040ba007a14080e4500141100c81100300f083c4034038424030140b5005007002056035080065125451041455550b80e2030400d01d100700000c0c80300704001000303c2c860006030003d4590444990031520700b01580912103403100001c580000c0140c0c4507020811403d8907234505003646d00ca820000140c400c410b5501001030342c60051042d56807660442040082c808400103010383c3d580185030180c200240b100c0d810741201e0000d80450712a540200106010750760030320084200b042901c62080f02c00180079000d40d200d0840c504054801e000390b01c80303d0340c614000d0000b689160360042c840380201c8a0382d51103016030100941000607a = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 922729370 1250 922728120 922728127
    0x10f060327030329012c040209010908010912090b090d03050f13290c060103030c0327030b07020f0c0d031710030b06010507110f040b06130e06220b0303 67
    0x20324400c0386065030024243d014480301990b120001400c0c0b04c400f13003804182c1900c074603034100c000c020310b441b40d520342403085502580c0c07200c030440100c8049a00c0c0e00040d240d5480c1000780f40410005070b003003440a044548490030210780e9404000100c1c003500b1103841d00010b00e080c0900000b4401e0006120a10750b20005a007403102481c031001d4102d000e40c00c070502c5941d040020004042203048620b5200400d4054107141111500d130098840c034042c0b00040038040754401080402d800307000355060390390b281b0031717006102010000d602502002c184410740f00c1c0c89984020034402440802c0300b4080700d049a0007410302c0044030040c0820000e03400000d07000c1162a030f6481d040700b014038400300c0c011254102140c8510f8110b0500c4580341201822107030600800b00304000005008419640f90050122136000310606010f021801030a000340000364403100000300c1c034245201c1c00c0c0120003980c0403000080032682d64a428864100b41c4070142d000100c3d6414489001100103400088402d42e024003940e0a = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 922730620 1250 922729370 922729391
    0xf1401060326033106050705072030010204032003210a020705031e0601050301090f080f0d11031e040b0a0c0c080d05010f0603270303 59
    0xc4030010381045030084441d809610203110444042e61100e1010150907246090041005a54100b020108810342030301c91104414640e07a40c02801d0743c0c503000041070041c0e181890000b0226400104121500e561081d0260040303d0207988820990b0700103041154000005520b07201610016035034500784007403100706603050101c00c0c005030008500c2152940d0340d0300003078840901c004840e00707034050083d800444808a211995012042e98240984a40f69036010180040b42003240d036400c004d4041c400c1d08440a00e18500c8032072001d803000d0301c000355511039803540205406d031112035802074a550350030320307444010a02e114020004c1110080c180c034a00f000c0c09940c0000d9030400c070701c409407491001c4204154900c0680c48540d80c82c602000c85001807615554602410304040d00d107906071580e5800a2036400d0007407612401843d003020039161168000d905000c0501400d020707200b07014462500c00200c2c80e000e030180c88200b036101004650328074008507104035000c13040c41094013015160041c210 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 922731870 1250 922730620 922730623
    0x70c031b06091502031e0613050901022b0c0219110109080703230a1a060f0a0e040c0b0a210906020d0605010219030914030a1a09010501060c0209040f14 67
    0x30083c00e020009600d0707180c4507034902d20301c0785000360040360440d4500030081d4580d540b07158100143c3e146800080d09442d40004580203002d0703e500f2120300d89900202e10901d5441c05003803200e040811400784411b81016034100e0f11000004c0101c1c07408491468070000044032000d00c0544001d040c98003004207540c07540f0941c502000e580c4140c624405070f0f42e0101c0300c46080145a800011a01c00030000c1030305550b18402c040100d2405103e8841d121004298182c2c0d07010304190020100420b0481c005c1e4031103000c2540c901007a86d04490009640760001008040342d030a4841105060f1070b86145100c50030701c0a9000380025008002c055645c000742c20020b42c03244081e01c4510300c4e0000015015080400281c600f0500ca01200e03480f010540380e010009074440010b00945204190544602c40c004011910f89202020002d2441019a041c401c12a00d9848582c1c49220810000d1002d41d0707035403000b616403040d41500a50096034800c00900401c00c3c4051034800e6510416000c1c91440f0101c2c0303501d = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 922733120 1250 922731870 922731893
    0xe0d060e030301170c150a110c04020c01021c09020a09050c190e130501300203240106050f0409021b030406031a0906100c110423070c031b0609 63
    0x7000c0c03080360351399410800c04008070190745030195108114920715000040150190301000c0082025859000c40700d9a0203000620025401600035511400510001c1d8040d4000c1c00c0400c07407503079a400000001090501034410100c1c0c000e4031001607142049802c00141000806a91440008000790380d00e01002050900684004d81c2d01e140404100d4000c0280e5036284941d4100a203040c04014040010390742c407001c00c402c1541c10103000d100c00703c3c0412020800e0111002e541405200700c20004140c9031060301102c007000c0001400c0684e03d5100aa400e4052a06441042c40302800301740301c075071041e038010608108903c441c9088015021080c0d032642c6d0040c0c0002c400281c460441800ca40214545001d40d507004940428251602001007100d45191030701e11410000700308130080c141310a003003900c1820180a042800700815070780f07a00c0180610345118040741d903006800100c206218203029080340340c1c56620036800b07000c151881d1142070b00c42e280656283d5039842d90440010b1600c06d21 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 922734370 1250 922733120 922733129
    0x12090622050a0b15040f11041401020f010504061d0120070219061809091709011403010b0310092c12121b040b0d020706090b040b18030702010e0d060e030301 69
    0x100402000d40701c0c00d10007074401e00e0261008103828201f08900402c0c000083c0d9090340c1b1070503107107680715104000403480d00e40031407064415540380c9400c1c8000e02009400003007940c8810803000861082c0d4040b40d03800c98110484c0c0d0b0b0f190000c5054280004441c0308010005940020a0b05a440c000c90520300c059032016030080010410640202d0f040c0c4020f45407060040c1707001c6004000303550f810340351142c0c20382981040c0560141c0010b180c03009030b03000d02e0403c2c0740603020400050316584c40c0c1846036078680c020f881054004000c00d40c0001da0b130a4a00800d40c60107c42c00101c171b0122800d0600e4021a0001010005540500341111481080020103070681e41c600e56044030580c2040820403140000c1d80694180c0604200028031076207100754101c03007803240104401655100c003820302d10020450004001c20142c0040b0034031051140b00324556000d04160300700fa90380c01c82c855100e02c5ea00d200300440203001c1040c041d0124607070f03e4102800c00ca1a801040080b0360b01c403011001d1030441c4d109800 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 922735620 1250 922734370 922734391
    0x19080102180316060905060309030c0322120f0b070201061a03010f06050a0c0b06030c100503240a06030e0a08031006021218040b150f12090622050a0b 66
    0x5140500d880c1c1040503d04800406070000c01c0030742400d8004041c00e07040d00415000e0300c000000304203500410422501c007a55035030152500c0d440364400e0b1118102501c0c1400d02164658140883c0d80406040c03241c400685c4201d0042e0240143d0742c581656003401031010040d5581c4400010f000c0f49401d40e4078243c0022040095500c3d030400d1800b42c0c4c15400d942003d410000188804109107030800c00030038607a9005000d4141903901e9000091030046e400190a4001c101c10088121141c0c104001c6e6010344020b580c00c10340c04c848001c20300c0304408044c0b4040d40c080c088060400c21680244c0c001130502c080f03601628000521900c1e211065030080c0d801c011400011074040150550512240310302072045040c480c40e214a941a8101c2e40b80c103444541e02c110356501d448603142c0d458101070940350380110a6183c07203a080c0c019041c010f400031001c4103c030b00010f0000913003014021403220700c80c0400a01d44400002d001c06100400062070004468502c100d10000740840c25880e0414420615402c = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 922736870 1250 922735620 922735657
    0xf060a0f0501140f01110c13020a2706030903031d030702090124110c03010c020f0c0a051f0912050703061404111003060e0f040507050a06050919080102 67
    0x344804903101607101841140103511200702d56680e80310b44040c500c50900e41003140b0005114441d00f01030ba82c118156000343c0c90403e000c404042500600102041c61321003044105080c1c3d41c0b25030074100c01d928560401c541c1c0d0002c1c00124041d51000b0b10141c001d107000030300c02845210104003000c51050070003441d80007140010031454080d18840c090008110580788641441c014141400140021041804240c0c600200a501e0802800480303844c0103000340941d1b4200000a912040c0d5030503400c6c030034040e50608403020f04001160f20112103020f000c509504006c0d070790030059001d12490768420040340e982e00060340400840c880c1c0c0c000b4014400340c518980365213400030441da5205004086501c0010070040440c020003595042c501c13007542c022441ca811f03030b50110024a040c0c3c10502c003000b601028405072018181080b03220b144030710110740f801501c480420014840921a00740080d008001c00c082c1410204d0031103403112840c0b04900249038482104609a8128041d08030010800e01c = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 922738120 1250 922736870 922736891
    0x1c0b0a230406060311030d090311010311030a140c09030a0b06060c0a0302060702011523041805280503040902090a0312050a090506030c041a040e01030803010305060c090913050f060a 80
    0x52881444134081180100020441f070180a8500d041511000d050040000b0505185074040e030131001900c0c80c800c010650707d00c0c05056501c01065500094802d04c601e01c40015541c140c80c6003196046400200185141c8100380d803400d040d054000e180e00d8000500340205404100d08000010086119401400c0075162400001342100d040103100321010114160410983da00c10540517964112902c480b00c91205000115024000d081100340c1d280403981c00c2d900901c00d0105c4c40301403071881c0d040c0310418180c2c0105161240c840e50744018001c0e400420003013041c81d01c40c1e40140410301d400b6021001040d52511032503103e9030f0306150310f070109100180c44522594408150405098102c40403421800c061400742c00a003c0d5019100c01518103110401002360a2000c8c1da00510004000b8400d5603102d00d00542c05070401c1c80203c64a100b084082000d10749280c0543c0d50500b00030346100010b64424880021140681c502501c5601503011100c00546041c4143c9218031b203109804201d03511603 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 922739370 1250 922738120 922738133
    0x300a0804030f0932061629161e05090f041103060d030306261c0e06030718090b1c1a100f03030e1c0b0a2304060603 51
    0x2045500104030a101c4148a0805940307074265400c03029512840d04031900d08100c1c0d96000ea4100c0132640326001080303c42a1b042104900360301a03108540301d2000f0312448090507150113041240148181d80701f000181102c1990074904161a50b615107001821080044124002403107030300f40780014000242e00d103841c00d2040100c605044c081d5020480b44620081401c4540009010b4a10801040000c4003d052003a08598040d088000c1c84000c46000000000031081d540300040006000704403860600c01820340c503019031a00c0c2902c030400101c1203070007049180c0d44000d00031406d0101842402401c15100d01c11040948135142001849200e0319003004080c80f002e0140c0f8048505154043c030004407010400348039800d5100340354100f03403649030902c01c01d140f06030032503a50031882c842c0000901d580302401500f50300c0b05079035541d05c000c04e2403504269140c00040280003a00140041a44980e07182d02c100d480010921600400504100e0203c500c20401d031815582541c0b135403410b10603c0795 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 922740620 1250 922739370 922739387
    0x702150c03061005160b09070305030c030702010905180c0702120313140a1d04020604030b0a051506040803180f0a0303020a0c090501080a12020106030804061d040b03300a080403 78
    0x200f5060580c2070031590151495042c044c0b1000420030321410000c1244d03041f0030081c03200515400f038242ca03103a906062601c2d580e500300300801da00041030103c0010f080d0400e0107118000240710001c150080c0d071450700d800000c0d0b0010b90200e0304009407000b1051000001d0025104404803180303414001c1c2d00e80000405558200d040b02403092034250f00800185134208640c0c0e03c02d04058111030400d80c1d550000610b20b00480d40040e003204c141208011600041b54001c92040c5080c1100c00a20182081440460f002d1030003800040e900411080501600c0b03007100700103218008142e03410784683c41000c030b0003a000943c001c4026074443c00005003000b0100200801a081c86c4104000c658034048600d55124a0000301618091681240f01d406910070740098010395000144541d4a0340e94001c028507a205106003214544c00b0008110b610b881c00d4050850144002001000c0d0140c5844903000c642d0215080c070326441240c65481500c2000309800f81261100c44d854001152030f050501420341300 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 922741870 1250 922740620 922740649
    0x120a05100b010504060318080a021606020d17040212010608030d050a0e1914010c080919030e21070e06130608061311090408090102010b0901031a0702150c0306 70
    0x2800c005090420ba40e021064030b088400514000c1707510000c4041d031720b128025000d03010f0895540090a200a250002030b49880c0070301884c600d800a40d92080102c2e200c8038140d07800c00000b00c0300455141d8070210311540b07542090000342400c0080400042e80c03400c41d51583d0041c13005400120307248042c8602c920959901c00300c0720009010b000300410f515a2220014190301900c0b1102d41076203014080f040300a503c01c406018000c2140344266035026102d040c3c122600b801c2031042c5407503070504540301c1d40b140440b03aa141c3c6a11044165203010083c20780c9224460140e003480c0c0040b00d12a6580c100b114500a08004200b0ba2440c284403061105541d80003001880341401d0600401c40c8150003e8031640c01440303100c0c0004024808d1030a400703505041e860466100100c00144801c1c00355540042105007001d070000c02442d07401f2030510038050824800178000810b80e00307401c50703148810b45030117510541c2807042d55695600c1150290070701e401070340c80201d0220007004114940c201001c0c00391101 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 922743120 1250 922741870 922741903
    0x709051501030b030c010c03210b0f061e1b0102070c0e160c02040b0d060e06010e0a060f050f032503050118120315080f0f060a060b0d0207050705120a05 67
    0xc400600030170340c0c400c40030381c046042001141400051510840d081c0c0b0141495066020485015105101c090401501c40c2c1c1d100b4081264040034515100c0125840d04184800070240c0320900b2403402c000e900011182c542510fa6060410070102080c402000103c2c4a82c040d017440134200445041140c5000700b4001c00c0030380d41029084019006804041c1c1190f04032400301d81000203c4c013042c0c0508607031500400e82803c102600b07010030000b1400301e058841803561511183c0d42c011002007920502c7c41210020040d130002401242000e5520800281010f011961004003082e00b480070045c02c2d1b15500c8a02d82d5410741030007013000c00c0c003903850301c40d5011035030b03e44c00030b403031f1703c665015403690110300d01850740c0d030800401403840c80c240b4540100000000d4a03690041010125120f00928403440d030700c2d000704000103141071607a110b003805441030561700c6810b00d01d408100c10002d510100050b40e803032080100014996959842442031300c0f00c0c2d00090f10000045240040c81e20700c1e0b0400c0119070 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 922744370 1250 922743120 922743131
    0x11090c1b0615042a0530060a0636120c0605120106120b03060c0d0e0a0f02010807050c010911030c0f06030a09060216120908060910020d020c070905150103 68
    0x2050016a8207400c0f6084c1c4403004070001402000355224802c0005194440c0c07404514a105c81030245510310681040006a410559905d010041100d05a001e688080781440321045203c0e80550361501d0b80750140450010400c0008038800002807207581300c0c0040301581d01e281c07000c202c04960400c005200900b40f403030400100310f055100d400c00c140580401c01002c01d41228942d0402e8001100c1140302034141c0b20107003090a0f07000d401d43d101a82089540d030400a100d00755a40006c0c00310700c49600000510002c96642e07004450b8000041c0c00e510030420140304001c6443c900f88103c00c1c003e8030900e4200c3c480c00c158000e050808450f03646140c030580c0d202c20340e040c060b154041165801003000c87c000071f49801d80e180190090050300b030802a04000c2c00c2003041041662900380912140c41c5e281ca400141d9940442607841300200d409002d20f40110881d1038041c0d0603600540005ca031100d83c05824000d4200c0c03254a083d00a501084140d9155028845500680c01c602402c4032800c0c80c00380711 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 922745620 1250 922744370 922744391
    0x361b0309080906180d0b1816050402030c07140604020a062c0301020d02040308030103050c06041d040f02030d0201060e100b090d05010b0a03080703090b0711090c1b061504 75
    0x203a016594402d40295000941000c0c000ca040c1110040d0450091030340302038003803604164804031811528100310001000d02d503c8400300000d07140c080410381c9003c50045034140020701000e5007020f80703440c00810781448402c00103803410f1540c006a042c5400140318500e0140100080880c507944640103011000159a2600c41800742c410543c0384111070019500b020f40c030210740284a142d41c0c05800501c003040c080100001880218100c0b070040c4d081301c540c42031560411503607109911600a601c24040a104a941d0100d0603695200340102e502c0000d082060300447e0521410400e1500180d54810040c000c0c5d460258403550080d4007850202842c1e030404184100c0ca104114010b0f2187c920012030804110307003504948000350010384a0302c0d03034a82c1c1f8580031a5a0300514801c9001c01e86002c0b010880001d0501940e084540103010000201700f180b003848807415020301a1080810200700d4800005826508068845002c2000340041e24000c4c80d864683c4c131502403802d2046040014040 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 922746870 1250 922745620 922745633
    0x2011e020a0f05391503040b09100c08060a06030510030201140915070c050d020d0605090c03060702070320010c080d18030503041119361b0309 63
    0x11030240d4000c14540340140c007401c01c94505110344110742c024003980d0aaa0310504c540032140c1d4140c0404070b40038955100f80f2002c02c80c07103055160100c0354044086c030010300814109202c0c1f9800502032015506038001421001c0159032005076280c1c041202c241c00e0000f00d04100040f200105524541005a82040407030220402100e101c0641000031800e925415440610103c80c070b64000101850049054201020100d42001c40151980c0880003400541402c10945a03420f4a600600380907920b40302d9907515005050141980d042e61282c040465610b8601f0442d00c0d00810003038004000d600d10358540003070540c4041d401c0c042c140a00040c0d401540e60001588100c1075441004a82c4a0344d41340300201c0203003aa080c40e1509810404101814150031200039801a07000360701002034511040300b8010540042c3c145141c40c2011000b00304001c0b2405800c507500302c800300010400303203022004031a1241c1d18640c1c8400b4982c0c1d42e07020342c441210391384c07101a5084145060a0001840645070351 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 922748120 1250 922746870 922746883
    0x1202041203080f1b0a1e0e010210020301060f0c05010207020301090803090c0a1203300c1209050703030e240a0314040b0f0c070206120a06090e03090607060e03030901020702011e02 79
    0xa6a000005c204038081c2406002e05441c00501d052120700c080302903010040800a01d0742405025000c0e006482848503a18001c07207040ea080c2d61078038014290072400440300d415450506480555083c001080181d0f000c0c01400c2805000740080c580300c0c18443c00540c1000d2103aa41c0602c2451180030800c00b50102d01c507101002c44d01800c0c2001c212017171010000040c1001d0128494181144102424a05540e48148480c040603a942e458050b801212042120711a18014042c1e901082040000a01c140d11500e168003001d0b00c1001c58801c10040419102c20844118000e014007040826025038180305040c15540c9403900c2d0095414142c5400818040140072100b100c01034000003137408101004a42d960756015000301c0d80c407100b160766107070708540a484140005040000c0001c0310070340c0307000e00b00784005500041c51422280343c081180c103501030417085940c66115002c01c000b4400600c05103100703c800200140e07485209200040490b00300c840c080d1010b12140484041c4642d000401 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 922749370 1250 922748120 922748161
    0x10504230a0b0d020306070201050a0c03050606031311041503150b0904080c120c0d020d020c0102100e01090c030308010f0f0f0603020313020a09060f0801090503030f071202041203080f 81
    0x30345042c410b008682400d140000c003a4240c42100c00340050b40380d0540c800c034070400c882c031000c02c02c1102418084003520390030364401364482024804180c400401d0602d2003a01840740d015410103084d000c010405880605840483c42c0c0e100383c1007001880b501e10414122140380c5441080409844000103040c864090070160080c000419412615842005400c2140007000c0d0110345a02a040a02d07030b0350700c2c0866514006003e03080c02c00d031144d40005811814001d050300548011340c01000200d0043c80400c920210343d64862000f08082a2038040c0b12000d140690395140140d81001ca2854a5604c544d1205000c58540c640400c00702261707100200a5030424a805680d0351210200000301c0314601401070360100c5a501c00180c038441542c81441141d207003242044545030344080d200d080301c58185000c1c0c1a0f400400008840701c408012040c1c0c041e00b14200008407104000504049030400e42105600c0c0c01000701d8a020705404c510340320360010f12000ea103d02b51a2090103507a10102d08840c = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 922750620 1250 922749370 922749391
    0x4141512070b0f0a030902040207080c1507120b150313050f061015022b0917211209030301060806030309030a0201080c0702130534050702040603050f010501050423 72
    0x144135182a1094004252280d002802551140100e0800403015405400c0108036032041d420405095802803504a11030b0260752a80340c03401d0b01d00c8841d04040c04038402d10075880500f1030001c18420b40c0d86070186010702003514924060b207200c0e2815074a408404466421203030711240801000c0b030703e0f070040ca0041da40342103024003006802d5071050303141a442004803c0010302440b03c00480c0e00310300340e2000722201e2998a007100548d84003124418440100c4c4060760301e07049051034800442e000784010b035106013403205040c5003220341c4003145c0002405660203c5141c000100402c001c13507008981d55008a4128003541c0340681c02c4000917074818aaa500030305006c505c1c0c0c00614181500c03004d07140c6058010303003135000180c120601c2d0300081c403045606902092003200c6d00f002580c0d640c101d840c4d001c503901580c6400c0340e801e481d0940b540e81041108a034000e0f200c05012000800c140208400070300130381c0000c078481d41024100800d8908051128100d130078905404201d00000d8408150005280300 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 922751870 1250 922750620 922750627
    0x303050a03060905070e040c0e06071e0f0c03020114040503150903090301020a021005130b04030c080f070b1801050c04090e0f0f0d092106050604141512070b0f 70
    0x34819030240c50140e111030416032605041040c0c80350407080002c402801220704000100c02817500b9140e181090142d00d4001e81c1c01c0c80381d60001403c1d03c40b40800d544000020b94a14a842c2e0f6495140400d5050104d821011180d0b04004550300103c11400c1402e40006042c145800c0001090340c03a41e04070001469000030002294040f8018405c0300d540f454060002e5507681401d0001a45e540315401540003800d1404000900758516041306c02445944403801d100c5607129a10122140b40611005440c1030804101040001554500a01401d8860600c041e41d40c541564007200311035400d40c800c0000e905140401c034a440e040030854050307801201c0001007401030365006500d400100c034034a1000e8410f41044820a450000d0004948991036a41b00861078541c070400d0b400c40e43c0d03e20036481403112486c0c1078000506540165500c80d0016000140d81120740d4400b0054007025542042a01d070003c4a0002c2801c2802011004a24100081405c1e0b40751512980302c500c200e0f21050010344020 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 922753120 1250 922751870 922751887
    0x5090105010509061e0a02011a030a080406050315041515020109081605120a02011e0c020c090a150b0a1805090103030806030a0b0906010510080f04080f0d063c030305 73
    0x445482c041d145c0c0c202c2c025124a805100030b402080c181c1441c1200005442140c2128900015207408255005c0c0c0c06e103040c9464054103444640018040003007a00d800e48500c1900d480e18440c980d41146100e8200040c14070303060440e1003800c3d00640d10421641440d081ca03001c9001581181e8800708120002000b221440c00c0550a01050000480d64010001307201c540c5194150000503055601144011f10890703505d00100c1115141800440542c1150a10810074501415a00d601c1901b014000c910380c4480024440000d0460f0400310548201184011080f86d1003e140c42c102d00700401c00031007940c00d2000064407003105100003020410003c1c0051b01d9070324148140d0150b542c1c401c0d020902402d1200186407614024019035004a05000700c05041d90720a142c0c06000d00d42b42003a104080c0c4468442d012140d00c040c4090703d40540070064241240b0052003080b004003280846c0d0300c6400380c20b00d034003590f20f1b54a9010041e00c004146010007856031800704003088a80c50700f855983c540c001c = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 922754370 1250 922753120 922753147
    0x914010507050303133e011b06450203030906130503120f09011206080a111c020105040902070606090516111b060d02250506010509010501050906 64
    0x12444028070743d0201000b8804804c0180c48100381151180040c14000d00c0e000d80c17a060b01d03182e20803200c044082d0300b41c1030005807420350358030b83c4031000c1c10314100d240b070f0a401010140f8204151000c03145640c0d00c030390781d240d070242c171031858104072005032251180c84998540b542c1c07110b04c20340b42c5c0203502454408420110b41d01003042382c1c0f8841c0c014119a03281c030105140780400719841c0c46014028000c80c0e008800b124064011a0784001d0f0308000709040840e24001105c00c43e10f00200303040c0c095556000420045001c00c80d1040306441101c03500242c41c502402d204400080303e1002100e004050170001c0140e800000f620305840100800603112034242c100200904003a51012110310701d01424400000c0c006100400e1604241d00c800c07807980c00300710b9104e648450160003e5111005000030011a01d030103801004a403404040c0982000150150743c40c50003896209189109810311303144041007030a1118030f00401781103407404095032400303002a0640c4156090075106a00005a20300e51818 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 922755620 1250 922754370 922754377
    0x50c0a0c0609021c0606090605010f1b300c020612040212030f0c010b12150408040f0e010617060f010507050709050f04020102150405060a0f140c03060f090108030f0703090b0c01060f060206060109140105 89
    0x41080103401c46c50440501b0007034040031401221030042c01d9844c00025280a03038210040e53f54098811071030f0480c010907401c2605030207030089902001003000c26040300d0013040900501c07620342548658802c1460341050031208070700c0303699003c2c1c0040c8102030700f42d41012400004c40c400b40590140b6580d154a0f001350207103d030707800c000c6251500410100e03e008052144505842a907180c0700b072040008010f06040104c00c42d012584001c44001002c2d29500c2100907200c40ea120b01c04603614940c03150100019524201c031103182c0760440108000a40d030b410441c400380b41c60400d4a90b00c0303604064440c580c0320040200103a0f900d589442c429420303da202d600101c0d440400e000501200d0600c50360442d0242c0c02543c00c913104944c5540b450b0000d16114000034125400c6000651610402072260031103900407217429014080c0c41a400107200c445075000707200c201c0c22100009a540c5c01d00051146191081c1c0002d02158400020820700d40d802200742c1003a1031208004d800351800020048a5510 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 922756870 1250 922755620 922755623
    0x9060709270e0a0f030513050f090a0c020c130b01080f01081207110310060303081e041103031e070b010603060e18030d02040603051603050c0a0c0609021c0606090605010f1b 76
    0x11000700782416480806070201031f1043c126055526a02c0041010066200e0090355200d4070721300110f01c01d042d0541c884945c041050064a2000c00b0040000e0301084e9190094240162980c0080c002507038001c80c4d240d441203100c04240300741d504000450740d40b00044408408140c400242c50030078045000c01e81341104000500b00c40c102c2007240c60041c0500214417007200880d40d144042000311201c2c070300c0750350403c402514404196440f038079a450301007154903985802d400708100056400e07030b900840c6c1c182c04081074a200e80e101c1c01031520701d0f10100c050380603c04042c6401d4080c00031303600d29044143c208018034041c02644252840d00d60551203000b02c4581128400140040c1b4650990032591203000400c401d1201c0600189058040d180c2c1100c031060341d000100600044140954010340a0b503024603c000341004c100e90100c0c100010080c401c44603050b84100850400250740114000b504945070180700e01454000064000e00c03441d0180010f00c01e41c10780081c001d1524103914036155 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 922758120 1250 922756870 922756883
    0x303150a0b0a0324060f0e0a1d01140619080415021303060e2e1e0515010e030606121501030f17070c0306020307051209060709270e0a 59
    0x40c1c1ca41040540108800b504803054140201d00005542404c41c00100032124a0789a481184401c090100d9490320381000440c0c0c029560440824001d601e0f2174044094540b03241e90000719414202c540d0358483c170040600e4858001008140c010700300003100d0620341000e504201c5c5294940745081700c15003c421814200161002c110a9940c0f00450103200403640969800c001c070b02c0781c0000307064480c002d240c0180900a00614540340e00468210103a0981204450004000fa40c0f41c101b00443c9442c00d1740c10f0071583d118000e015502c4e280b05d00c0c94201c48000d080500c11101441c02090301c5900c0240301901c14a0082c141d10140d00d0103010841e400003131452282169078403498034901c080b4881c4015209451401840072000c0c91140803140e10301d0b0003210071440c1500d16640e00e006948024038003c1088000d200c0d5506111030f024120303024000c880c0280080c1e01d808007009011026a03404a0081030740043c1288842e02800100c1c5a004005500401d54070000300c4000d142280d005c2e00107020 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 922759370 1250 922758120 922758127
    0x30b0a1a0f0f10091d252148020a0b041511040b0405102601080d0c03050d0207060e0d090905060f010e0907181212050c0303150a0b 58
    0xe13a401a107800540c1c00c0c1d07151901e10000090450107080c40e080b10050401d10208000154031070b01c444030000030b610149410a42d40c140700c40c070082044550103940003445d80350344080041703e030706c01002c0418072009110a01e03051545401c2406484d00701c03800c10140c156400000e07008a10034454281d14541144503d18a800d11b4501040c0f210704443c0061800384c90211103601c980c84100481301181c8459243c01e0810341880c08100da03038481868000e042c05407005140c0a648110b0342d16040860009501d8003c0f50b240050040c01c003980041d1900030000444841400079800c8025a003869401060058071a0f41340c1c070b0118000c0ca00135050114a120b09100080320036400866401910250391050049444041c01d0142880b000c80c0c0c2d82e0f0100d01d00c8030031301001f402c1c00c41c0300d50f601c00243d02d040003402d600c58240041c18107040e00310f100300c00c05411190040c800084804500d2030950714000d840c5c81103140c00300d92240406032060308805451000c9495a03030342c006040001d4240e289841e0758 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 922760620 1250 922759370 922759399
    0x8120a1104180b030304080703031202070b131502090d0807020a05040e030304060e010c0e010323070c02010212070c0b07080405190305010515030706050c010e16030b0a1a0f0f 77
    0x40c0300403002c1410281410090b01c0405030078040300f0f5404642003400181005030a42d50152070141d07104000c1880d00f03500303105c0c41c008280c3c0210390500900c1c90210396a56807844d420070685c01c450242481403414010400e80603180c480090341e007120b9801004194940d0b0480c4000f0f114001c1d00c0d4081e541c06800c0615004029002000460081d841040702b000644102407007a400e80f648010b02c1c1d0301244001c2705e40c054950180c4c20450342c0c40e03880e4031f481030581020640020420030544103030002841e1411000c04550301008076880000043c0c1485041c40d9040e95003943c3d00c2d42600850b003c008000c6102802c01c00c0c4403040d200a0403004024500c410160b00202c6180c0740248019503d0f9801c2c0b10201d60003400403880400345220103405040303440d0400109648641c0045042c0c0c905642e100c61b90369030007900b4804003041d0307104854054810751075420300908101015159100c6149841c440c15900391149011803804401940d41060a80030400051031105150100c01d03040541c1010004 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 922761870 1250 922760620 922760639
    0x90608031309090201050d0b01030b100801170c0f0f12010f050402130209102604140d0206130f020103090b040501060812070f020411071704051c08120a1104 69
    0x704003414000400c040e03541d90b0ba400b800341c40c410b4a000c2d0102d0b8007088104851002900b0901e107603801070401090480700000400c20a040041540000401030401440a0241406031360100d942550040c0b040c030002800049040e40401e0b880361041d800d150524203140c48090400c40d4600060008020301c5070720f65048406040d0881d4100d05c161440c00340710206840905c03e0310300240700901918200c403c0704c030064034181541010091491440760b0b801c4500c1d007803030607070324407a034400c2100301c4150000388013251030581307030346040f00654100c0d030304009000080c3c41d82003045030303000110b981c014003060006030000c3c034038000090700a880c02c0042009001c0305401c46011074242d4001c48810b120040300540301800707802c07001000d402520f042d1401620f45a0040318280c001c0804103031800d0281d03620009103401c801e01c0b000c500c03900864108518605520000000c2c0da15002141d64005255510401071082001c1d4446040459000c607400a130154082c40c03014507280c05a51f41e44d51909e2112 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 922763120 1250 922761870 922761877
    0xc01091502070218090a0201030e0705040c0e030c010309030816051204030e0109060509010903083907060f2703060c09081605060316020a08032412030a0c0c09060803 73
    0xd900540400040905910001c80485d1142408601030000c0d14101da0044019002c2122a8006489440e9022443d6540c0784550000c1c00d1040d140e201c40014450705050030100100300807410f06181030b0100011a4000c034a00340d10400a0090031407035440c440c4151801c0c02040303086202d0703030301e444208010142c01008201c000f5009803542c0d0700d4184d0304c142c22030fa94410010f40c1c50014081e010104006203c10300035001461617510711070703901c054040d920341213000115140f003045000c07144401d11071901841040044c1c9544e00d0842e1480305043d2024048002d1902200d110729002501c581d40200d500c04840055a4090002e20041440b210014020380d06409141418010340980001c0c201142014000702c640c098039031411541c0b00e003984c00000c500c030300714001940510f03054a0300180c0c91000a40c440c150340340082c1c01ea045121074030045201040d030024025402c50382c609039120000400c0d14600c509500d00010340c01101d190007200e404643d40404101810003c2c081048800030010b0f = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 922764370 1250 922763120 922763123
    0x90703230f010e0718020906030c2106100806030a0f0302060a0b030a0c0e0405210d0b04021303060b1306091a030a03050405011b14010c030c02070f0b0c0109150207 72
    0xc903100c69412a84003800c0b241d0300f020010055008110402034410792a00112107180c00e24001401d0041c00004540745500071070316140d50003c001a145085c5941c2e041126040d4810004d0207d1441c1c03003404200c862581c10404001c3c00748200c005002690b003042514800c0e58000c0c0171010842c042d18000c3d5403203d0503200c0c1240d8074104110381d07800b414005090300039190000c14503403a561a002c45020200030203442079616000d90107024000d40c10151144102a0000c000755a076550100a140d00f00c40c078162109101d1740c010024400000b9443d1105000e42c0d8104400040040e200c90008400495048020034210300380200007a1140c6682e00495080300030069140e042035144040584403507072001c006010810500c818030895105240300084003924010417040d4803456140c061000040c15a5010302c0e86d110040c1c100a2075050007599464100d90005203e01030030402d014520420340d0150000100012422401080d400d422042d00705804c003424000b001070031481500a584500d80 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 922765620 1250 922764370 922764373
    0x3220b0705100608010e0a0204020a020c060403080706050c070327081e01050c09011e020102160605100902032a070204021306080601021c080a1b02012003040c05060309070323 77
    0xa000883d03004c18018041060245005032003004110f500300802034101d0781c00c5c00110701c41c1000d40443c6440341001032000d94003561031103854031540d00e4032806031480280300c103040500130301481c00025080300c20000602e180511100e0309070016a13000d4410040b50303002408900c00c0452103a80034074070a010000380341118000b44000c1d81c5070071000c540c034800d849003140050350f04a00c80c618074007003c0e0280d510392043c1c400035140421901f404504400182000e0b031b005a96101400140d44035460b00a0081c12008410f40c01e515046058460030280182c03e6020302e03512501c00c500882030b4404880506078010011900c40b1040c0c1b001c50340540081c051136021a90040200ea595800007580c6090840e4180307071031441e20f01c064030840e08040c020704012170031074030fa0b0380400403960a10f030807070020380c11940000b4009081c0710012900264440700300019450030800d000200726070b07000c48000d850050324200d54a440d00e480303003442c210007580007a180007003902128003040701151281484080c90030 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 922766870 1250 922765620 922765631
    0x21e030115060509011206080319302c0c03060a020c0a141f020d0f140708061503010e06180f06190b040f170a0503220b070510 56
    0x56540c0d03101c0c4040c1c020940424000c0c4a40d000540c80b0303a00c5c40e074204448801c0400c040d5521440d41d1f145030403042c0110800fa00b41e80190079201d900052481805040394000e034006070002d50407602004040003003512007a1900d86c01400c2017000c95000d5154404100c094440141199101340c40d650341142a900c00d00841c00403c06140e13450003913a1b00071a000c0050480d000c102d5035440d54502c50300b84030a140307008031400c10899503101920340d444c0c040c0845001d60b0f81c644140c004c004072089400f000c0c1d03550b8a03260f001801d104070394410700e0b80b00c4e40302e081c20f008940700c030340000d10200384c0a0303c1d220107100000000f00301102e80010040c0500c0c000d4030711100110f01400008400a8200c0e400e1402c03203002e1001640b80d06d84140c180d50355800c2090740c0d40c08503841380411822070380950004001c120051104000486c4a040c2c0c4c14941e15460740a0320b03400600396a01520380c49511540c903028020b5980300819420500c01080061496175000c59480c0e4142c9000b81e200c2d41c1d01c41600480d1885c15 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 922768120 1250 922766870 922766891
    0xa02070b16122d1403100906170a11030111070606030b0105120a0b18010603050718050f07030b01090b0706050708090f03160813081e03180d020d021e0301 68
    0x1103800f0141900854040b0520301c55a9004102101c810702c01c900c01c0080c0c4101c41003515410340002c5000f04040f401c0c400415050541d0101907990561001c640f54030220fa450041d520041103100c481603000556044402000c1e0009014001c42d1582d1007a41c40c2c006204002c1010340e600800c00c9900c205480040c603030385c640401800c4000c012032107465410444d0403030b000802c8207448590010000a804c00c42e207a01c96011801c64005420494690b8413011060103d80c09180442f0703c1081941d8090100d480d00e903a8295040d0000b524034014542c5070340404503668040c5035464044c1400c0d01006441d80c001d41002c002810040e948003001c2038264010801c900300125501c0c4000401500071868a044502c020070503503141c10040e103032000240061100601041000c030002d01c11440180700c45403d800c250b002c910119000c0c0f00103644104900b020107103600d48140c8a0742d2003280c2040703100c2a10b00114240309902c0714001c0d84216041c00c203440210b5a81103d24611009500030444110f21 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 922769370 1250 922768120 922768127
    0x606030b160e0a0f0e040317011205060f060d0b07050c030324010c0206030c0f120106030606020d05040303080105090601120c120e0f06010504020f04080d120b01230a02070b1612 78
    0x203003e00404c1007078020040c0300b0b16072080150303034015120f454060303c03602c40045803008090080c1c010516080d566680346092001c1084440e8014030f84a440d107200703040150004045000b90607006204000d6035002034075541c010310a4a00f1a00c403007055135520300d000c54100d000040f12011320f40c40c0385c0740030768481080e5104206031030581707901410551651b207440b0046c1c0a1500981201302c1741c42d82c20400d08540350031400c1ca490003030002351000710f089400c001000e030509198152030010000280420408039038007820700c0d411603405072085079490702e4000049603c0c42c00c00300c150404d9428400b5200256a2041c4103101d4200070b40300400c00200d40880407134070307017020b440385000a07440900144014079090b03006008000480880300d2a00fa80c0341281410041c140c0417000c0407521750001401108154064a40416000d1921602801035480d5803269101900320b01d207001d10021604524460082000d8405008004880b585910340402c60003600d960042c0308407042c259088130354500303d02 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 922770620 1250 922769370 922769389
    0x506100e07111005090703020d05160b1305040519050f04030e18180c0d06061d0412030b03010f110c01110306060414191404060f080a0b040606030b160e 67
    0x2209000c0c00d84840320f000e00c60b010b0078020307203900c0c114043d908000005a9640012001440c4a8030250102c40e4481611040010341c80d4010031442204108416010905011002c10790740b08440000e0181c0b5560108171600403d1440708001c0f40c504818840603500e180801407140380310340d4503120381040c21424400b004540c5c048000490a40c1808605044201c0f04002c021000e03034821140400c0d410303000150220340302a02a40d0159903840c0503c001054420b01041c00c407018091881203041664900ca844c2401281e400201641c3c3d80e48612070750740c290800549201d4450003881a850055418801d80c6e0040d40041c0c0a90710b031141001c090340c2000150382c890800281943d081a140200b0a1480003004042d10340c031112410b1342d44504084d0040350405400c94848a40000000743d00b400221082600104640c01d96002d04210010000504a0082d680403a841c4c00d039072103c0c03600d403000d40300e1500000c0601c0c24001c2040f0201c180d40f001003c00402940c1c1c1d07600c4850780401030100049 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 922771870 1250 922770620 922770647
    0x9070311070b0603030f04170709020a0c020613051e01030b03011503080304060e010606030e0c01020f100b03031306031e150b07150c0302130506040b0403020d03020a0506100e07 78
    0x40d09010400108480722185035101002409507450054000d64a00c034591013900500701040c050000d282c0151010401c0310090021380d03404514081c4400c60251062440081c000d101c0c0a0002707000450410100c086001400c0c06810700100e0742c441000041406080303d54140041c1c644042d01e001fa01d41402000244442c481c10240c10b241951203078405070f44014002e559494403104800103540b000d1144100800041e40d00003a10912014050b013418051545141150701c0359864500034200400c4001401c050280c00041c5c01d1406c01c04a401c0d4040d118a4806201c0c000c4000a0400c1c0c16801c40c00124006000c00c0c41140d111583c80c1044030403a44100c188902240d10034421888800018003104d40500310f60141c0001c0e50b80d22070243ca8031103042000007500031a402c2d5800701c8507012500546030845413241000c0c28400540c565000b144406803003100d48403c100c0501d07000744030300d50420390802c00707650051410b0782d10710b01c0445891003030401e00f045140020307604038854582a403149 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 922773120 1250 922771870 922771901
    0x5060601020114061c020d080304030c020f0603070206010b0309010e06100f05090903030f06040f05041109011a030406021303050303010f1401050f07020405072a0c0f030f0602030a020720090703 85
    0x1004a08202555400d0302c01240c1000c000c0e08241c002c64030b0700d2301540c400e5100e0707507610790039080c541b05216140d602c00c850640240d405009104e01240c02040e400c1c1035034541060039031a556140006809014007282d502514000c40043c820152030447c00c600554a80c0c400c41e401c0280e844041c40620881100c51401d250402d00100c2d140703402c082c1c9150380001c001040494a1042c48942d50103d420a903000c4a10445485a0820714141155014010304031304034146110302805030106010b00c8014001042282c2c0001c81844482040e007800340038542050403a41ca83d82c4810a1004c0d0900c540102c0c40c5855298401d1800c0358400c204641e0f0039901c00d251541014683d40c00c0c0005080060050340c20b021000b01c103c2c0f052907034031036240044140030b18450303e014440c0c10041104005600326101c403084501080c00881e01d10021036231070716449000165655203081d0114024010240c00816400d00110328030078907808440c8055610764100c0b541010368880c25000d9046420441e0405400e = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 922774370 1250 922773120 922773139
    0xb0621010e090d090308030c04090c081602010b310606020d12060b07150e030a0c02090108010e0a0209040c0b1b010c0807271a12010b09151c090506060102011406 71
    0x41e0340d010103503411808d540c1c10030341019100e40c540d2060b5543e210007040040c43c05d00400a6a802c01d002043c8000305500081001c80003a10110703e01c1402c2d10b0040203200c0f010034000b50369902071926522a0a21103c0801005459120082d164900042448001411083c528000004500c40d003021603000110381407500760b1030b0392201e042c00840c403180c0340c00c55903420500e44804003c2c0020b100a920729959446a00305501c1001052181a0070000c1617a1602011051105001803c40d00840c4c04540d0448950340314a482402020310303400c034814081002c20075105ca0784101806031601d85100d4020302c0350f451303d00011143c0d00021103424002620408680107880c540c9119551141c100c200d861030b400c1e440d4101c4081c40502001a10500e140009503840e64240c8110352501401503000103d18000c298800941c800c0541c551141c8070700c00c0010748075402c0606440d03a2641c1c0c021014107204488107410410307200c0d84100c482c54099400d003d200e101c216446241c0510810300102407098 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 922775620 1250 922774370 922774373
    0x10060f061202071407090e01060806010603050c040815010906140a06050f0f12091c1707090e090106240212250b0709050f130b0621010e090d0903 64
    0x25640050603040920701ea00700100800700c2c0700c440010150020110042030140e140c886010116a115007a81540d03901d4075100b4040404046030045c111143e600e0007044a0304c3c1d07010800050301c42d540c000700c9644a20342041c500000382080707081c120340c011482008815900c44442c013102008800e0168001c2c942402442a14041c0b0041c154600c2d07140b020505107006a00a0314080e807014200451740e549c0c0804205580008002d803000130001e04020360f0040c540302d00e02a140304908110031034040e4683d00090800c034810701c1e4800051145142e0704c2018100400345034000c10090041034400c01021581403280c4080b0b07444407407820b05650041202c400c868903082207540240268801c1d42c0413000f001c0d5030299103c031207040d01074064046075141e41403012016000c007106a102502811205442d40e2880d690480000001094918003042c20401c081c0000c4491059521f4200c00f0442c03040c03810342007607040c031080d411f03904403152900c90360b01c0b40031449070f8901c0844480030006004000070300 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 922776870 1250 922775620 922775627
    0x60306041520070c05030718050a090605010312030e061005010507140303010303051b010b064e060d0803070f022107120311090f0d0803071110060f06 66
    0x32295007900d240000c5200001000714426500440c07041880c0c48003040c2c480c144001150114010130003103009043c4140790079071050107400c5141c801c410311a51080000d040c010242c0000030300d154005d008010f40c2d81c591401580d9600381d41c81d0000000e1030030444905070b0400080103070140803840509201240340400450b1340f0303440b0350000c43d034808000710805500902000910702071072298032140c1d152110b8070040b40c00c10101d105c034803109a061000d84603c40d2078102c200e4240c180004002051512000d1082050107205c00c054075109405401d8072242c03d00342060010b284000c00d15084143d1140d00800c2000b0800d81c03800303041040200080b860f141c2c0039050458040034280140e83e11202d0000f4142407003400000c2c91410107000140300c20800507141080e1501402c281001c0044d80341c0781400300d5003402407074200ca0044400040c3c1000b5540c641c030b01c08010301d0380441855079900e041a00103143c2d184864140019116282c202e0042c100c16024540948486480943e445032900d40c080317 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 922778120 1250 922776870 922776893
    0x40e0a09080324041103040308161b0203030c0604031e020a11190b070308041202010218060a03061e060905030a052104080f1510030c0504021305060315031506030604 73
    0x5203c2c0e4440e404021140c50f140180010001072402c41d6440303113410b08010b050594002d04400c41c0b044400040803100e5005240610361448201d8013200b0702d00c2d0b510110b455845410351003840391050b1010002019480200d0f140c400b189011445240202840140e03641d0200c142c2c0101108100b0311704074807a0515846a04040c60004130740c08085a031401400802d500c240b40075000070b00b01c503040200340314104c0d074001660714080c802146415038121041c072004000c2c01d1118408c2500049000c041d9219800400280c41d0341c0f11306060034240002c098036101c40501c82c01c4045003400da03001801d031038045403070503903642c10101500503e011b490441915001402400c01c50031f5061002191002e000c104484100508000030114003203942c0c030850b044640200340c02540850f0032024400108003c40603001c03144265009030311009842d9503600d007030200341c200b6500018003004010010180c810710f1403540a080e0243c07041003201a02c012250311007200c5590301540410f0225000641141c0c2d031 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 922779370 1250 922778120 922778161
    0x20a020703140a0b0c0d180209070c03050c0d0c12050301050a030b06040912020607080c16060e03210118020403020616141b030c0a06170a0b15040e0a090803 69
    0x242d50301d40103d84d44422891605441e40500810f010401822034009817040312074845c40e00103071501000302580042c08400006040a080002001440003007501840035100348880c200155001800d038900010000304603001c0598180d450501c548889a008404581c103030b0318013800a0b141e09080d5101c0744055403001c0d0032240c2243d90f688400001c00d40c0750145c0300c1040f2090b80640300038144218010003110000d0210a00c2c21001c2080600580366250b01d00e4040394490004902c1c805031100d03443c19400b07101c1402c02c684001180801e80c1418442d80141a02d0900c66a4260840e205440000300c4c0918003009400010411804030078100da0244641c0551007a0101614610303015282824000c0b504881c2d0034290168a50341180d18040c4441c2001580980c1c900343c00b14039150300240141002d0715840030848080b00072070b441c2070340740c1c102e10403404000d03200d51000070610741440b52a45c454800c0790300030100c1801041000e202ea00450000640048541c0e0568461044500005400095 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 922780620 1250 922779370 922779373
    0x211b0109170a08070b06120106140d03170901020a170402062b0609020d2904090f0f0809100309050a080904060503070906030b0907081f14090f0f01020a02070314 71
    0x103800000300c0500090500c0c1e40f09070840c1715a0304151080c00004040359070440c41c10f0b4101041808054058800e03030b45814030864511044041a040503610b0101e81a074044101d9550420011000350540081c86441559a9900f40d01d4200000384041120240c5000b58002c80401908070350301c0c031150508502100d100054581070450307040308004c50380c0903030141500c15004500410031700010f1190040c45107040102005801840e02800e800745649107429210700e07524848841407001040c1c01d500801d900800030b207600d07292402d2410040c0c100741c003c035101c0c80c0346d19000a01607100340505108664044000c0c90200130076590400309801200140e0740080d960030000455540c20405000103084031031000a486046040094000c0c00c002e000d940140e02c0f02200704a488000280008c0090490b1403841150301c0d40c18a9038050081107050752650b20b21074041c885064004524050161201c070100e6102041c414003031801d07800f0300500940940c000710810400304803584d410a007a00c04070b40 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 922781870 1250 922780620 922780633
    0x10f060c1103160e01080309010e0613170c030601060c0f0b15150418020f030a0e010207061a0f0406060e0103020c010f0504030203120a1b050702030c211b010917 71
    0x40c003103454100003890200c40540f0b4000d0810501c81c90018960240c50308001962030b0910740380010303105d10040701c0d00741e024002c0011146551407554040e4000741100480c110740100103107500300da9801c0103000c8603103e40607140001034540d0054568445007648101c60030060300715a240e40349035a10003090500460240c11a10803599600c010050104514488403620b03241410031000d0042c1c1280c102c900c80302d204100c140c2c40003600c070061729800708030750b20003140c4000349803003030b602a004103600201914180041c0fa00c1600c802d42c00e200d04110161520400c000c42c01d0b007003206580b5180304442c0450440d0800c180d855100350010700b1092180302c00800e1820448025004460703040340d05a0040e04003041a00c0880f11071241d894105103400014400641590381290724a080914014103218000410008548082c021a03101340401062381003001910002681c106213411454221800f4000560810b441c54056401c01d030001030b51004045806c01c840e403180c0520440c5061203074443c09 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 922783120 1250 922781870 922781903
    0x80a0b060d060905030a09060e030f0c120c0619030c0e100e0105040305070303051e120f060d150b041103040f24020f0a030f0216031d04050a0221010f060c 68
    0x10170003860500403c0d03072405031a9140610041525400d401401c1c403e41200d41c10340c070000c10001c0d007040c01c038800304d42e4200601150301199140990107080241c1001002c5079100042c0040c03c2c0fa001c00c2210740c1c45c180303c0503070200c00031611844070a20701e1364002c9502c4c0c540f4640911a401c00c148100c0103042151800ba120b03161949841d145500450001e40001003400a480b240709aa513505242e9022407400c0c01452100740f001c0e490001e110003c00000316001502d1941d0309450350b40c0e080d40020078918460a02209075010341118021343d4022030510700c510741480382d540c0c00c40740304a4010411a07840c3c2055a9411914030b021054403a55040c0c040040100a141344010704501862100b0f05070350300c54042024081d121014203000c0800c4c07043c4814060300c610310030b1001100c0e07070524009001162221501c00c19032110001d0503082840e0600b000780c044465070040441d244880010b600704a01c51280701c400352405d018501510703010b440d0401984d07008240c0034040c1ba00c20791551070b014212 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 922784370 1250 922783120 922783123
    0x130f0b030f06011a12070f050417100507140f0c011b02010c090933090204090603060b0d080a080702150708040611041a0d090b011e080a0b060d060905 66
    0x481034003100d03402c42c900400007490030840742c149010303a8000482c10700d03161908600c00f00c0c1e0014910014001c8001a500e4858801c100315809010240c9165000580c2d2014080d42e81d1940810510050324000105144034041d0000d010f415807035014603841c103261803020200380d4000801c511615034803420040c060500c04001c6803102540d603800000c40480b1110014062941607000380030407881c00884140e080010240c0c0e1200c00d245050420310b06004d03418803a291040350307015880341440031030301107241d146c075400c0642141d00592090003131441080070403001c403030a0540100b4003402007240460030350080744c4840e40300c14140162501100909090b00e151901203510000142000703003000204116489520f101150404413981054101a02001c5e841e100d15110345d6000301c045944641030200340c000102c80c44d48410855000c0d691100d0303a6000000320300007194281c28900c0e0100c2d50300340000e40c81d428076070441c1098040c0e0b00c664050048041100320180d41c01c1e501c07200d001c80420340 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 922785620 1250 922784370 922784383
    0x904020904060b120906011409070c0311010203090c0103060f06091806052115070f1b060c2c030a0206030901090b010611011a06030f07111614030c130f0b03 69
    0x4440000c000c0e491700c000d826041080582000b10000c034018080c00c0715899902e0101d83c010380905000d45914450301b070664803824001d201484940c000001c01001060105085003441d41c00c1c0c90510105444450a09018516000316000210300c003904000c620541c0020103039041101c2000905a42c4030030109900ca4612021402c04020000f403100315001c00300103c1d080700800301c19042d003506003101c0092075090003040180410416a252021160b4820080816241d00600c2002050003e030f00180031034200700a80310031904003040301c9200000c007845400c11200000c02509842481d0707400c01c100c0b50000343c80240b681d0343c0c1e2158400006c0744910b060b03018040035100e20700c0c050600c1001a0940d01c445071100c15441002d6100c61054030741106403a00701030795014003607036951608030886506400f0341040e8030b0303881208160221042d0b00031640c01030719080c20311080d171030079240705155075001c10440300d40d0848506420500390000b241d1181e100703200d4000d0045510329075540001d15194 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 922786870 1250 922785620 922785637
    0xf04240f090c0605030405070b0d021315020f06070203040e10080a05010b040531020f030d170f06091f05101206080a0321110d0903030501050102010b060904020904060b 74
    0x156a000c0301c00c24800300311001c00c01000c0c40d1a041d0b00d58039203580c1c0d00f0b454030824801c0b64105040031a01d10b40741a4550180c820003840030080c11b445980d82e40b0000946070714040c582c40503000c0d2a841d0090a0030119600c0e1158010b0f400840c542442c1852809040e10020194808034020311404a090780c0c050083e81030304d0740036000106001c040e10702003104131032014243c10b05003c4800710030310007606543d0949100c030170080d41d9020452154004119a0f00540c0704150341b50085030302c00d5500c16008481041c2051403800801080d50758981380c00864541500c89503800380104000031000c07101500c0484502c2c2d000b042404030b4580c1d800214041c0940c10110102054840c81d032840405030510070107004289280042004850646000d45030064016007038122003000009140c0c1844540c021501c2020344001031a621b000000c40c1000034074080e03500310000b0b41410000a0390b036105016103405110004c02d07580c604506402008004c0d0b202c450b021744c100c2c1c1c6071100001c000308000c0c003818248 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 922788120 1250 922786870 922786901
    0x3170409020c011a01030e1002030406180c083c100203011701110306060f0c070e07080402040f050601050306060a09050d060e2a0603070e031e0f060f0424 68
    0x1841c20b021942402d0003000710300e0304241c5401f16405480c1c1c0000703001d4402071101c1740016a20740311410325402603c0b07030084240e0030484440c2c4081c1002441d40101c07044460810903603141e00f015682c4880c4000b480b90010281c0d994884c82401120410725043e0044038003c8201c3e080301c10400c040310240d8109030310003507040c4000101d164110038203005054a02202e1203017980703985012000951540111110f132142e0f406c0206481994140401441028007200c54102c010f628103041c0040c1000030454049000342d00b404003c8100541e140100303805104140c5507142503656580070710001c4d4001c0200348040025a240000b403a840f00307520400c901e4026000451103d210382c9415240c02d5021b190b60300f02201010350140d0344640801c81451481c42220116529205d01c00200c070307410780c200d410a9140c02040f08000061040700041007015000314140c1d842820304201d00360322210111819040c040184e0001000102e9800c4480c80c1c820031140d024404021450f190011a0800c8084040700b = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 922789370 1250 922788120 922788131
    0x306050108071e0e07091a031e0609070e04090f1a100608070e060c0d03091401020a02030d0b1219031d010c1412280201140103170409020c01 62
    0x1e100091040001801d00c0802c50140e0007100c012040c0120740c10301c80d4030440842003000c1520144210701c490300500c4e81808051101c0758091582d1829442624105210110100c3c03c1140e2112498800c1c4101c400038441c1d00d050340d13106c0c400d03541d46211940403036200e1f0b0b94106020008841c00308000250740240d1203c0b202e580306940513030035100003820305030f012001c0800402c51503506c0480300b5072044192900750007405002010501900404004440c940030360b441c040d801c26230591110b080c09000d0350f001d010a80f2940d0a541c06c030b1003543d00c00310050704100442c0d41c070303801150001c18603204c003c3e124503007503030311541c0d210f040c00c0020055085064200c0040360906a02c9540d04440e051056801d584440340640043e01d002007101000384001940302030780101210038045500002031310510039a0b0b40d000402e00c21034404031703401050014040145041c400710b205200c1d542c0080c04031100b00350079900319100c504454181d0200c00020b4082000701142c0c1c18654009021010004000440d0 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 922790620 1250 922789370 922789379
    0xc0c0302060a09150908120f061c03051c0b150a0f05072d0311060c16170310050405100f05060d0e0a06060302240406050d06080708061b0705070501080901090c03060501 74
    0x1284002341c030051680e01c406c024001d00b6514403104066602c85a0050070038205503180588160040408410004000c1c3d00c0c20507900c140c5800c60814250200e0301160800606c0d181c8001c075016100400e00011324000d4000b18041c0503400510400340215181110910f0030038106a0644828240c01c0740940040d110008041d0020300030440800310801514443c6001d80e4030300c00034000c2c42010380c100400d4854003402d1000c050141c0e20a885200600c946c1c03841c060103030712030743c000034031909004918003000a59880c840c450f0080a03180030802c2c03c1e402500c0c0c84208a001e070841d000d045500c56598a108c614030000308a500c1c1003a12902d400706e1280d15500400c4000b010005418400c404184111080f0146460481c4c0a88020b410565101c02007461400000c0041c1e030055510b44c03040fa80702007035031400010b00c184598200d08210b615071070000c00d10f100380d00540d03000403c542c3c071454040c011980903020b000d5100360800c000007600801500c2d0332410000d254429180c88ac1d80e40300501 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 922791870 1250 922790620 922790647
    0x908070201091203020309090a0f0507020705030f160b0918011d0609090a03200601030503040806011a07080d0f092303120f070e1306090c0c0302060a09150908 70
    0x900500203d882c030065041552000380d144c1c454110304903c200c80500000e00c003020390341c0c4120b8207000ca182c0c0c10440c1d85403441c1c0280d0340c1c00d0180a075500c681302c0d9280e420201c2800048485c05204900c4001d410303540350600ca05015001300c0b00d60744e0300c8148204082e000380344140200d8000c011410a148400186000041e05064085c08483c000d996100401450807000680181884c0d1715241071044028034024500c0310b001d002070048014054031000006000001000e0030903102614140c540c0c40e643c601d10b220220384000c445075034a00060103400301107021034024201d035000d1010003103110340506500d2000c981e40c050303080320700a000640ea000164502c02d000101114400011484c00c200c544030094007100081c4417004142c9002c001590340c0340b15000c15109100003800800040064840c08405416913004401c1e41a1511a030302003420300c964640303145203405401800d90764a96820040c05800d0506c820785146060030046003000100d4421224414011032000b52644400c58110 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 922793120 1250 922791870 922791887
    0x90e043306060c0f02010c110307060302090a0609030c030803091c0f0201060b1303020d0503090916031407090b0c070f0803040602060f1012030c15050103111e010e040f0908070201 79
    0x100420001919010008000c42044d40b40d06409081400041d0450b14240d074071540e4000b43e036601350160482c0014500c1d05034000d450b80e000121015040315031075050403110034219102c041e2440903d25030030130100d90312400858100c41510150345c00f40c0c1c4116042d0400b80403590410340014251208245c0455080c452130014080b04411036182000540c43d410a001c0c185c040a88600a2100414200325042003200c004400c00342ca06503e5142110580c03100940041e00c00717011070300713101c5e10402110003c031895100f59011b48600c02101d0800d20f80d02e0198100740c0005a03144648100800c9080c0c030703c1c2e0440018003105008640d5182003500c024109403029000c00030716241d4209102072841c25001c40015181e1a188a0000b806c2e0342c1802c88100c0d4880c580980000c0000d141c0502c03504480d00494142e034040d910300e60300600f41c9024414416444519800c3e100701c80010300d55150300c01c40c0d09070380380800188082111040042c05804848041f541103039503900005080d0110358000b0400c = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 922794370 1250 922793120 922793129
    0xd020a1a090a0f1d1b0d0603050d0503180c0108040308090a3c11010e06040f0e1e090d18090509060612030f0703180b0720060a090e043306 61
    0x4108681000c07000c05e074a54444a074007808000c0081105100e26015a000c1001107400808484e00d9641c5a440030780301c0d901c1560320310510405650018002500041c4902c80202c0694170801c0b00e5070303503480c03c03070b4200409040c1035030f540580ca0041e00854403610810000304c445041c0d229400101222103400c1030303100c0e4100d000f990521503c03540030450a5190b11002030007800d16214040424000401701d100d41e8102041c90340c0b40310341c04980d0048042c009440740c4442c43c51818482c10848084044440840c0d4840040d446207950080c9184140da4100300490000040c5c000c0ada124141d040c181c0d4801c642034100b60340b0020400100c4d107410104008510391800141d450301d21442024030701c0c0d1056040140a000508070a02c0014042004010042544160998443c0001c4c030b4444a58280d00d2132012041701c042400105c10318060382101ea40d014079490307014955192202044448100400a4600443c4040d04040804501140505042c4101310420380340303460b10355000c11903402c5e422 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 922795620 1250 922794370 922794419
    0x11040b0109121401021b070806071d040e10020d051005010c02010c0618060c0c050c040509030406081509040c0e0a0204064107020405060d020a1a090a0f 67
    0x204461003061075882c0b4079507004220005400160b4801c0341c0a80300b40042800854249981c0080302c500116019091700c09200035618192030300c00c01110020313081d490300c00420200e039050340744928065015071078178254082510075a25180805c1d604980000180e01a000d0300c4004011103a0015012403018000900b80b21904c280d45400081c440c00c80d40384010001d55a503501c000c910210300c50440d003c0c43d4444d0060080c15440100200846000d0300205d0300791180640c51519440d09019151150048030001c41c10b10785400001c5524000103401c0d107020310180b058800340340d1a211446840303240a1031114000313526240130050705120080040258900c184018000d6660000c19900045a069402032280b1140d001d80148176442e89030407100c0d5440344420107842c2020501418101d8002c8508119503541d1300b050254405400030001e50180f05c025040c8015803000721105104038490711000d007044c40d03501c0480c1401116410140c6000e032408030070801c0c0d025964850240414074403 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 922796870 1250 922795620 922795637
    0x20d1d01020c060f18100608010b040539040b0702100c2118080705120c0a09240f0321170703021c20030112030804020f0d11040b01 58
    0xc40141d03d4810291284c0f2010030490080750350002000a8504440340350380590300039a03405d031000d40c01002184100c482c1c650901d80311400e20301d42881054030500200d0300600d00b415900c1c0810421030003000c504030319100400320350051101c41034060005000e224107070582c0c0740018010170001100034041c01c000c000e9840301c18400280611003500010300c8402824081c01003038401603401d81c80c904070300341e0b007213050749400107660700300140301d40848406444408405003020b0383c95455a0b000b1561a400541400c3c0800030480d95502070044214540d02c54241341802e9480d0b82d00c9500c0c00c3d4088524485650300134400e0055500c9040d082884000a602585c4200503006d00303080c4104443c1102000300c1400a070010f8080c0d0120b07900d1241c401d40c04105070303221031801d00c014452a424010480f0b40004450002c18110013100d0694103010f061482401c0c9a82d41180c1c0745d80c0042c812600602c00080809550311100040748445200d81b444a0b411056481800200d42c20040821304000d90003 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 922798120 1250 922796870 922796887
    0x3060e240a0b04090207020d020603070207060e030a08190509030712060c030218101b1b0b0c120702030c1815040605010512180d17090615011d04020d1d0102 69
    0xd080320100c3e81044e5002d81c55240300d000043d15a0010803010750803840c00010010000da0200384101941c1d07040d10b81726402440b54003410380e00e41070481c009204003000c00511010312110700d001c00b6000100d2030050302e095040f5012a0a100340e40c1e100068404c3c003910100104951409540074480c042c1c07400b103041100f10807043e551016000034650040305001d207100e12480c401d8401800700001c88900d02040d541a291440d150002e4081c1c0303030160594160003189001020084400d2212043c00604101c1144a40d010b525440084100c8e418892042603540d03980360280c54102070311628006225a1a0072000d13084401c400e200c01d00d10580c03a2003020300c5030342c0c3c01c4415070b203403909508410b01403503440580300c041175656950460034511680c3d0046003080d9012a49914040541c03048d800540ca521001550340c86055070005500c0c510240942881e510030b0801c0ea032070f0f20244140c0b010300c09408000c00e040b17901c0303540d201041a460781c41c1a082e02c42c0c0340340b510040c4106c10000b1894001070 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 922799370 1250 922798120 922798139
    0x70608042a120203070302120a0515040b04290c0406030e010b060426010509010501030201171b030601020a0b010b0d0b01080105030a0605062403070807020606030c1003060e240a 78
    0x5000d602c600c107030003819220940d141040094061a800381031600c007152045203855a1f024848021180b500c10141c0d00d900d003c03a003407020380c051540800c4103000390725030b640d1b090360107510a0130101c14000c407800801780388501451902c0c024800100020340c0c89080010083c10349000c800001980d03818191484d41d144c64a40841c2d080b100e040100413041c0e450f080d00c40c0503da0305040105550340c00e010030f22801140640c07202d03040b28401d0702d444409407401442c80a1800c800c071500041030344203681d0a9500304400e00116031114052041c1c542c40e140c1030742c5003403c2c041c00b83c204600390742d004a213404503294a4803600b0300540090070f080141d07624003c00030b40e540d60140e5005042036116400301d8810b0320317055900003100f103031071034541c200010700806803606e03030011180c0000045240001c140700f240041965805410083c0c09030058140307490a008001c510140d90b181095507582c1e00050480c508008140034050080300e0180c507002c2508030200841c0c00c0c00c070061140450443c00c00010b000c = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 922800620 1250 922799370 922799453
    0x20d150c05040504060e090a110d080f09210307060c1e091a1206060c0a12031a0a050f1e04090b041a13151806051801051519030507060804 61
    0x1408440c9c84521004507001c901482c0c03c030a0010300e00e00c0041a002c2c0e105461901814411006850440c1500c0503840c000b9030030341d02c002e101c0d250758204202040100c0d00075001b28050001c4d0342000c16003010649815640420542c4039200019421002806501102120502c400f001f10440e907050076441803420400f42c00180c40d492184c0e00c002961348100d0703010b04c418001540c1020690840d0034200d100a0058004d40417a01da14200115009000d450100c0c060707016250098405e4206030a4507007804404c15900e5692880e0135500081d00715942d980780940307015117120302c0c61540141410700d040d1880d1071414450828100321305080001c00c2006c20841d03505140c00601912045000548901c01040e20941720309181c00048180d4090003065000180030366a40066500c3c0c11400e1342c0e00500700c0b141038488240d4001003d25200b05498401040041c043c0000c22011200c2c1d42c1e1b681741494007104d07901c41c41c00311341c1d0701c0100011b01c405102a0441d40100c2d0084009074a1400e00d45520020b = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 922801870 1250 922800620 922800623
    0x14100b010504060c151103070806010c0b0402040f090b2a04030302120304030306211e0b0c07080c01050901140106020106060807030c0302190504080f0304050d020d150c05040504060e090a 82
    0x610b03e140c1c3d006222044a989000e01000702c801c101b0085d110000300318581c0300715031748004104d0810228031254412a40c18106e5604040d86030103a49640d820800944500003055840301d80300c04801005c6041c00c2042030268903d216001082d10084408215415110042c4030f07803420107000400c0820b4011a200e8952003440540594a070303107600e800c4d001010560486210010705001c00c03103200300c51b4000308801a01072000d424100c47c00e0f0301421090308021200908818140010900c51140314002e819100d1288070641d041900355aa035a08640c8115201d2519a45a50380d000301540300c1e580883c05002148000d000d03450030040e019065500c05046a4200f41d5120700d001a0a03201e0790503116410100b14050b10324000810000740580c00c00d000d0941c2500511340006401c00c000801c42d41114009048140281e2140d0204040c9203210b00090384c40701c540c00202d5002d2a414855158400d08917203c40e9265410a0107000c2250303031507004080f00244080910a441d0800a00500c44a = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 922803120 1250 922801870 922801877
    0xc03030305070c050a050c1206070e061b060406092a03030e060d0905070e070f080a0f1e05010f090603020f09040201110d080a0b0603060114030702160314100b01050406 74
    0x2d0b00c50305411a00090300c00c00181080c026800c1c01c00804c800481d050240d81021102500c2c3e8000300c92806d61200c0c8141e442c403010032024000d0034420b003400005015042b41007040408032071107500c1000e041c90780840307040301da990341c4117100c4003013040c5c6849002c5080341d40e4500d05000d41115002d43d280701c40070300015060203d51042d08901d9a102e90881c1e11501140c001032100901c0e40c42d100d651007403940189804000311100090040b441602440d0740070301a651040c40c13944a00040c64000c02140d42922401c039140c0d009051002041d50100d010540e00784c0b80090031750f2400e000c06200b40c88540120030101e0802804001603900c0b02e50301454102c003200c2c1d0000c04d494604c0180d41180314980e50f81401d004081580d8400c50f00030441d5482152001c00a00480800307008000300e40c4001c640c818089100c7d0380f600995000c00c10050b547c007950a004032040e0071581400006400015441282e0100c0c50003500c089905080c025131706105105003060048035500400070f000d50190380580c9042 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 922804370 1250 922803120 922803131
    0x406031104050d03080415020c1209130618060503010501050114030a06241101111923071104060630050f01080d080403140a0509040f0501210c030303 66
    0x1410050007141d0007004000e0414541e0421890041c3c1244012035060314000041002d44a400704a03000303c0c2e800c840300708003a01c01081194010311858008642c4550003081c2d13018507401c410128401e0b0809002c0e034031148000b0500014641040d01c041d07402035802a41040300407c40c81e60030034200039646800c00902c6440e0341e0360704100c0c4005d061650101e204c4019a0710340424400081c0c01442188031a5a03884880500c1701002d01e00ba01c1d0441007140152904118405500d100010304901c01c8049140200e45400311001240d00b131103428980c400d0038038001601c4410050076281d4202c44070070613a020b01081d4a0302c4006010b0384040101c40083c0228243d04a200c413a02d5030392551244c0ca00101000242041508104124400d00450b00c243c800c0c900e046104c12301801c00b03207200d1743d89550f940c480e0900407007040076540c00240501060107004e10113000680d40f00d00513000d64443d803500014141d8503010046500100b21003c80c81c0d002800c104c0c0701d01250000351840242c03038060501248 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 922805620 1250 922804370 922804391
    0x3170a021903050702032e0b0f01050a0c0c0e16030b0109210507090e0d050f0d0f06030803070807020c01030c0c0f230c0103050a020a020a170c07300206040603 70
    0x142840f0f030a130002e40c14010015504000301329031050000c01080c40461816058000720004110f60098905c168480c014020f0403020750b2254004221108640ca401c0e00e00c2d14050361069840c04441e00444004900030302001850b444019460780400b10910f020700545c0d41400001c1d000f00c10764019441f075501080901e5040d1408520b40d520420b90100448103507a039121080001403259441c1200e090081b541c040841500c25030640d0784040800320741c1480c1c0220055041d00420158001c5000c25071640d10020102d141d22014602c2100642c5400758245044107000342031985416010341418a04415442041d52010b4510821680b2000c0030700c004086042004008415084c1d11001042da009084082140840c81003122a4285c0f414080758440d42c80150590080d000d0700720040e40000b003c140411804943c199202200350308943c540703001c000304681050101d410602030440b0580c82c5610108100c00d4640c54a140c2c808001070058059000542a00ca50f109000405032036261100 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 922806870 1250 922805620 922805627
    0x22050904030e0126090705101d0409060204080f0f1209060708090415090f06030b0a0b0a090513030810030803040308101d010302032b050d0b04020703020703170a021903 74
    0x1184c40010f009550040f5081e20012901c0b075800319010002030003038280014803800c0070b07510340c00b282c9256101c184070f078401c5688510a8658603986280c0c003c0d00c1d00d10100200b000361000f4005020354a02030005800752000052034844500990607040c0d10154031241c2d003e22044c180d03040c00c1c00441e0a142c1c0d950150501c00942d00070041c4440d401458454202500b400140b15001282d003042001d10981035904607140490b84540b03c080c1c982c008110008140d642582d0002d80d0b00e80340200446221919506030104888c0100e0f03149071460140c0c0490024140c0004215034413103c00c071079000d20641565031b1001c10780000362000b828800c03d00042241308514041c1d0300c1c05004807800703289a40c40360355440da8500c602880180d020780180c0c152000c50b101d51892040c19140900140e001e40b008040c0205c92079408030003072407502680c070000c41056660703d000800400d40030340d00501806003503041c8504041134007a50603090040c01c106020401e5008501040c2095055012440012607420143c = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 922808120 1250 922806870 922806887
    0x15140f01090b0402250506400609062301120803090a1e0c09150608090a020a0f0501020f03070b06010c1104020d060608010b0901090b030408041203020322050904030e01 74
    0x50014000082e0498610070085c40924980c1d406101140d1954443d400e216103000045e000386a90140d401c0c0044604068034201d001c2090202100100f8004042d20b0351003c0710b000800848100340ca41400403d86207405c1003904603400c0988042d103055240500004147d580b100000700010701c00b1001400c0e441080c860f2082054000340700c01030b040440342441c040c0c1c403820f1000f15002120f842000c901d403c45445601811002001c0403080c1da41400000c1c0d1303015400515a070f865101c1c090107400141c070b50103090002032144044043d029400c19001a081001016104560760300034401000456441c06070300743c10102c00e00744107011400a060640110b0000d1401542250000078101c1f10a60030341e005100301d989568548520307903240c403c1c20100340700359024030740054690b800500a1610b15001150018400c85d0700394906541c41c1e81c044181840e002003030b00035800221340d444102d07007034114102548403040c40000749241844002102c10394050300c080c0821005046070b0302d09034061141e0 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 922809370 1250 922808120 922808137
    0x609060b090c12100605030a15080d0314010941090f07080c03071e0305070b0a020c0603010e1602010f061215021827010315140f01090b0402 62
    0x1003a4035407034a4003415803282c2c03120004480300843c400c0000c81c03900000107441d055a991340d54861441d15a800180c014002e041120138001d14004d500090120302002090305042554402054400008820f0212854141e200c3c000c4036040c4080403030b44004044102d1000c003d055407004d0201208180010038074120381072450350610041c14864059000900705e14180342000444440c962101d22140d110080001c400340c00d5800f011b03040c01080e888070130000b803e824041c002030481e6600c3d1106890140c0035840740240d40d03800030791b23050041d5040c40b09800c5004281c824614552414810b070b036201d8001404003034510818240313141d20501c00c0d0044030003980d030440240980c03034803070904c460080a48201150610078074280c01c4482e1460340281c54001c2c03501d90311851300c207000300180000c02950540b076629860303200200c121140740c1c407082140a10b00542c0005940c0940070002301c100c0c1d21441081594012090801c80c002000c00d035010b054a203800c4003c82c5840350000414068001c0004 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 922810620 1250 922809370 922809379
    0x307170f070e04120c02130e0c03030403061e15120821090d08190b0105130f05330f0f0c06040204050c2d0708130612060509040609060b 60
    0x74001504049000d84034040c07405154826045241403109640f1584a2140250080b1220002c1491301200360f001c0e1081c400a482603a0040c0c400100003802d6901542040340d00b15075961065203000205a012042610740141c10049810f2944101c07040c450184a00f0f80c1013040c007080103041140020540c1d0780d07021409042c03601000720003c045080c441c211174101013403080d490380c952414401e4104500981d544900300490001346400f00000d008804407a9041c050104013984500c08a0072985008104154a10b010181010104140100c0d00905107c07400d5140090442b14030040d8910b9554440030742a00380d84030414014800703940501408d11150a001180c01e0211600200e84188241d20880741040139036610805103029020b19000c03416a00005444000081e00304544801d400b5080c921090804a043d529504a58400b9442d881c100801c00da08009103900000c1160658110420512100c1d0600c0042040c070400100050681a03c88911400b8803019501a5140b16000390 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 922811870 1250 922810620 922810633
    0x80912070c051e040b010318080a0c0b090102071b0308120612010e06010519260309091815010b0f030a0207120221030f010302040e1c121a0307170f 65
    0x3a030b0307001c1e072180455050007282041c1e61704005612034416020329883e440c0030180c09610b2034449a5154100c041c580f0240075001001e0400302e03901c0d9951900c100905070026a54008a00d00030040811b0082520804e6505140c103000140c1141c090310724070007a1213664203c0faa036140c00511402500c2c001b50425529000c0134036400c1ca008503002c2e058400a88200c03000070300e0400b04d407042440328400d24050840711820f80502494210003494103004840460b4205002d13503002551400c0144d80e80440c200444802c60104d00c0284081d2140940da9581e8004d0b0b903142250f101b005108403180304840c580b0001c0010750403140d56040d00c0c640e079088284c0303124241642d400a945c0340c101401a00e00c0c01a0704203121002400c1e40c003161b1240c00d11024840d043d901c3c0d035091001401c2800c1d0411154000d8002c80c0185003a900000c0c41d0006841c5c1e5425404002d0300051400c4525040303403005145610000e651450300d001440700b048ac1c6407000d48020703442040c0e014034100549508500340c80d000d20f5 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 922813120 1250 922811870 922811899
    0x60b0a0341060f0619231c0c3905250807030b15090903090f01050c0a170f0a02010609141605180a0b0a030c080912070c05 54
    0x20107050341d8103407007904051440d03115007041000040c0d03280199544000d080082c0210181d4001900c3d03d504014140740111034580e01c4034001c50700800c20300d000034440c081003007281c111884d1450360000d07089420070000343c8554200141403401a00072403605c100441119108400301030200b070481c4011013210f1442e05500c0c0340c49502c038541e4140301d010030821151a02401005002e80c5021141d1640c0244107961641c0d550000256008003103030311580300d803111443e4035200c4411161041681c030000d03650340d40300601040340a0f403040c4c2c2e050f030401c04148009000300c400010040c07a84d81c1c0002800038401034005050b003140c400c1005200002e80d000c42c188401d240c054102d8000d8500790340f0103105a800100080d6401a001c540941d0029807010800c0d03040d41c042d20080045491510381c0401543c0c207800818110221a449034000c410300242003646198140b040c051200e1700c82c54081502d05000315199903a6240c25144004483c00007468000c201c112601c00008040140ca19020b80c51725 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 922814370 1250 922813120 922813211
    0x140a0e150301020f090f0603070f030b01210f18050601170c0a03030e182403010e0a05060a05090f0a080a051b0307020118050307030f05151018060b0a03 67
    0x5c2c04494016906000c644145151003003e036071041a0b0756a0748001480c43d210120701078801c0c0300c0f5090500110070001c4421052608195104603c42580450105104000401100c25010351002107d03651003020002840c0415428110b5441c7d02501140301d240b108440d06202181c0d0b80715502008240d0004101138005210b000340c071900700c543d034a42d001e81d04507580e8910811540310840f546020511030709806150902c540025026000154050381d0901c05490907040d5903042d1010b43c001c00801c0b096103814014182d200d410040540b521134101c01100307079220084030009160301408912031428910560a0b1225040700f0407001d9482c1500d10000d64481e808114241c1c0020030703100b05804501700f04500311080b90742c06001400300c42d00e107441c1e04072010100c4100315410300444403c81c040202094105000740e20070610004120300e0442c0e042465186180c101c04180e04110381000768090010130744280341c01c01e00b000b142c0800890018a00f05800f012560425440d005111209100 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 922815620 1250 922814370 922814377
    0x41505040c030b01060c02060a260109140a1b050d0905030313030215060306070f05040e071806081005012105070f1d061b0f0304120606140a0e150301020f 68
    0x10694483d8598950384111180c40c043d0902a412200c20403054101a200380c00d107801071b01c411000300d40840018042d0040c000c0d420307409008403e4883c1c00c0496003421600d0303020340200f482c103020042d8801c10590384a040081201c24018448080b9440c00e1190040e041082c009900c501525035a1508005c07284004e680110300341d00620815040c1d4102031009041c0314050350703000b0001c0403642d40d02803089070f4241541220504010041c400091104820510b00f40580c12680b1030707000d0422042c00c101c0c6403540d0303a031100c010001c1240174055a1410740c100f41040d05e00a2170181c0613500c102c80b0520329843c8803051104958074180070486041d43c44800d00002400c0ca0385c400c00e2421300c1400c003016400705154078aa1200c400c10003d10890300741c08d850086250004160b4200742108140369055030000c2c1d009003200000880038030200502480780034054803054843c481c1c1440b00401141e607000550007000a000c03152808500d904410404006034050020029581d80400d210222003031340 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 922816870 1250 922815620 922815623
    0x190c020a110d020f0f0d08041d060a0e0a09060230060a050a0519030c080607090603020f09010e0301150b0d0b030a031202070c030209040605040c0801020a090e041505040c03 76
    0x41c100d0303803480145404580c040256400400450035280c00c1420000c0041003944204c0e80600092041c1001031a0480075000404025241340c42c884440211020949002000349101d031410441c10720043c034404a403660030407040007000682c6105450110000d104864826091103182d8000d1010402e2190720718643c0c007010b101001481d00c4100912820710154024103502001400081c8201d043c04100843e100704020200c25985aa039119070071405c5c11600f120482c0d8001c0c13400c000880b034000281c040240145d00d07045207401290340d081c0f08240a00c44505041004841c030000c00f030741e425007021081004802009242075036030b04103455203074401090450018100708540700b903841d000c60742111280d055290750411000107031940009500880040354814121400400942c035a461040e10881c482e04c4d002030036041c24144140300590300ea101c1d83d216030040200e4003106a2007518031045500c031383c4030102183c6842c40c14400c0f1590240c0c816840790315010821007400003440701d01003200e = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 922818120 1250 922816870 922816883
    0x140312012315070b0c070803040f05011a0a12031809021806070c0308030a0f020d0207060f0c0e120c04020d0c0f02030f090904030c0b04080d140609040308190c020a 72
    0x440e0a205010803680307982c070401c0c1141c10a11040c004070307030000406035001072010666171400010343c0e1514480d410581c0e083d11a07051134141403042110920400400c46107190143c200207144100141605901740140c04080c00900c20709820140038800c190f4500600200c03c0c00c08548920030003000350040c3c06484c2a281b88044506100d08001e0700711030f01c00e9040303810201803506540b100c1305075520251120300d001307a40f101680c101d0009440981500d0002c5400543d8171031081c00e1080c20b40303000c0b2610422103031400750807540541e003100456a14020a441c103000c03064100c0e09a03030a00e01160401c982150001410b2554443c3c10351111281203d42d48a403e6005040b0104a03501d02952071445040082042078400e20719000a0881d8020711a14041d884c0b200c2d150b542c45034200e0280d0b0115000030b40490350001c172170300a008404100c4030745a02c0810a180c020001030201d00050800b8043c4071415001c039042c504c12039001205030074200414400000d82c01070096645509080540c0c01 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 922819370 1250 922818120 922818179
    0x60c011a0f04020708040909140601030317061e0405060a03050a05030a031b081528080601090902010804020d02040608030f0a30051512010b0414060d14031201 70
    0x145824429254103070b4002c225a4181070070501c47c4001000b4841090344c0548401620f00f0501e40c0402032a07020314402d0b69a4020880c0d442100c3c200300744090411031003030b10311488070380d01540301100c2e9000c2c0e02012507000c10360741c80b240c02040d0909032035000a8a14040c90780c00c0340a00400000400d5031141d81da0702003140d100e0020300c0a008448a00c120000140b10401060780c1e403050071981090200c00800c0140305001e401c481400311002c0c041e620000c0b5402100400c480c201c20b002007801030107400402d02507004664002806500001c02c000d00c80c51b05050440c05541b0713503500c540098880b4404581c1c3d210348600d8100415000110917400040d0384403143d0703150044442e400306541e100041046101c2e400da40e9004080c2400a00d81c4100c06030740c1504c0040b503030728005030001914000c4000181c00002800340300540c1e41001020186801050601400b034440c9034000501703681080700088030700c1101d51544c1c114801c0c21401c2850845040001c194000324002c08401304c1c00a079040b100 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 922820620 1250 922819370 922819399
    0xa1421120408060f0717041a090d1202091810030f0812071809050a1514030715050708030c0706090803160804051c020708010e0616111209060c011a 65
    0xc3c42101218094001849402d81011180003400100d1f00540702d441600043c115441049140200c12035444000758070580c04650a1908a421007841030904001540390401d4070005c2007000c200403081c0c6907114001320020f0111180c20329044080c644c0000144000201420946141c3d0050100c4c0380b208901303003010402480c0680d6207144500324000b406003240d0324101c03418000b088000c010901d41078407448000030001c1c8014103e405040000364a0388803849103401d041c03602440303402100507012181c0300d82c040560403d00340d030745255000380b8240d603d41d1201c1048115000f5040c0082826007041d814004010300680079503c2558201d0140d80758945d8071104a50149082c0e9014007a41c00c000ea0745007290050560f4100302c0346450040f81c800c40da4400a003400c4070300b050210009500030006100141e8110024004c0072241c0e803403c10188009580b145845200e20b030b8040007a48400603480c43e142c2ca03490f003980ca0078003032400208922402d00f541c0700d8280042141d0076105960440c10800e = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 922821870 1250 922820620 922820641
    0x302070e090c150a1e0f2007140a0e0403031d030721200d0219150f0f051e0115200a1704050306060a142112040806 51
    0xb1030000c0040c20600400c030940c8150359a540039000a82c200301c80503003103240c00c0c140b440410301000700503030302c1501d1900001070007000c0c0340c0d00500c404101400d5281c542e00c60f5070000340002c1914640642c0590102e04400010002e090179444402d00d100c400041006240d00f50b8403164140304a400c2d0380d00c0524008041540380e20540310024070020703d50f0892001507030510064000454182070003404448014100741c1c0416401c3d04101e581e9000254101c0c1699040c081094a182260400800400c003940c0e40241d0302002040fa40183e0fa0703545520310036172201d40101000d1450060f08110508000703d841c4015811803090100303081d0100000100d80203540400b440e540b02035035038001303e0340080010461994010f420100603100d0f840c104800b15102c03455000311604c2000c9029a11441c4c5024541840d200411103440f40d10301100800201c20b042113801034403d400c540c103504803500421400c80922010481c3c0d04c9074401d002c10780615429000c014402c0d01e584030210340c0d442e07903480382c0c50 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 922823120 1250 922821870 922821883
    0x309011a0105031b0f0408010e1c02030f07380105011407080304020a1e090b180c1615020d05151c170304110f0904050601060f0c0f0302070e09 63
    0x36001032400c0000810f0503a0300c0c40d0f120442c401a072842ca15105420a5400250308960000180c82c2d642d9030690036218002c00c95034143c5500386e40340c900d044804000103501d03801110250701c6908800a24141004001c0c1c0f0240704265a28100e01d00040800c20304882900c103101828094a000d90004074581d0300030482e1895810115607014a49015aa90020182c01c00b8104981000130800003040740b2894103000c0780310140001c01056814a850fa1540688a111040a012318600f030140040490118905503000c030380403001998400007460300600501070030310f0161081d4010721915201c8900c039001401d4282d4004000c0c003644d11000011150024002e4411f5032209003011907070000b100303d00e280c0241c180504001848036020240c4004158803c580031205030305410300002440c40e21000286440000b590070740c90a2030a6a1481d82c0e03120180946e10a10065480740707100c50b8810146007208680c040494030030780300e1603d8041e5481601340288442c0d00d071010300107545424000340700d = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 922824370 1250 922823120 922823171
    0x3060e011a010c0503070b0403080f22140c09011e061407020111100905010203040209010824100b0d05010f0b0f0406050306010908030318010e010605030715020a0512030901 76
    0x81520a0710000196500d803800703001100d645c0011310a20020401d100360381d80c483c900a4030b44955a18050401c11418003000705501d4009042503856958a10104040190310361b20802c05400032080c18112032400c098282400c0d0b000700024004142c88100c4c450683c4540207250300210b030151101400d13140540b11b400040b00c2464240301c003002540c41580006814012041903680400040c910407064450008080d00c06a4000091004604155400c54010101040075090030142000400b81401089208201e208246000300303140c170803030ba54041c00600b9820b003a0390340c0340b50140121001d440d00348205180c03000c505400045050b0030104503414000a440010314040c103015055455401c060041410841d01344d00c0414a0802080158020000c40c1b50101401c2da0320200e8509440e1001c03200080c9904091040006480c00070b842800d0321502c441180f100c4185580480c50002000b0003d002849001c145104a4144100550150240300005d00007280d003081406400b0030219807 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 922825620 1250 922824370 922824401
    0x1103060901090b01051c062304110102060132010917010e0c030d080703110913090b010515070303020705010b04021909050901060f051b030c01020d0f05010501210912080103060e01 79
    0x20306c00c0020f40da90f2219a02100c940400e4058060204c42086540012101115000c2c00a404d100c02503030100039690051021050b0039440104d00071180189034071002046107014500301a028091313006044000103014200740e00c140c003110022601d40681559500000d180c01070a20022043c140801c07280104072249d00e5580782602c440400314004d0243c0d200080514400384074003c06075813000c2d050403400c59103d20124940e20389040c01d240340721040e801544034004030320344c4800c0300e0840c1d0180c54046030141001178803107515042540c00344c2100c009032640507100180b22a00b41006614401e20010f00da40c80c60a0a42c8800500600b50001c0c000c03840410401c030305100358144580002c081004110112446a50902c000245103801040d6a003026035004542d11720301c11100c0c451940c0c4c849a900080c045549408000b900a42110f0074030b200c0c1c88044c81c00c01c6441201c9820103c08c2c42c0c0d2055811561a540803002005443c0a0008036000c03801e003009058621014050102031140504 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 922826870 1250 922825620 922825669
    0x41202010c0507030b0a020a1e0e040908130f0f080105100e04030c02040908041e05090a020307090806100317070309140102150f01090b0d0c0504091103060901090b0105 74
    0x20010340d0400568601224140314440e004800154450407090150b1803c07040982c90310106a00030300451780c4801000c4103e80d0424111241c141d22508641d1008000c0d200010702d8002820300910502c104030b903080c249041408002180541c1c46e000c40201c9242209080440da10307203489500b45c43c020341c3d00043c03c400c1004c0900241da90842825041840f03070402a4090000b60b02080c00d5825000c4156210034010074200400000c044805c0c05000761846509640c5041c0800581c3c803400c0680f032810019400300c0080c05d074500400c80040031f0900c0c0d00c207e0f01a850042c0034045a2041400100c480c1d0601c0c41e4002c521484e080d083d03c640e80d40c59181c03c01c48904201112031485020601581180714280c0c6103107410b10305000395401018001d244120760341c18800c286040d50880090180600071907121080840d000310381b02c82c00d4031360448010405143d2400c01340c204456403030341c09a240c05440148180d10b001507200403070140c420000100183e070f80d542048803c141404400300121880c0 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 922828120 1250 922826870 922826873
    0xf0402040c0302190c0201031d100506191710020408030913020f04081b031f111209010b13050c1b0f06070809061f05040c09082508030412 61
    0x1d41141c404101c0910b001030414480c0e02c600481030120740c00760310210745c070306441800790b5a2500411842489c440c4041006d6000e240e06150385201d84200c0034011561170000c0b811503a00e5200b5550800c461203240f803d1140c0b10040401c080000c48071445140c41903003240088440703240240c40403a000b81c0080c50409090b034081c013107140b04101c4c080b00d406a0070401e02440d0403100700030b000504110070052580b00075007600b0030204d074400c5802500c01d17800301c0108403401c690b601d161000100d4408010800d0810f0801d415064050a4002114152204200400001c05605c0940c209a0446915803155401d10740101200c40641c0c98158a00c070030054a5009000806000d500000c0304044450f0503401080c031078180101524000000b406590500c408000100b2041d6040103140d4051004100e481d80f45086280440c420345016a880b0b850f583c130341318059086800201110303c25a001001c0e000032200240300da50b49100c040003031a1034045590f03003002080d070341038500256403a6843e00c01e9 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 922829370 1250 922828120 922828129
    0x1302011e0309140109050c0f06091905031b040c2c010e060c01140702010b0d020d05030c120406030f150905040203100204031a180d050c1203041b0e0f0402 68
    0x584081403540381c0c200380b00054a014901c249000d10040001002109441d10505240d040c001451050300f00d40216941c5998440844d008148211003030f510710072821784d039081260960340c0010343c036000f803113102e040c0d0401e0210034a81900d0200c408111195400c40309840303001d1898603098002c505080c1803c03c406440c52400424001414002e0029244000041841d07103d10707040780da07594445080c05c142c211400c41007900490030740000d11095648801080f400c116681d0081d2003100503516010520005001f12a49048210709946000036014080c404a80c800d115a00c00070740f4141010380740c41000d114130540c2a0480d00c1c024080d52901343c2d828040c01d80940140c1e8540547d01024440c051280f0003080214820b1a011001140c40e040603040904001e24a01c0e152802c08640f8203450008550a4400301070341c2000c1c3c0d1916a4920710702d03c0c21a08006141011030f000052105104142c80d010b400c003a83c400c41000e0503a1039002001c4403031002d542c0030010500ca000802c005160 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 922830620 1250 922829370 922829417
    0x3021b010516051c05210a1b020c090106050c10020a0509180103021905030d080c04050d0b1f080607121808031803160303150e0f0f130201 61
    0x8145011030512044481d1000030324a80b0030121529444182c50014044400f000b44150303061504042d8101000c20041c11307501da207100c4103501003510130000500e202802c0c2d031110a801d40c41d4040d031942e0f2901c824002e540c480e04100807506c00c00141c800002e800c2c1c4104203c60102ca150000b80444031482c0050304041e42010a440050080c00c4c0840282c50700d8210a11920010404415015514500500c003c644642c15191404042100140200d4078005881601d440587c13034180d44030b5480c40100c1207103019039000142d101041c0031b5030405202002c03034100d0103100e88041e41209045208002c1603405154410a0603c2e084000002c48140c000c200c1d0180082c00c221001c104514410740204289144210407076071135402105101c1854144820548001c500000071841c00d035052002c103980300b10b400001401c0ada1282c144826440d10110284020001c501552816082c00800030000390340032103240400022240024442d61010394001d6801501a125900009410100c02d0b01a00 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 922831870 1250 922830620 922830673
    0xb0922050a061506090f0b04154404050c120304091404060b030f0628051329010303050307030e060108160608010b250602180f010c0302 60
    0x101d80ca40c5011640d10301030340c40354004030449944075038100760001c0c0c216a510b4200c04481400380800348040382d400c40c112008e5800c5695901d000f881549400c0350094841a00e9140660400c1404110043d002c5c1800009010040b248a500e07401c1c82180910100c044a003c2d103164420481c1e24020b007080b0080b0f0358405c13009410359103001d46642c2c801055402e039070840f0950b10806803c100600506200e650710040e0204d0180006007178020a056940902400c2e089039078050b000f0301042610b41c880c1030f0941c05032030101440103140c03444103030303590024400e020740d9824941c40200c80600c40b100c1320300317000b413240f45c00c4000941d0854030111800e400042c080c07014141c2c2c4005290f1084c0040098a00928a00008000c400c10042d001d280c1c2c03085507071040c01400072000050000d800341905603a000440c200007015241038200c0f1b9150103c485140c0074251520020700c01d20303030150f0f107500800f1084041d56207040e00c80403440110382404c413400740a00143c200d0f1a031012070403219402281c440c07 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 922833120 1250 922831870 922831873
    0x50a0b010509210312130308010905190509210318061003080d062d080f2a100314010506070f02011107050604091a1903110a0b1605010b092205 63
    0x180b154401c0840c00764054074403035000d050400d06c0408069011010501600c403d0100344868103041a00c031181d00e40c0600482c503c1380d03e5034005200c4490410104461000c036607540d11040c00c204030402700b180e105581214117800011110383e030306880080d555000ba2202501408210310b1601c0344840745d007102544200e03103a11800000340180f07010041d0103241a00c001072507018020300000c0340010029502201040d08580784620a4040110f81e00d524038030000300783c0c99006c81e09908100710b545c80508140c1c1c00034145401101190380b580c090314046007080c428450690702e6104111150082540091401549041400055105a0f2074540041040c0111168a6110710001d80380390459040080b0140d03451081c1c00754800f1221403070540102c140c0d80c40c03003c40c40b242c10003072071110345002c080c114a80304107154800d501c1d0040705100421038040695250300c0c0015220845508801043c1c0f03641d801d081e0312000f0342c50100300f11070040c83e011500c0403402001c2d02c410941003c02000a0ba040d = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 922834370 1250 922833120 922833127
    0x1171302120f0d0e0a05010507020301020c0601170106080114070e0310060605070209060904110d1e0f030320032a1201030201020f0705011403090a060906050a0b0105092103 76
    0x141c81d20071004400911960250440620320301032945001c0304541c141e0304001c0110180c11503903d90100c00d40a90340280390039a0b580340e407400860f019215159035203401d03108100c0002100d00403c0f18088004c80a00000e00c00c140e61000d4041c266194081d101041c60503400210340b10600404c0c0b0003295141c041c2c02d0b94003403000040e4400c1140d405c0d0344075a010440026801d0118a002441c0782d074460300443d0401028249504c40010f48021800010300545100c042403003406030f11244019850798240006102090030b182c141c903881d80840003240071a0921105410382400c134507000c0c0038411004241d0b415655031448480c0840d8410041211801c1c80604154041d0342000084c100400c0c502c0301c001c0207501d5440020300e8040d100000401c00d410240c8140641e030782c001400701807010040c0c04662280c4402e04000d04050846200a085070320f0114401c0821080d500840c0c4210f001c040200303e02268240191018400c01c010607034000982640c40c0d030903d403100d03180506070f1200d03001c40e0b0a = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 922835620 1250 922834370 922834373
    0x90b0c04081e0f07030b06040b1e040c0c12020703140c090402151606050115140a030213050d0c030302010c09140d0501060509040f0c050d0218190603141b011713 71
    0x9029040d04291b4004c0090010006541458051170000764402d94403406840e0203130f03051080c4841c0c450451813180f5160700c0c0031a0030500c1245400701c1030b600b0203240c3e1020030f0034000183d60b0700c2c26880211a5a60942d030040100c0d03a0100e080160310a002e840c0c070b0041c0e9115801c020f400e20301401c2040803400c0c00d0001c40c0340c5090700743c09090b05512450001a103075051901b503d02c81444545c036001041135044126003102c070b00c50242c0f48600041e080c00350702ca980000740d140d0301d032200d90440c036040039100803850140078010340104200c901a800800010041030380403140504140a00c2e90f112041000c8030303040c0c1c184180d920818502a01c00010000c1e1903000040345450b0585099456031340c1c50850f40207014007a85505c006000c110798841c00002e043d0b0100c0c2c801508420250741c954a00e10004080307083d071190820700d5408401c0b0401c5090b071280303009803a81c102c0110030150742c0315a990885410286a0503440440e1f0140c691520408c03618014412070800180010500000c610b404070 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 922836870 1250 922835620 922835623
    0x1f080a091a0601050d1517030703021b040b04020c0d08160207050d380708040b010902030a0b030f010e0f12071709060a030b01022109041a060d090b0c04081e0f 70
    0x5180f440360002d510300c21b9203002c0000799203840e009203040440e001000700c180000d030009220b04c00c0707201c00c680c1d242d9110403200c0054010001303c503802d5003041c000541c0a00e880d101040c0c5412601017502c030798900d0b88a0301e64441e03400e02912410030260340301c001c1c1408185401e40325034100521600c01030f000d45c00c1d074010321141c8109407118008501a00308045000000d80082640d005841e0314000080e45880c1d160302c001c01c00180302e5811101e42c00400b01d401d1040c9908000cac4000006811128980340d00552140208100c695119003402256880c205908000c6141407510088030340d200e00701501a120210460564070040681c1e100c100007000c0d558465201415404200c0e480018445d182e140000e030810f95140b83d8a0080140b040764111001070100503074141ea0015140042c4241485e04095442010551201d40c0000d0105110215150a8221811952180c0e0542401e2b03110005010300c00c0c003c50007128116000443c2d0000e0501481180c941c13207010308000c40d91010b107107030f0800d07 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 922838120 1250 922836870 922836881
    0x18090c030c0e0115050304081b01060b18040912051b0d020102121303090308180409050309120d0801090c0e04050f0619030804120609021f080a091a0601050d 69
    0x100d0300007142030340420045440b01e58003401048501d074154940350309008020000d00c4020b0005205580100c2c102161801c02d04180040c5400c0400801c50b96485400362019900420000800c0410001240d10309051901681608991114161403e901c62044c01e0f1450b40200d490041940c1c00c001c00071a030203800b0407551084d624103400050340c0d114401419180c0c1180202400203414112141c20700180e406030040f000c99420104003600e030ba061481c400b000103852502c01e6030050a050343c1c0c1060000c04001032000c91821200c81da040c09802e0f003016200d030700c40711500c004170300640d00400590000344c0102c42c0303140f40e030706e003591860b419030001804440040e1210b00d40c111a07501048128145480c1c900c40708400c83d04108101455544d40040511070350044070b0040601500c00410041c00380c004048460f030060140c182c14a80c0300104203404c5010180300f00180c04c0380086081031203035114070001244c020001038105c41d1035141003120594094009810400200200240480d152051 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 922839370 1250 922838120 922838123
    0x1203090a020901060804120801080c01030c0210021b0d08040c09020c0a06020706090204140c1b0708030a0810050105040e0103110d2013060e01170c060a0f08130c18090c03 75
    0x30403a446c20a410144260303408644a1400c5c4101a8014054800001681409880c1c00d00c2c021410b010f104100b2402d00c103080000c90304150010841d0091101c00c005030700240b9154070119820700075041d40c01c80d81e00105032009058441103000c14070184840e41c0045c203401e020b1800f1614081e402d5600c0404aa01100050b2074455071500c00d10110300d060300412001c00101c0d040c18070345090051905e4094411409020420850002c0e0f4504800c4107001c1c02004280386026285c0300d0b5080e240142c80110700700c500d5100011002c0010507076602130000c0d00c05a84d0346a2064a150382075568801282c2840e1444552090342400654000344803c43c44400866501040320b200c0120442400b11001107109494000d50134083c080c0408110300b000141164500340d03071041040d1402403c10b0811004440240d003041000854070701d01c50704540081900d44060b982e40302590707078000d14114070240c580ca00511818201500300910f0401100040d0711050155002410005503990f0250340c00c032982c0f0 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 922840620 1250 922839370 922839377
    0x150c06022203021e09272b080705090105071b08031321060902060d1103060a14130b0109090203040c031a01290403150605031b031203090a02090106 65
    0x1c18411400d00d40709a020045503002a212501c4181e00082c500007001401d0a113905040c2186940e00ca1900140da0070201c3d0082c145e50003401c10001400f018403c0507001c940711100078119128241c4245511841116030ba900c080c06c0c001e000f0700449107039204c01c0d010307290100070103865208941c2c0e4808030b400801c0035100460340e07005c032000018108012a0b2200712035070501a40e004c1032000304403d51460641c0b2a200240100701d81c400101e0500403141c0c0764034100c1c9032020688201c03407580002e501510040354012804c0f030740c51080c10080c007103008425800189100d0314505401c00758001c001c4014050405c903044070740b5150030404076002210165603403007281d5020018000d0482848014440702603801c000d56041a40980e40c0c030748412541d00245101c10700c156441158a0140ca001d581e019600000d03044151f00024042c150030b005182c42401410035001200036000110f414010300a03000c1c100003900320003da44c5a4000406c011514040c1402c0c8a0050f40c5250400b03010780741e140c4 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 922841726 1106 922840620 922840687
    0x60403080903030415090f050d150507050c0d020102031006030513030806030a0606140108090d170a090b090d0e09040201050f071a0727150c0602 64
    0x2c0c0701c217400d00b01030401d60a80960210003981102c0c1044142240192030b4400c1100c2040c0000d001401c4500a103680107651201c0d0b0411507001d116401c09608040c0c142c82442d0400c207081410700010b0b580003040000000c03208104030302405003450308118a1070f080b465200100000c803000f90502441c203000620700e03a4100011000194400307000d221040c1e403000340c00c070b151142d203800c14003143c400400191004c90010341c9000b41c800b40d9407076180c0d400b9441005c09401502815606403141c50342e60000c04241c0d80b448050040001d6402841040580c45008020a4283d001c461041c0d442e84180300140c0e038001c0941d0805910010340c260780d03800610349803030f09400f80400c12000031071041c100503c0580291240d407100e5028500080700e4414140322000c01000d078004d00341703501000365000451a00c00c0349552415841007200515100803005070044901851314601305850000 = true := by decide +kernel

theorem cover : BRFrame.Cov 922661870 922841726 := by
  have h0 := BRFrame.cov_init 922661870
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 922661870 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 922661870 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 922661870 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 922661870 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 922661870 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 922661870 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 922661870 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 922661870 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 922661870 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 922661870 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 922661870 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 922661870 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 922661870 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 922661870 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 922661870 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 922661870 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 922661870 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 922661870 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 922661870 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 922661870 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 922661870 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 922661870 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 922661870 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 922661870 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 922661870 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 922661870 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 922661870 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 922661870 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 922661870 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 922661870 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 922661870 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 922661870 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 922661870 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 922661870 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 922661870 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 922661870 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 922661870 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 922661870 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 922661870 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 922661870 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 922661870 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 922661870 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 922661870 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 922661870 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 922661870 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 922661870 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 922661870 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 922661870 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 922661870 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 922661870 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 922661870 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 922661870 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 922661870 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 922661870 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 922661870 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 922661870 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 922661870 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 922661870 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 922661870 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 922661870 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 922661870 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 922661870 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 922661870 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 922661870 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 922661870 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 922661870 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 922661870 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 922661870 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 922661870 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 922661870 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 922661870 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 922661870 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 922661870 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 922661870 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 922661870 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 922661870 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 922661870 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 922661870 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 922661870 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 922661870 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 922661870 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 922661870 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 922661870 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 922661870 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 922661870 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 922661870 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 922661870 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 922661870 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 922661870 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 922661870 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 922661870 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 922661870 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 922661870 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 922661870 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 922661870 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 922661870 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 922661870 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 922661870 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 922661870 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 922661870 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 922661870 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 922661870 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 922661870 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 922661870 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 922661870 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 922661870 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 922661870 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 922661870 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 922661870 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 922661870 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 922661870 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 922661870 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 922661870 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 922661870 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 922661870 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 922661870 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 922661870 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 922661870 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 922661870 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 922661870 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 922661870 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 922661870 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 922661870 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 922661870 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 922661870 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 922661870 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 922661870 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 922661870 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 922661870 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 922661870 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 922661870 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 922661870 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 922661870 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 922661870 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 922661870 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 922661870 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 922661870 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 922661870 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 922661870 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 922661870 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 922661870 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 922661870 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 922661870 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 922661870 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 922661870 ≤ n) (h2 : n < 922841726) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
