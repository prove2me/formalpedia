-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_0299
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-13T19:03:12.999301+00:00
-- url     : https://prove2.me/submissions/3709114f-cd02-40c7-a731-81543c91b6fb

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 53597126 ≤ n < 53776982 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 53598376 1250 53597126 53597161
    0x60c030702011103011706011a030106050f12041a0a02070206180a03020307031104050c0301141002030c0d09150c030c0605041b061805091b130b0c06010e0a090c0509 73
    0x7100903544d0b50380d1038118020b100c0094401394001c0c0600400000c21315203030403542c1c03651140324440d5803543e4600507095030503500031400030302e080b9021722000c94000980c10034140704a006c0c1c1002ca030054007808442000085c01010310300028414001040582c8610003030b201c44459440c422140004442c0005002480c20340c0000c0d81803051303d2010003005840b040d0a003203020300f07640601107903c3c0c4040e55100d500007402280b0070b203202c03e6502c401516003841c3c20290b121090050b00c0c9400c00b04500b041c10000900103003000705200300b03c1080084005084203010b0b54007880c20b82ca055145541c014868600c1d00e4001e08155110804101402114645a610b10508004140c40503566201c09050003400a00340c02c2600100342d030000391070406500e520710400c0106031060704240c00071584159a00890590030503810302d0440801e0180b5504010190032312802c0c001c4c003807507240c186284c01d41c2d40c0051050031702c00e090030801c3d400500c1908414081d164201c0e03440d400d5a85c1c0246200e05841d00c03 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 53599626 1250 53598376 53598401
    0x7050607110a060203070302010b06070308040206030406060b042304020301030201140d060503061602061005010e012001020f040f080d090909060b03150a0b15070b060307090c020607090e09060c03070201 89
    0xb81c640c0010a035400200034200240300c0d8000341700d04c1d2000741c108407480c0100d050180100312504000b50051078008015540326104000c00900c40382c80c0c07038150a9540082c5c02c006480a00a030000c0c0211821030000305100001b00d801358070b1981161300090402c00e40e0744440360b80702ca0200300c8040312081740e002036002c2c100c00b50440d1b1144c58a070b20105601c0400b8410100540a41004a032080364017140f4034081c1d81e8180c5030b141c020000c5030011102c400c041840522204001c0308406210381c028002800080310241072181c40b10305125000707140c8a419404042179034024811640c1554002c014070040703174580100012081b0706420818050548005a2541805684842d16440a1030302da014010044150100308040102c02403244560b007035024559050300c18440c110018049076101d9038440b001405484c80c05588a6591095801ca962001c3c0940c202d1401c1002480d84940032a00070071960314240c0042c2000780c1c1450b21900f000d01030300c03840100000040c1c6164001d41000034075100 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 53600876 1250 53599626 53599639
    0x4020111030c100b030a031d03030702030a08090306070f093606080106050d110f03070f060503010e1b1e25060c0804031209030c02150c010e030c0705060711 69
    0x180342c2c07142a203e82901000c070450b030f4500740000515090010300b803140c480d490b072a40c1e2a00341e07128618601aa6101140a074540310402036840140c405004908910384a040d0b031580320004501058104040240b1007410041c0000074114603a40c81034002d81100c80618020038181c1c0441c0c0b03036003603040c400d2290030f011040082960040041903800b05084409070030081003e1603d800411003040030703d2201a054040303e003060f4150f071074140a682e000c481700a0484403843c0d5644003001e0800290b50000001c29000f000400c848800460300c9035103d05681e00700e00c0b0181c00800981454000e0701e1100c0841000342d40141213800f40601201e0a020002c0c02c500c600502200300b880d441341c07140030100c4500f03050800003102c0320300442049014661540303076852829407152400b070007001c11030810b50410240c09580790158488040d0b001010030032292041d598022280c2041c295200e14000f01c03450742c800c106404840d80301090740700c20f98100711400d41d6101614140310f441241b40d2900a1f51001 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 53602126 1250 53600876 53600887
    0x604050a35030907060e03070b0f070f03120507030c0f200303090106030c080604030e130209060f09032515030e0d0302090312070f0f03030f060f1a04030809090402011103 75
    0x201d000107540b10300703140c50880f04150b854420403540d514205102642641c0820300078031000880e40301418a4000c01c85c00c603410304080d85c540b103000311a15401907002c034000440e13043d0001410f0090329849041420305000b42e40c5e42e111f0061580d49014150000c110385680740169101c1c100601c00145446401100c2e00d0782002e02d00c403802040c0c02e10088811603600b4000050f10746001c00c0f41c510480c5c040d01c55035020f810040900034044803071844600c1c0c030f0340d0070018103942e075442c030020b410f000c0c400081841c0c90354901414146407961b20012050002c20078440c038540d905d81c03600c208041e1a65070301040e425414001040c0c001e450702500400f268003581030410b04055065000d004081011411200343c0d1506182c41019071060a6019101d11402c14211000c0741e503a030549080c4600c80c2c600016005000050541203854a0b0000000d0442c4a030041201d03a600882c40c09212a90600c6245024035650742c40714284618408240942c501200290541e0701130100000d45003504030a4a40e41c5 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 53603376 1250 53602126 53602223
    0x305090f090c04081005270a050703030507060605041406040b0409051f0b0108070e01051806180f03010209130b0d02130203060109060c05030901030915020f040905090604050a 77
    0x7600103000c0c4010600c201d5210960001480c050745014102078200503461401c0e200c10b244487e10b05112864942c80b590306040d0004000f0440800110301990f1100c0c0c40c0c0703400c1c2c6440c400359682ca911441c807490610114050381200f000c80c1076005041107400080b11003229010801070520001d01070607070f0041d001903094034503c40c4400151000c0c2840c041254000f01c05c010b460758002034544000040380c0310749110703195001c0c1d4010002800d20303565111420307054034009000d540c0701844001100005011404083c1801c042502042008500079402c2c0310005012a58452500b03d01c4107540b0745950100c5490307122064880203007500946135803181c401e40b4405801a5109132495030006841c084005070030323407040c041038010075442006946040702d6a0011006400c80d84010b5640c07581e90101c0180740c03801840244880611003c400ea1181d14208022044820003040c0051a402010030080018000b103441d50606511200c2100d80b8149803000755203c203102c0a50b049121020110341059 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 53604626 1250 53603376 53603401
    0x2041503030305220f060507180b070312020f07020402130504050f07020d0f0c3c0b0c040f0b030c30100e011a0c010606030203040c1509030305090f09 66
    0x1404c2e101110b40a0708080c0094100601d446036000e000000740c02104000070304180c110507006010307480e020000c00c200d00d032054002041c41e03004800c4500700043d0207007010f420480030b442450201100b14100000a9040c4040d03200e0440300921660340060105c01e18800090818060f1002070410070003841d0031017540c4880a03007501d411015104070800a00440d210304217504021105541c1c00c1c0d070204466850503010b0b00e880044140c00c910301e0007804200801001c4407005121a802508146006070521a010150140a02076004000c000501401089000f108110b030b501e01c00181d60b0f60390780c4003200e0709802100e0240101110080351002803038070200c80d075286002c010352010302d55110318050f821a06918480e0a040b06440e1004101c54036a18520001c422180c0b5006413900c200c5031007903030031078030750703821103004a40d010050100f400459003000c4090884007142000040040380003405901d8070344001000c20000041410f4251602080d1510300303030020f00300008604050742c81142 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 53605876 1250 53604626 53604631
    0x1103010f0e0a020a020a1101030b030a0501051e01030807080a12090f0c050906030703060b0117090106091b141e07030e030c03030405010903080c01060803040602010f0b0d12080402041503030305 85
    0x101c1c0380700c010104030303898224800c544012100d41c00030031480f003155807042c0f51102d901e1b12003810700daaa5440251540c80501c200e000c01881840002101c2c605184040c0c0101008030410311036150480040c800070b001c46d01290301041d00450115141c80780f4503401c482541c2c2191200300d515050803250010084c0c482c846480c114031442c041c5d00c4058555051161007001110b0b200d5040c0d012140400210300154040e0792501130616008100c0e01a010041d50034500564000c0c000380e645000030040316082d44550741400d20300380203220911114510041200841c1d851607607e041e80002c4010040c855101c2c180b141044800f030007502d0340160704003e0070900c049529a0f02901640c0601c116524000c0115416100142c442440d014116114441242c1201e03095901c44d44d40c613040130034441c0e4200054401854540e0020074000b020403032030000d032102c6401ca140233030b003004201c0d00000d00c4190070b40da0b41c0a0b245012520350f41c0300d00000303001d804040280b403c0e030300d0900030100074554580c10035407 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 53607126 1250 53605876 53605889
    0x4020322050c09130201080f040204020d140604060e0c04210f120201050c0408031c0e01060e01061107060503060103020a09030c0b0d0b060408120c0a020418200a05060901031103010f 80
    0x1441c3e50740300c00c240c041e01c03441018020300103010040041c05800f40c1491640d0040d0003e1b000608140340c3c00c0a020840e18460602510b90170f401080007403a141034010440078101c08526890542085001c203a8580280e01a0030714035800c140801a07441c80c2d0303a01c2c1260041e0030090176036840c140c604112401a208003400c1005500b4403000030b00300b00f80803085504030ba4844005600d01016403c446240d16100560f0801886e01c0b16241c01d8407160902500c0f0103040701040d1f03d101545049400361a0704104119150b1030f81000c0303801c10400b42c0050540f03502c5402800c000d83d50759441d030011140d40c850394100030181c000300071011a001039000081c0c015400500c004101241304d00c01000194042c0303104040300b0340d100030f0414561401c9003001d088584140030459080c240607500080c2651044011500919181010138091185112109009240000a02044805c9280411040f00c1c107406018040c5600088100e050f0744668043e2400303150816030700d511b035611840d200c5400c956601ca0030 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 53608376 1250 53607126 53607139
    0x306060806030a051905240603100504020904121211040611030f030406020f0d05040b160302120609090709060909060c0203040608010302090612060412090f050901030204020322050c 80
    0x607072905000580d901da040c1c102c001001c0f424145203140b45050f0000b2012502d034080d110404920350078a05800c02651000424804140350441c2030510b042c41ca036100c958802d080c60140000760700d03080c2c2000d400c2504a41410781c1e03e42814015141c3e0300d04a568920a07130300d032040003004401d1200291007a01d1003591031031408000a80c0341c942c0c9000741e017909006400d00300041000a581036004080d42228440030b20304000d081e2103240112081120142c0364030b8114010010070380745011046960fa40c1340d040450911002e02d0703030324070441801001d0601885020000c1158907000f040880e00500a0060a20000d5103c544580c0507100c1044129207690a00144401507400441524243c4480c1d58401080307038030315001c020701044060002600316048080d03904c200d4800f8000f1074421400b403601c481100401c0300d0002e260071b48680c000010b001e44c040082c0b00a03039035280365a0440303804942c0942c980d20380d110080744040140c8824680807240c2170540d41003150100300714089410482d00d9 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 53609626 1250 53608376 53608381
    0x305150a1b0210020a1107090207050c120d030c1202070f0b060d0503192c0108010b0c030d020702030c190608010801150501110a05010204090603020405010b09060f0c0c030601030303060608 83
    0x900d084184500750000240e009000d071210300c0d0403258064a080d00344c0b81340c0321280e5415500b0301414a40250410380b00160005070f100709100041040d80c218440544007000108540c0c0c0c00a600d541480c1c422b5002c1580303039644442c04510821182540c0d02c08e42a045545446d5890425100c82c100d40088541511050000d2100e180041e080022542c110010390f180107203000b443c80c0c1020320100e6500c10300c1540305a00f034882081100011256400011081c1440942400904580c1c016170001c0800f4004014541c0420004410745800541c82e520141e100c0e032a910000381071010454006820441ca69641581c1c0c2c480c9503840012034103151250601a41c0390140d441c01d031041e643c81d880408200700800c21455118410b80d040f50070000090354420302c901d030707581401d80c0e00c10b92007a0301a07900e40c28180300b9071409108407401424650b00e0280b504501d100803c241e0301400d208101745003004640515548414804018141c2005060350059a12460007030300a0005000c4c140c0081d070100b00 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 53610876 1250 53609626 53609651
    0x70c080c011514030c0d05120d02220f0b0d02040812040513060303020a03120f05180d1b08030c040f0618080606010210050711160303030e060f0606030703060305150a 73
    0x43ca100e0001028004d0108010300c0002e2001c21084600c00300d07021f22845100c07901e17010484000d4401250496809681c0b0a514a001b452540d55a00451075039042035008002c2c0045510640044402036107615880d0740070349a40c0b0000340155446003040e400307070014100d1490340a00060041d03d000b207805c01c49c516600308092040b00d0590000070003607441014250040789c0100b10091221428074808125810a5a95a001d030703070040c1c07031441c910707036240040720412182800030212803e0036141c680386c240303030302c0c544d0b040c1111401201a204140000110f807070200769800310381c00780403101d504000c2d16581c0c65005014580140902031800448000419a510042841402440140e00074003a04000340e01c080c00518029110350300b03100c0c0c1d501c194002c1510a0112440c01400340c1d11500c0700d1407031804c002c0c05803000303d101d41c1c110713402c92401c01101244c22908a50050f4050b00c800d03440340d4940900350014541a040075115104141403804044130800c0d0061042c07070034000520841c0e11030700 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 53612126 1250 53610876 53610899
    0x101d0303091903050d0813020409080c0118030206011d060402032e090b040b0117061f0206190501120f02130603110f03010501050616050106030b0403090f06020c060d05070c080c0115 80
    0x7d48a002c40a854000f4038054503240d0070020049014051031483d01d18074415030340c21142ca181040512100112280c800d0540601c6141e0060403e02081d4014200c00422081c16017401016244103075801f2010803003c03208424520101e020407855404403800c0e00500f2082c8207800d2140030388103403c1c141d026810342028001c6443c5d50406031210940740e55094024803504400804607900b10240700c207940a84a52448441e60100c0c82e50082d0499051007540741c541107020306815170180341448010001032484c40b40a0b151250030100d07081d204100303840000e0f03640441021000070a401d00c01d0100c203000701d60000c000403900803915481e940100303000389401e0395002d2099035030040042c0400c0d000740d52036101501006108000019201e51030350794409490005440c1a40000c611080602c094020b0ba00320030040c0c03401c0e00040140551400008074148104010440ca01e40c4800100d0885400303509a1520710350701c03200d02c5448010700b5803080d00074090074480c1c4c2d00f0403907490710001d00904441d = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 53613376 1250 53612126 53612131
    0x10209090c09040902031207030318050616050d050709080c01020706200f0a0308070813020918010b0306190b01050301051c020a0b0a0309020f101d0303091903050d08 73
    0x152121119903200c8501c100507400c000e40903600f10307442e0071008005a4060101c60001619184440c0d160402410018200c441c10f18440103001402d00e0920085007001810300c0e84841d480c80c1100c1051019202200c40d80a0490310a001c941010b0601c5032088d00704150006941c4607a0488514003003d4004903035031061840784401080e88543d40180c040903c201e90b00c1d0004810b1f04a82540803404d0345c0c43d2400c0080f1001b03800282410091080e01c0b5030003521940c01c009e0080440410030300e40e80019010000c041c03c1d01c594006014175464071000c0030340126000003c02410741f8494a418107042143c15070045000240a00d8a20300380041d602031000e9034180c0301e0150804081140105c1c104180c0742d10000103a81c0040c007030200045400103100248070448640d0f0700864841202c1c41400024403200048520642d01c542d580c050361a80046040c0403511208183c02c00340b500c00d0082404e51103101e9030b1a40200440d03042603c0c0c1c10520b0003410072031f4800c030115060404102811030b5825800d = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 53614626 1250 53613376 53613379
    0x8070c0c090e01020408070f0e06090103120c060603060507080118020c0705130605060403140607050304031e0e061b0f060613020901050d020d09050c01020c0a170c030102072003010209 81
    0x38000900684201da8400c004841e405400107140c80d889943c02c516280003030740314080502020707009000001c20851502e82050059a10104650550742d03403803d2921004460010000351405034018020300f038020b0001940c0001082100381401c4d0b000074940002401171281c803000904940030818454030807610720f03a45d2400a0000385042130200126030906a50705501704d83c55860214940e070f201d00040008600c00c02c1c402d110200345449040c18400000c09001c00d0004c28070401c000710340c00c000301181c0424092182000020340305030a80e4209070000245803c84c10100d04402c5031004411040c1070003144000322200d5103481d15010781e58035011034085400500c3c3c039140c4100704109401400d0781200504140c0d06000ca003552a000320b80090702d0900c00141c0346c504600500c40180451a80c1c03010070301c040c1c60102d0b807940108940e04210b01c01c00304005480070203001e03160700500042c548107100600a40d40c03500e1905205280414007045100e0120642c0791684c0580790510803244500750 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 53615876 1250 53614626 53614643
    0x6070503090a021302040e01150216060516020a15030207050105091618140406020405120d140d0e0d0302090a0b0304030914030a050a05030418020301080312041a0a050708070c 77
    0x82d581e0030b01c00f080c0f0030020201546a000e02020402900c3d45071710070f004c0c1c80c0b81d5002030025643d41100034034028102a01c20600040101c090240a17403040c101c545195040f001c01c04800400d01c08031314000380c0c59204402040d4400702c0703c10401d506800a003500382c050402408039444a04104d9298182000f051190f0713050301004001b201d00c100e540c505100c445540004507848032580b801003000003110126102540040c0a1080e407404000c01d49070110100d00410b6101d8031040c0c003070301c4100300c500401804000485c0c04503022249030825210743d180c00c000c0d14030390302c135804015000e90000100e0a100710703164000880c0102610080e2032189805a80d400d120703600c0d00e0071841c03039001d0b010300d8076416010710004000414410080056590700c11402144c0e034a29214403040854941c0e140c18640a00400041100c03c000100340d49a03c1c04002c1c0d0000c4a03111481c022284400d81b407885010140c1c09410003422040c03070780c0824441d04954854890315651304008407403403a05031000814000 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 53617126 1250 53615876 53615893
    0x50a050f01080403021603122006040212010f06030c0515160818060a0809160f03110109050d05010b0f0d02060a1404050301060b09041a01020a08030705040b16050607050309 76
    0x41c03240b4000b82d00180030340142e40b595008910000700e40308213504103803405184500d83c80c03a06130b03020340305152100015081540715044505201d4440c500038101a1052203d007100112455082d841402120101d03602000090b40d01d2902c0754100510b4032907541b04207500380343c907200c0401043c00c464084c11281c0100b0f80d0250035696a14030703034000e60005501c4561071510102c0d103440d0b107401400242d1007600d444030382e45800001745e80f4142622154441041d00f2035000c12901d8155004007013038030b9208003403d20455410340100d8079010268005540800c1c44005042402410760001c52122001e8a11000808000d028022200801440250080401c000344d0200d1480341141011510066419614069039080000e00350b800c0c40d00f0081c1104800110390486180c00c0c4603c000c0b00c110003d40040800c0e0040c00030f03465100220300a42014400000142018031403c1164040c045021125494a4100304107840b034902c100401c07140d0344925030200d0340190040098a2095a00d6001000d248 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 53618376 1250 53617126 53617129
    0x1060602030d0e03120106020a060c0306080a0201230a110610060914040603050d030614090708040305161502031f05030615031c080910140a0c11160906050a050f 71
    0x20045010403003021300041c0b02c5210440b003554540c1e0300030803150b8020710f986842814240d040783c01d00b03c65032080c1490000100402000450207544154090910b0170b50040d50b0600074800c98030080040c003403a2400911603460f1a040003208902c11000d100b01d59150b65420010705410180f4020800811038003d801c00c1100000c00c4510742e004006400440c00303968079690145040c00d4014850302080c1c641d8000d200800a210341d402d282401180e040c1010700701014041c04074240030f0301c09020000001085045142180300e2040e8075680300184915030241091004000d400543d62051414100c15145040c420200454401d80e40000c002e0041a26010051040c0f03c2144d00310541500503c243c5002080003810a404010300544035400685000404141884c20125401504e645481200340642d600881e51960010b0b400100040240c1c900b00182c1d8459101d101c2000c8600c01c0480c026484800c410304082100d00c00f682c2030001a403180c0c2003014052941c050039030001e080f011a000603 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 53619626 1250 53618376 53618381
    0xe0d0906020c22090209010e090c150306010f0215010902030115021f05090c0d050a0c24081b0a0306051306030321090f0302010501080d1b03140d06060905030f01060602030d 76
    0xc1d14030844001240004c640c082640040240c0c070004e6600b54440401c1124182440714000d452821150314640c81c604e07119003c02400041c0010703040001d00300004a01d80c0c020030600380c0391001c040c000402c640e510346802d030195000b4010b00c8184a040d00018003058000079940320342070030800c9034800345142001001c000f07010003400d0141501c668085214540c46920071f00701d40d140520080c00645820382802d504580e416401602c80410303224990170040031942c2d1401c402d01c090321f050b12481d00d0b80c4018a06031403600d03c185c0f1848100198000304150150700540c00c9600680d8040528940c03124000c0442c0e596100142c0803488040302140c0340d05401d107040519500c460000184100302d40c83e158030050504100300c0240c0e5454005125030f00e000c10070031100c09aa480d01045c0342500501180700700900c1280101800459654403031380b500c40005542910300050070810169582d401e000340140014422140079005004800003030385410b018101c01d8078141c3c2c0043d8a425014030b0007400 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 53620876 1250 53619626 53619679
    0xe1309030e0d03030e010b0625050c06030f0a11030108210c0304080322120609020102100203070c1106070c051c02040c0801170105040b0a0207020609040e0d0906020c 73
    0x300880401c44203401d41d00c502c1c041d0a5280203540024100400b21400703400c41d032008410750311a202c140400103400b05540b065001e0019200c0c442107022055282040c41c05c241d145d41e00b41c0c4000c01004000071a1411101c0301d100700341000742400108a014021021844280100012a04203100410b035075035098000701814451017903014601b02e000d20300e0740d0640c0c009401161041d000040c091404641c14402a6203200118242c0c00c40180707005138902c06c0300d01c4c001c17008102d1a1074183d85025a8002d000b4a4140000040159544d28020000800c071006031310701100c92071180745208241d8100380742503a2169902c06000d11520f8140805c000c0041ea01186460b000c417000003201780141c44030301840c0c01c09402030310b03842519418221040766001e030041000240360314040401001c20580c10800750030501d060700c01139070341529001003069842421450398001e800c16a0700d4130090302c0050390001c100725035908c03000056100c2c803080743c850411a011070352000b10060002d504001c0c1445460 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 53622126 1250 53620876 53620883
    0x3031314070306090b07020601080307020f031f0506040c0509060703030b060c01020a171f050f060409020304050321090604030f260601090b040e0411030a1a0a0c0e1309 74
    0x2110900300604803468141203820842c0c0b09a11400c0302010404030f070780599007090260000d451190706207001e0076560301540c1c030040d100340583c02e50b404282d20140a0702c40740d60400b40c42d818003c80c0c2101481c1c060f02c0300342e03071290045142010f1111039030311402c00e0b601d100400500107458002c0c02c1c0c1307007100502002d12030b040c3e00042c10446c64803044d40c2440140343c540025119951104c007605004c2136180d500070a003020603210440400160407407501104182c4d00111010301100007000c011403690300035500001c0100d0b10010600090000c004003900d0040b03402c4002491400d503030718014610000c150b401b50220360222000c01d001074041c82180219140d00e140484800c1d10500501141b65412040d80c0101030b201e40600005503401111100030344140c001d49890070f45010322650700305600520150088900320b1404007643c1d418044403411a8200d45100c0c0e0780401200c2d0102c0403001a01c3e0070b9250f81c90400c41b95609030190741d810110b006c0081c5071281594890301014080c1481a9086 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 53623376 1250 53622126 53622143
    0x40209030c030a2a08030a1103092106060402130e04020103020d020412020907080910050a0608070e01090e0616030209030f060c0c010f0b060a140403020a1d070c05030313 75
    0x1031a89403000c209101650313001e000401030350120724100d0389410b003500c0900c2000364400c081c103104d40c002c000111804250301d458054044e01c4580307545810741c041d02c10a13503440320308038147c10311a4028040014030b24942c48195402c1f03031506400c10049208200704e954030a80c01200400c1610030640b00e96078402d0040c100903140c401c20085440c1207a10680011604640c0341d03c0c90025410301100c81980f003c601d09120040d801d215640c903607500b4110a002d0710b55a101c0300050005510380e0000001428404e044485984c0c440038000368014090040b100500e04d09400d1960420300003c02e0340c05031152400504005071107400480203984440f100030703098418180c450103c9030303041000c00d00c200a03804c0764640782c04010380c0160a540c803542d0000340917800c0a00a1903560b5034081114406041802c4c0950100b00d000240305581c01a984065804101500300240030f40ca40188842900000fa99502140d9100c00d0140c41032403c0080242540d0310a100080c9a60030386000603401d05d0140080 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 53624626 1250 53623376 53623393
    0xa0f030e0604090e0f0105090613030c08030703020322020a0b0a1b0c05030c01080405060c0307090810060303030c0507050a0201140d050903070b1006120c030615020c03070906030f0204020903 84
    0xc240282d201e0340c80500202e982c0e0045a101c00c505101400007184540000d200506004010540c2d5210141c003003500499038070250010940984612910180d000459070746a191161010380203400c11039290780c00c2501d00c6000c00785200003140c0340b00c0d0107034000c000048050402c00d507000a50001d905030300502a170301100c00152031200344446e9109201e0f001d0702c440310341000300341400c04c4103d00a2030b041c0442042403000044001c20096070100b032203030b41135840351343d0a0011500d00303840303500c0b0300c465000e02680b410700f84850307410120950b40251400d010070030700c20b0f0f0116094440c0c6140076190790400240c0300010b6129440140003507038024130720b40c1001c8818001c10103e030010744842501d80e00002d0031a08100741d656280d544079001d40411710b0700703a152004c0508192410180c503030b5031070396500305805d003c0c0c007aa02c01405000a0004032142c40b0807807101940d11000590440e10030303c59280d0014003071100c4e01414060703c0d0711503030460b0014145c0d42070001030b40102c6000c960600480c2c04 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 53625876 1250 53624626 53624629
    0x912030f0a03020a0e1e040c0302040803070b090309120f0d08040b13170d0b040609110307030f1d0f1605010c02010302090604080a0b150d11060703020f070f06021e0a0f030e 76
    0xc0c14246d8030311540520340402001400c100403143c00a86281c1814018402044904404030644900c0d40e0440305440d000e648051403a800e43c810121a00d074810a001080900303c04002105c0c8020911078045a46114090b00f094500c01d204a400800c40106140040d0201006001010007184036182e09540c0c1109486490403a4000402140d10182d580f80424110b107403602480d401000e04140c02c201101c9501842c000c5407000a00403802d054a54006d00b48100e020340c42600900c2258003598604007902c1e0503a5100d03804980821510f02c104d0202c2030948809030004001c48405071a0361105041550041d0043e4200d68031481d482101403100150240042c40007043c40c501c0f03042c03002450319201c0c0900502c001c4140a05008a440f560b0490000d108001000100c000440b011074813400c20746012440d00b1107154280002d07000310fa80004160480301d1014095032801d0702900d1810704d0360504503a942d446071400c1000745e0f01c000e10b0040407403071040d00400c005000385410150304a0707520 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 53627126 1250 53625876 53625889
    0x111c0b0c0901020601140f01081b0a0f030f0b0a17010e0304060306051302090a0902030a021908060406060c02030312250f14070b01030b07030e01110912030f0a03020a0e 74
    0x3959903100c1040000c01500d40d40c0d0603c0a80d025018840303000d8100c0031010042408030840b4148681400b1004000c07402c0c00c08648030360012510104079041d60ba449410004045808080088000c07030b0418a088055811601840e808000c01500d803800081c81e2045026041a4140c0e000c176040d580c0d9900c96025140034401400a0121604e02180b11860001441100c90548003129442817051004101030340e100d00d046400c4403015080941c403900c0361406600244a400c201c0c5040342e01d2401182d4140c0d401201483c40b54000316410040107075122015650304041e07407030084d4580c02c02c02c200a43c07030400078200c1d50004284255040b080c601d00940c85c504402c800d50031404a640b84034a45030041c0d02c03107042c103418000f030900c082c144001d9503580c2c14a41c20601004283d1051140050703035103071095203c0030600582d04000c1c00100c01041c0f04100561007850700e180603000b00c034403420703044000108903402940c0c1100058038000300150210000e4100110510400980300c04400709641c401 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 53628376 1250 53627126 53627131
    0x20301090c02070b0301080303071d030307030e04060914160306030c0303080a23060d080c1b0907050a1202070201020c1203031e0106091403120f03010608010e04111c0b 74
    0x100014400741007a001a2034050b00d41c3c08414403a10400040c4401032002c0180c0341c21130b08900f400240f801012a02944031000c20880a0b0944008200441415401300c0b40c1040c030f902c140d404000340d54a691701c00c401d0380e91170100c4c40355030001032000c41c00180541c101178950943c5841e00291817500e03030787d854000000550054001030001c07014081100070301c0c13241c0d100b0800180d41c2003071441c804400d80c00d904880102114856400f000e404021710841804640e42c080e0303107a00741d07541c059814012441e0340200002c0b443c0030f6507040b80003805850007401100c040c40f40d640c88040c003800c0c0c500c000c58041d41c001d1030200d045008001c0c00100030344900f90440c050081c14805940c8a10386a2207200241c03883c40700e800910340198004004e0641c01c010600c098070b0500200242041c808004245804248250b003018682d0020300180d8003403074140514140c41541d590b070305250340e032080d1107400d04509543c09088079080355114491843c11f05d000b2034280c1c0c8160905072000c030081e01e078215048401c = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 53629626 1250 53628376 53628389
    0x4051005030621060702010e06060f09070c05030c0a05070510140c0a120c060c0c0206090105070507120c030507120b0a050a18030806010f020a050601031e0507060e490501020301 78
    0x104d4184403c1d80c0d0280150040464014001d19591502100280e0540000c0a600c0d0048801402142038144100d900800994016040b01d0b55103032012100350341d480b030400e801d5417603002d00500481d051030511800440b401d01940c031944c198003a00d0000009500469031000c2c1740c8103075180c100008181200c1440788000301d403501041c01c0c01e135084c035506480340d83d032650741085180841640141e841c202540e002c1c41081c13802c152034640600e48240703000b50310f422080003031003e00c801c0401c01082c000b01c141660311901c1a9004166101024500181ca16100624070b400b8040000d1807198030b540443d510421002011801003c03105001003040c4410205900042c5010104072040d600000c680c02c0e00b04503440280301c1102903440e801c2e140c4d00103000080c9a1002140b2084005008031a200680b17178001080c0c072103265851038080c2102600b4403c00d4000d40001d041c038040b101d40507a4510070706039088421760302c0104940321003010445004001c800300000c0d6000b507002c16003d201a40c0603019 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 53630876 1250 53629626 53629633
    0x10e0106030b010503030c0601031502090d080306030706050301080604030507020103090b180106140108180a021915080c070312200d0b030105040f063206010305060604051005030621 80
    0x96051040b85001c0c160007a0b400382d8800c12032148031210004000307044030341203120304182c5254084210040c0c8a0080d016500c0706007003002c0028410140000e500421003241101d60807a03980c4816142c60100b441494406d4108400045c0424004c4000389001c03441490300060035000b81d6500244a80103032048040901d0300410400c820100344200e801401c5445860380000901c0c40000740102c2006245a240600400365041c0041042200000182c1d005002c107030358404408080075411030074450b001030418031098003003007240280c241900400d00310703811600e071201e551001d4a01036a008560003550380d481940c074000c0c2d084400b42160081003110020350310400c8882080c00d071010b0742c3c03c1038842c0e490403040c440011103103081010443d900c504080748164002c031250b61010441e1000e0300c504001d035288603c1b04000c44841d1031107800c0980f02000f071516124248229030103503004140e08101c2e159901a400c5001e103014540c851001050001111119030b94100c2000c1c0c1c07102203000551 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 53632126 1250 53630876 53630879
    0x170d050702030712030b03030901030b0a0b03180607030603080a0f17091b03070608060d0309030501050411241b03090a0303050301060f030b060f1c06080c010e0a0f06030b12010e0106 80
    0x3642c601e0800f00352146410302040700301b50b000036141e210310401075050607540c80c0c07a1180c2da1908003a01004100356807601c0d40300d01d024041100f818010b0001004540522000650810300a100f100280c0750000001410010f940d00107480201c6044122002c1c0003042c0724069001285004640c410a44000540103103005900000c1241040c01c5080307200b03400541003488400c0d030146030f450740140c085810301e0b40700c086400c0603102c4064070342003d07185500b01401c0106008040c211a040a036040d0348802404552810140511400d55800c41035144100301d01e42111140c020000d480c2d0000c8000d4a1030003481030700103a41c0300f9843c0c0c421004510040300401060b0317000140c80071800c4040c182880701d42a840e002803124070614980b5015000042a015649502c5050108400c80e01e90000c108840e20b5000981d5602040c11020b40010070004501c0c045e4103090a2034401c170781200001410250130248103501511204403865000001881c041810382000d0003401103115100d4000103407103 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 53633376 1250 53632126 53632133
    0x201020c10090f081f20030c120105040b13050a15030506070e010206070912080904090c0905060d1a0408120414010b06070b07032c15090109050703170d0507020307 72
    0x4009601c0001079400c030030500050a00d0110502c0300740320091750700144201001094541c0c1c1d00c00750400005202001c010070502c3d005241c01099494050401103440f40c0c1e0340c8003040b042d10071900140350407004070014007000740e8083c0c01060300305a03141d1000c95851382e006001c031640c025540c8103403900d41c0f1010500040c0c0e0381150000c940c3d0b10080c801340415180c061009800c1e051305210300618a840c040161050100d901c060b80e494030b600030014080d101d09807d08142c5810580100c042c0940340001140c00d9283c11084840d106034414502d40e07040c5e141130880c3c1c00d1008001d001307480c81c131010414000d180300705000d400d200f41d01ca02d0815000315003880c0d0190031a2040e281d801d001d000c0820407200415400026164048098034010034005600c2c1b58080a40c40d10b03945664902c50451a01d00c650400825144a00c2210f44a502444c0c2d68003c01d040c00d075841d900f0060210b40003510144003040c1064041240107000c00e5425240403c5c04600706c0c201c440450b074840068101251761400c1 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 53634626 1250 53633376 53633399
    0xc030706180f080a02010f11130f12140c10090303020d02070f1e03150e0c19210c03030905010e1203040902070609020604091d06040812040201020c1009 67
    0x256480100001c80490469030380941c4031a80308400350810328041880040903200350003107a20003a0070368040c00240e00c540c3e0015071940041e050540a580d04e0100454425800081030044840041e100d50042c5115220529030700920f01c41111035003e00c410f60005515050002e0801443c2d5540b5a1005442c504000b0700781010165450215088001c0400507000f4510b5035800341c407281403101c1c1e203060003801102005d80d00c43d4001009810304051003280c0940d0b6521000e01150300304243c1b202c011007501005500865080400e1a80e5004007091207204840d0480f0311500002d056400c1c0903e55580b61403840c3d130080c0e40200c000600240080c0201c1d68401040c17001c0c00300541d81000c1601c143c00240e500c034020740c0500a1842e0340030500b501480206e4000481e442d4018041070b990719159242003004d41402d2a48085601d2081d081c41800140001d070144180d400c0410581810101d0a100c207800310090030680c1140700c2c4d103081004035662603003400501101511440540c5145c002c0c3c82c590b = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 53635876 1250 53634626 53634641
    0x4020f07050a0c180509030703120b090c0d110f040e060307030614060a060201050708070e0a0902210601091d06040f150302031002040815070c050f03040302040b0406060509040e01020903030c030706 87
    0x6205045c038084c84a960000401e650900d649402d00d5002103002c0907480004200300d90409520920000901c10004114002442003c410070014003e0303540000303011b4103a00c9008110036169034108010880f51108c00d030f4854001500030203a50714181e41ea00c49600f42d07519028056500f00c101400e0010170b00d00300a04000521190000340418a001d020280002c50000c040d1424801407665050043c1e5400003080050810b81004640354600781c1d4104d000d191603815981711812130040851100c0d806001d580d0704494444200141c41c0001035890880b01402900880e00b150321026103c1910019004043c400071004a01032806441c40c010145040d842c00d801c030023414410001448881c10200f01e18040740500c03081501c040e161a40200c482081525020704580140d04000444100100050003120b0082350700703200c0c0706400000c00c400c852140c401d28000c01c1041000020b00c1c24543c00490745400c000000600381000e20001c030341180d2000e03001c1c100c65000025440108138040c1324804 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 53637126 1250 53635876 53635919
    0xb0d060c08070801050d060b0a150507060b0102060105092404020a0206060301050a051b0304050f030a0f0206010905010e180c030d0e041505010903080705012301030b16090504020f07050a0c 83
    0x111654540070106c4d41c00c02064402411854840d26515810703116060324500a0281a8081c1100d040c0404010102c0d005120211182c5040145014481d880042c4d80d6040e1540140149034680f90304044031400d026000b00c40200c07402c003104462a6647e1171014040343c00441d0054102071620300201421603000402c582c08041ca06818840800348650180c2e400f0072088005603030b66211400d15518140c842240100340d4800050500705c00347d4840302188222042d6000c980407640c0380c05501003074650900405003148034450015803281201e841100500903400c0c02e89950181d99000300e810030700d100108001142d4025407038001030900c1d02c1510048081d0540c031485031410140000d00c1e00d803880c400980620b60100f640b805222084d800522000c00c042e51a0220a05990b1058690b400074441920301d4208400010b50101d00000640104a41d90381d411030b0050a0000700402900300900c0d15150f1841448440000356081042c100701c1030241250200035441c1100090045a801000a = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 53638376 1250 53637126 53637137
    0x1f0806070507030f2c010302040b04121412071217070306140a03050304140604080102030406060311060702100810030b010902040306060f060206040303091406040605090c100e060705010b0d060c0807 87
    0x40c110170000c1300c01c910310b103561507020103d10722203603004070068080c640111000220003c0d00003048140e01142440007403141e0340b021005444030704126150560412a5421030804104ad00c0000f500c1c0c804510641e911760414001c05100e17112401ca29403021140740c00801d0351090180b00112800490450a4400b26507903501c0c242507540d90307134a9029038454200100c011310074241c116507802c03040c0d802810240000315181c0c6494100880034000b6031005555074140f040c0d210443e410000c046451031034024161000c03242c880201100c2a500003490041126104000400011250188140200185000561200d066040c0b4000302e5401c0d512005407411504410440e440c0c020446580c05500340c05d00042246d0071b03091400c2c0da08130454070602d2038040d410802c000c0048d203a205c1405915000c045a0130048074105104040141c054900046540401712030326a2400b00d0080000b58400d00001c61440c1c9401d01140030307541c3d103641c12a916074543c602c500c43c0a5211490136407007119441e20 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 53639626 1250 53638376 53638397
    0x50d0302030d050601031803031509050103110f120a030809060105011e030b0f0603010603021201080d0507110f040606020604060e0105010e0a2003010b070213050f1f0806070507030f 80
    0x1079600d2080d40d0b84107180c580c030b407400650140e002c1c2d803120301c0f000320031006a203030b5240d140b4000b0020044800c5401201021080111762040148100c1d410380354844000504a0f5000707080049150001340103d80c010031941c40b490750b901c010700070f4151b021701ca51078208060a04843d00d9040100503046141007102081000ca003080941034401d00755007203400c00045894006001c0342283c030003190440c0c0c0041000000054041d4903a0081c400d880001c2c410804076625034000700d490744048041c2e080052018804c0e400802c04404118881c140300500303070f25441402c80b01007020380e06240d02203400758011000700024003000740508040a40e00700c1c0204031f65030508955110080000e090440344c1c5070341e60344441c40c840e50300b0344c41d42c07038100910030311500c943e91036031100c48a03807020008034000d40f034004602c110b4104c1401745500500c50a4032546040d80c0f25016440d06501c88504000e03035034804080055090310505c0028041c0b00d00d41c0c0ca0950312003c906000d04054a20241542080000c500 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 53640876 1250 53639626 53639633
    0x5090a050303010e07050c0106060e030607091a1305100503090d0e010807050306010215010b030105030f0627070b0711010801050108130308070905130207060e2107020409060f050403030501050d 85
    0xb00d0781034810b841101c10f00380e198100100c03010300402c2c0d0982c440b90310306940840c0c82038104044080514007181101d515644010f400c45012a00d0312811030a00307904501d070b00c140940c03540501101c1c1d2030140d071f00038020b40d1000002d400d00f0440a003440030075400010b02104030028000001d0b405100d041c00c40c80e005107900002e1503044000c00100c200300021012036a02da1090000c80204070703c820301e0380c02d00c2d40c403278600e4000d80d402803003014443d05c01c003060300030205804642c0758880d0b260b200e40a00750071182c0300c2001c0380a603801c1050402d23003d26180401e205109001030030070140a055810083d021040c005040894103801060500440a00300b04070050054070000415a0500d82030074242c65980080d00c010500f900720540c440e429034903c0c40d003030880e80c0c042c022050041409001c40d903407a0424a44072045003142e800549401d05899a0002060380100181803004d000000d0145403a00c81d40211928030101d103480b076441d8401c0c4003c0c5645805030707502500b005c6440b07118160103079030b = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 53642126 1250 53640876 53640883
    0xa0506120c0304060e0303090c0a050406180f06031b091503050c010e0105370509010210091a070c060e0106050d0318030f030203040305010c030b180a1d0c0405090a05 73
    0xc1c4003065010380000020100803040e040341c2100304510040703c0d03e034200a0380c0b13982c40e0455881c0141c050307a00301200180b60701c4c05000342d0044902c801d06600030104462621000b501c1c4078056000100c6d150500000081d416490300010406060044107034030f802e102d695002d0711141198203084129240703050011a502140c8080040d400342020b80ca20002000141d0310303402444842c94440c40400c0981c9401072015001500c00664040351800aa40c04202510070380661603074140140d000c10049040503c030b65122200060194900039607580440705d4a403048803048402c0000130303010048842c2000b0090140d03040f9444150000d0000038200f401090300241142c4000e8201b10310f0b450ac2484406003451094041d5801a80d003079926101e030305010f03680b54000e00c0b04581d10340c80c2805100c0310900c24071821078090070041451048070701c840304401c6290401b8081280d0590b4906119643c0800300c00c1c8070014045050240219040d0101040304031600207201519039000105040e00040c1d010 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 53643376 1250 53642126 53642131
    0x601082802010504090f1d0307050616020d050d060803030c0c0f0a030806040f021902150f070207030201051809090d11030301030b010e040312020309010b0901050f030a060f022101050a050612 84
    0x1680081c0424541110303801038908030b0148040000100100e22516034080010007019001cac0c01103412603128820820f001031810a142001608041c950304003040c4a90001c00d130340c01620b1b1021074040c0d00c8241d507a0459005680c5441c28400020784004003100520008408140346000781500f00900d48001d0302c1c00300b0062035035100f1030b91641c07a6640ca074001c0c1c3c140c94240031402d4001f0340120140402a6486190b80480210942c0a4000071070050b10000c080784070340c2442d80a412400e1440d801514290840b802c4400b00c1030944e10000101d40b40c400c44103114001010052283d100e07003490103000503040004401080c0c00400040c03010640710310340d4904640613510603035800c0d078480c1012070ba054000001044180e00000510044c4841501318500c1d081085801d10740c41e90762401040041440300040a4254100c0f28140d0085480c2d6401054607500d900009481d1103072075603560f0640d0348903050400310085000010300c0350781000100c010240070242c0781503141c012400e41950483d10300 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 53644626 1250 53643376 53643389
    0xe01030c0f050f0c0a06060608010e0405120f04080d0e011101200c010b06031302030d050a021005180f070305070905010f0b0304020102030d060b1c27020f030601082802010504 77
    0x160101520302104221010105104c081e21500d003036515000c4042c001c0c174800c01e00020000400852030b4403085501600030b41e07200e40107103002c40e00300b403c070f0031940c000e46441c0000100500001441a03000d00841b85250855540c8061451040001401c0240c01c1c4000d280140e00d00403886504001c481303a040302d003448450307060b07840e4506880e059000d810a09071075900006c020091000c1c0301604110242074900c00c90070344a000034003110403605401825180c2005038041c20000000703560651049800803460800d801d0b10b0001580560700e0b01c030340c142910f041d80c2d020031420000d20505100032009019108400d10403035140c400e41d88102880c0c7e000b41088810000007041c11a0300030001c48500d020100c800307111710742c0e441c1c81007402504030001c92242c803200504038076014281407146403904c200040381d001c0740b8090002d131040304980c0e080c0201c0c1c10094042040380030b1b036400c010140c000c048110003400c41a40303998031002146845803500311807407040414036005071780110944050720103 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 53645876 1250 53644626 53644637
    0x40c0207051503060a03051501030302011404081b01090503030c180a050f091e040c060e010e01051801030e060c0307020d0509010801170109060c0207050a120b0a0b010c061505010e01030c0f 83
    0xc41c08001317004a902548002c125100e00e03021801c004001e081868102d03030003600200305e103400328905000410821140201002c00400018288502449401f00780c90030341d400020b1a90320703650300c491866200740c41c101c2040750007099141000d42d0640d0345060038241540c0c03401074030f845c090218008018801680b0b01c902c1c1d01030b00088024401041c80844d0071031041011080341014202411000c0450140030300065001c03060b00000d501540d4400340600301a0354881c03625849180d480034080751541c44604140d10380611034826241040000c4c00b60301c0710381e40b159980c100800080d18081c000d82242c014400c0601c40c03000981e03000300b2000d04440707155941e814401182005140106424a40189039501e00034110712110350011f040019180300b81da00300d680d19168107090094500085009200300c0d01d84c800104000447c0e00100603400060400d160341510558892040d540800d010107215401e0040170001580d1019000030111400c0c01c0402c05a222043c004201139030b04a040400e201 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 53647126 1250 53645876 53645881
    0x108090f010c1715010c02010e060715021201080f0c090a0608060906090d020712060903053007030905061503030f0711040f1503030c0c0b0c01020306040c0207051503 73
    0x2001809480c2060005038000c00c6407010440001d400c40404400d2002c0d0001d0010018007200c8503e4426140000b05840d8105800e81a0340115450b41d00104200e4101000340700c003c0025285100e01409014010700158a502d03200e001141880c0050340b001e14a43c0c44100c1d0081110008039245482c00b2080d50700303c140755180d03a500c001605c566804440c03288988020480740201c00b092160140c000030381038030500206002c1c1241e40c0d840c1800341624000340d41d25600300285030340d8002e2111900c2400d01e1130810441d219002c0c23550703d2030b00b0006a03038104071061404180383c14400700d07400001c07070070b040040e040c494440f9544e03140c005000140b185103510310314500399410002d0303c0004845121882e03407034500d07251031891207a0943c40c050140d0304203059420b00c1403a070b00401100c04908016039141510310780b400c490b04851984181c600342c0155002003002c180303400c010040c0b031070f0580001d6620708204041c08100e030701c000b5600c0d045400c59102400982d41e07550100b01d8070520645056147d8 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 53648376 1250 53647126 53647141
    0x2060706051003020d03020a0507080f100906180c0303110a151a060a030c03050c030c0703050a030e03120103030216080709020901020c0d050c01080108060403080c0a0507021003061802040b03060108 87
    0x2c4455000650f000f81c04021000030194001140749506100e0803e441ca06990340190360b80d1b4001e01f480c10740c005e0700038403d2842440c905500c101103241c0107260218000114401e03000c0040c3c40305606440314001d005c001c1c01410340190083d5103030001b5600070040803000762242015846404080000c4d16100d500303008041d5841940311185040c002c2040380ea4a90610003d8004d10800303100c400400c1c101000200c0c400351000960b4440c00d0413802e05850809107942c1207890303600082c0000c0c24951b5035501104010010030140c0b5601c1101c09841e040c0b54152309010746000580f060702500d4040011303080c8207041011070230104071101d10f01e01507112031003440103030f080400d08001d881c1c200300c120300000c0502100003514071140c5002e0300d0f071204a0340c9549005403030760003c45014000c1018400890b60703100b070032001092003442da4600207091180c2c560010340c9074000c0b40710140000c0c0e00c0d22001c0c016002c1840c00c200c040114140114a003e20301010014280030051102c0c1c1446165400110710 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 53649626 1250 53648376 53648401
    0x51602040e10020309010b0102060408030f180a03020304030c0902130b03070306120503030406110a0c02090601090905150906031609020906071505010602060a0204060c0b040201031b05090411070206070605 90
    0x61196007040e0b4000480801d00207000350000ca452815640c24a4440c40c40703940041840e5024580014001e45580c2d9025411008120007403c802d0803040030140004803180d00340b05985040344254065551280303107080c01000d249258009002040c8100f100d810360090300c02907401120b200360301c0303592640d440304000c0d4000c0c911644141c20380217461f039a207020800b0110046110368403c5800700072580120300110224054100c4080119801c2c0c0c4040000d40b91003580351303522200500d00019041d85811914064840607915030030f110a0310840c03c450740c548100c00650107403056008248030203008550075440e101d1407262203002640007402d010710341c60b010100d503103281d00503050030b102c070907076240c40f5004000c24402c6200601809001c10040d072114002c030f40c209c1c1c18907620198514002d07114402080b5025000702e06042c0c2e1050701d0403c0003100c01c5e00a07092410398641c01d0b102c0794514184000e4924030030f1504416001001004010f84e260010f8449258002500041591303a07610503c45 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 53650876 1250 53649626 53649641
    0x1140d021012020406121b050337050414030c0a2006040815150607080a0201150603090201090f0b1903150308090f04060303090b09010306051207080d08010605160204 73
    0x3401030002802085d00c1e9004000303003100c4c004c4104104030a81a1001644051506c88400c03c00140c042000c192101400280c4904c1202c1d002c40006542c00c00307094000d922454641d1440125840310f041009201c01c82c0d004014002891019519142e200d0445d90703100d42800314014048142d054004900160141e066003c0c0c010181070b0701c3d5070383d03283e4090300e682c1c40800d5002c0142d0f01d400c00010348620031050b070b02d42400c440a800300d8200700a940d603500c11604003074000001c6650700c1d5001c051105140f07400400818a6407400140d03500180001004064990800d81030b480d0601000c00c54503400c0c20440e5041c500c1e0524070201483e82c000210302030021903800c208105860075000c4140000c1400424503c2006c507180d145001c0800e00b0312042e03d19030310001d030108a00c0b24042017141c10701c0d80280076200051400240c6241c4440000e400e000010442070300c641e10030385045c00b0303080041000a07251401c509110515600d0000014064070520100607012942c9400480854a070f035040700e032 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 53652126 1250 53650876 53650907
    0x10030e030d091e0c061d0406090b011d060a080403020f060f15040c021b060913020a030506010203250606080105090609070605130b07050a020909030a030501140d0210 73
    0xea4480c1401c0a80e806407503012010388401104081d140f03c980c80c60303050103d01503031080e2600c90042c94090280c132501c0d580b41c0700400607658020104919079072441580e001d004c0d6003000042c0c00f003201e40018a240e0102040d21036207007101c0c4691526540e244151b13280f402403883d1003115580d903442d04030300700341c50913048011902c12101440040350040c070000344100c0039400c52400d514242c07001c00099800710041a0701682250000c0b0190542d007050800e5800710142c6818908410341c004a000740003032502c90044241e0103e000441143c0c14015203402000c00d00c010741c20a002d8111141081742885070200c0e4071480600494200f05031a00300c1c000601d05107000300304c146025090191100c5040362808500d0103039030304c0442d503140200182d400282c032503485194111704200050310f450703229020a0740c980c4142200080169034140d6984d00c01e00d4035030b007c0d54440400b100040c3c00c2d00c006130047c6a12880120041015440d111446030250707030104d42c15950554210b5050341d200603c143ea42 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 53653376 1250 53652126 53652133
    0x21207050309032b11070503030c010b130501051305132003100e070504050a06050301020f0406110304060807081009050c04030b090303010e0112050f070e0910110910030e 75
    0x264140080840a8612040c041d0103940c4080041d00c1110001a0149000321000c2c031034080100c201d5215000c5003081d503202c28100c0e03040380c0d120000245140c000c0403400c2c002e41e44402c42140136080c0000413610b110f00c01c4605011950400000030303940c1200c0c9440b204110741d0341c0000392440b1411010003d0064111200c008101c0f41040c0c0c42c00702c21301130304520380284a900214100e503007861244008000982001c1c212080c142030400000e044050440e6840589a20020560780d0b800c0c401032600e04001c045450f526885d080c00030f40384407524081c0c514140c000303100800071517810000950380300803039242446099403140d21036004005140c216103200b610300f600b0410005040401042a030f405118024a16610520096a00e210900402d03450038001c0f40100310341d000c0c7c020220002031040d411350f2582030710582d40c1ca10705010303540311003031500c402d90034800310b0035090200c1107407102a41410311601540100d2113880e031040c0310065014031240c3c6204600720b8401d5008000925508003075 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 53654626 1250 53653376 53653387
    0x10306020909060f0a090b0303090a080d09080a0302030717070614010602011103091b03120c01060918050a140a05150403020d080f010302222f0906090f010212 70
    0x5600250845040c242c01a060500810007500d010b101c26040039000510803004d6600742950b100c0605058101542c00d44400d0110601a40e902d0301751070003410344400240f080c0400840c0007400c4224540c4031680301c3d00030134915400b2a03804001c0b514055007201280c500711074421400c6545100301c030382c0a0400b9141003065401c4200e507000f01812602e0a80c000d00281420f100404601e100581d9101c245c0d912100b10103099254444a0031aa114001c0685258040700c00c281c81c4103500840051080e83d5407104c040c040c0101611909a031180980080c4030641665a42d841da036032024480502104444110103526620400c00e00031419880b40581d01440d0800d0f40d0000750f08070964084004d80200d03640d229203c1d00c2207141030f2141c400c03030340c044131603074615020311041c2e903045000022409000c45901d40301d040240211f061038114052600c8620600c0c01c007520b001110b600694490540800c0840c49070744c1c8403c20389000440446201d0075000c00040181e01e0a0181c4442e00b80b0942c01145 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 53655876 1250 53654626 53654633
    0xa021813050106021b0a0e0405030c0a050703020306010b0c0c0904050106050307080120031e060d020a140306010806310b07050d0b010801031e0204110f0d060e040201020705010c030311030103 84
    0x4180e040310880e400b1920f40d280041d144514101414541701d81040140b00104044030000c1149900305008038243da1030003101f0380ca91400c040402d03805880c183d01030b800800c11803d08015080c01000101281424052524441c80c0c0790810407015506c0381c514000403800713104003980864004c0400400b100d16040d0f480d401c06018102c0034289a51504e5040300340c0c041144884c0860b071040c80c40c101000d810b50443e00140440090142a05400c402203603507402c0161a0300250401510203074181c01c0d44001c404e0304162500c481600a00102e81180d010710101111007900400030050707c0102060b04070301c0ca55402c080c1c41c941040648203038940400e00c5159900b240082c501a5900002445509900c0c0010f540040b8284001001c0b900101e2505007210801a06c4500c48c6100810110f214842120a8012074101064825001c1c3c800101d0b8001240c036446544001c08170010401094030303068002030740341c05051041c07605012510941d070f410180b20346c2c03005d800d125840c994140c0303c0d612402c = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 53657126 1250 53655876 53655881
    0x61b0106090e070509130b070e030610030b1504090c06081f08060105040209120604080a0e03010504080a260c0403020108090a02091801020d050a050609070f080a021813 74
    0x55104515440c11a011948014a004952003000315900808000d480c00c0d040c4105504024881034000301d0180c040c1d0300081400d00d0503809010240e4940c40385030309000815043c54400f80040b9800300d04510104001041150002c0d030145186c0c03403501000c5285401308024101940c1e00400b0340c02e0140d40403030000d4101c96441d008000c80411b00068580314065002c100290340940c0c4000e44c8a9801002646400c1e0001e0060f880068407900010741445052441c140094504882d42c0b500450b056690960144440d1083c0804a000b84140d0401d03444094283c03040031001c00030400c0011803403d4031070018810f10012195140301d1103c51921142d1b040380c82c0c005000c200c3c0012400c00100e0207104001440158944d00200040c47d9620381c0b1701a000380c0c011104520710155000d02201d0019001072140341e202e0303030490350007107050718000e41000840b620042003502030200700d03254002c1d440c0d80041c0140d8400c20318240140d0741e0303220300c456240e25482c004a42d80d105000340c1d00c1600d03455054 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 53658376 1250 53657126 53657167
    0x40302070e011a0f0702040c030504150207030c14010b0307060509040501090507020d0315050a0603050105100c0b0705090f0d030f030605150901080c0d02030c0301030c060212030402010e0a0506 85
    0x25425140d4858031a4840382821200703100d10341c01c91103003101e0400c240c1030b294020064245031101c0c040c50851198049007c0d00c80c0c0401c69008a555007040009111041c00c0b050a08110182c04600d04205136802410346072461101824500c000c1c074040221200075405040362040c0103048400959580d040141154030504005005505180c000039140c1902d001d03c40c0210317015005080700d45481c40c0102c00400f8038590424460413200300004e0030303441d140c024001a1030269000300c1c4541c100f6040c8074000202403148030070000c0e94807484021424100c201500b02005103005552000640300090312000c4881940c1e0f8485040400d1030b0425820070004415010607071024031443d90342d0720400c45500b58000162000101c1008042d0356584507425003940580441ca02c2800c118010a0540c101d03041116418100702000005006020007003031044014800352000b00b040545c04150300c40e0a00001e4002410f2012180003180c9942d00c400340700c0c024000c080c150079291242c4c8408141041c1c0170 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 53659626 1250 53658376 53658383
    0x6010303030c0207050901060c0f0b0112050f031602130209031c0f030603020f0607080d0e0f0f0106180c03020702031006170a080301030305030702030f070b0a061205070302151b0604 80
    0x38242e0700d00c00240040346101c01c86100401380381d00c5a10345a401e5902500c400350032219000b04500090001d010408442d0180c0148848a18140380358503120340780c0065866140c0d000d40c82804010502c3d03009440b0031010036810b5812109000c40c07140341c800603014a6070682d50601400081d120b5010400300f0502c100c4010f642d0b40303941d04e114030310280d045500c10b000194000100d00016400360401000800d2845c0c41090b820b0316190300c081440085814450f0f11200720b802031280006c8181d4100242840100c0110003004214500b41c41d143c2c0c11180f00190a011a880c2d001c80f1580382c3c02507050f900c0454000d81135510020f6121003c0008101d10701805029010044030b0886071500050600c02040d40019190f1450342140c40c1518141c20007405803086100421407007aa00148001034032015218401406150601ca041130382518119004454020030800420001c500001009400c803501900c04920b0b03402c0d940b1800e03903248100740c0803010340c0d81c0ca115205005040000c1d4039106500 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 53660876 1250 53659626 53659631
    0xb0a090509091005150a030819090602061302011e090e01060203040e0c03060a03080c01050a110702011d040605041103150603040201080109050c0405040c050d0f06050102030a0525050601030303 85
    0x46440c10481400c0c010748601c6510b5120319000c800310030403540480c0d080042100104c0809501c4000161411080d803c100d0b510800806c610b060540c00c4580a0101c00190406107055401c4c150001d40d00c140041040b007204000100c40000c0da4010f104404406a503062140d000c005c003484050003071409480703224035101c04000000360341c520200c01e031810307074050500c24211603c030f01000c25080d42026080a910805c2e500c40000080c0114000b400003000c03501c004681071500748800d074211841b0701098200c0b03180800100340184ea10410b070704105407409800d1680f5542450105000384841c0d00126085890001c2d4006000c540801652040c0703800400c000ca15544c1005000c11400300b87d078000d0100d80c0c00c10050255115030b40015030b10004000b01d05040030b942d04001001d455182d1030302e5012900c0002c0c41c40300011035000318508840c1d04402402541d15041c0000c0d03482c4560581501049400326a20012240845610340c0d0b24071440d015401044840c14038680301c04080c40224003107071 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 53662126 1250 53660876 53660879
    0x102060f0406091208060a0e070504060e0301060e09150f07090302061b01020a021b030307020d08070305070512040e100b0d02180d030806010f090f050112090f050c03101b030e030c01060b0a09 84
    0x8c420104980c4600c01c2c0783e0b51641031500e400c0040d1800b45e12a08a95890354841c1c8011441e036168402d0a8820702c00403005105504141d00c8507080080064a283c41c40d2004004000943d60010450b404403503054503500d940c0c2070209551124044500201e20095000042c105a103c0e03000819280f442181e0541e090080f840f101015a81d11030810300941003628a2181c50200b410b403005404460b0180c1080c1d8030341142a80e81c1030070505a0f010f0034850380da0124060004042c4424444d90104c0c03886001c0078600e040c40c40c007010b00d02030444401d4035280c001400e036080c070b001038092031040c0c50041c0498a112285140103000e2010443e019400610b180d00c0d44054039110b611980111007402508940e0307070742000300458961040300058603565403110700740d40011b08010407014640b4041c1d400f805400c40380a080504281c88030420309040c3d0301b0714810070600d507200f5040010400d007604002170035a4043c0b6445045000d03c0c041340404e03500c0c015000032062051001441c045c0100c0d602d02ca6480d = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 53663376 1250 53662126 53662139
    0x50a030221090d030c0312050c030f06010305040308040204180507170c1f030b0d0807050a060b0d021809070e01090c0807090b1206120f0f19020102060f0406091208060a 74
    0x28002c00b22150340c01048000404042030040040552250092410540c0700c10503a805c9801e40e001610710164540001003009a00c41504500c00d03040300007480d0034421414203032002000100b02810182c8107581d00da000c55808049407050405042e40b11003514000c60742d03001541d01c21038071010840c1c054000e000b1040050b2410784c582e02c0b000810201008602420000c044005000858a494202c80c10b4005003010400480c090302106108000070011030765180b50803800d070b9804821050181102b84074020050303807810800191030301e200440d003141e03540d5904140d291500d168445d4241c8000301c400800d16004e246c22121805260b03440740c0c0780319100c006003220519800e200343c4541030070500040d1b4000c0c00d15810306802000082805801e0490700c0392141c2416aa56100c0150380e0006400d604114030510603010020011400c5040d51280c580010f905e4882c0207100403822548440003908104880d030240800c1e9804c06000780c6401c004100107040d81205440281c4551220607000030003 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 53664626 1250 53663376 53663443
    0x506040b0d020109031203060b0324010e1e2809140106050a030218040c030204060909140105090a0905030304030e01110a05030904021803060c04030c080c03031b0307050a0302 77
    0x590681d603030f04e9134603e107845401d2070581a54240040544400c0c0000d0071070041d80145018420080503149070300980c40d1500c1c491102150101c0c18040c3e0105c149031240c2c0d4965101c05040f80c0603004000c4c41c1641c400091009940010780030403000250b0007900100340310f60086d029246204000c0251482e04071007544010b5091141c480094401c02502c441188290040d081581c4180c0301d243c03042040c4030006042d40c00c83d0b442031000a0707000c5020000154007418442c0280090002004181620005601030a9050160078001d602a84c0400d007050210b502c040110758006080e2a00c9040500d4014454110ba61080d0300240c5107034518111624081407503207030b05910000031807410f8003034418800a90048a090355010010204800e003070f8609008561103000c4400c103123507580e030642c5407139011b403a2140c2100669600074003002450792000421140c42e9459003844100d0002c19a80803840c502c66800000c1141c0160030f640c2c07080580005000c0360440d05c41c85002044000100d88908 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 53665876 1250 53664626 53664649
    0x6061809170a020a0210120c030207020307060c0302100216030e031c1b0c0308040f0b0f070201080411040c030f0b190308071a07020303010315020301080a02040b0a15030506040b 78
    0x808100c4010029807900000050044419a0060f1030059801d0740001c1c40c0003040707004400c003144401e0200e0b0b620090600c030396481003049040450030005181c010076540c0803103000d19002d00205404000516001304000103a14900321015540d519088035484a0f80e6030142048022071248000c5008501d8007240f6412a001c44213480c5125001502d012140c40c0c5580040f010380c01041380b0201c010841c0c0443c0c02c00554015241c55550f03d1a00d9140030700d11003c3d620104c55504d0500540801c9101403048451040e02407a0880580c0c44900303103290794841000950384e0061520070b044140380c1c0c154001c90301026845008100808200090204102100c0c010803403000c0d525000348009481c00c4090b0a52602584280c207000401d038070200d4900100341c4104015034000300c010004c00c00001004000038006101c20b40c00e651400c0e46850361505041d0f00203200d113840d00e00c840055200e40c111000146040c0592605100442c10080c00810080d510f640c01203081019056250900080480b03 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 53667126 1250 53665876 53665883
    0x50307090507270b0c07030b0606030105030d030b03010f0e0a1101030501050303070206182119080301051c0210030c030b030106080312090307020a03080d0e060702030301120206070b0406061809 85
    0x424108585140f0b40000c0c022000039401e940e0700711030109041c00f01e14083c0c01011615001882c01c40d0441c140040e0400009180c2c80c03003080200010300640d14082561507001d241307810041544022000000c0c0500b00402d02e03442036500d4038510f0640311100250500c0c060b40100c1c410021002200300440c190b074800d004403500740e84108400c0006040c00b80c000c2580c2218041503040c03488102000582c01c5943c01022080742611348441ca90b105418801504c0204c181d6400100b1094250b54000660105108803031180418003003010080f200b941070104c01e603500810011004101010243c0100701c000c0b124000039140100e03d5202d0b00741481030720140c3e1000030042d8104a0381480564180c20010001c4400740805c1c0030310801170300e6400d6040042d6205003007894a49510108500c11510107400364100e960100d4103020481d40c01104a0b130544004070000c09142e07035107001240840c400c00340020b059440540402c402d00c0f00c00d6100f0320540780300407002e040c800500750480080c1c8005c02d4028 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 53668376 1250 53667126 53667137
    0x7030f030302040612050603030a0e0a0b030a0605011b03090302040c051201030b090d030e060a0903091a07290f06010507080f030a060803070507060c061e090308010501180e0a0e0304030309050307090507 89
    0x401d48601410314803c88050080c00d040c041030301c0746600371841c0c04c240c0c0c98204150321240709105540c0c02082c60942100c40059910020200b80c5004008901c9840040c1c01a03036a101e24000080c17280c82150904c44008035805d0041d40d4a180c903c43c0143c00b116090814000d0301d0202e10164400c0c080e00724180a240004c02d1103480d82a101402880406406c40c2071000c0c8910010310440340030085191060860072031034a842c441d082c41c1140f0100700ea040880d520414601c01004a002074140d60407080f0090b2221240d0746940040c1c405201e80a0040c082d03c4020441d200e994a80000451140100910600041e9511038419549014031040102943c00c008800d11805201c0da0658601502075040440c50300c1c00c01c9042451000c0a24417030005a864051400502d500101c4e5640105802e18100e00307446130801c07002d00c00c0003141c050009120010b03000b284541d91a0380185920ba5a130006891b5125900e24029050440314401c06009014230b6030300082c07695440c42004d01c603040b55142c0 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 53669626 1250 53668376 53668387
    0x2040510091b080709051806031c03090521030a09030e19050f0604080d08060f0402031f050a0807050409050f01050108030715050708010302060c0109060213080c0a0312080907030f03030204061205060303 89
    0x4a00b01c46600030310a03905440f4146010142b010b41a6144000c68403a0b10005000b100700c0c20b0450400700b0441d20107200c03043c40a02c04400d0b40d241d10889a10207004080004d0400d00c500d804c030380f004021482c03542e00004440340c1283d1528401c0b181d0046a104880d914210016941402000e0140d4802c4074100c1e042800c1841303100c0d0081c4525076001c0030040c9204120709050700041e04a820503031308480b0307a0a1f4803030301d190801c504000e0400604011600c40006514103c441a40c4000f6030050b035000d16140d04d21001040010404045080c0da00c100a101a60b150104243e0382d8000c5a02035817542c2410804d050241050b10805004840591300c2100036070031131b000d11420303600c81004000b40f90360714443c0300042041803001d00388030400001c500006507d0154924a040c25003a4401d00c42c21a5900400000343c030780d490b000800d0b00318106100d20f503035140c000070300780f210660002c1d02200060b9002030802d5415030041003520004d0321184040030031022508101c0d101261000d0305581308100 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 53670876 1250 53669626 53669659
    0x33030601030f110907050306040b0d080306040c0504030b07020606030d08010e06060901021f05071211090d020307090203070f0306080d080f0901020c0f010207020a12080702040510091b08070905 85
    0x4108002c42c0074440b15088924070002060481c1400c50ba03403400103c010082c06000c0c5803500584241d564100e5040d0319400181c0c80d040b07110321014080310303c91550f030b1a40240003070088060702c0040d40c1000d1508000d203044034000c0c1d1125411074440f4841e0140c803081c0804207000700842c505940b0008a00304155a54405000e040d034081c511b450b040d8401d1028501d2030078070400314038042c11070865000c42c0038104524003a0003040c0001010b00d402d4284000f085440c08004291004100100c6605401da03407c0c4c00424240f10641c5c01c28544e460002040000440e040300c48400145416038003007002079512841151600640c03003106c40003441034000306600207421000647c10141c01c0d0001403500c7d0301552810700d00600c003280c404040c5d401103105c00075842e0044400d0010207207102540f4481d0025603c034020b0344a07100c40244115541e801060310b50401c450580040c0690300c0040040c1c941040340b064090b0000c104620000320441d000803090361145d88030f60308958001e4000320403a02c0090 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 53672126 1250 53670876 53670893
    0x5060402010f12050a1b0f05090d020414070305040b0a0207020306040201080a0609150f0f0803040603020d02070b04030305040506070516021e0603010b0a11030918040510053303060103 81
    0x110080411840b0445807403d03041d107104c2e950103007401c0f840000e00444018001e01e0420003885404042c451a0b019400c00c203030f000f6048600c0c00c4801c4617500c42c255107030b10005001b410105480785020105500708505d55030107901c02e03809a4064030300a5616510701152409030b2141c104000d40640110300480c1c0154001d400c0d45801030b031041320204480d612030820398100d41503000c60181031071819408101d01300c425070368100509040c0c01c20103034150806183e103690b40300e13502c500310806034001402c988d0600240e0541c0c11140d0312500082c054241410024050202960305036403c1c024200410040c50258045416021100403149100d010503004c1100c400f00380d181c0b019180b008103607500100c1d07a58030019030203400044517440c0c0384c081ca42001020a0404604035a00c1d0384108540700060b0744004403815411a01039000c0102d5440d807038610700709080785078a1a50f081c1428107208e07082c41d0401c00e139500310590900e159044c80000b005810340354054aa1160903410800043c400b1a1000 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 53673376 1250 53672126 53672147
    0x1030203060a050301020a200102040e0c0a03060305152d0105040b03010e0303011d0108070b0405040207080d06030c05030c060304020d120c0f08030f06030307020a0b09030a06060803250506040201 86
    0xc002e40941c40d030720800300342640c0c030a01c42140011920700610800c8915070100068080d0800021401c081c1803014070201c4800103000c2c107100304004203616070785d24820b400440265901c1020340c0c40300520a4070b840301400050354a0b0844a00e041014050f00308800200c101911601d080900d80b64a0300e000c0c00b0090600c0003c1c150035548810309406d00c01400c000a50007001810034181d4280c0e001d010300405450180c014102c0c0c0d810012007040648401d9050320b040e101d00300c400594804003071030822100d01c81c1c43c2145540508165002060249800c040c504449050302560504843c0a04000c000e220441e0002d52210f00e0a15070700c086120105403650588842c00c01c14001401515420244c41c6082e00c101c403d0080042080f40c4015405005604a50190000c50800a007540018200442170154000e10134003c42c260802d50740420400810a030814410003042d5101e03035240d03860368400408241680000e90180001005641e46940d1007078000f405081140c60b141d00448406100 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 53674626 1250 53673376 53673379
    0xf01060f140c070305031c06080307080301031101030608160303021b060313030e0607080403120c110f0f1801090606090612020c0a0c080f0d021207020d0519050304170a020d020103020306 82
    0xf103940101c00030720100000d08001015100c42010407c0e001050010350b820341d00002c0a0350014092b0900203010081640c2c10350340d0025551888500400c0100c0082003181d000552510804150740700198203414150142c2e800b907401d641810f651400c41d1016610b140da43e09801074010000605080ca200000304070301c601c24a041c0418022007400074a894000d0390b400d840340f41001804004008155400003801d44044c00c1900e050101c644951104081c1400b05030701850350b8980030102c0b6078910f441040c6070000103004040d044d45c1c0b4015072005072000d004080d1051701d02840400c8042c0241420b0048440744d603100300d500349501c1c0074030002e50448210304c51944140c00c82d11300040c41d01315000018110074001800a8410031150707624008107811424151b40180c10f2500244d51541c00b242d4800f0703016507484087d141a072803c1890002c900701c1c42c002e0444003409942c100000400100221030240289803078500c2c50703919803510350f940148000c0d48209440c80c0140154001d4010b5940f0810 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 53675876 1250 53674626 53674633
    0x20915011b0606030614071209030905060702190b090f0d08030c07050102090a140301050604090b0c16060219020607081608130c0602100609020c070e1312080f01060f140c 75
    0x13038a9451074155544070194040c098401020000700b240d00c0b4081c00c0350701054200074800821107441c064410000ca02485000d4040003a100041d515610a800c0030038a1a100070b048003681d07000039410301d4200403491407145800d82460b042500d458194408110f402c503060742e00c3d649507400200000d034070002084419540900240f04556280e1141c2401004070b00300410840340d100003018211640202800c0c881c0e07290204280100d45d00428099124014400b00e9035545e025041000c0e1a501e403000c014642800012040b08501303602e01d2803407035508580c0031600c440d1902281030310003a10445080b121410502411140c5901c1203080c00c0d00185d00c40c0c00d081c1c030180c0c01e03200c21200b19255002600540e10404042070010340034810034000704000c2c001181040c60700d0385219100e03032151080b414a40101008103104158101e184000c4591080c94814000d50580001e007001504841b440c9682da1604000641c40c0d005015035202c920442e50350100d0344200303403030140c059005884070300e000d8031 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 53677126 1250 53675876 53675879
    0x50d0c080f03031006080f0a0b010504091109031501061d0d080c0105090d020c01020c06070602040506070b0106030b09040302030712090506121512060109020703170a09020915011b0606 81
    0x3103060002640080000001c1c41d52803800d5405629408000d500c00300030480c02e0002c01004032454807040c0e4128101940c0421046581030041307030140559005440b0803071070011840d059484150041084213015000c0d118541020088074a590342d00f449000d001c44c1c5900080010340c03c0482e142d0b042d00308001c0c1504440669900d0f91090307a0414107510006039540c206101800d1300400249841074040c0c40113007983d11041d00001e44503401000c03218002d000c0454581c0410055806903000f9001c0500352300e4a5920a040c86240d902007841004042450b03d065450182440c0b04075a22032a010303001185003115503a6000300002f40380c0320072400c01012900101d560385d5048001e111401010b800d00d0200e05008444e41614009007500a11800d940e1002210100e0013017102411a004e030341d40161500441c1c10f0503030314090304940b00000541c2e800100321040d80340d580a90406402030701c16104aa441d480d401048041001c401c03030108035901603008000d03072800080450b00c0e01c2510003050b4079 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 53678376 1250 53677126 53677139
    0x402040207120f170105030307080309150408071205030f0c0702120105070c020f0a03240f3314040905030903030301120b0906070f0e040b03070902030a060b13050d0c 73
    0x2d41502a02c1e000142c0003004140c4001e5000e00c0411124000c80c02c0e00c0040d500d0319001a94138450038a008280034404000100d007880f040c000f07403889c00700e1030300c04000900d0989040d580c1a400305c002214024502c590700040d45204006032485a491442089521786680038000c00681141d01e04070380c030494020740b0340407a603000e00800c0d001c0c070358544601001c10241d104210080c1c0c004000c5901482c42c040301000407c1c9104001d80c0451500c1e80340810703d1070480300c00320240c1441151201c0301030418810740541c00310841026480c1c9070314001e0b000c544850300311701c0074803101902c1481041d1a00840880705441c4c40d80c000e04085108004036440d0448031000b20741103030000d90010300c0002844081409001c040c92005c1ea00000700005454149850349000e4880314508002c0001c00011100207201c60300c6030f610210f04180014100c2d511541e0b240c00b200d0107503100700e5a009501c0d00305800041c0c0740d0182001c0e51006012880c9084481742820103115030030503805800c1e148440300e10400640e0 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 53679626 1250 53678376 53678393
    0x60c070501150b04050f061c020307090807030821070c020103051302040516110d020303040611070b1006030e0c030a0204050c070b01030b241c21051309020c0607080402040207 77
    0x81038107003100c0f0744403480d05040200502031051b540f030085404004801381aa00224280b1064410090050f06c94642032412280315800f900142030031310450001005000c072000103001e0300000c01d04070201c6241410320701c5058020640d210000318224000304e800560182d00425401815503150300300f0050560001429103c0c02da42003c03a44142294a001c440e0707200007551583ca01c904010036641882c0d20000703590b84401000549500d07503807187c20014200341c1003181c0701103810280315801402e01591200383d140b81e81c132500d80860f02e4251800a030000110b2030340c0003118000e02600042103e9028800900401040d1030511801003054100103a0544e4455001e50301500b4510614030b4455092001c1c800c030100c0e40044103004542c2c0a007141d807414202944010840b00080c4c01d2a954038013546a00d200c1c00264000c02c550103545015294007401410201d240c40351a142f405942c0c0c0d40a00480c40f0b81314400d0155004000003400660140481540043c40500014544402a202c1111 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 53680876 1250 53679626 53679629
    0x110c07060903050706030209131104030204020f0903010506011806030506031c0c0c050609090c0a0c080408012c0c0d0305040f06080103020915030c010f030e0a03020a120908060c07050115 82
    0x807900c400001d10900c0307010022840544800d08086242000000003d1400c1d0610301d080d02440f07444051000c021410304040d200150380c0a4029519031440e41107005194000140144c040e61030400040d025610071403502c3d4820440c2d1000340403442c18440d085000d400d000f480d6070b825200d4101c01d16422000ea1903030603050800740d69148021801ca01c1e001584404030752040e4030400051041c0085a5076200c600c54100c3c02500000c0d07642d580b0b440d800d03074050300e200310040c050f1040030400207080801074126a0300448044a81408544020510007003054003545000042d40100c20511480c1001482c02031150300a0a03e2802c20741d07500c508111043d1035800400008043c80010421402c082e02d031a50440a4142040d5500344440b000c80d5540f480030b076080d4100980c840d110b1907820700a91202c026040b1030341c00d45800c100c0d1810040c1d659808001d00b100c1060f0001290418030f0f105200717140c152050380014040301d48131400740c2001e9410822096425540c5c2c1d11041641844000300c00e030 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 53682126 1250 53680876 53680889
    0x30912030c0b0a0501080c1c0f11280510020a0507031101080702010c0c06180609080714061b0706020d021801030c09140d1a0a1506031b03110c07 64
    0x40c02440c0701c0c50540d801c0c280140180740460b0811006001c42c00b0080b8051084d10415920300e02501510108110694008603001d040340c0407854000e030a10030a5030200407d4070040e01e0450300c10382d0f0007078080005820600558404904580c090007507280103201d2100300c81082c4100c440003a0291580d60a051055000715100981808225240d58210060740d0340100310340000c0000c0716220801400100018100800b0342d540c5024007000340100c0300c90b8414807a0040420440c00c221482c0c812500d6121341802d81d0703848040c0c0d2101c0c0e105ca2000030740c18840c0e030a644240080c00d00c009071810742500007040031a071b1a074090100e00b50342c0c1c0c03d600c0034002440000c84084440e40e801030000d4203d8072441d1000040010541d401c0c400c001c502030030f10320301c0310090f584841c120103541014025801c0c42d000010300250644180303c090b698076007000c4c0301110314a0110011a648410070303001c0759003c0b03020f10f0000c0741a4141002c040d003c2da018400030382c8450981440c182080c00c4881c2410b04680200 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 53683376 1250 53682126 53682137
    0x515030403090506160303050703020c010204030c14191211062a16050904020d121d04050106090e130c0b1e04050607081605030d02031602010902091303091203 70
    0x4107041d40030344044003c0c5015107001e0310f825011455100341c10f2040320081d06040c2c5030000f0415a5100307504488520500200854440d92a031815108034034051240c22641c0400f100740c6600392620114101c1034140e0b4602c0702c5242d62030500303500c2400f000400c058898415903484152503441c0c44008103015148400340307001c2c4070b121280d4100b506030104807071a82d56000c42c0340d0300d11800d80c1c801d622007601c0e01200c0e071803295550340c400213016000d00c8100421920701c2e0540d0111f0150031040017030085088801c1d841c503541a00c010710046840920540001460011080042d980312440341d5800401690307807031404025a454150000040f039014007811800000e02c0700090b0200e100c7c82c602d03002c80d481010b24040c9044006400341c0503c440141c2005c1000400415401900f1001038020354030009a98075021114680130081d04129514424000100d0740361250a20601c209100c1030340c004c0196030304e929240c4046500c3c11003a54114188208520046040488504103070b450901c02e130341c0c9 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 53684626 1250 53683376 53683381
    0x7240f02091c030909110d0615080108030703080f0411030a150e0105091e10060609060e01020c09010303080a020f03010801090c061404090903140d0b100e060919051503 74
    0x18000a802c031510300d4140500100710800000e54130501c001c0c1212601c00001c03841030310301500401d00340309007104101c85624000d00012100301c2c001c549160014a9141c600182e070346c2d080466103034400c03160b00800041d10784001070010700d82e680301c140e00301f40034007052a4043c0001e00801d00d402c140b85025602d070201170742401000003c0e80202890702c040c0d070f40203000b542032000c0007a0b580d1188812030030184408182d000743c820380c100050b20b02511074040134030965690702ca002d00011054000e113000200d012275225880d500019901c220380001501100960707182d40c0b030494042001911100031242c00b089000e0250840c24059406808454000a009481c61804090302c08090340604184881c00846540c080000e0003964102c0e04940008501d400c41c1e4901110b0441103403212a00c500c1021940711703100442d82d403040c03811010070f850032201501920015205c2810a9100c250b0020007003141180c1390402483c001001641c0d842c011a002e5282c6c0d001801f4502c442d000d60201e82408000c = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 53685876 1250 53684626 53684629
    0xd020403061a09070c020303070b0a0b0904061a10020309090408091302030f090d0807050304210804030906110c1e0603040311070905010308090d03200a11030105060607240f0209 78
    0x6250380080b582d0901a10381703e0780d640869242e004442c1e018100000b040f00143c0401456000401314060080801030b4901e41840c1220003400f00b02c0c91554600d80c40030612101d42080d41c02450807a005400442c20010020108400c550380180200c520100a000004041c2ca4030444c00c0c0d20100200e002503141d25000100411101e401802d000142e882000d4920142d900408419040342d00d610f4080d540390350fa4201800198103c48015650740c10500d0840c50b1140d1090342c0c40d02883c03090791514000c659074001150004040800c0c0c80044d0007460300c03251581340c21040c040001080611040905160000060941e0012601030b004501c03e042c0c01404110244180e0015100030f103010401541140c40d103a0182c003421404a00401600550f082458016461090040d001f555283c41c030300031070a1026161450904201d82e62201d401100b400c1d40703010701515110384406450581044800c0d03c652900c401410b2464903080c25004004842800b1400348070345030080c91001613039501c014030 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 53687126 1250 53685876 53685889
    0x405010920040b04030231060501030506011d130f0c09031a040816051c02031308070e0703020a090e1e0702011a040e0c04020d0b04050702030a090303050d020403061a 73
    0x15140c1c62031060811041c0301d0700c40c0340c50650b400c1c1e940644040c4614036000b1410a402d00002054080801c0b1071092000045003540120050316030a03a410700c204d8481030010b448034120410542c1101085a600e2126401c02c501503603140002580e02103003100d45400c03200300b00c0d400704000c0e0000880702c8506005006d603006e03142925030141003002d1b03000d29041e190803105003d0b20107000f4a0951042c1c4610600000300301c1442c8010310f48040f550700c0c0718490b401950301d034000340517000040c807081780000e80000c011a40d802155071000200c4081d640d4030404500035401002d0220a003d0644000704816141c541c4203842220000c4413003e4504c41900c6d040403c0100500c9a0110383c1441e078003511003141085600312116042d00c011031910550700b0410705100703c40220326005480801c082c07210104030381180700403102c152410001c5480720503049840c1e1050802041c04119200020800070f48650014007448059280040c00c041e2681d9401084d10781d03807203607200140c070b0032000f105003841c061 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 53688376 1250 53687126 53687171
    0x614040b0117120a090518060108010506040602061302060c30030601050d090309080a0602070b0117030a0c0f1502120108030a0f05030a06050901080a05011a0108011e030204050109 79
    0x401901142d02c2200c0b451550354004403442400c08a00071402c508010300032038143d0003402c3e0003001c0080d8040d115501d0754642d2403c8603140e00242c0003c00001d07090400c0822101030700c0565000c0c001582d1f0b05426001900d841141c00c0f40c102e0801c0100c65503412040c04030062028038203041c01000c240c1c0c0319030b6001045449034080302c0b6a00c104141702960303801904032115025140c4003c592440c0a050564a2440d03a070300011003030059442400402850f9401130030042e104507600811a6202d240201441c90b60b03400c4004103034020842c481c0564007459500c642a840340781ca141d9040b80c5503484c4540001c40e041c2c03500c0c0c00340d00483c00c04039003104c0380c044c2805003003400c0c0111b0408080716002400c82e41c06459800612a000000c54401d19036a0040c2c409884081d204007001d503942c0700050307513030f19000740261000e5290807004c50040d1000d01549040030f1059640441e181d0a1101c0b020721020300700c071480002c1400c403400000688450080398000c141103000024505441080d1f4002c61560 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 53689626 1250 53688376 53688389
    0xf010b0102070608150d0b09010c021b0102070b07110406090e0c0f010f050a1b080903070e0105010e060c0a050d050a021209090109020f13140f010c0c1802070614040b01 74
    0x45414003c0c01d50102605034442d9603526058104a0b42c1d00c0410b40d004040d00b80a01604040c0701003141220301500a403541e01311903803c94858503060b210403042d2598107000039006800282c820010070754100d010300312490240f100322403010485400103084400c10340c80440300c81d40f1251101c3d00c2d2a018030884044100558403100c0a00d90704000030080301140503240280000400c2210a0038440d9208400d0a101419494011a29410111965080141505e100303210741140450020148a07115040703034810786819140c00c40507c00c202d00c42d00100c005000c5841a008100c1c0401c4c03081100003584030150300e03403036611036907003200a052030551903060282010800c400300a03910340d00c0d40300c3c1c1159400240180c45590000005030244150140c821803010459000704403402e001240c0003030464200e80d5581003010b920010b45420700c280102809580500104000000251800004040251800500e0400c0e1075441e401140d02400000e104401e00004000030070200322201800b4048 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 53690876 1250 53689626 53689633
    0x10506030708070f1107033f0309030e18010e090a02130c03110a0203031e040809040e070902070609050706020609060411030705040603030e04110f0d020f0d0e0f010b0102 75
    0x4000501606012000e041c040c10810881030036040c0910451205004000717400a84170030341ea40e400c10310604205031481d0342210600841c2e40700b0714040390182290b12442c40410814200e0300390000d5000341318004054080c40000030000c0c0d00c0c0c3d07452b0070f459243c10800c544030841c0342d4181902924204c01c01060100b06a0000c0b9415025958840010b140010350310340c00324031070a091a080380906030700540084004400308801450503008009580710b014200b0710b0784050100070030100155002500c01402e00c6804000140e00783c10079402104803407040100700c4e40300ca50b0740d4241400701d0340001810303034203a6500c944000c00c0043c00c1c0b01150042c005440200380504048602d5511000003400082c4206c40e5600501c4580d10240142802840d00400401c45180d4904001d403800405a0303207075124a1a0031700100c003089104043c0c1c0c07480c2404800706410190010300035130017036008424040d500300c0d00340119801c441450080c0748441c114013010f05520b030300084c141401d45072402c00c0e25042d0f40 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 53692126 1250 53690876 53690881
    0x60506030910090606080a03050a03050604180308040c0e10050a0b091f020a2306070f020d030e0106090c052203080f0703050903011a1206010819050f0f0c040501050603 74
    0x10001982480b0034401100041c11541a1030881d0040000b41d00ca030202d401800b4500040c550080042c01e507851540d201400380360340f4001040102c54101c14001401d001100c01000032a00c508011603000b0b00c04c00c5580b01c120f8803070320b02071640d400032140e01c0b901c2d400f21402408182451031001d0b00030520300d844141042c440348009082075249030104203415100c4510b002145d442008800da8080e04070048001480c524800a03400c3c2440164982d0700d40720b00000702d601248150020701080303041d540070300b81c0301d00400011005040308260224003503480e5600443c0200c0c10341b086071000d81180e01c0340c0b595100011007019032906c2a0358201c00001015204102251f00e4000b1680c4100d41904001d0351001240b805413200d000c0d000126802d586085510100e042421030401003850046481054008035950607682e100802d008245564200710090f0807090301524943d00e100e4422000c0d502001c07603094400d454644030f40040002036200c104403801c103007418450305d805003038113403416855071 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 53693376 1250 53692126 53692141
    0x3160e030d0e030a080703090323060a02090a08060a020301060807090810020906041d01080c060a0c020d0f0f050c01140403020907080601090b210a02070b0c0a2001020d06050603 78
    0x507103078032120038240705101800d0442642c0c207205101102d40d203c0380c8242c0703c0902d03043c010300c01c41081c0821604481c10310f00c03044901c02000b9030000c410150301c0013402242d44290850000e900240f031541c0d044500400c01081142007803050324442c0729482030058403585450001040400d0203060a4240200d10109004546021503c80c074000d48804025a0f10301d0183c0200f8401e2141c3c0e8404004614601c3c1550303070b5048e080f548a8101c5401c10100c840e8825079034204844e61040c190000b0100e50500d9903400181801e00c120a40e05000700342103005104580c80c1e88103521131250303080300c807604420640e403e5580c008002901d1940b00040c8281000c0c11507002c1078500d80040d20321414000141e00280050384540c02c2c2d00040c0100040c895142c041801d0329003014011007a19020704030140c40000c848250610a60799482d0f0040222101ca403503955030341c0403a0303012182060404c8503501c0301c0301288000d0803520001e85010000141d81e25032880072141281c0d1550031043c46001c00300309002c1c45 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 53694626 1250 53693376 53693383
    0xc19050f030403030c02210307060504030203040e040302100606141204050c09100306051303050a0509040f020a0905030606060304050d050f0706090c05120a031d01050d0c03090318060c0602030405030c07080303160e03 95
    0x10275500c90000981350720340b41001d91640c00b440d8081401000c140e000c0008041d070105603c5244010900e00380001616541c0c1074070800166824804107081c1032040c0c0300c00085000d07000d07803c24007603000c1c0e64154907040c022030740100048480e40705101202e00b080003044041e1142650003144640080e0017011540d400604920649401e00b00308100800e540c016a0b03115800030283d403910503c211340d140442500580700310f29900c1010311a020b1100018000d0074190102c81c41154444080c1141d003000981c00c0e00e454111804d940a8048284420f800041c0c030f070720480d4400d500460f400c500c024604010010aa118100d00c5080383d0082d103000c2c40000e0700f12803160100c041040c14000f43d40d1030040100c44a028803d013418049052031205421141c0590100d041c2e14040da4503080401d6111101070102d07540c130302c200710000c0c0702e00740042e010a669601854206120300241c0c1d103032000940307000385800e00380d420114564200000340060486500007884441ca000e00b40040844880b400090300d = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 53695876 1250 53694626 53694637
    0x309030c090411090405160f08030f0a0210020319050108030c0d0f110a06050a050603070609051026090607020f0601050913081308120c19050f030403030c022103 71
    0x80e40703208003203070070090f00360b02101d40c144001d04480c00d58541414803039550b050405204440082080020901d91001c00a4801b581c0800d8000c6140c0700c10300500041d6035000503212030840c0580340e400708030b070091400151701455031034410751139040c03564885c42e04840d03043e880403039103610401c0000e4031042e010942110814030346c00c0c030048081c01d00d0310550350a2600c42e03c4004500a401305201000500c1d03102501900d02c0110400050380d44c9002d26030b41300b50750300031403012546c1d908080050f441c01105181c071740402492b10ba0b684400849501c002108072003c1781d1580b840350401c00280010400c60141d00200c0c920081c000319010b4a0001e4031004103008084c0515070460000301440307100b00740d2400850384a0400c1d50f480041031312842d210101c41c00360072450b016401095040141c4c5806840c540e18003400074021034540b489000d21004582c14044400d401194406000d181e41803005d84000c1d402a1074180842e034076071040219030240500700d035a011071214400c1424060000681e107 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 53697126 1250 53695876 53695879
    0x2010f0216060911100c0b0606120f19020a02030304060f0b130b06070804030309060f170a05070c05010c120f0603050303040f0f05070f0603050a0b1f03060b0f07140309030c 76
    0x180c094150401400c8007903201081a00483d0a841580420b030b1b01202d00c1e503c540c014a030030a184c1d01e03400c0822140307114004002e07030b9900c40380c408030318000c050307400403030708001440f040c0c14100d18200d000005907002035000c40b0243c1c1001c0100002c1c042203010318454040d04050030001034442400107040c940d88a810788030318a40e41d5184498036250901141d42013504a8550743d282c136624540104841800e000f01400600c01114602c100c03800b886500400f40b0388180c4c1a20596030300d150400003010024040c400b04400014010040b030000c2c4a01d20304285956101030740c21b91b00c950321206881c0b0184140c02550701e4904200046070000c01900c2d00943d203c00884803080c41400c021851202d40170004e80140541c4100041071800101c4550844129841c18480b0b0341d9075142410445030006d5410390000745000c00341180700588510802042d00c5410001076864441c103010009400285034001d0004001440c5c9050003004480e0b65001d842e400011032610240300c0100c1d0701c403440c544809 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 53698376 1250 53697126 53697131
    0x10090e061b0702031005090a02030d030c02030d0903051603031a060c2d060109092307030206091201020409050402150403031d040207060c02010c090f030201081602030903031902010f021606 83
    0x20301155030605c65440c0c0304103040c8060209051214440c0d8030b8200e04641248688514072405211038047e00500014400c80d40265041c5010f03215410050000c1034000c0303080040822400f60401103481c00703440094020781d0300044074211030505417031241c450003980384180014002202da94800040c024003108030703020070030301c07000e503110829104a50030207000304540200b100206035507240e039000220040c0224103540b149800e004400c40d0681e400b40310750311140c120503030a0000d410044014202d4541c080c0138085182440e40c1450308a0b000354004d00d42c1280c80e001804294900394034605000c0d40c007031482d145080e24555000e01440c24903018003000103071840e480d6641ea41c2e02d505980315a03400083c10b210071018020001c1c0249610220314010829003080860380d01003141109042e661306031183c115644910440464a0710b900e203c40c000c510007000b040c91241c03010301c0900302802009203458802d0741210006801d41e04500c503107020182c418040311043c0d0701c008203030890054002800 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 53699626 1250 53698376 53698387
    0x100803040e190b0d2109080c09180703050f0f0304060801090507030f0204150809011107060902131e2301060c05010f150f140d030f0306050910090e061b 67
    0x10758040c0182c3c00007154440c43c2512400c050200d0340b4088184034070b07001c250710405024540190f43c1d403141c0340100c0340944c2c40042a0b6005042503603102d5040030b0303078054818400d5032250150b03260000c1c9410407107643c0c10109420004c0d5008010008190901501441c100360030030b10020a407141c1485004105134a841c0406c1d415070080e0710500003c0c030310f904103651348d513290350050032036184400e500030000c1c18450001d01c0284061240100d440c4510b821280f41460948031040036043c0040300b6a0700011a64800a42c0c400d2481036500c447d1405244007000c2e5007640c1050222824031480c013000307802841c07801102c0020940c2113810b462550419050680c0c0c1c81c01d060340100a69a0f20881a51070130302031200120006810b403080b101c246e009824003a45444d5400c4075810011010354010140c2d031a0880000c2c0181e860310554030007403400040031556000020484d15068420700700d95040345400703110005a0b07019207a90451060014546401c001c3d0004880805100b0300c20aa020301040 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 53700876 1250 53699626 53699671
    0xb0a0e09070903080703080105090601020f0715050415170a0c020a0201080c1e09040f0207021e0607060212040201080105090411061c05010906050f090408030610051b06100803040e 79
    0x12002c09140c02c0700605459034114940948050001c0c00703290700c03905002000944561001031f20020081c2c0100141800919200f00369001d1082d0380e100c10140401800080740b0710041140300d0702e0501403a40c4510400d56038104080d417000e8080c10000e4040d0034072020178103c5400040f0500d50980c2071901c10380686e100410055039004000c8000c031006000c01410307810b1034580f00078007080d001c03c6804025203440c2c006101d08034811084029000200301a039000020141c00040c142c0030000340c0141d10b88803240d500c07001245d00c0100e0b07004030403031103006010030340d41e00c000740310302502017601d0500d031a00341078403071400b1000b40450f968400c80c00000d2030000b04007803501c048400f040c1c034401400f09503184d0a0350806885a80500ca000740c044000d884c0081c6001c41c02d06024070340045c400c610b56200c1806003c0e540d01070810308414850200035101105070001e1996504028000152495007001215032580c840386070700031119640309120500074074607201d030460b800040019684c3c4200ea440351 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 53702126 1250 53700876 53700887
    0x5010813020915040e01090c0501051e070501020c06070c170c1f06050a03050a050f01020f0a0c0611030109020c011d0d081806010609090b060a0c0209060427020405010b0a0e0907 78
    0x1c000f26001070810300180c501c490150000c0e9980c900c45d40d01d40003a287c458004488078082c0d051460a40c44025403c0c800c1c80034420002c10302076008800252404074803982031407038144192031200c00141d441841a007480b8a08602e4402e120019220a00e80540728a41c160750742e03660b440d50840c6003c0008000b0481c580c81c0d024034000c02c80a0710b04c13060780d603817814629100c3c0d400c030001f95041c0c024610254079104040c400c4400f49030415044d00c0c1099040001142c0c14544150f0444025039240c0f1202400307054040036500038455a1000350303076842403400c8a429034001c0d154210b844101c149004215a0000c02c0c416a881d03a02e02d450f50a643d241c1c42d41280c038803949000a8401d02a810010031115400102041a01c0b01420180f00040071801407040c00e00c0350441410000e080c140004005150034540150444001000850a42003501c41900d54102c4034020044002144140c482103007024014503006040c0f840a607414070501c038802401d10b0b07020741e0303902e0300c5120b1640005100c0c070f0040c2c = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 53703376 1250 53702126 53702161
    0x6070308070e0d02090901020d0e03130303050307120f0209030c010c080f07060b120307050f06010303050a0309050c040509030a030b060301140405040c030b04060506010318051b06090622050108130209 88
    0x2071111750f0358105580e40314000c2d0b10401640712518101100550a01c0c1c1c00800c0700c40011040c844400c50a01d5130301d044405030405000300741007180304080e001c0c508207039001e1b9910300c0010303080050340e9009140030035260002c8244400d0500002114007004210703000b00f620482072400c04015502d00052a2141c02002d0389061543d010103035018410344950000041e203d1184074804840c011143e4011582d9104000d00c0b00a00040c02002610142c1e446900890601e512400071a00d0030b46038000010309070303802140e4004056101082c8901915890300480e035100409840c00d074034550406645c030301c840c0c03c00b8844e58000c944440100701085614913403c0001c50304965502c00c181887d2414502a11050f5001070009041442c0c60600c904400c0d04030101136401001803d18101442d0401c6012402d05070060740a80240641c180c142c84007030040c1000d40281c06c2030403854800706204045102c4c1d84d0040b504100300f420400c13061042d519501c0f441943c0440d4120200d42e00c111800c60400ca51 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 53704626 1250 53703376 53703379
    0x10b03010608010501050a120c050f040b1017010b13090b0a03050a06020c01140c09010e040b0a0603050108011a030d390b010602010e030d05180601080303090c06070308070e0d02 78
    0x301500041ca90360103604c0030707058032022100301308919507450b41d40d2003250050f6800303400c240c005a02000913103071209080401c0d403005000852395501810000e6032400b420141c840c00b0521603149105107003200396481c1e014143d605917450a146c80011074000020303d070b00403040c0450f501c0710010280d988030140c0341c009592200480c1c20b0403025240c031034082c1d01300f507451804640c28441c0907220300c60078004141c442c80302e683d6050f041543d804011224040c40f4041b0540159075420240c0c1c05031545003221000c4d0034640c80c04982549007601d05400c4480311842a0070000d09482c01800d60354010810b80c00d50034032882c0042c00f00c04503c0455030284030f030b04041000d00f0b503c80c403c44402c10498488000352800f0f200a0a042e03030342da00c020b900380c070155400d182083d0020001d03011a01c40340d40c403180d000300781d840600349140e0041c0c0f00300d85442c0081c0c00c9190310f030f130020080143c0c440c0700300540a00d95006a611074100400c9503409042003d0203000c0c0014807001e007004131207030b49542e0300349000141c0 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 53705876 1250 53704626 53704631
    0x7060c0c0f060c060b0109150e040b031c180b030c0f040909030f020d0906081803040e040f02120c0303030a05091f050105011d030d0f02100c0905010f180506090102010b0301 76
    0xa0b202c0c0007503c1d100345a0307400c891031420240c01e501e00d98000d12002003140d011901e0040c01c0a00e1101c1140c0705100940ca061740141e403507028074440d072000c01c0300c840d8030007222500c004140003183c005000c4003101c2a9000b14064110418801e165600095903001010003200a40752075503450070f03e00318081d6030042c4004615002c100c00915520202402c000404c1d5001d44100381220b2070215580803a0b40241804988001302044a0050b046c1503031182030808429a030410391160341480c90030200b541d05a941c00840108441945005818006891008801024a640c025012980700d00001f00b85020b00c9076110002202e814050041c2e40b50110540403e90603a003425902c64000c1c5003c0c019503002401d41d480009a1842c85064800c07200402001082c005072100411501b0700c1004a118003140a06681100345680c2c1d40204d04040c0100e496042c00710b81480e0006118643c122001010003405502400c0c0f941d005e5080030060700c400f40c4202d559a40000d0050f03014080c49170301e00d0307019071 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 53707126 1250 53705876 53705879
    0x12012903030c0d05030f0a0c080402131401030c0503010c0903030c02010804110d0605180705150d09020d0503070201120b060909180706120608070602100903030902090408092107060c0c0f 82
    0xc0c1d010740258403402581b0b8183d800e540710a0b0f4000308a0784d4100c40140030805031000704026144c200300882040410004c0816481711140140400090a90045901500d101d20611840c44d080c0524103041c203052401c00d0fa540d2840e24010f15048818401030705000d5134202040502c00060900e410f51040034085244101903450040d009140442e16060702e403240348540c064103800410807208494000b040044242d0781024a109154480320221001b41d96803042c0500607150000c802400a0003070001d0360f10f030300050002401c09040d003410300c0e205034900506030001f130f522034050741c0c0402c4c0150b030621070030303a1905500e08041411804803000c521581c440055070310f030700422045174261804024068913541d030990076641c1561f40900c03800342e00014581c0c2d110030070540c0100111402490040349420254000c111288401e9500340e5903500d002900000c0c0e8200356583c200c02420844114400380310340082541c448006d401544c0030022256000020300c035034044844040c2400b02c413694603e0b03 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 53708376 1250 53707126 53707153
    0x7031b02060d140a0e0f0a08180904080408010605090c04092c0a0203011d030403081305040603080a260106030207060f02033108030604180c0308030612012903030c 72
    0xe250451320720a400b03003010008030a40c180072070111000391580d40103240b040c1407591182c4158204181c3e11800e440d44801c08540c03540c400700018042c5001c0d1a4076555a418009140d003991100e0300039600512a10040c00f0508844204940c2104d0181c1030000300c50004884104982d1040145802c2482d00000021040c0c503004c02c01c207260902c2140204601442c000f9807400d00301c50001d000510f03810030701c010404500c0801c024452810388240d400300e0b0503207074030014003124002c2e0000ea0f55804049600704507541c0049884186c0500b40342800c0903407049d08541d8070500c005001e01d00815070045100000c1140b10f1f000751000a50a4905540b00d107822004040c4151a95842040302401908022412892821800c14030b5410bc10200d203160703503450500000c1c0001c6006905c05041c084411004580001044005544a00d0403595281011020817840801c02c8560140356450445840900080c00d80801c0e51903002428074040354512900007420b5002d95000c4440500031010451850b = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 53709626 1250 53708376 53708411
    0xe0a0b10090b040506060307030228020307060b0303030411010f0201060302040e06060a050108090304090c09050904140714060301031e0c0f050108180a0b06121b0a05040207031b02060d 81
    0x50715031440c0c08004120560041209562041c0d8049800940400201e0021172290f002000090100d0488100b0340e070722510040949010030400000503003010856204010710790040660300b4074100d00550850600c0c2d2a201c0040241c00d5075a0306120500e96182d040038000c0d0400c800031030f00204204140d0403007a1403107861718011181b06204400c00b103400302d0070798065180140500c440d40025070a047c14081144d005200b80c01d14441401082c00001415660b59170307a0500c214070411070240141c0c02207040c80d10b000f8107a0000c21070340c0740404d2420f00b203403a0f8500307032070449070010b06900e5480c4828451340b1030214600009044a1103c1c0700118845d2600a044000c0350030030381c1c420002d541d415042c4451900c3c008461881900301d802c0340804242024881074001000130581100c07042d800c0705071480d10314843d0310042000740b001c1c0a0046071405540d80c8004150a540c21b41c0380084950f00102501c203050540100c0150124081096450300b000341c0c5c030a039080500c03c010740729000840d0b426 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 53710876 1250 53709626 53709629
    0x720010c0309050705090c0d181509061a030a15060f0314120403021509010e060d1e090302030909040f06020d021b15130f0b040f17041203030e0a0b10 66
    0x81d140b00b04400005c16003402c3c001c862040705d01c1c042141c2040c03c00006c5001800028441050780502c40384079602107441903184070015002c41600080c584114940031013030707900b196000d803d015040d0000c0a10b40d1400700325000c0007039010030402c0001510030b10b00b800501594014a0040302400408020440d40707541340040080030008843d04064441100205072285000c020f4100842182d084c28040d0810080c185030601410b200362201210008a51142c120745080800035403207810030880b085071100700324881c61900030700b4000d1220b10b8402030742c0c03480344092450040d440b0400160511030b00000703100c4215440103040d5601ea91203180381c80690419014007400b1070020040300100700d800150101400d40d4001c0054181c2c1d25681d042c21178042810040d203628000032002700000d8840300185126a2080e4007580d464002c40c14840000c0846a10f4094050b83c1004241b01c1003a1841e00d181034582d00d480c001c03503044520281c8509000046034010800040c10047c8410440c02021400 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 53712126 1250 53710876 53710883
    0x1614030f04081b010c030f030b190906050f09060d1a091011070309050402030c0c070305060906060102030a02060f100312020a03030b0d030507081312031d010c030203030720010c0309 80
    0x440700030010b5a02d0000fa10f070103803000c1c04280070341d100000090181c40c00c080312803020304000440050340404201d24079508000304104207175000c030500040d14548078800c041d100c155030b5250b0200d0800040ba02680e40540500d00c00c6401d801c644003040000c1c8c505a0741008034068000e01ca0403c219820303601d41190307100000890500c52080c610440a03016503001a0f090b68614000b24900b1044c08025400a0710504000200304a00c542e454800c010006c0110300c12802402d052500c1c998550810002174101c0d41150000c1101c8a100e950005600ba0031000149000010f030700c8010044800c030070140d00c000c1c54411920340e42098140c011072a03180c2c19000e52030034840c0d00301070b01c10450031a10900c00100414414400440469030100203449403600c0b940364280c500361644501c4448440d00c0c0012000254010722881031890b503031402071100082070a00700642156507402a440380001001070301000700e000658203e080310041031503214840c01d002049071005942000b405410180d03130a5 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 53713376 1250 53712126 53712133
    0x31a0108011b020a0605090106120807021503100b180907020a050c010807020d03050a020409020f0301061106040c05040b01020c1504050a0e070c080c0102090604140405060102010c051614030f0408 86
    0xc204034a5000b4a4400e07011060b400b80c0f00c034042070b98038a0b006210142c0b03c6481d648d40c0c0c072008100e4001510740100303540d0044200c940c13601701130b00c104424034200b181203503035101082c820f0144130015011094255000c903050b150f00e800c2111181c00081c0103000c0b10640c06009482848001030700440c0800842d8001c000b41c0300040741c20310066a00040076154400181d01203c42460340c94407d030b005c0d0750800b010007005490a560780328108140d03044080d60602722800000100300e0f1540000d07440708003840340c0020388124030709030b00c1c0c0b42e50710601031041070302482d20b40c1d01c4d01d91507a02c203009020014100070400240c407007000320300403229000740c02101d000c0d5407991030100f01d0513149980688586115a02c12004021aa03900b212030380101249220b15034081c056814581d403190094005048007650b2098401402d01c1000181c80c1e0141141c1d042da45041c0c110001d40b51b201d000c45d070344684005507203880083c03240360000a01144a0485a9502000c117101e002c0ba81c08200800071111b099044 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 53714626 1250 53713376 53713391
    0x405040b060f370f0e07021e03030c03070507021e100309020d030f0212030a0b01141204031b0804030b06091f051014070f02131a040510031a010801 65
    0x80c0f0400c200c0d0f0b29015501440c0316115440050701c0501034807079801c10703a10301c8400d840e6140406000d82d03286400c000740e401c1c200c3d4104011650f040044110100241d0700b1003020111f100d0725151039120190400e5840c440010015121500817412a04c0095014010314050031200ca80080d1612207241034038400d84e055009d11090a10902600010300d40082520301c600b81e26030b50a444035044404c00000350300900004051450300304010b54400c41c035185010841c030312808001410250b40203951490078900384006008440c110910542c802d40c1810095400b00b0035003545079a85400c2c04008142000c0003801004100d81d480c00c250045106584815640c1c036003400c2c248024014000c0680251010b150402082c6080c000c1f8119a070803501b001d010f04200320082c00101d504c003200c01d507021081c0c14000801c600705500307001e0040004210401500e5254505d40c410b405519120500c10381c0c54402007103030301205120a50045038020003c4500781c01a1401014440d0240318000e155440c0154 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 53715876 1250 53714626 53714629
    0xc0905121006061d0f01030b03060703050403020d050a0e040b031905010b040605030705090a180b0106080702060f0105010905040209040b0406030317010b040605072003060901020c160311090c090405040b060f 91
    0xd001302824005400d1000e4643c20f88184103154520b9104141011f07100d61004106440500600f4062161580c0114403881c0070700b40640780ca80c904100c3d0007004010052824420703405800340080172001c840c08546030031003d000078076007004401c058003002801603c0c181001815402101c403c802501c0505c0500e03510f800b0152900c2c1d952154a811210f0240014801141035028215944200c10302040c5400b0540390720482d00026040741c804520601d05100c080c070b404001d030a5118410308030000c0198104400248440c0d410b10030140103c0e00860100a550b5640d00840d130060005001085646e9690400812854040c0f40d140d01c12607807003002085200401e411503060340d0140d150a07107004242e030359802100380c0c8403062a04040c00c000320080310b03540c2403182e0f03402003034400c0015032607214001e0074a007002d02c1303090b2030080b4200c83d000800004441d030260b5001d501d0110b901000580da40c000300e04441c071401d42c0b04c03540300340b80204003c2005621242c16000307501c203440a0014004800 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 53717126 1250 53715876 53715887
    0x30a0c090b040503060601080a06080111041410140c03041d040c0f030203070506070204021c0219030501030525090f020406080105010206040b180f030304080a020c09010b0703030c090512100606 85
    0x6007500f64205c0c10000707405500501180f030300018880c400088151b034030b003061821900c0d03401303040c502c3c800700081c1000f103c51207152403803201c1400c6480a0188115040c043c014040c0359911103404000456002c840400c00e0007590300500d07078052401d0904400c80c401640c1c11030211800caa0743c2004007008200c08000b0f85003003003a02c0e8003400801c003440c00c00301002480e0b0084401260300540802c44140140c04981081010410714080961164194403200d01c000326509014420103203040300400100390001683d405510325420140e01c03c0e400d81541548000c0306800007003615040004c20600340650303500800c116025562804240c1e600c41004984900041d140945515140404682c50f0004071010501034900744041341c203144a0724003030700d007560000c031000e940340c1a010505101254050150900740d20003103480441c250b05200a800b950302842030007070109951000034121481c044d002c16006044010000304650520403c01e5944540e403218a0842c18205103000a5a0b800b49 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 53718376 1250 53717126 53717129
    0x907110304051903080d0911100e0609011701060e1f08061005160f1205190e010306120b07020115060e090907090203010b0c06060603040b06041802030102030a0c090b04 74
    0xe945041d2a04003000790110b004000f8042c1050a480b0001c0041d0f0764900034404010490004200d810407420840198550964034901400c2284514501d4950240c1056100f042c12102d454444030b46c507004840b100b403525040d11260707032080004500d540d00a441c0b016194003c450f00e000c00044498146044001c1e1044540424404000b248043c42c0c6118420030f220031134540b140c10b2100e000c070012494a8201e00c1a039a0b020002c068900b40400c02185030710200032400e000b4a8429180090715030302c5801c0c5d509800700f20030b488000b80ba50780300b500b10400802c035041c0303102e4407400581803107820000141c1d040000749d841c0440c8004140b14440e138450440303803a5203074804948146400e11419500042c40b60711940500030f0082038500c0f041c4095130180510701d403504c2c1c403410b0a060841c07900c503010304220300c14001030040100044510545c3c0f03621030015107000c904212000074401d40100300502c000d40c15400442042134120007a400b115640005a548010260707030345002c20002e00c602d = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 53719626 1250 53718376 53718407
    0x10050a06050a060c020312031302010219020906060c010e06010b19030b010e130b0402030405010b01110304030c0b21090c030c15040317070f0b0a0b0402120403081f03060501050907 79
    0x2d2010400005014510100140780046d00f50388030505501c41c0200e455104a070b90340c015451001c1507406659041040030180c0d1001f2181c2c500301c02c5182c00140e03048000401d036600c070b04070010300c03010702d0324081d00032110030740d05042120a1541c4510501c9119000030390100c1c0b10264884031101d40d140f02e130040c48034001c01a15000220706480c014000f44008240d05d41c81565101c10b96107000d40c41e50310081d0310403402040002000313404140010b012110865a1344100c0c1e01c240000d0020480c401c02c410100c510709485541d0ba200c040144901075443da8007142d0f14001400e0400230050004500990601012421703205d200c0c0c040c0041200050701e0050b10180c2080038070081c0f00041e00d9412a108a0180d960942e0a24040342d5490f42540c01c1c04804a8844021320309100c80d00525004104003060215011360414000700f00c0d94152000040018081110140c040b404aa1101103d030191000d49181407007016160305002028043c01e02c601c901a05603200000c1c200c903c20928001500d10 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 53720876 1250 53719626 53719639
    0xf0a050d1202091e06071a0405210409180501090312060501050c06060609150f13060801030f12050f0c0102040e06030a0302031e0409020307020d0201050603010209060a03150509010810050a0605 85
    0x14070400c6802d4584c016410140c014000700200780100320b4101e881c01e1020a40740010000d8a41460802c2c2004c0c5003518080151403d0350312001000340e400b00380c034240c45a4600c001080d841c20036102420340c00c08400a42203502c0c0502d01d509050b48440d5126000100f040b0a2141540c2c50004562910500e04d008070341d600720001041180c0351103002400c03241c0c0c008100064282d10b072200358071654845140b6070300035600000d100c02d81843d00c0c0c1680c0002d0240381071100c902e625640750300d0824040780390020180d10b03044c452001107501032001d07198074034981c1c14010b07205c0c045541d0180c000c2d401401040e84c0014a5000034890340b07400288030340041c0c1d02d85d0203903060454034030381c2d10762010482c148424010400d0001040304022403000d0352040c20a80c1c02052054241c4001a00319800a0210303406030b401007140790110348414040750100186481c0010b0303800128403150240b003010b03800c801c0d84400306a000050b8000c00040c4448400c52202c0c2c10002926500700170b0046540d43c1c40340302c0e000354 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 53722126 1250 53720876 53720899
    0x102070f06050f16020405010b03091501030f0b1902130f0801020f0415030f0213050f030705010f0e030708010e060f01060c050a0f060b0307060f02070e0f010b09030f0a050d120209 79
    0x5940c0300190030a00128903281c20a03103d13a6001030280c030301c240c100c521a41c90110800c010240104030421040402550003205035065883e40c128000121201034400003401c2d02103034481c2360104600001101c4201c003103480e03d4400300d0030309560410f4402d005c4182d0b400700c1d0100318a60180708032512122000ca103a0b1805107000014011503010f50802000d1558503c0003500040e158002409410100041c0003126424481001500103001d40b80724004d600809040c05582d070400b806900c0f503403281c14410303009806640000d24000b042c2d00003803400e50030030100c17003c041c41c002502030049009060128061307880f6181103502800915014001c0e03840f00e480c9002041036181c1c2c0c0803030316004441c0030031032508583c0402e2406200c1da10140000c0c1c0715013103003094503a0602a40c805003403040c0106030581407403020b043da103103c18000d49840c4400007034038031240d1b513040000444031020042074901c150094209030b40c8990416602101141403401042d41e40740300c601c2100c140340e00060a416104 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 53723376 1250 53722126 53722147
    0x60602030405100c0c081b0411030f041b031a01030b060d08040608040c030206031005010305160c11030f07031a10050d06110f040e01090b0303160b040204060b0a020109020102070f0605 81
    0x103103c4c09001c0d1000f07100c5010105003040244840c420613400b0b480b0784050b00329103009000882c5d0032108110000b18050051040b01013004c114070350482d401c0020b010300310282c1e1010fa15002d480e544010f0140301100c481d0080752103440c104c54126030003001c4443d80e80c2da4103410b004e50041c00500c014030010f0b04100500400d8007071a64990070034010700440ca02540c42c2d0b030100f003e40e403043c0d9110368075942466040020f036916005517681301071a164403000300090080090498080800c000b03045090280c00c404194808224902e1103e12820807281c09641d241480c02d00d04882140e9500c0310040000083c15066400294000700c40020344a08038460f82a00c070f140080150070ba10400d290340c100a00003000046001901c05419a00c0060b11654503050741c1d2011150300344641e41c064ac000340301c68091107200d04480c100c515000888003541c0c1c1e4482c4001801810542c0040c10440700100c1c030980840d50560048181074802c2e021508990744071101049220300707600c0380c070000880411084c00c03034 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 53724626 1250 53723376 53723387
    0x60a1205010b060a050d05070513050906120105041b1d0a020c070302030d050a08010e040b0c0c030c03030f0403080a050405030d02090402040e010617010b16030e010c020904080c0106060203040510 86
    0x2840d02440c00091800d462200003012507105036180000a82d0110f40ca45540d9014441e56402140904005280064902088418612a11a403403081e01d0040004846440d000b50440d800c6d0280c1c00208042e1900d450900f04048801c3c0c00303c40d5004179007401260007021102402c0320500503900c9880c007581c1d405048006940300d9000c00c106030180721000001030318200450101800300713407140c54a0741c089070740c02401000142d02003244000740030140000700b500203400315004860f40c80c0c4c40d903880d0344142c0e019285129100303101019200000800c00b40a40a11441c0d000d68403c0e501c003022922102e130b101c81569000c0e40e025005410420440b103600c4aaa402012841c04c00307032015050a590751141c0c01508404d81c8000007081c0c00b402c0c5c00e40d4510144180c5800740c0b0342c0030110780c103001d640f00510310240200b25005052140039059000140c2c000d406900041d68020031010444c40d01b07107401246a007000503400c2c510741c20b017030020505e180084103076020356170081e04c4401034a1302003c08456 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 53725876 1250 53724626 53724659
    0x90f030a02031204090c0201051015051c0912080405060105190306020c0601060206012102040203070306080d0306031520030714030c0408160302010e011103040b0414040c0305060a 79
    0x9062066000250050728103110020b80100030494481e200d0f4034215110054640c2000c0400469240200b0001e4100f52028110241c610b01c041e0620f21402d4007506694038403480300707010503003081011444603020b9a0b401881e1031a100d42e400c03c081e0303a0841c07020307101d07108c040d10020f0054110000510060805101480381c01c0c10500000309619525210001241d00c504020f0781c580d0450360041c0001d5404115141c010042484c3c005030000d2408071300512046003440003403207203400102042600f0300c01c0e0003081c06480d0b1002a40c94100002c40081c0041c4018070080b90050060b0b2085100d0001922416006803a944446810000304510304048d07944000c00340750602c407604d850014400904400303540304880c804c165664950410543d1850820070070003920044580102c10f00043c0d030b20190103000d0341c1b02820310590030211241182d00310b0060390005183d50101080014552a0a42c0020107600c400c2d9010000f20b820350400310156501187c840d030300004601030400040c21502a5141d = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 53727126 1250 53725876 53725879
    0x6070f0501060510050414010203090907030506061c0903020d1407030c05011104030516090911010c03030615050a0e0a080307020d080405090c0c06090d020d0c0303090204090803040c120305090f 85
    0x350a94980000441d0030220130381a10000b0380100b01131051400c65400c004060303800f4001103003030660590000d8294031004020404058035000422680c1d10386909846ea1501e0300c441c261172110426040b0030040c01c0640c0190014030900742c0c2c0150140c000c0342c081d106801201c1240d0b2620a113600d055680301c50103c012a01e40d0360319034241d012501c0c0c03007001d040a036110348081d0040079940b00c818484150250000e5181c40d28000c5040b00240030040004140c03102807c1140070345042d81025001400d03254030158990304020003010501e030f880002081c9000d26a11080c901292842c107006070f150300e50040d04525072007002081c0c054a010b8803140195441540c5941c13500703443d203000c80c041c1030060759036540804021503120700b40743c0184400ca0340117941e200100081030300240000c0d502c81001400c61b080c04043d1038507609040c40b03500300b00c0d4203a0b0040c02c117009848075440c000109600132102030341c0b281720300003011a910100134840380c1c1c03054040c3d803072a041c001c2303c1042110914400b0381d6075 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 53728376 1250 53727126 53727131
    0x302031504091101051c0501092309030406110c030106030302060912130909230c040c050a020c010f110714010215011a090406090f090b01062a0602040812070309120206070f0501 78
    0x90641b4542405558080c0151060115143e400e0b0342100c0c4051b10300000071100840070b01c0c20007038880c900105840848056251610700c4a003140c00780c50034002152180794140d400d015020091680000740c10340208510030460f08036000740342444c80540140f01090302c4070041c10a00300a0140b85810a004032400ba032240c8440300d489004814000c56544206e044641200b204020300340740a1040d0000e03000603051542ca0452245002516140c1405155060249440d1019030b403038818149080045002d40c00c6810140d102c074500e0300708900c1d00010900611501c054822110300c400c0660303040b079010401e0601c441c5108140e580c82600101d0050350440c3c1e580c040007506903440c0c020b011f403d0340c401c1030000300c924240c207100f115a10140c1201044c045416000040d0600b14200341c02c40c20710110749040c0a40f660310300580a4421030b403006801d84a41103840280c416080001c200d568800e840d2040750b40c1c0da4194509240b0325860010750302501c140f0180000c15000300121000901c5075000 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 53729626 1250 53728376 53728417
    0x90b01020309031506030606090c03040f0302010b06040801060e06101d010c0f0609021201061503050604090b16020d0905010507301107080601080613110d03030203150409110105 78
    0x100f80f42c0f50f584941340c0070483d0f1000034440a42400c3c002290416800c0d15101450301d000d4024400501c00074100418190000340c00c20103043c0300307511020040c0b20092050341d4030b60707403481340394068120b42c01a40340381100fa1020079202e2800000c08042c28056403039031b6009a1200750f0800c000b846a00e0b01c0e905115242d1810b00008191010f0404070b1031003040000303a00c40c01d0340140011103003d07840c3d02c6070b1a03142c900b05210060401915079900b804da864041000d03600c80c00420040c000318000144191080c4060080c08910078151010300c0300a41d0072501a60704800088a900c01d03e84200d60102d1010000013000c1041c8080c840f859800300300e01c0c050200c0d01c403100c1c00b0180506802040000d00c0301440c400c440d40c41032220400401c41440144640d50400d4007041d11858080d01c4540e007070800a0030700c420850032006000c41100e00400704140c0161500307014001e98002c0351000202500304800040e180b030148101c40003681c00041d1034840d000c41c1801035816903c441810015041081d98 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 53730876 1250 53729626 53729629
    0x601061103071b0608090115120f02060304030306050108070503040c17010e0d02070611030322240c1e0c02010f1b0809010219030c020d111c0c050303090307090b01020309 75
    0x34102c0036004068000c4900f2458182c00a00c00c1c44084c1c40c0c0303402e0ba41041d049080003800215210243c50f4900c8011600c1d01c01c61030040c07003c0c51041c00094111070040100010316401d644101c0403100d00f82c9420300d281d5903100080301d042c48100c400a041c001052003d20000070a20100751a9040b000000030b80825144a070619100300410000c00691091009202140d417000c013201c03517808a8030085040d400e00b18070901014804001c0014694041d01d611030501c0090b101085d0b0034008090303c201800c21400702c00340a80700f0500c440d004504560704c0da00c150844007140d650703e415960342e0b041c005c0d65680e004540505250207014101302110f000c041c410b150800540c01c185105414083e03446040720006803c00c200c070560b04441001054041001c260003040740c00395280e04030741440d8400f0080c40c02c82094482e0801c50307908422a01c0b556004a0480b020b003420345400351616803601c587d54400c1696078403c000c5200c0c3c240d0016003007044500880d8120052000050060703074104000c040 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 53732126 1250 53730876 53730893
    0x2090d02030303040f15020c0601050d051509060604061403061501090504060b0309010507080c030a0b0a0f0324020901140c010917120a020a05220b040801090b01080109020102060106110307 83
    0x40d02500d801040c02850410010565002c41b040c00ea101c8040d030030060300122680e1910414440c15010350f04a0442c0b8040044c18411141108a00c8117030504505100c0d6000742d444c0c20444580740154580311000c280c00c1e81c80c00c0b0080751200c0046c02001a50707142c0d80346100020300b240e100d41c10302440d12004100f95607240150800b83c1500604140c0717a18004101c42d00390707407010b00803109010624080c8003192030741c03600300ca40c0008200004501d4410b040041410440c240c1d0000d405000c3c090004810440c100f40c107a01d92103051281c4500c028010a00d1b5030403481859031032404075001c250b402c1080701409000e440c2c40c100d42000000c410505484a213001c840c0118002400c0d40000384d10012024683c03030031500800555000c40c2005d18404000c0e04611400401c00c4582c13108001101040a0120355400600b00c500859501c0e81c0d520124640644511801229031603010030000c202c000c0144200343c00150140c2c010a42640390140c103480c12801c8040310b040902003044001c002c0f03001d14 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 53733376 1250 53732126 53732131
    0x30314070309030201140f0106080702030d060e1807060906031a040c050304051504030207170f0a031e02010b06040509130f0302100c0509030703120207080a06060510090e040602090d02030303 84
    0x280c40210b058502d524000b03084580701804111000f80c0a0144109140c801c0001415a8154142000ea0f62a9902e06a140d40030300c05a098001d41424008030701c0d013141daa80c0300d00623800c070002004c002c080603034200e0b101d03a49800744100040e00e03078800f0081188690441c61020030003101e162000b000c5080441c7c150b400285410011070000000d1104011007000681540400d0565821840c00d00d0758000b5280c00c4640324200d074500503c014409d001c00305024640e01004954103c0308010282c0c94044c008400c0d800038000743d1400c1e0a180103e1a0040c042c2d00c401c500000c080c0d5141c981060100326008101030701e100340c03051001a4080020301c01070046000b2a00903001045004e00c1000c41d64191513400ca1b05404011013030012200c29100059080103507a408151301500209164007240b40c4142035110340034500c10881c8600c14080706611410654005035058006404103400542c2c52070320b94400c1e24041e80c0c90f0340009004c00c0e42a800740c80104402000d10500002c1070300040e01e540c005 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 53734626 1250 53733376 53733391
    0x301a04020d090308060306040b040204020a0e030f0f0d14032703160506071106070e0433050108010b040605090d0b01141f05040317070501090c0e0601030b0f0d030314 73
    0x840780042e09064010b800715600400440c000c02c030a00d85582d0350242c00d88003500003030045070040345981420b4002d0480c02c0391500040d04079101010030300b0b842a03452001d100141001d020f44289400c52901c00c4c0140c40010320800c60151664890049070300e0041c501e102c000900d4a60400001413020050004041032114803880114a428508180d0309100c40030707051038180080c1110000440d20040b41c15580701c403136410295641c1c50080086009071641800b0104088060070038000448030f0a01c448100443d01007007418015141e40040d22000d070207025120000c4024081003041d54070920090000c4c402c003130034810210685079216610100207800c291a901c49091800240b82006030b100c0c1800614507412900d00c1500301ea02030440c0c03145003c040c0085000110b4450f030703c04070f80b00301c5144a0384407008101c8115681080a2084400d0049402542c07500000c42c1c501c1d8440d0090006c81c4000415240c0d24a0141c0304000c00340321403046c1241490f0b20b4020795031601d8412204184140070 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 53735876 1250 53734626 53734631
    0xc071502070503190b130b010602030c011503171b0105040c060f0306030201051b0a12030207020102060106090506031603230618010803090108092803301a04020d 71
    0x1904601074100151500490302030b521801100250040c02d01880d214140c0120250400b5240c0c00c070b10520024000c00090010342010000054242d800070081c5140f042ea100204101000390081018880741c0d4400a00002c0c034400034100014044e10041145050790800c0080c070351840985d2509603041290181c440e40c03d140020408030b40c01c1700748050a441039141c02c000a909640c0042e10602038000d4000c0400c10a141003080f082003000355802050b0091300034850000c1c8444000d02035440240120300600900c400002d11500408480056510051001c0e056a07605800c00d20a4101942d14004058031400c0e03901c503c40e442000c41c0451380114100650320301e03003030003070160541a8010040742040024010000e0314801310507901c03041c0c02483c100c4426110170304000c2c900a60a03508683c03030094280100d0096120903200c0c6105803083d01c0c5d000d0903040c9506280b0f05042d600fa80f0000040304034001004034405580b1400e12507114445c2c1040c0c18043c00082001c07a0000c428000b01c256 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 53737126 1250 53735876 53735909
    0x10050706090c1503050907150201110d1506080103050c040207290106020c0604030c050909010b120d03050c070f0201030b0112140f0916030618080a05220609060e060c07 74
    0x811480440c0f0742c43c07030034140b00c0e50409030980c6903a1019486000c400384084405030030028403e404c06014402080d85650f202c2a004010600818220304820003220044100060840c001c1031140d0489030442c000d03154101c3c0b54001e0101960180c80d007258402c0c11450002c048881c0d80c20f00207500007400c0c80780c0d1115814500081d25058200c001b40d4407420051000b000000d41c03d070b03101d02c1a40da080d9403014182d11640b42c918058000c0c0c071490380e4405101c03004940c83d100000340c002070742952175900b07000603140c2040c014180c1c820800b0140c02801528028805035001e03800c02040c0d840e040c03605100013035044600c01c04440c002000225298800b4080c0014803401c02d51071a003012101c4080c046e40c0d00980103d00300710030f03a4800148045d84948005e50f42c2d850701401c003400d170340c1c12500036079a80072220300c010013036440b02240e5200b0a90840c80805109090045001999230ba038651068150820200355a000d0040c4941d07a03021000300826401550b041c0b12080003800b0540b07006081c403 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 53738376 1250 53737126 53737139
    0x1a0603010501050307080a02010c050f0102040b0a0e04061206020901090302060a0201020408011116140703060906020904240b0d1e060303080705030f0a020309010e0a031220070210050706090c 84
    0x40c1c9041e442103204e503014000a01071a400880c03881d405a90900340864060b400c0e00d8034600b408103000184c856540301240014611140c00c1c010464180280d84401c0d5450341481004100d421600444501120302c055880026003154014000d6150506242082c0c0d59aa80003c1c241d40c01440710314010303500880c0410a0300c2c0240138204852800b80501820b08000c220481c481c040924405001132820b050308800d454410b000380700c0950b421400c01e2042410340c0c10014081d620800d012402603150400e88a500e1804c1c8140030340192400100d03001c020728180d020003860301b0500424600e030355186100004901070340141ca500c508042400301d0b03807034a542405894102d00500840620908100300706000c02c43d080c85ca540022541c0c0c0040e00c070b855109105006100c0e15901203860310503041b0340740034142c21803804071620555100034840512002640315a020006400620752441400608014070b4010f541010520484c6403560510b0f0160300c0d1401622060318069030040007030001070108 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 53739626 1250 53738376 53738381
    0x509060114041407050d0f0603020d030f110303160801092309011d010509060609070504060f0c050607030b0307120203070b1e031513060303170705190504090605030703020306070305090a1a060301 86
    0x11455521040008da0316540124030411403070b0340000d04008140040c040440e002c0c620b109000b544280842e61a0316003c411441103404002030307000454100d2000040146442c003400000b11510109803140c2503001c2820360421002901400207035498010b40160300b10f0300c1c506110260305040020a00d0308140d100c241c10310f100a00f580e8001c1c0002c07010013130b0194009084504582c000c0c54822900308a0840445414083c084010810300a03841400840369041d0025054040700710252000380d9590b001e04005411042c0c0d00035019000719904000b064200740c068441c401c921804080d1103505032070810000e074000c4642d450603484c0707800030f00041e040c41e07010002c101880b80c808100080c1980c42c0034100d810000c0c3c05e00b2030002c11000040003213110f08140c07029160549401079922600c03080c00340c0190802d000d004419481c003240007885140000b40d0504594000c1c0c09001c0d0340d1134440c1c00728094040103160b12114400c412030107002801020744800b40c24590b401189030750401004060a = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 53740876 1250 53739626 53739641
    0x3130f06050306010516020a0b0a050d060e190f0b03030a02030a0305061912020f040c030902030c0423040c0812040905090d0203040b09120604050304050111010509060114041407050d 80
    0x70810140b00300501c90760400211a02c000b1070301d0501580c8082c91000551007003140d00440300c0c0c22800b0440c00d183e55001005041100b4002100f031103050740364140030b090720100321181800038a10341180c070607400c21079100d8040d10b0420f80d0041100c400704004a40b07554050b03880800141e00000e400451507504d4400c06800c08402c032600302d003001114403460f041c15180d01a80d4400480640c0c17510456458002c01c0d0a0b421010f00248207111a6500240c0203207402c01c003c0c0d00900a0442c440a94a403a11070001108400c0040030043c03071801c07c81180d9004004c03c100c0300e0000403034001c5170f010402c03c12111140d01440c06140e450b81000161404c1d00d802a2242c0345960004407080b0b800e94010090b00d05030340c4101007041c0c85545a4001802c5c080d81c0c0711480503180140414807082c8480400200b064480130b80360a01d801040c0c480040c200e0740c003250030b902c01d82c00007030040c00300540318054a003d45600030400300d00d9a14155215031651825504c003404540d0001d54005444100d000f45407 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 53742126 1250 53740876 53740889
    0x909060115080103110105030702240108010b0409080a140403050601080106050a05041803120603060501080a17070302060103170f031003050c030a020d060203060a081c02101b0c03090803130f 84
    0x30000d514585c1c3e10200c0002501d4401c0c10300501200140e4030501c00c00031110030031001041d0103013814514501d00148882801003c00e95400c112425100c0d0a050050b0304240d64814180d61500e184420308448420142c150300714804810000007011910406c0160302801c0384800004200d0f24007010024100d0701c2d1340c40313940280d0400b01510510030000340b8400601d50917040a0201d0364241e03001c0d070014000341c2c1004080341c1c40c0c10004154502d002800c000558401c844640c80040c0c0c41c0300b507041c103000796100280140e101e400184001188040c4503a000950242c2e205d08241a118101281c1d400444402c000c0e22858001002400010001d803805054142c0240c02c0740c81300d40e00490500c3c4000240a0040360f00000800c0780e81d103494121500616401c4117a83c04185010880711000b603c5880c03480051043c10710100c0c4018452258408003070b00c3c04180b06004424050640c2c002c1942e0303d00780c0070300041001c0081d0100301031004201d0320b40401c2240300901d081030b012a4043d0000d42100 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 53743376 1250 53742126 53742137
    0x10c0b090f0d0e060d0b03010b04091a071b06020a1701060206420307080102040b1e0307080106080a09020901060509090f09030304081305060f030906093403020909060115 75
    0x2290071351224011540110b02d81c11022414088110100c0d0240c98602c003015001031600e074203e014009a42c011038022101c015040c179054170b030030504840c4a09030804150300d542d018030345800000c013140d0080080141a0030441d00c8004a0380244090f330600760700c0718002d82c03c0348040000140c7e407400070201e103000011003c000074200340c810202441090300790b4141440c4917400000650307410007141d001040d0050080d07542c1c03512028141d815070083c1c5501c0d1080940800184a52803800c001d0f42e100740c050b40d8603920542c0c41d05008648881d4040c116014081e56680303450007588410b855180600000e8480b1592103501400b40200d040d030080c200220708000c50188801e2070404400c40e6001a0019105500d49a9081c1d000c0003154441c1d01c07040c0e000d10b000403004200c84401025500c81c42c0440c065410707590f1002c0c0c405444007002c050b0a03131518030100303181c245031030449a2500c580e400310950300c00d0591070b6804206080410750760001507901c800010030407080c2851aa141010b207500c0c00 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 53744626 1250 53743376 53743397
    0x50a240b1210090804080a0302011b050a020c0d0f0209010b0c0d0504080706050a11070603060501030b09060108010621090b09071a070206030c0c0307120207080d120506010c0b090f0d 80
    0x180e502c44503950411180740b80c0b2003880740140480c460549015010410030340311030b410303d4070f4042d008003108991801080460034844201a0044068500a82694010f86181141901080039154a20104480302c0a040ca05100940c652140c01c90181541540c0c096860b0001000180b5054035101d40078104039041200348030404021850ba0219829401c1c400d8440240e500c080d00c10031140400f400c92445481d10018605030b040c3c00010031a5800e0b2010071400410724144026041d00f181c0d0180410f900c00010005a846034500d4180c1c1001e02e0307803100d0310083c0c26410509031902c1031000d4484450300c0080c891848000e21402d001080412560740301c00c22001c546030304502400c40064416079010001074001c3d0980c004448000d404603060700e42d10240391401c0d140e113418505000d8010710544034081007105000801c60001001e42e128541d410185406038030103800e00a094034108411031003490002074040d1030f204d00500c0c0d0fa0000d0445200301520052425a25451000411105800 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 53745876 1250 53744626 53744659
    0x90902072616061b03050103050c0108070e06070302060a0f0915050c04090504080d11030c09040e0f060f0115030203010e04060506030c100f080105040213060c050a240b 74
    0x201c0301c1c03010340d41c100c58039088140303801d045401000002c0100c03011007076141c1c04100755a802640f260742d68180940d2444031341241141180c03c24000188180e01c40303a500c036607075030107144102d500c943d56181030341d4120740d6034011030030541004608401680c44802404014880d50055407a0341c100300d1801c024550043d1541d0305014a04803250344466a03e401040b484100d01c0212805043c00d48424010b83c281071800010b0356002c116258412072400e140307000003040c40b1048900650581200074204040502004010000081403107958825500d095013010400c0c00740d03c0c4100041481d50196624020001c2d00c807014001c810020144100014072003485260702c030a0b00150042c000084950f201004240f03884a00d829090340110301961034000707240d0090324032003a607080c2e41d1a481c0302d903a15000d1005034000c41c4075a001040656205001051043c01c8100b101800b0303000f110340d840c0310ba84030170302c60291540007001e9104101114440c140300c02e002d0b0390680c500c213441035003103200c0901 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 53747126 1250 53745876 53745893
    0x1603030503040c21030e0405010e1503010207060e1608010209030604030e0d0605010b0a0f020a02030606040c18060c0b0717010510090305060f06090112050a03050a140703020c0109090207 82
    0x4028148400400440e06008208140c8409010310010004204140340100c10208241d40c004600003440790000700d00d03070b044c5800356904031340b040c4100c40c515440b940c802000801820708800d070150f500b1300040c030219105004145442516102410031030300007184034210440d00c1c2c0c2010106030300400c0303086055100054401e03481038141c0740145490804000250300d0300c14181001d04900d08003000800c0c0c038046d840c014148558141c079440d81c2c0d84010740f020b03a12101c1c115800781d403642201c0002810340c145034100070103160044c81c0402401103401c0c00c00034a40c4403074000c1d00c00280200c03402410030460303400351900511036040c040382e003409020300c101c0381c503605020302402040343c1ca4803040964000c0c41402c0c041d542c0002600c1c3c80c0d2500400591016104075040c612500300b8038000a001440348031515002500940a09400041ca84080c0c0e0f40c2e91181881328108821082000d080700ca86201804034603110358090289174008400040c00c44d5903640140c9415032040110358002003020 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 53748376 1250 53747126 53747129
    0x105040e0a0f06080a03181509030816140f10050906040201030c0e0409030e0306150607030503060a0b040303030203040506090d1b060902120303040c120b0a050402030f010618050916 80
    0x192010499101d18002240500b110790b2202130380e40b05071200c100c10181c00001d010000916200174240e001d540f01c906000103c01100300e00049416080c0c18808070b20408000c203031038100030b41d60700080394032030781d403080389000b5101e8000d2583c002901c1607502910a000c02e1a1008032504180002c1c00c117040ca00e03880d00d10150009045c07540d40c240e14001e09001e026200c16061005208008428003814003410800c034070700d6040c0c42400745100013043c51419000f19010008041c00c0c060034002540ea043c0c03a90791018020b0340d80a00d51030303400030300400307150020806144a650056103900745450942c2c645800076200500740d400220060588991008107070103d02080500415001042c0c1840c400425034404041d400180c400000144c03480000300844c026031107807010945144d81e44801c0d09000009900003414080350401264100c0f1040d0403154200e40000d00703803114068148403a17400c5403513692041042c0040d030b0000c01720000c094425543d21022040c098008111012024404550035 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 53749626 1250 53748376 53748391
    0x1c0b0c0403080f271e031006140102010b090103050705090408040509070309060e0c0f101e09030c0e0601050f0c150901061d1006140403080c03040e151f110312150105040e 75
    0x240303162408566410890400e43c00c1c47c8900400003a5150514008030711503041c042409582000d40d45211401c0043c4410b04036500700001c1d04c54581400200620000e0140081ea5080414003001ca644d58902c0981c41c0141400d46000408203102e14082d0151004820b0f5141c1e42e070004500c4084a44038407961803156074080f03d13005841c0c1d0101e501a00c0340444001007590040034181485095600140303540c0580f4001c841244605645404000490800303c56250005006200c10010300524a0150140798410f13000c2d101551100e03030070001c013010125410900c40e03440d40005c0140110380303131640644401b480e01d0641c0ca40307000e80b19400a00102e1040b00204044580c0e00d0b007039244582c09440c061030f0300c4016079580701e0000e131b050340e90703074104d801074100e190400c0002c945003990000c2942e024103001b83c034901d9400c08507441d880607070101c0c1d80c0034028440e80c04404e40503203000f40700030a0000d94207a0380401d50f04080300100e40c104498110780707060020400040c041c4280607000a1741c842c14 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 53750876 1250 53749626 53749669
    0xf0f0402180c0d0908040603050903041404090f0203161404020a27030c0b0c0705060414010f12020d02030906070822020307090501231c0b0c0403080f27 67
    0xc8042c5015200e110301071140c20100d00e00440803003003044000c0100100d5440c1c0e0b80c1409240c4415005507100c0c8218410004140041c8003592a44c0c141074000040b0140141d480000301c8055802090404645442c0c0c01226211100207010422000c002130748651400d0300c00f1400e0441000e00946044030105480c5060611030310409030611111091a000c2c40d8841c0004100036a01c1c1441400c1e0b81100c0054a0507006124010a5034201801940d040740c26900310398404040b08001518070040b4107042408000740d210351007442c4001c5000400c030160f0258001a40c903c0c15410711420403502800f001c0400c04110203004011041c07000e0b00c491018034864402d500905440081d14190059021400d16405c0100000700d88561901c0c3d506001ca0304001c0b00030107000c00d410041884800180c0008100140b01100042110313080510b40c0711020f010f000317107469107030b85072072406070440c40b04100b00060000e03a0b01c50034480080360707980c54181030444800101820b030010342e5220107000e080c502e00b507 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 53752126 1250 53750876 53750881
    0x8100e0402061b030714060c0901050c100c0203040501030f0c09032904060f0e0a17090a0803040312020d0504050a061409101e1806050309030708030f0f0f040218 71
    0x40d1201c0440d10201020041c2c02c001c100400c00f000d0702ca0300944415117501c0407822400d10b011102041c0b4510079034500303e40b40e1030565500d0055503181c006a140d100b00e0701c20030121500c0c0004912495005c83c0440d0000e686542c40c082c00101542c401c80c0484240504001100a006400410b46c90650794040025900c080d180c01c1c066242c5c0300044212181400303414240024010030381d010107802c22010311705000c080f5201141d280e507021101001460000b80b414405100340002c40074007484500107000030308840d55002a64a541c005402c10355208405400c0601041c0c5c04100748000d8459500b0160b0405280c48001002e0448501c150710074081b09565020301c01800a08540300c80c00c00030a1038031308860040006010420010360380800010403018840b08500138142c0228002c84000b02190709410540d0403541c03504050300744951840700744044d01c00516031001451042d100000c0300500e41c030308030084201048001e407901001403c220f041c040541c40e09052482141d100300c08031032054 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 53753376 1250 53752126 53752129
    0x1302090603131403040b13120203060606090415090f06050126040c091514120304090c020f0a080d0c090308030411120a0b06100302030f04030e0303040b0406050309010c08100e0402 79
    0x88035501410500f9010005010500c400d03400040d0082d445c20b50303042e100c011f4481103003500c0071a1400d0042e44c144e01503000500280340c210300505144401400100314104400004005402d140c0c00880486858500700381d910180c0d0310174000204424078000c0416010600750160007a0840407c512420400002500388050001240b0041240c0a01004095240003108e000396610b4000c4999403030006c0c400328100c1c80c284034040f661203010005117181c9440d060030b050007080342c00403031402d5014a0003102c0300040300703110400481e400784610658900ba064417040849100e024000c2c1448540d00041c0701180158040d82c0d4050750110056000c14002d2000440b030075142c1c91031890500c0350700310780402c12507138640c00344c01400140d55038118484c03081c03800d13000d0f070004607003002c50404d40500040200784039486d030402000b4041c007036a14298a600c15050a030340241c00240c04500004107101a002d024031421410310510314107082035003072407403520310145a203200d0440c0c0580e25034046030070b5 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 53754626 1250 53753376 53753393
    0x90414030f0711010311131806030807080a0e0109030803010e0702070906080109110913032d0921030e100201020c01090f0212071202040e0102070c080c130209060313 73
    0x7990118840240ca4100e00d1034414884442c41004030700180c00c01d91105100c00d21903081d510484645044841200d0034070401e5810a8440c81d442012192a180c00001040c1c0301c074002d00b44c2900541c07011307076070742e03170413038020b0807802c00800168100303c0c4070302c8204042203000040d0390660304400c0d882c0d0301549440204900e0040c40b03400c00004107181c201c0c00a00c605055211101003841010101d0400c80410100124550115540b01c00d016480c4149400280324005813824281c0e0b2000703410f10b000890032140c00f5022002c06000103c2c0404005006040108941182c031011800244032416019540241012070b042c1000b03001d841021003070f5060078000e4050b41c0c0c000c61814020400c0c2800c5060001c0c1c00503030303c0002e900071300032480d000d08030303000c041000e1094426800075101480919401d00004113415400285195400c0c408640007490f50b540407001030107490001c01d9140b88041c104807003258000340608102d48100640c54103520b504082c0c2c0e503c916144080003c0c110541001c290 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 53755876 1250 53754626 53754637
    0x30e070602011e02090307050409080403151d01090c140f06030412080106090608010b0a052107030b010309030c020609030102040b161a01030317090c030a080904140609041403 77
    0x14140506000418115415480b0300d05900c0c0903400c01003851102000d080480c13003030011460b01a0041c00040c402c5043c56040515002c0c42000a185050707038a4958a01c040c1010098400f8a40c8030203500394071022013452142c40c1e1210038001c210640c0b140c1e907182103503510b9104041d10b06041504a00450707440d20740c046920034000e8190340d0380349400d18082d03001ca40c55100c8007000c218200d0000c01c0e000e02c211540b1090b104103885558031a42080d4948007e030300066520000c100c0100002b914044e005681c21200c040da19592140d2814400130140c01d072150210124101440c080011000c17940c00601d000140c1e4041d5013456941c3c0f00d0401180c060322881d0810a240b40000501c900150030b0190015615030003404146030024010311840d410341d0083c403001d40020504a094540358a40c0c202d426000342420b41104c0d042440103001c6401d010080d941580c03000700200b80a02ea03420a80141c03200014524007042d5245804c0d00040c030718a00145c0050910f40c01c01d00c0408494804004440 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 53757126 1250 53755876 53755901
    0x5070f0201030b100809010c0512040308060307030807030314010902130509041703090a030207050a141903020406150315030210050c03070b040c0503011409060a091511070b0903040501020303041203 87
    0x200040c4406406042c1400a50342942652301c0c1102844206201d50140c503052400c444078001c1544a40e181200e0702c90018011940c0340c0503600d0000000303920a40200000c0d0300c42c0e180400d016031400b41c0c256100304140c0c00406447d0040001118850104030000256141202d07000c005441d5800d01c0480001941c010004003917001080c406030110015064003814403e908492003a5101c00034042424800e20801e00c1c680403d034010803407483c00307030500f4106224142c00201559926000102625072507407042c4491214030301035001d41503246c09504248a44500c58000c202d10b16030115600605103101c00041040120301d80046410510842c2d14098004140850508080c1400d501d07408803849660300c41e62801062050300d522003402148190f4102c005408030340c3d0784284e01d00c05003500c040201c2345812140980b03c2d01801a00c2a91700c5d5000360300c28603442d2a12440d00c05024030002e410b2100d564400e0104206603030f0300000b207036880359104000350706403043c1440a4003c0d004455451 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 53758376 1250 53757126 53757139
    0x3030f0124051b1e03030907060203070f060506060d050114040f0908090d0305070606080d080702011515050409060909111504030312061d0603011d03030a0203180a0503040f050a0605070f0201030b 86
    0x5100d540000141d4040c0d8400015035032309541d619070a03643e030710500300c009103200e100007019008200746a10195001402409480c130f8644500a0a0704a445c260421403020310940c10034ac0441c00c180c8515640542000003c00913040e8903102c10003603000e00e00d50180700300c9080111400b0180700300c0a40d800c0c00c0d40240309001c0c107521000701903201e2261048e4403000418140002d11958414022100c80000e041c3c4c142c0f03061400c0800341d138006548802284c0074040708000015043c400c1d0701c0707a90003c142030b540000c0d01d2040381c9080d181919400c1c0040d48251a10460a6100c2407000d00b168100c0e580b60800c04031004e84201040054845588034081610040c01104031803407001d810184a410100c00070000e40b1100715040c40035841100500c0c00d20351081c070009811200607030003190028414200042c50301a4800082d1400e8400881116260804201040701c121100c5030b030405030500700e5000e00361a040c654002d060340070b404005004501c2d80d03642d500969000c1c1d4020151f400d00540345 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 53759626 1250 53758376 53758423
    0x20030a05030702011706090402010e0105091206160306060801060305040221010b0909071d0402280e010902030112061503050d030917030601020a0b1803030f0124051b 73
    0x1a00c036003102d002030b408201414004842c0e440c3c001940f42c030800009040314265150364004682503060301c400e09060090400140c9115a240c800803426140c60303000510840c0741c02810100c050b200c0d10540c0701490300344034007401129080f5150505440280c9800540d540e07071400000ca4103100d00101c0d050358048142450740041040d0400c6801800940d06150350351648200300e40d581030f9a204480300c403442e601408488200c6e04009a8000c7c0c0006c01546610301c880500c2580792542c88400c1c4002c9410800411418050001e164010038140c1001c5080d5890100841c4004151102c000c0906598818501c102c080702d9001d01d0140d0781150440d080d610800c54084c000306024a01a1403e42e086401071580c2d92241003100c1c40303580c040c0d014207200b954a50300c44401d02c07400391000c452902d2138440c9102e28032041018500c0303030741c84000702d1500f5450151100849040b00340c3d81101090480c03804031549400c07508a500c2c034107202d03008001c0e220502c40e40904200820003080d002c84403041c0c4 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 53760876 1250 53759626 53759633
    0x7030504060219030801090f0f05090c03120909040f05010207050f06190207052508010c030203070e090912031506040b0703032f0f041203020703120e0102060420030a 73
    0x3510550351540c007114118440f141025049800030840240011103070310062014907055040814124641440401c1c522200b0405200340c8600310b815014690100c0350b29009071070f0400c003d290031580085e40354030f00400c3e90b0224484e1100104058003e424001100c0c0800c41c1c250304407100c0c150014140c441c0d0743d4644a4882c0c490000769101c40c255010340da280480001c051080311000340e4044000c1405002520310020121b101865100c00e00860100002c4d4241c001e01403003041c5512070b900181c1ea442c02d100c02400225001d08100c2c06080d00404002c0c1511000585840004c028078600ba2295902c4405207240407040609542262001c1340010320078039150081e1074014400c1d1414851540f5540140c041d0041c00c0c0203c82c6603e80c2075240190001c2214028101071041540303640ca85034490301e582c01c00140c151021001030b40407072010000d00442d45036a9125102e249000180142c00e00700003940d480d000390000e498030815031258008980e0440407410f0640014081d80c000224604 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 53762126 1250 53760876 53760887
    0x7020d1a011e06170a020412080a031104060f0e0f030d0504050306150607060b011218020f030f0c06090a050901080706081f090e070f08030a09080f1e0709020703 71
    0x20902503288902c00d40650070b90401c0c44540c00f500c0c82541c038601400140c68410034400703000b07003440800f02d070300f080081224201418140c04241c090700d141c43c1c0c0d6565100c001130485000300e90300000c0c803200b48818003116a11022080035555145002d403131005128001455501301c0c0303410180d1601c1102e4680c03441e290020050700072120100c0940311583d68522003011400848405030390722130f02c10006200040c1055025985415042c03512051142c54144150111751031281324030482d915001002c800c40c90085002e80c80d04505401070300c00540040e00e00c95440c2007101da491b01c03c15020a100c502c6032203140501c401400028020401541c1d0361090a44034240f0740100400241150001000d60910858500c550b5044880704201c981c41d0000080051034488500c6046014002d000a50043c02903170b0b040141407607030013841c0e8407035003400090800007040d0300c1956160490144040e1181d40822002140641030f1240c4520811000504d400c010b20380e0801c0041500c003240d84018542d012 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 53763376 1250 53762126 53762129
    0x3090d0e030705031504060204180b040e010c0801050609030a1203140106031505010c0809032a0306010b031305190305090a0611060106180512010e0d11060402040207020d1a01 77
    0x1500da15000189a10501d91525110701815400d984400d000703282c0c0d1001842e0a60788680251b1380142040c0e00c6403040020811440000c1e2403542d22003e4044c0c140c0f805104084a458080000700441c07061702601030660201440f803107104180100c0c14a0064900b80203d1001c070340c0c8072150250b80c982c8088040d00402d0000801030107034402d0000030035154000e00c602d2140c28514035200040c546010011540d1500c0c81000700c595000504c07015002b070301c04000d4204002341e4510340c04c92400b107036000100704149000016110f548000c00421078070081c0c008582c2c100e00c94030005159018a400d207a4a4281c05c840c0040510440d0b1a800b000d15500c880942112441159441038141c1c0d01c940032a0315441398202c810319500640010081c05008012569090468841c50804117940d800018030800b50074581126a075194034096108510078041e801c0d100c1190b060148008982490540d500c0c070004100900580d4002061002c0d0348d5440c9100c0c2000c0d6000c3ca240201180d61012011400400e = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 53764626 1250 53763376 53763403
    0x6030803040b2208070b0a0219020705120c0a091109030304060504090506010302030105032a030708030301210c1203030f06080d02010605030f1902060405030d0503010f0f03031b06110309 82
    0x2034003038080c0300f102a0b054035040d05402100003410215542c840b00700c0751001800030b0780c00b95420002c568280c064100c4c200400b81c29500a80103461034241130011001410b01c9481858108a91007241540c41d14560030503501060000500c0c040c0d801001c40092190301880c0354540700c08500028055409401041515841e900c148007503103480e00194140d000c28090158550001c80c0307007000c41c0d440e03000c103060300c0030041100c0c15a1034606008603080486941000150782c10000c014002c180845282d2050300340b107503441300081032840c1c031a40c003c48aa80104256040c600b41c80b04203041c460303000f0b644080202002041280d941d414a140d4a02039002c4910240d401c221b40010715180100b007102d142c40c245405030403124861541d070b0000016604089901542c2400041620380f020800e240c0f00341d00d961149507903541020601ca400c403c4c0c0781c0c0100c0d01d00d146c0c81401e01c0080d42c030001e03415410404c0350803110003083d94504003000d072070046480c1a46500c0402040310780c8400050b0910203012 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 53765876 1250 53764626 53764651
    0x15180406090b010e1803120105010e0a15030218030705010e100306080601240f1211120906040506130f120201020702040f0507030b06040f06050901020a050a0506040b0f0f06090a06030803040b 84
    0x145d1403180d268050b58521200c111100001002194000c2504501c443c1004004c040c0b16612031032801111441b2a44400010303034049840c0741100304104044d800580d00320020304100e80b4180000744895628a0007c2c02030b103079070b520040482e010350082c4016007040c40c1a100c996840b680c20104e8039003003e100c0c5940440700781c004403015000d00d11869404000d0350700c400c02c0b40e0211074214080c1581c40030440490000f0056003000000200c0082d008100004c060000340c14a070410a2a046c0050001c0c246895045540c40004d200306100c400c25561101251600d4401a00141e0090242182c0a5007160401d03c3c8444501e820303500c010312407038550724200b107188943c02c2032010310300443c000e01001307203840101880514000c50140054201c140304803205050396684007030501c50040001c4440ba030082090204101c000d40c109540624581030318516032030419000107103900d0141080e4011ba0704040441c40040d5260401e4001d1904803020720355a00f403605c3c0a800d81d0700e00701c0e90101100c8 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 53767126 1250 53765876 53765911
    0xf13030c0b0316030b090109020c03040b03040813060512130212060a09030906030207050712060b060408030304030801092a270906050a08032b060b070b15180406090b010e 75
    0x14000d1045c541251000b41210000340e081006613002903200c002d101481d032106010001e5411010401140b1031031280388019160345d248807450000c007a0f2500071005100c0144074100100c2c2c0090b041c01e5100c01d83c2c10640e41640001d0002c070f1a10240900380c010180584801c001c034021a5800012000744641c1d88d00790300300d03030f00d0380304804a008105000305160402c070001c001c48400c4038070200c6100d000d68400500b032040c080025007a035100c0c0c1e1240c01c0c160004000c00050580222043c3d0040030240000d00100304415400f50004041e0440d02d40c8001c2d61702c1c1100c1c400c510610a050754040790a560b092045a5007000081000c414030818010a00b050804a61800c0000c8041c0c110b50b00c843c000e508041e00d8150075810341d00d002d401c0c00f080c0c10309041802c1d12504107001c1d40005040c000301803a83d8814908044150b803e00624106800d850824008410f40310000b01c10800303100010001c20544592074044050500043d0207400900001300110f490b85001186038000d411a0b02c0600281 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 53768376 1250 53767126 53767171
    0x60702010b010903032303040f03020607020106050d14100f09141207080c0f07060507050d0e0609101704060605030708010606090b03060f1e1201110f13030c0b03 71
    0x22801c0404031800a100103004000080c003d55400640d02c8203500f6600240036910320108890f042260103031200d910076101c2a045c56018440306801052034402481031504003400b00c0c01600140f900104807568036082d20700a0071040c00580000e6121140038019501c0903900c0e0005809083d50513901100022001250444001888019100e1034a041070414805031241266604183c0280449006070f200c00c8000c1c4400f808900064415526641e84030740d268103240c0d103070021030014481844280440c1c6142c658404007a90709030301c405c85202c0b910142c1904203da1500b00750072115a0058903609000030000d080d084502664416000c5850319951681300900303a419910400000c11021502441544542e9006650003003010f461078000104100100c1e8a0a2940b41d200c4409140103820303480d40d2030700710f0060001024040081c440200a01030000342c51180d404401d450440c0042c12141e0302d003e2452003c01140c1080c142c40303032580d40700c501c44059032040b10a480011880946003881 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 53769626 1250 53768376 53768381
    0xb070f03050c10020d1a1018080d020d030c02010203040c05060f040306090b07020606010807090302010e1f1e05090f040504031b0501050901051006170705040f14030d11060a05130f0b06010206070201 87
    0x100401000e89281c241c0b00740c8143d50000440602c4123052140e0180815060010418605c13402095030050089480d162002422600c0c52848034013107900402c1480003140e04130b50b02d0019540201d0352030780c3d95250802c20900b41e10581d4001000c4504010a810a2051408049204411540a03922540d454500456400008480020200d481e4100c00e1025520545580f680c800024140d0031403014401d614450010140080200088c0c494040e1140300c185140017462035200d0382001404d208906001801501002ca00305002d1640d0f14002030a06100b2003400c40c0ca241c02244000750107009062040c00f030242140e40c0d0100b5800c1002045802a65064200c02ca8051b95a0b0280c02c8040182d000f44d11100500780350208841800042041400080e980005080700b001030054030396080d09041c01c0104010341041030040f44c00c0c02c1024480007181c010340c011043d100c00140c507941c1901c6c8030b00a001042000e4100500c2d40b4a24003005400c0c821240504002d0302118516520340c90124203 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 53770876 1250 53769626 53769671
    0x2060708010308030604020702040207050307021002030c1f0f0c02030a0e01050f0d1a06030108010603020108010812031803190c060b040501050f1504091104030b010f0b070f03050c10020d 82
    0x26440c00c004001240c5454003440c4c000c02d00500c05840c0c07000c103400103802c3c0e0700002019612030700000f42a108620b09035000f6040d0000ca0b0016604007605402640c2c0c565104050307609000310401300781c4102c100b0f540d01c24498002c041208020346410420025540e40100315a103011031031a0a4180c3c9940c00344045d20841c41e8540d01441c81c0c0004440c3d0100682052400c07014100b0a8105198203942d6020195020b809000000030380c075840c2d400010000c01040c0c0c04099540c0000200048600b0030208882d4010307112202401c042c00c075003003407500d14070500e100a01051001400215140d5001502c00b0205000380c2c1c003031044036900c404210403203100f0302c03c85030700004100e070704070070750404806040c881c03003004584500301aa2094410284d5901e0941343d0301070130002409000700b103d00d80816014111302e001007249542440701e407003101e100342040503040c20601c039180700815200781c0c01c442012150710151502480080002d45c0030390013035401d6030710050600d141d4000c410b2a0524188 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 53772126 1250 53770876 53770891
    0xc0e04050307032609060912090f01030e0709060b04060809030a0909050c0d1503020910080703170d0f0902100c03090b0c01021308030a0315030209060112060f12020a05010206 77
    0x6282c104190703001e032809079030007060b0381d5440602245a03401020000c00385100d507407900c0140072589840703110142410200780d50502025001d001e1180e00780c45a52282981c40300a0a002800304843c10500b440e000c2d041e0301100c0c1a0342046004103500000340e0160040300c4880e110000c40352510050f4070b881e40609c551a00005181503810000c000040d00f0040d04003e4440400346001480403008003a10081986150310240302c18003042103003450700d0020740c48240300c1400a60300e03003880b501d1521501c03548005040c0042441201d06026154002c0350700390000c0103400c002041034044420044c1442d850164818003030380b4149a0700900800031503900300e61540c0c4075405d241c20a82d00408641064544818541d030912082481c01c404c17069000180001e00002c588071403a809000341507960740b140600114080d81c40801c0140c441c2317034403543c20600900701074034500070045014000b060a07074044036a034059400005500c1c2c000410b4010094000d507144090940c0300e80059035565800e41e20310 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 53773376 1250 53772126 53772133
    0x62c10050303180a09060603060e0f10090f180b040203100507050406050c0a050a1b090605011403040201030e1b041103090712060b0a090f29060d0e030a0302070c0e0405 74
    0x41902581c005040710600c80004c080b0010140c445a001045480c0e0350080c20101e643e6840034400e0500310044a40d2102450090180c14030b05407070110300c00b180b0783c41000d8409450b8000302c134002c0a50f41110000034074108070314100000300c0c10000100074040c0d500364007900031400540219110350040c14440c54080c3c4500b03240601d8a501160654030014400b160f0703002e0766603c00002402885440050f40c0102e201c40d80040b500020401c0091160340101c811900d0b00310b0401c1540d03080103d6070310702595041c030644c6a9940d400103074080c0102c10303080c4000e400b80101d80b880004a03000d441c094800309607003c0150a904201112045c03005548440443d0f00044003000205050014652201d102e42401f213894400304c0c010074a004d805800c01540c0b40d4032226002c41d029420700c9484034a012a04182d00900007440c0071108643c0c05284460150000107400b141007030054114100051444003200e0740c403154858014000d4000c1201196076907544080002c000c100c10b03500300c0c01140c204028 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 53774626 1250 53773376 53773387
    0x15060d0201021005070302091c02010e1e03060c0406020f01150e0403090305010608030d1a091801090b0f1501080411011206080d170702070f051003062c10050303 71
    0x200201015081800c904510800d0000c00044401c0c1c0151030056009881c0540c035007140300104549850310701001c01c800706101c004030300540c5e40b1000c0c5680d0703404195448510048030207191021580800700d0a030709072017403000740302c0780c244440018000c854031542a126151910342041e0700b038400e55030a0b512001c3d40428280441c80380d03402056005442410100c041c0c13035032542d4242c00d46105900901040c0c00200342d0324080701050042c0e0f03181070001e4050ba03002c1c070080c0f00000d40400011b000160203060300c13070307080e19841401d6004004407904005d02c0030540c035001c5900c41100c24100c03002c802c00c2a0b4022442d07450350081c240303240102d07802084c0300c02c4c8040d00c3d001141c2104090204400f0640c941c800020001400d109252540005988140c50400c0c3d103101e00740800d002814140031036102480400c207130010410710a00381ea808443c6d0708243e645c221000c6000e41220380242c0313803042d0784e50015101c03902c1100c500380d00c00403420b841c3c031070a0303942c0c003c2d104840200d4468690190030800c42c = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 53775876 1250 53774626 53774629
    0x6030115030b0a030c0501080f0705031b04090f0222180e0114010e04020907050408030a050c03040e010b0c0c09040b07080702071a07110409020105040302011404090f0c111506 77
    0xc1803140e00d8030516000484181800005054811507441a22800c0d2074000c24080380d603000780340a91040413010030322010305008100514900c0000c250686100d006e41c1000310103903d07242102c0c000e000c101c200b802107140408190009500c00a00c110480b01007064080d4420318005010046034240345129440400015000c4068014510301a46035581c56044910500303090b00018060690454120510303d054030510140d000c0282c640d0003404400d2000b0030000c0000821115158460300d401610740ca215141d2600c2c40c02540c102c000a1390880c40003040f04500000504007a000b800110307044e2884800500540d200252406484507405500181500d80101241e9400010910446d0740c00c658030315494a00c5105090100d0070100c00003502e100780300302501e1003c0400c408940030003562200d9800a00a8800d5101c024180403996075508101c02c541c1003603400a0a1000090006458904a8500a06c08040e020021648803219500b0541001680202c0c04103000442c25198903480d0 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 53776982 1106 53775876 53775899
    0x61206010f0908061305070b181005030f0a051807170c040b13050702030c07090609110a0c02130608100504140d020d0318050307030c0c0b0702060301 66
    0x2010f0041c0f0707201003092600500d8140800c210880d95213042e83c10000c0d0fa91155081342c01c04580440c002c10180300003000d441e000c4a501d4202592918165400c0c002502e124121114201c0024170098681c0c3c40079400c01001040e00c48a5924218158a801001c0d040956401b2005140c004c040780100510403070000111400d01c19204100040350300c84800c1169552210f80307600116400900900444124603402000d66048540f90010080500000d00c0358000d4140f40005100c20410b640703050394051000c030340d50703110100c00c0750b0200003440b44420b0010010943c2c4500000e111a02009806110404890085014905400c000052502407205a030042c0c10415411101aa011a55042900850900007045015901413504500c0d5511008285100000300b0900f410b400005613455544602072035100f01d625100100564008c15100035003003001400103001800050 = true := by decide +kernel

theorem cover : BRFrame.Cov 53597126 53776982 := by
  have h0 := BRFrame.cov_init 53597126
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 53597126 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 53597126 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 53597126 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 53597126 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 53597126 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 53597126 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 53597126 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 53597126 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 53597126 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 53597126 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 53597126 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 53597126 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 53597126 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 53597126 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 53597126 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 53597126 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 53597126 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 53597126 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 53597126 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 53597126 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 53597126 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 53597126 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 53597126 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 53597126 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 53597126 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 53597126 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 53597126 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 53597126 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 53597126 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 53597126 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 53597126 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 53597126 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 53597126 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 53597126 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 53597126 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 53597126 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 53597126 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 53597126 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 53597126 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 53597126 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 53597126 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 53597126 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 53597126 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 53597126 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 53597126 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 53597126 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 53597126 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 53597126 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 53597126 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 53597126 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 53597126 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 53597126 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 53597126 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 53597126 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 53597126 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 53597126 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 53597126 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 53597126 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 53597126 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 53597126 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 53597126 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 53597126 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 53597126 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 53597126 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 53597126 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 53597126 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 53597126 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 53597126 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 53597126 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 53597126 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 53597126 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 53597126 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 53597126 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 53597126 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 53597126 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 53597126 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 53597126 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 53597126 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 53597126 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 53597126 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 53597126 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 53597126 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 53597126 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 53597126 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 53597126 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 53597126 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 53597126 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 53597126 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 53597126 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 53597126 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 53597126 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 53597126 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 53597126 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 53597126 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 53597126 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 53597126 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 53597126 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 53597126 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 53597126 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 53597126 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 53597126 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 53597126 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 53597126 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 53597126 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 53597126 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 53597126 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 53597126 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 53597126 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 53597126 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 53597126 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 53597126 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 53597126 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 53597126 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 53597126 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 53597126 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 53597126 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 53597126 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 53597126 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 53597126 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 53597126 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 53597126 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 53597126 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 53597126 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 53597126 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 53597126 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 53597126 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 53597126 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 53597126 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 53597126 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 53597126 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 53597126 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 53597126 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 53597126 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 53597126 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 53597126 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 53597126 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 53597126 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 53597126 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 53597126 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 53597126 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 53597126 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 53597126 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 53597126 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 53597126 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 53597126 ≤ n) (h2 : n < 53776982) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
