-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_1802
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T04:43:38.025563+00:00
-- url     : https://prove2.me/submissions/c2e0adab-f397-4c1a-911e-c1e012a13e25

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 323920863 ≤ n < 324100719 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 323922113 1250 323920863 323920867
    0xc090a12030f09060c110909030d050c04051302070804030b040206040905010801060f1401090e1e0a0606030e07120b040305250303061d010302040b210f0606010e0d060f11 75
    0x41d0030001e00c02000d400e0780502049180602061660144402400d443c0c0c0c07041c5004480365903903050140402c000b4103490102d11051044c5a030704441801110711030300741408542c0c0c841386040100200c8540501c00d210310a8070411505000c00d13004821201500d4121008103021344079403011903941d1050b80d1240006619003030021907a01410b40002c0f0803103201c0d00030026599240c0440d44500c10054200a000c5034141600300320034a2003a24035540220411001c1050030800c00380c0c0c3d0b0344c0c61412541c001440d69038071024000301e82c151149109001c0e0000003070852606203650208401b01512018220341c1039040000d08161142049910217441c0c154071804800400e1400c034042c016a030401c03008a4200403000ca00e031b404000c00070000c0c0f80b820310001090b910b16024880241040c00a085d003140046210000c00c00d030040450400d1245200100a0701103581052030400b00003410060410031501c03411a0250f0b2011404846a9006840021114900c402d060020010900001c01314040 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 323923363 1250 323922113 323922149
    0x6170a051017060717190e070503010911091003050a11030c060c0105040c09020c0c06091203160618030905010305060d0209070e01080901050907030312020405030a080702120f060c090a 81
    0x4003003045400741074103071030b038054600e22902c030800e449170100c5845500c6554426201058140d030f8206012030300d4100c0648118581b580302203400d41e044218150b070b1401c60b500d6419441e040000c840e1358420350f64058444164215070701d454807642107403005041400c0400c43e030611954103206494032840300900c06959221a01c940c0c44c00390401721029a018000441d0008520345030f402100e541c05c01c9200a081c0225020302000380b140c002d00c427800d41000d0700c00070401210300104001c0005481e000c0742c249640d1070b545400c000b55801d0307030031103000c0c442514110000203802426500c140c0c0c2003401c010400366220808070307405050711403020b90300200e224280500d80390040c224101c651740aa0b0380c00510f9903144101c600723880064480c010030303034401e02c07040002c42c0c4240e0000401200500d4054a01690358000070b191580580e0155140310000a5500440c58110145540d1866040c042d00d0403c0194a4098580c04020221100c035072001410f4003107541c8405001c1e001e09a12817801c000010 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 323924613 1250 323923363 323923409
    0x1b0c07091508010c030c0221040b040806011e0b04051005071205041508060f011808012d050f0403210212090607090f301104050106170a0510 62
    0x1a540310b940002c0d4a410540300541e8400c2c080d81902401d030b50000c22110440d519000080003d5410110b05c16805200c003143e00402c09000b440140321100c0140269410320b8045040c225040580841000d02050100300c15451401510704840301103a00d080c501c180345800b51900c0c400e10f04003c0c22038000c41c0d040b4112a4025000c1c20030b9030354003078005583c0001003d0580310240255070030783d4401c0300d007982c82e115036205007407041c1c556040d18450365420341d030342c1c54145c01d484120440e8070f400803001d10034007140008007440050300d90000e03009110394202111500640d200240c00581007000381198080d1461885001407003000c003082c4115503485a200d417060710400c05490540c01030007000c3c08038050340d1180c02c007036045e5000c0c41500103200b842c09140c440014181080703180d0040402c2c18040386110f0f9814980003031400350788048a126041410002100c7d0160007032010b1100c5400108403541013800c4080c0c0c064000308000a01c0e0302e442e598062004000e40c44512480303001140000741607 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 323925863 1250 323924613 323924651
    0x604060b0d090c050402040e010306020c0c0d061406040212151c030c02040605150f071e03020a020306010819020f1305190609050402060306060304030e15041a031b0c0709 75
    0x2078024800c041c0c2284d100c01c2000142d00c1280316020200700c81e00014004104140d0007803010210200c11146031040e44808030b03207000004582600c200350740d0000450810103102d0010361040d82142c0031454103501c0e9480210204000d056070f10b002034505882d03c0c1e5510386981c405c99032004143c0c540d5412a0610700245241c10300c02d01203000f6400c0000015441c28200c980d0f004080031401a5418001300455a8245030071224080e500c0b1505107400c55108a032584c21410703810f000e5800f60540003d070303005151a081040c1e00c04200d41e80308180c0784086140400420400300e80c11100306c20350f40440030000348071851500409502d0392230a402d0224015140b0340c03144038240f80d08018006c1035500d85c50b00046138411100603401560810004140d4074101c0000c0d9402407003801c00402c1401c8001c04500c4100c01030700e58048000700000d080c4032040e150080b5050014420480074554030b824103c0401c02018003800d601034600201d00548820b4052041034040d1041e01820028030000689040d00c0c8 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 323927113 1250 323925863 323925881
    0xf012309070b2d0a17070507020904060c180f260105010b03180a051914010912230f21130308060609011d060c01090b071b12080604060b0d 61
    0x9080c10700c0f4042183c0003d84144c90741c60306540c40d000e0904130202504800b590740286800304000007000004016500e1401d42c03402903010351000100c0c0030325068080d06410039541d03030089195080d02d003004910010b030884801e44800e402081d50845606130f03840002d003148603000c02d031542401c0010451001c1c503030140d88501103103c001062020329030b0006880b0906200e0182071a000119041c046580c640702c9003c244d4861442c07040d101090f0f825042c21500f0100e02181c98045041d07100c40c80c20313848000080d4400718100b80c07010302d004224905c141032154005042040b40041b452003240c9400071072910000700c070b4070120883c524248150ba25a1800c0103c101c0104a40030702169240c100b0ba02a180c04013130603101c02c00051038816040e100842d104404e41c0e4045400c0244807440c85c03080c042c2120741c0d817080e510030985040994000d845c900d120001c580b01a045800c8190116402d0340d41c52480500e0340c140780c0440c3c1c90740c5012901400d129001550000400203000c0101081035005542e1 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 323928363 1250 323927113 323927167
    0x60c01090215040305031602011205090709050903040e0a11090d080a0315050907031d01020a0c0b150d030c1b060c060605061e16020d12020f012309070b 67
    0x403250910789000c0c0790380510301005d00981d1041c440e04568507035020300012441e005040010000310350785144419610225440c0354603811220081025504501810341c000c411720003d903040c02e0900340c00314130904009180203442030312000d401a9004170300d800c44441510160020f8084001810500001d0744081141400240fa15415850241d030289200341681c00080c0043c10325169031608074003810311490042c0311b0500038100079000d150b091005009403006500c600c107030b030b42131030074081c0005c03d00400f11500340c00840714071101591f406003840503a90f030604241a4102e040c0c18800c1e80c050032002d034180c0e140300041020410369001103807020544c1c41100c0a02803e43c42d030b014000340d07014290f955507a010710060a44295030749080070700382c1000400030007007201e4810740020300d040e03030444c000b5102402206010000303194188007000b03185450b01c1c0280641c903000c800420310a03d005102424007107800c00860800c00c4244035403401883d8418031942c95201c88144001caa03030450202c803075 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 323929613 1250 323928363 323928379
    0xd0b1c03020d11070311010e121609060803040b03011206020403051504020405070311031603020d06060302090901060c080f07320106050a030506271203040b0114101b02060c010902 79
    0xd0f05000010408190381d400540d10000d00c1545005580a800109206070b00c040081d8446081d04010050203a500071420380b581c41c81460901c40800b11242c1b50442c0595030020042480340301801e90807207044411984c1d11080f10752080c10410001d0013241c00090150007040c0e141040d80140d044841e02940c02194100030301c2d25140000ea04072240030040500c80a002e200088120822003648640c08145081c00340c90b148203c090703d0201e03070003034000d140420790200308003070340d424088070302e40c050056400c000700c1c10301c1c407511500c80d00c0c0140e141d03a80c80b005000600000300326030141c0340340c0b07154240f643c442c1d440e840a4008010316440b00214a0131036291035000291850042104000c40c2c3d080310261000c0e4071408441d040300f1410a01d074402214403c0f00c1a40d2045040100f4038007002c1c40002c0035185d003001d01d4655003924060744030351030303901c034210101080b076407401c00e480c2c0f5502c0c845c20b004120000140c101c00300e00c44480300c060f500160102b1174000604064002c03807000340c1308880d0701c1 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 323930863 1250 323929613 323929637
    0x4030501020703182306090406120503030901140c030402130b040504030903140109031707020a08030f01081006050f0108060120060f0a090c03030e0a15111b060d0b1c03020d 76
    0x40640060501000c006014800319005071b8100352009002e07400000d0004103030182c80d166449030401d48440c0441c0e0303e60000003003040b03a040030300c00c401480d0180032404100f8103202a807080c05001c041c0000e881401900c030040c030b80c0d4025502c142c60856001c0d009021514240c1000307895041d01e440140c03400e42d8800481d4182103010311030858210341c0350319030010440c114080e03041e507000002c00360320079403049505040c085000d500c041c52180c065602640d40c25814002543d0515280c08441ca403d1418030308240219a0303169000812001c081c40d01e503015070b0303a42e40120781026000b4550030030452030405105c1c00010201e01c03644a08083e0350440392984030a2103d2045415102014100b0b40c4100d00c10320000c2c0c82a820203a08100090400c2c0086844d0203010150f51405c000b980003088030019040380d104001d1003440d0b40180403440c2d000c50841540c020032421320a10380318a0005039580116401d564802c554a0005c0072510740b8a00032220502e030180d6a0615100d158002c02d82c04c0e5141 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 323932113 1250 323930863 323930879
    0x51305030c010c03030911060c03030a0e01140105060c070512011a06040f12050a1704080615030303191503030207050910150305130629010c0c0e04080403050102070318 74
    0x40748008183d607180b01d944120b031400c4008003a00ca01c02c8072040c0c00d01445480a43d2601c000d0088500584007940d504e04041c001c0360b01705c8600710224be80c03a904142c0a4a20300c50555000b504680090301d8041d5540c61580b1050308003951500f016601038810508ac898078074055010642810800800c807480410300401c01415000b54420714212506124080c4140d407040080389260b503100740e0440700261420383c0e8085d40301501d860241001d8601080030440c0403802c01c00c00760020366184c4003e1540c0c1107400401c0c0c49200c01442140041d001c0503c60003282c00c40ea220072003071b070381039410800072607203c1c6002902d4180e130f0311400e44202000d00201f55200c00824444040f240c00407240e0340c0801c107803181a005890018007854038004500e072400c0c00b0880c0b501500c04480304100912451448032250400d151090080702c030b0401101b079441d100020040714101059581411100c400c99a841c0342a004611680e00b004200b94004a00e1904168229007000807880002c1594943c8035160400 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 323933363 1250 323932113 323932123
    0x30a0606020304050f0d0c1d04020406050103090b0a0b030a050f03042907030e0121060303080106030c09030b1807030c08120a0c030f030f060e01080f031603270605130503 75
    0x111030f4421000d0442420343d1809900304441c0e24405c1c80c20306203580d03841034100d8010025880143c1003023401402c00003103240a20030b503006400300b420304101d09441502d41c0070203000c2c0185540e001580d41c1045c05101d507800c0207018200b541c0705007159041015503805540740d410500c07508551401240e055510000d071181880a00210078086038200340d00390710202c0b02c580050786031038184501015010788100c1c110204281c03900b0300c0302d00440c0e03c074554503000340380b1013050348501d040518100520724525400b02154044a4100c0740000c030750b4031541c2044501c40d1300016412001c5c42010000000c01017030b02003c80494065806440c1007000d60114a850751052862640000f24400840400a8011018128400001d05d0001040e003500740c544401c8450a41106075070b00c028400401801c4404c0044c40001081c40000d941002c004505545541004100c0101400000c0145110f41c02c0420b45c80c194081c01e842d0b81c0c070102a56920f0280942d8450004c2c0b881d448182da401003980d040000d8 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 323934613 1250 323933363 323933369
    0x60b10050c071202030d140409020301030305120a05010b071103010b061908060a0b030a051305120705010b0d0b0f1308031e09070e070c06020405090c0918060901090903180b030a0606020304 83
    0x39240c035400506c0111030070300c0c5c3d4a0500032110380c00d00000c541e5607007030300c065406188240c503440c2c1c0d0f885079402c02c020001c4000303124040040c10305005000d003001303120980f0580d90f0300c8980d24281072244800a409000703003099264002c100494412108400c5a0b030404481c0b80544504a054544006210320401c460203091403407801080410400d00280e4040c952182d1200b428100b0000c9071764078281001c01030a41e00240400c04546001400003c2c400d01914890460380604450034907035035414202c1008000c040c400103e04001242114000d4140c50455880144d242d502e00d0080e84074000090014041c216007480880021a5003600181e81c101756140c4064403c103598800340101e9400d80c0c400b10031510303642c0a2000045940700e0011180c0124003131821aa00e4040d58400e000d0410074031140841d0104421003031021641320301c507125054801c0e01030003281955407400c0c1a0f41090800b00712100c03004000c0d00005102524074091409144204c04c28400315542c1d447c220b030342c1d000345c0c0 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 323935863 1250 323934613 323934619
    0xb09030c01050a030b181906030c0b070302120c030a0306080a0f1b030614010e0916140d0206030a060806060102030403052d0303130c240c060b10050c071202 69
    0x10000030032580288040c00c11030b001c038034010070000800400b140342100000a01c0d11800a0300c0c0c140803079490b2142411140c6c0300079500401c001c0f413460f21000e40c0710441e44242540c07401c0004d109800e15209010b21585a084030300800e0342d030154800c034a652584015040742c000b070319210011a06150200301210002d80203140d4182e02003072a01c400d030a90b110809100c4160280c07460000c001807050150032231500d106038a011107585400c43c000c2c407040b401030820190780c202041100441983c2e013220001c2c2c60945030400a59243d900c0414100e4040c0900070790701c0040841004041400c0750000020f507040c09054a0045e1030320300059039240154080140141c10405040c024000c001d50a04c608800304244041c00507865801107003142d1003543d103a00805183d400c00c2d402c0c4040b0383c00040042001d1031a91110009007000102c44050b490004404c202e000520300060000c5504030794081039004102c600148580c0d03202a103503038000380d1319500d1401036000029180c40c0a40f04500720030380103 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 323937113 1250 323935863 323935873
    0x50f01030b15040605120f060105030a0f060507050417011a1c0b040501020906030430090e1f0602011409031318091e06050f07050409090303020c1006030c0b0903 71
    0x307002402002488109601d400a941304800070303a6981d44020f042c600c10410003d041020240001a4100fa205030401402641700454907000118000c5103249400c0d040f03074001600340c0f07805104a031248220740c426034207000182404001980191f0010906070035000c42c0d4582152000d0500c2818080c415505016282e1034030071301e01041c001c0d2202075200d40710710001460059a0030003d440c0b50020750b001d6840400144917119000100002c04d20140005042c0741e040c1c0b100c4160007085562103008507035080d1074600c081044554076040a40c540c16010320340000954454000900811609240480e0240c144000c07e02c188400700031105400801540001800e06010b014509501e060142d5558a6610b0b01c0c2c80380451001070004a21042c0c55a810b180c00207941001001c0e118040c1010000c4004401401441ca4021003294100d40540c02c012640480f54142035000f0b0044002c00500b9000b11000d820601c01c440c1e2250095a1082c0f03c4c03050440c0d2100c2404c1c0b1103010f100c0c5e52070381660113 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 323938363 1250 323937113 323937121
    0x20d030920030106090905010213090e0c040b030a05070305010209041514010e0d050106090903080601020c010206060f0a0f0b070309061d041a04021204120f02120705030f03011206050f01030b 84
    0x4101079001e210031000c1d00201e550341d43c82d510324044507030103201034809950210f0f40341c0025001d001908010801c10300140f0a60304006aa03d40f9007107071070302c0244210b43d20010080703540c45c00d000038210190841c003940c8440e0780c1e81c00d000c0d0203075111000941c4210b1800c108144954000382048040d138501d641903000090200005680c2c9004150300942d01440310079088002031030900448011f003c8100010500014038580a0103c900240249044d5000103100c2d07483e0b66400a411130307000ca001c903003250041c2c8910001c40e80c0c95090f504044482c900302030000c00c950034881c0007044203603c02d95400f0146513031a0b004840f04a51600010000c2c801640e0380342c010700c2c15800034180381078000400d00c1c1c060f01e41d00004081342d105442a1000305c0d8500100030901c00c07140709a0010400c642001c43d1003a403c1d080003916040d20104003038003280007084d00070621000b04282c0b100c0403030042410b40e0300c1d44c50f004141520f40354000300b03c0342c45003407100003842c2c2095030300310324100c0354814107808040d21 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 323939613 1250 323938363 323938403
    0x2060d0f0b120a2d0503090f090402031f0b0301020706050603240c0a14040905040c050402190503040c05090103080408060c0a0903060b19060905040615020c010f1103070b0106020d0309 81
    0x190140e484203c4840c401c0c00d0341340c0103203a40d520f4a054404c0c8011581c3d5800403090004800551903141d108011020070400503880201c0c1d020011806000701078a000400200c0703800421b0410701403905036101081e10b004000d0164000c0d401003a00300c003260944550700712201110142c4442c3c4c01044030100707021503c1ca81701d41c80503183c50104c0d03040c1070401605c520b255030003a0b0450703440122002e4030381040c80207200254240d44c0242c002910154500b689200100204206491681080080000c0003405102940840c0c3d40038000003840780b0f51950f5039041442c0b09030040d004030500780c02600c000c104903211407021200407140d544c0303400c080d03d85035480d148001d1400c102216000205011b0f00e0b03016410a01303548000d02043c0c1c0b12041d40a06020034041198400e03040f04000b4041094500c1c0c00343d8001400340000f20007480c00320701a240400c2c4c00c0302c00a001d43e841118910002c1010020400c04441460595242c0e0382142d1582940e09811400e48541c3c80380074240025817078581e00003c07 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 323940863 1250 323939613 323939633
    0x303051308160f15020a0f020d0206070c03050c060f01030b0903091f0c061d1203090307020d050703050d031b0806130e03040503030301031101020d0f0815010c02060d0f0b120a 77
    0x150084048803d19903c544680c00165551495215074640c0040d541d102107802c0429222092224070003401c0c08032509402030340d1010041c100b9400d010a1501d00130805104030200e030444a000001c2c1c4440d41081015416001820b000403228040000000b907901d440000076181e030200300074108c54804d0b94066000c02d02c40d0040050404000100006a001c41e10311300170b001c0840002c402450b40c8045200c4c40900702000c08048990000b410070a0040d072840000c1035034040364048406800300345292400074a03100079a40020442e0148941102c101034060780902400039540c00c0052214007010001c4a0080e0126000f43c0e200c0d0b07c01360290343e071080e41d0b444256894a084d040301d151603181ea00082c6141c000340d0080b10500307501d804d01e1105590610100030406018148a44509a040005450410010300c448060100404449001d0380704607540d41350240c010b0590350b81c030b07482400464050840705040c0309059013042c80a40c024202080103d0005151601901d4040080d6680e040300c4 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 323942113 1250 323940863 323940907
    0xe040302190b01260109030e0306010f0b0d2d06141206070e03010e121b0712030f021c051201080f0c04051008190302070906050609010804170c07030303051308 70
    0x356014441051044e002440385a948502075103a40b04074940040800d864650140c022060301210402d007004040c48160954050340d007000303400301e6540b10070205803004001c2820702d02a2030f00d10250001d0603182542c08601078480100c00525401c500c0018403005030704500e00b0341440c0e40207000241d86a403007088041801e01000740007013507208048024904c1c09810103e4248440302c005000989038441d09240c203407500c071003030141078443d19120500791625810b010140070300c60842c1091800724401e0108052460595140c980b44640200004005800542000400b984c1040020899080021b141503441046000500c4140d52130300a01001e008007400560710211b5800001c5180c10040c4800da8003100704604216001060707080c0246003c5140d401604060b00d003200902054480c0c02c121881540282072001190305e030380c0b074800c040820803412250046070203c1c018440d0b920118615088074040d540a000395122586030348000031111034001d000c050208074480c59145860044400 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 323943363 1250 323942113 323942159
    0x904030e0406140118060f080702160902070302011409070b090d0602030130080706020c0c040c0f0909271406040f120e0a0b0c010b0a0e040302190b01 66
    0x11550380d5002103000d54060350420030009001c40b440074030b15640211603240801004000c0c0080c10716010026061010703050f259400c00c40c0030000240308a0080006822030010190843c0d20303a0f07551490304009401c9200d0071001942070001c14541c50601c80b06260051000c0c8000d46102e070b16114018881c0d600001c10a6007194146000e2008507407244061802000b000711007011003c6041b4420f09003180d96150804c0c11004041c041700440c030644165204103034400b000698820000c004585404d411501d2194007604043c0c02c2c20540d98859045020b000321600c40c4001e20b511174a4240070b13101008078680b00c072000c800c20101d04030f01689040340350305c0c000e1204802e1005185401c84c181034040ba01910120594458a42041602420310340406141d141854146244100040141805110303070180903002081481c0d5140081d80a1004200c004194001540e03958940c806c18440841c2c1c240c000d4000d071403204942c243c0400003014441d074028007203400f81e03082c00740401c5464101640b01d61 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 323944613 1250 323943363 323943377
    0x7081003080408060402150304030e06030a02090405090706030c030c0206061311030c070b180c01030f0b030f07080c0102120a03020703090b03150301050a0e1b0613030311010b0d11090403 82
    0xc0854400c0d40100701908002c0c001e06094a800d005000c1c0d002000303100318007013070130400400c00401e9014010424002701214129640d4032088081c40190040c0c0041d10351161425003030000c1c0307060000d03800d421141ea0340c4080c880500307410f6080e0f04549000f000540507800500025550349050f50b000d02c10a151039130000b51121441403001c1b80e642003180d080781845000501c040500090202c016880940b21100c20f011224800701d050b11142200d0740d032814191625072845a244842d044064582e00c0501281c8800c24813980d0555a01d07024070860815009800d9400440d501c0440c0f502000400280081e00d8604440421002544014425010040a134602081d510503c50085018011200005080c102c1c8041050b08440001c0d02e5124034a10b0150b01d002da83c00d0102c0c1140c1da07400842000d000c83d00100303011400e241301c0c40098807a10781c110300c404420180c10104050300d298a40008209110034501030001d425007151025001d0501c80c2c2c1002c2c0750707180c88131b40c1541c06440b80c038000c0 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 323945863 1250 323944613 323944619
    0x50d030c050109080309030c25050112060308180f040603020105030f040503090d0303023105060c010e0a0b160e0303071e05011d0c01090e0406050423060613020c06070810 75
    0x313215800c1600c0860300c2e034100180d12501002e04011040c403204119401c60103c198022060460940c18861503041c407a01130907850707502425600100c0215002040e003940c40841100c4002c40310712610350b851041040b10b00c0c50856041921501050300e03810384600d03286444004400b01e80c03c00c0180111150b02c81000700f041036845002c12030342000c0c400e03100980c682c203c0e030000440e01c059140c00760868403400075220414000c0e81d402d035021600b00359441075841100078070340d5014251941c91304416201d104010400c008141c2d04a512902000c84900388084551100b2502421150541a031540c020301000700401d445400b8101035440360090000f09034503e54815003555041d2510a80185040315880e0141e1402e01c2041048c48e000d18000c6405414901c0e0016103800c040c0005e004940c0d10f0001504011200c00c11801190112000002100078500c81e2a542c8200712a1680240d580d4a004141c030b000f40e000303507500f025000c3c000d08200d41c0c0f404400c4800381c0000740040d000d202030303035400 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 323947113 1250 323945863 323945873
    0x30e030721120507020601060e012615150702040c0306050907030e070816090b0114030405010209012a02010c0203070b0d0608010c090b03010b03061318021002030301050d030c050109 80
    0x1207800703000e2424400000001d24009024101c0d04500100c0550608040002003a40070825505484e807038140039003640c502100480c0c40181c121810350040d00424900e0001c2e804503403045104902025548614031480014000f100c800058100d0240c9801d2114100516207a04004000f419529000859580d500b00144a520040d1042c0300860307641c0e42c220311b4200007401500007400030300d0010184400d281103000124040c0340302d04003115075100007070000d582c821840c02032202036030803403980c485c2440e0034414001d5000117252404915402c101c10004076809808107600000082d0603010304105400644444e8181d00b803c9a041c020342802082c138180749000380451041c40c0c0d08c00039020b420040c5050031a210514600c0034014524010044011410100e90640b105002c2032904ca0b21050042011400300417400388440342882e10040000d0180c0318a41072070b40c0200e0341c8600000180c0001e9880388420700805400c02c8100007000b0101c1d00418240820034403460000400e41910b45403 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 323948363 1250 323947113 323947133
    0x20901051c021c09210f0c05120403050d080114010e040b0f03010f1d0309030319020a150507021902060427020c0a0506070503011d0a0b0301110901110f060106030e0307 74
    0x51015030f107511301d105010b6500c203407213050f102e4480f040c0341c04201490050401e8041c0c00c80441000315442c00744081080071711082c88805007890556840c4d6032a45010390311500600365150015060700300010303080750000c079081142481a1219a2030301c90b0041440302800e89600320580101c0321342400916a1804d100d0042c420b005490002590321545070f1415030080b1220342e54049034411700c0003241c1694007104907031841c00d040394401d5140101450a03030401440403c0a85280c8222119a01500da00d4020901c115200c2d8241d4079070001450113120b51140c4098041c2d000305017444180810510b1688a0103050110603d541e140200d42d0300c00c030160f0b480041c542400d90000c03181c07001000810003885400003002c0c00c0c468110340c145010306d141000608880d001d405019004100e9075070043e440f910741e660001c2c00a0000b00d100ea01955415841034001900007006184801c0a10380d000c1600080300b103100014110a9107040c0084000d401c00c001c2d01c41c99400b04102c100700048034104 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 323949613 1250 323948363 323948407
    0x20901060504150527190303021c110a0204180b1e09060910050c0c0115050906040c020a02040b1f080109050f070c0b0a110f09030c0103020901051c02 66
    0x507a05030380d41d04080402d9a02e100040e003080c2400020f004444d2804c0c8101c09103802071103a811403003200340e0400002000c003c18195202d00800c400e050200034580c0c00700350116820800e4040305021461024116101f80c5a100344c58103d41052070900014075140d0401e0712072000d0032910351000d00da9515000d01002080d2100782050400d502180140005841d41d0340d031001300c00000e4080c034605912425168030308042c0f88074259640790000303030600341d4034019a181410300740000c003c0c1c15080300e10840200d140d800b40901c100e41e0140012031328a010300440e4422281640606491461030f401c0c4005440c51102c030540c4101e22000d130b024510003110f424880d80c1300581c2c4040c0d60b0b505d001d010104030742c0c014084100c00c030305000420944a410108140d00594000701c80c0c01c095036010028002800000d0b03c0103100740001500a44648240c0084e001c2c0b00c204a003aa03200c002c00c0c60040d4100e11a00c2200341c0801c83c2030042003180d04d0044020b4010300c0c2c00f181c0c090319090048180e4204281406 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 323950863 1250 323949613 323949617
    0x30203061903080328110c12030f0a020a1b03020f0f0609100f1808040f06080103171e1614030703021207060207020901180e161809062a0f090306020705030702090106 73
    0x1142410190b4008c20100b40302e44009140d580ca5810040008414100b001300a10703990b0341c00060007104140701d000e50516003d80c2101d05030741d64019160003519080c1504072a8801d10a0003884541e42d9404603905001382042d100070558500402e41030030150002c0c21000124964800340c6021848400341102c801c21710942c0459074071820141e0310103042c0b03c250001020046d041d8018030000310250798140301811919031160b2101c00c0301d8007551285c0c805000a08054a01082040d600f00e003a4180c05201031080c0c18002d0359440c44203500790f8a008000c405001a400b49d00c51407103140401009100d9140500d10143c941080354011509101080e80000035201300c84010040e030b1100c034070400b881d020718013010b0800399072034041c2c180c03480e1507030300811a080661901c4106143c6180c0e00c8540c82070f2b40003105021001546210101c064100d1803100952030b8000c400b41c440c0b0380310714040010150707540c41e0b40d0410b0f070568441000940003050101c54901c0700308590030140e6504000d06008003942e03 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 323952113 1250 323950863 323950867
    0xb0703020604051b01020c0607020607060603050303090c0102030906040608130803150f01050a0806040b01030905061e0c0a0219030522142b0218040303020306190308032811 76
    0x500d0010725103250381d10401071a01444c80500e43d2a82e0100c1d20340100e04c01120401d44403516800000ea481c41502c1c0700030301d060328098000007006004400340d0b00c135052000658400c0c070880c0c401644c40380702d0b2110a41e40504c08103c1400356501030000581c10100e0005c0540c4000202c0c1c1e9080c58036402034900090301401c48144004034608002004001030080c40c020342042d80c59940609408800b0784018415512013148a450b03920941c00001d82c142c0000c22105a0304110180051501c1070081030404498010005a841082d00c001c80d80451025802003102180151890b1105900000700b10200042040318503540300d50013007400d4040d000740c0186c03440e15142c002038021040300a5903030350050341c3c0f00c681c0c050700780002c5801500764602d08810b05040d1045200160400542d66600541d500400d820b2105040e456800f6502c03e9000340c0342d402030309148400001c640f00b0140304c0213101200c00c10014044241018030030080f1004101100d00c040040e404003000e5a10683c4013034920800 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 323953363 1250 323952113 323952121
    0x60a020a0204110408030703110309190e0a020f0301030f15050a0e071a090f15121008060c040308162307090c020a201009080d0306050919060b07030206 67
    0x1040c8943c803d820b68000f82e40f0320f0285840b010903101c3c00b51000240c2808445203410882d00d07400c0c011a180700500901c0ca0040402121000c0101c00e483d01500e08440031060000c0d0300c1c0d002e02d20840d80340e003140d01005420740c2e281d65111000c580030603008549044411001d5210030416000c0c45000310382030100414510800d41c1c1551030000c03154489070000200e9001001046005401c40e00301e00b00943c1c040314480701c064007140c440a08c00c00055101301d0000340e41c1d00c408180d9481507004884039200c502c001556880d40990740d407030903622440e010303404120401c001407628005000e2100d2446886101d9a015120303650410503402c500342d1000174a00b550f2907400b60034003c40f00039042c826000c20030000750100080d5194030910000f031200005500c0300e501c0c50b140390001506050014850342ca40501c10030300412220081c800c10951344110030740402c62902a025107402d60b0b03009018111540d5402042894520806681c82000c947c1c81c1008509107003510010110f007400380e0024805814 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 323954613 1250 323953363 323953369
    0x23040b120105010e1e10110a0501060e090c0102060a050a0e07080c010f1d0d141f0b030a0f150e070b03040506070c0302070b07150c0c0203011b090504050a0902060a020a02 75
    0x400d03800703070b403041003038686200d07050422001018170900107451b180f00035116503c017600d01c40380c0c1d82c42070501445a2400c60303080050541001040e60601403011805071610b1040c290b0f900652003038180541c201d0303c00541c0200d425481154401500d1001140c80307c2c20308075043c1810400d07009401d1940000d2481051941c014180200703000042c5800700c460802a00c4103d1071200000f5858403980070740b800103041c010000009080500d04006a81414209480005807003161040d040e4210303007410145222880d000c0b50700c00c14a81c02210311441076640b552000d01c0727181c4610811140d1591443c188907001c60401c10800500075484100c0d644e030400d0f080092410400401c0c0c2010415203050b40800268003243e080229020004225114107161030b101501515551048510310701d8200c0b040341c0c040e80300c0b0340282030b98000c0d4001c00c04002c85100c440d002c46000d800c05800304d444040300f000b130360900368400b036404004500c0c00640142280d0016000307500841c002801a48001100e105501d = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 323955863 1250 323954613 323954627
    0x30c220f060e0d0210110303071d010c0b1f0b04030506100f030305040b0c070515120903030105010c020f04060b040e0a0e0a0209040f050a080309010c0201150623040b12010501 77
    0x300390b0034600301804946000030074010b0803a0000340100c1a1031038981e010b500811000594110340f03000e0b00c1d140e03d024200181600c1300c0620b401880c2c40c080344030450380d50090441034142c2e60401c85908007a0b40f20318801c00d100700c900120700034011030101c00190841a90000d00051803040011b041581006049441030284030342002c0c030704e84c521810800010780c00c8030446080f036041c6183c1c0c517111908402c0e01814880366502a0b500070540300e06407100502c040c0020800a0030513402c0039416142c0303038840c9940340000d01485000c1010401d480700580b03800700a80d2002d103002800070072000e880e0000c0251a40150f400000d008039100c2c01d0069950301400303160b0742d4002070130003001914282c0d0005503840742d001e0005401c900d850491030092050904c000f442d642e03005803200c3e03039906101381443d00906a1000047c015444e0034240301201000e040180212101c0d0369654a500360420f04842c201035003590000d200798420080041c443c1080c0c1e000d401040c20070700103240c440d850100050303c11 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 323957113 1250 323955863 323955869
    0xb03060a021201050d06021306030207030f08090c06070507090c0203040510050705030f0d0902092503110406182309090a020a031e020402030405010203090c010809070902030c220f 79
    0x4a4014084206a68403a42c082ea044071401c480303a481764209804d158009100f0342c0079020710101c4528002c29510f415070010141c191180e0b80b190041105003034110b6803042c00380d840100c40c0c1c20200000040c0e14000700a408024050000d80b10f079a80d0355041d0348115065030040c8800351700040b800b00060314040407548150b00c4103050a070300d0302240c0e40d84c182d1a4802c0f15841c0d40040310119241c0515445540709039065a40648080314030b051101032108071104881060441c601c000903070106261290040d1440c400300103008908081c01e014003603139200030380c0310000244401d014000540003002d0211101d401d05180c02000300d42104400c3c480d02d007400822100c1e1691210b00348400503151046604101ca0300540d1181010010b441503500300d004030712002e50f001d400031051005000065000358007414030030041b01c2c0c400c402c03600151101c0d4400c86a841d11707a00041d01c2041201e125400450b44031200d0b0342c4040c075001c5240360f00310a0010007182c00002211030a010301c0f4400740c008004000d = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 323958363 1250 323957113 323957131
    0x70e041d1c18150311030f0a050c040b091201020909070c02090a0501050918010b101e0c030203071b2103020c0105090307060c080f12070801050d1a13020307090b0306 73
    0x340304200000340c01c0b140024412182c00c2510b60b43c08100e064030960058801785c000c600c0b625502c0c105840403071042c040a96400325080d1810020600e003030b94400440303044518040c6c4607401d2107044410009a1750603002c9180841d50200041e501036a00c1200c0c040c0729009645800c400b000d403e0050006100c1e004001c400b01c180362800510441d507896030420b40c4001c200003684c80030229692828050000b0400003500410403030f241403507403074020344100304071103495000d049a01100034046804100003600507026070010024039000c202c407000b103264a04214000c0b51019541c0324075504001c0315000301c2c010003d0310340046104265041c40015420902440c1850601d100080040c0e194511480f03071f2004c0c030031001900000c0203541015662821a030b40c403180d4917601100904d5905e040b04682490000380801d00114480c540814000314036900142c000d000100541040ea0b51210081c2c039820071101110200740059404114a401400c0706480c08101c80c8170f1001807500d4100c0140070200e03 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 323959613 1250 323958363 323958377
    0x60617100b040c080408070c0902131701020f0f0304050f071403010506030a0c05101e051306030c0822050109080903070e0615310f090b0306070e041d1c 67
    0xd41e83d51100c205a0010703007140086545000c540782c441c2141c201d607031211009ea0b001040703400f03000b03210031102c50448200c0c802000488080b181da075803c1384542d444540e900c5500b400b01198561058016660042c852400c40b407107140d40d400c14900c0e06070203901184030424910180b803004e003000e01a507600100c040d0018103030304045950b40725001c41980a190300441c0942502410307a44030314001b07005003140110040010f02044030003411584080b200c101c1c107620906000034814401d00c81e850b8021415610705109880b994044020780360003003a6009040e4407034603c0000300341d0a01c40d0388001882403030300960740e0b40c80c1310a16080140303640c00b803141c0e04050420072029898500c05011030241e80d0507455074a08410070306150940b017403a2880c25007041540b40110070207504914209895039002c0340300085950318020000c0e51a0482d145805411840100d4803031409985100100b842c0204080754080c030306081009001000e400018243d417140c1e0070540382409503403c03407044003483e25042c0 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 323960863 1250 323959613 323959631
    0x1d07080c01030b18070f0c14060f010b190e01030207060f09060f090f1211060414150402030a11031e011a030a0302060411010207030c0e060a050102071a07060617100b04 74
    0x40134070714020000c5042c0090340c58808840c6104804050b15554403402c0c4002030030302e03113082680e10704044405c0300c03c103003c0000109000c0e1181c0242c4107240c118008803103211340c1c00030049400c03200410010b8141a000c0c060440002d041d800350980c15401c1c5030001420081d80e052001c10380b600080364101c240d01e496001d01c0841e4a00c080c1c502c0d85070b0094002900c0491100c0e04484650030300240601c1400340c0c1c0d05000c1044904034101c20050a400103e8448400121401074030407015075000b03615038003401028001948401c0c480c844403800134291941400c440c9551500c0c07017030340c03825030340240d54030079480d000081c46140101703144109a006085000e0641c3d0003940d100d80141010705564105070015865071b10070000407028583c400a44032070f41c0e60342c0e0464100f0394025111944280e420a0002c14035510001e2000200c48010040118010002661035902d5004c00d4080e51452b845000218005094423041040d8020480c01840c0050b40b200c03601c0d00300c584060001d845030f03040030a11 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 323962113 1250 323960863 323960899
    0x30f020a0207050402090f0a060206040303050a11030604090c05030f0a03120501050f09090c10050a1707050301150309080c060f13050307060c02030702030d0801050a050909101d07080c01030b 84
    0x7400d0fa00e007a00e005035074240038400102501c401c2500702e035007c00307600d40200780b2a60126045006070b100b61818429a02c800c9503290540d05500c007102c14a0809000141d03181c03400703802c00c00041e1300888020034016141e402103403d020305510340145c40e41c040c1c05140308150348501040003600c0c1c8072004221550400340080c0000e07d00e140c250380705003000808103244001c00c4c03080f1552000b00415103c0c000c1000c3d1009081ea80062454002040c0402036034035510356001d4205108521907669589107a080410207a540c0000c82012020150b440d2801400103181000500702d0302e46110040101d072138040160b4114080080000345c2c071403544000d00000810020541b0602980080041803400c84850100e145004443e400795040c40340c6151164000c1d0070202c554180c1d44161000303c2400e4070360080c40801901030342c419510b80d11100d440c0340900060760003501e1054403480b501641000c5100107920741600380d00f001d04036800c504410781d004d68140c03141421514054880307990a16125040e = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 323963363 1250 323962113 323962123
    0x8070f0e03100c0915031406010302090d060c1413090e071211010c02061b010e010207050304030f020120070906090c050901031104051009150509090c0f07140a03030f020a02 76
    0x2c06102240c50346001d01209004030b000001410042130000300d507850b1643c0040c043d10b07209409840d0402040701203007555120b402202c894902c040c010f114014807590f1150000e007115890201000011000300400c00180300061103640c0540d03440c03007101400c000702241241c2d111514001c1641c032404c0d0400601182c44020001d40d900010031414544240d40180c0300101d00c900029031003100003e00d0810300512032000484504080c2c02001030b00e051548c410308038850104050030310b174400c0c003003080010b100500702040d0510601d41101c03003110403403000491124841124501d40c0008900b84102d0400740308040c000c040c1c84a044c4001044614041c3c01c0b427246548217410940c039001003610300031000d0200c600509001d0100c018040c1c0d6031000400e40c0c1d209010308040790032200c02c0d84160070310460039141000c0b802400c0c0f90341038584080d0350b165a4000030152180340000c1c40400f02140070b2032013004034000c0c02d2003d0402c00c40720789001070071240c4001c010700003580b05106540e80c036a80010 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 323964613 1250 323963363 323963383
    0x100305100e040c060c031707200c0a0e06060f0307020d0e0312030705030624040801060509090d050c100f06031401050106020304060302130315150b0a080402012006040308070f0e03 79
    0x400105040c980d0078211f9222100d8845220750038445803d215103140d000c88040500e00c241c0110502801005403025100c41c1007281090303000314608814400042c0012031070750481c0d070050060b480c200429102d880701d50400c4901c0c40c0503070011400085242c1c1c0180d240c03107030380340100e000d4007031191200140d0078940805401041044400700002d40d0356154102e4260901d500d101944102601204417005035a0242c0904c030429402c01200048cc3d040c10703008540900700e000040c051a004c5208120307140c0e040444112201c0c8600c40350002078020b07a200c3e40084415603600480d0850850030030401e42d820a03070707003c12640e24140042150a501105480650780300e854090381d10001c0c81140004d14801d500064881c2c1e40203128000c0420316680700302c8201400200c002d0210341c0c0c8144c0801d19000b95801100403455800001d80150701c00c5000780c010f031075003581e1a04059000045281343c40811a000c502040d8140144440d5a4001c01c40c012002c2c1d1510b4000309203518040405d0b200d600c518 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 323965863 1250 323964613 323964617
    0x1061e151403092104150306140105070510110714032d09030303090d09170703020112060e070e090a060503071a04180506011707050703120b100305100e040c06 70
    0x100200c0c1040d070f01442207008503032000c1c50412606610044404140d80244a040745494490149181c00b5000c1c1c000d940440303a1803014614107904280040d205540144000c5030070740610036018000c91150300c1580c1c0d002210740401740e12205246845145510308210520b6161300034020300c40303120000d00d08410000c500d803020020300030036801ca4085c41c1c01044111035160102008111400f40005542d94000082d41e940c40080c543d41d4410444180c0008803100040d0030a00c0244007550155070b0082c00d13a078128400055196485004910681003964160001949070701280410301e01010740c0c640000000500708500f600c0c003400a0b55a0101d0321600b10070301c0010780d6050301180110160703001400448062003016404c0d8250000900d0103d46003404100c51280c0100c6100c0c0c0307580f119104410740d1729a1860420551419190304034007106110340139481d941c10307217005d0710340303009028a0744000c0d18081a18180000003045105164000c1400ba0707540c0c10411021a4030b0b1210722044903014 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 323967113 1250 323965863 323965867
    0x417011b05040e19060b0a1701050d02090403030c090f170c09060a05120c1206011526040204110d0209090f04020604050d0627140c06030106110703020301061e1514 72
    0x2800214011740703200d0b409507200740d50108040301c0b0290031480e1400503e50300d020603a141e07030300d4008020280f20341550103034109652000180c0080d009501c044108200307402c100105550300c084001d0840d07841d1b04803440da9205070400324a014420004444100c804507a0110a86081404900186480e1140510810b072081001222501c14441e1100b09400075202034111100b881010340c1c0c800f001e1080d803900744150020001194070800b554081820049240e400800c401c40040003d800c015006030b030b00c551381c0d851000411044034001c6c003400710102c01c05070321860140c040200b07081e0010040da21640c0c1840820005039944001c440c2a5942290402410100e03400e091000b04034151411000158a29950b050028100042013400381300341a500403011129203042c1d00c1e81e649500d81a00f00c0307000c0c4014081d8500440403140c400c080300b000c40d11811b0b0f4035000039080d26100d43c0305440001c0c000382000c00140510f038851000d441020281c0030089080c020080c40b060420040b06160720340 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 323968363 1250 323967113 323967151
    0x303152606042a0308070f120807050406030b13090b01170307021309140102030108011d0c0109050909011112010609050108150103050c0c010c0f110f07090e030417011b05040e 77
    0x3c1c40860241d9003104100351500c010b86400217454508403000d403810b243c5841d03003e02661040304034034171441d41580d40d24241880d05101754080c00c00e401400341d000180c1044a540c00038a4481c9000715800780980396440e51500300c134984004140c241c528003540041201001581341d0b581440c04000d80e1041c001a48442c5041489894405494002c2d10f03500000c00000d9190054010ba028028140c85580c81c105400c0700a541d03404e0950942404110a0f0508010502d8000817032507000300140f0001c504040006010821588140c141036040b100c00401489099880510720b07000d0b040c00c1c00e10007164103203d000240140e5060b08628100f584560010f44070460181c165440580035038002d1200300c084000160004040c405100d0000e00559803e0214202c0000d07100140785507540684400c500b01000ba10292a811255031a1803004000006640c50802c0007443d0006030103000280c80801800410101101a0203000c20084207100921401c1002000c044d04036000000e040e11010b1 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 323969613 1250 323968363 323968433
    0x1009170a02062a07080c12070b040f03050d020706091401110f0703170106050d050603010612060f0912021c02010501051e0f06040603020d06081c0c030315260604 71
    0x40c01e0f403c046500f00302045000421083d4005815101e48a20a660242c8101d40100c0700318000d650000d0885e2018070042404035450f1148004072a00a01c2c01510704843d0342c00071400c2c3d90089404603070555131880c4200c1400740c4c54055a0040045500902c104260710341d0b000d070306008030b03a61840007003000540c0780700f010b0103001d96008903031400500d0f42066035070705405051504407119001c210703400c0200150b021700c1e043c0708040c1502c520803440d5640303024030b4a0b008000c00f030210301d010100c0d5030b4030301000c003044036048818183e0145900505000b245481301c1c010250504844800b513a041000601499580c2d09076901c4c044925211528003649840c0080d2038441202c0380c26070400c0d40044c0c0030580541c140c00800713078003412400a12119a54051069442543c0c06890101042c0c00301014402c5103c1d0134500c030024040d190106500c05806a14450303240582d0150300032201c42c4140b10101009115503505e407958031001b07801c0515068580c80100d500465900c00e03901080c5140120050b = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 323970863 1250 323969613 323969671
    0x31809050103030807020f07030b010902092706013f0207060c030510120203030304020d080d020d15060e0306070503100e15030114041e0804081009170a0206 69
    0x41801050115580d24140600705040a03201c9900501500c0d8848140500001d1141c2c202c0340d102c0d0406032240e18215805000350444441c0503402551010162245106262001b0208015602507001801c1010014141310740380900c056005000416a1a02c5003402c04c8000c41c6480303d600b100d20000034407070303900001e10507410014140e500e090011382c0b071286d0540c002c40c0f180801110000c400c4d45c546480035883c15032a40020740c50b600c200300240c01401c0640c1a07807400e621404c00d4a041c1071500c800c3c50246e07000080803400203581c449102d5001301c90722035000300619080c1080000810f0b002c01003074403000000c10361028003500001040c11881c0c4040c07030000030602590382c0b9000b801d00c0d80ca80140c1c0b900c0203c44510035824051f00070507044904580034022507100520303840c1405101c440e010308038942c0d613082e9000901440002040f00303042c0408601b012034081c0001da07080b0700b4504a03004045404000822910500070740c402650005002074106e0a852202c2119180c0514411204 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 323972113 1250 323970863 323970869
    0x905030a080115020a05060c090402071a0a0615021b01020c1c020306010b090109061101021e0909010b040518060a0510120501060c030c060c2c1203160318 68
    0x54400060015005640884007905070b0b800d2240d8180440c1800d90200d030307103001441d400f400a0b080a0701044c1d00780103040061101d0b5402030400741c100040341d10340d0082501a00c0400e1000262002000058540c9219520141800d85c02d03d884581e42050003c2d6200c044942010380e00b5100d03815034502d0303070081143c0d0b111043c0041c5030b510020400d0303800c0c6442201c07154080b0300034480c2c5400490a05400410344601c580182d4920708080c1c5007681c2101c0c00140c40b003850b403840d5820000400c401d010042103130000500c908443d0341d526040b2041c0885184141c0c4100b443c1042400280040d555118441399480d00c2d140200010380c80741c5000568403042d9500541d40683c0d030f00380e4188510b4008444248003600c0c41341c00c0102da13a80d00c4003511500c0d02504014000780218024000061040d441900c1c01c0380c061411060800313000c0c00c2c01000069201401c6000081f244003003880b450401c0e2030381006080350000d035040440036002e56aa091451900405010381e201c00034070701c45070f000c02d04402 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 323973363 1250 323972113 323972123
    0x30f020301060504140901031a0408071b061704080307030e07090212060108070903030c151409070801060801060b04141804060506040515131a060705010f050f0c040605090409 77
    0x52942d4648000e0800d500910943ca4050150580c80001d03203840c0248a040700d8210403c0e18a004000d125800048001171040314800820700c00c01020038080b06040c801002407410340e2400794107100d40901460702d801d9a10541101034401c20000603164815a0380221050401144030940c0e03454050501d082d83c1c010325038040c40441e121074220003c0c80c901e40590300c2a00c441d01540c84006084400100900010300810504102c0000103100c00701a9a010001e0304000904100c010551401d003110545443da02c40e84005402c0c000c0309020301c190307001010403500810000b0f280a0305600140554800c940b40c0148800483d40103803201d040031040b024682c0c005200354540b03454401c1c01440145e030520701907460000010300701c031244000f02d811910000c00c515086208052060090404801e4641111b44104a0620280c4623907001d8841c0e80e1160001185c040300050019040350001400100011444014488110340b408100c6050310000d140090b5190b911070040390103045500b1000340b0b = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 323974613 1250 323973363 323973367
    0x70e040e0c13050f06030d091206020403020d05060a050c0a080114010314040f0b01050d0b0a0905010e1009060c0c170c0703080c03120c0c03180310110a02010b0a0b19030f02 76
    0x11000b003254465485440e040c0c000e0340e0703203440c1c100600d0b541c0c420590f02c41022a018640500040b0024031a491445101e881c000d4034160f140c1d03004c150324000601c0202c0341a4040c000740600d148040c00340651055041c40381e5400d009201c1c0c2d0040014406100718100300c4201134820305c180c0d00c03a4125070301112000200d40501e013094a000c0c1680703920048180e806c6682e000000c10746141504110603040d401030854502034a441420800400d03001d40100c5456603140402c40c032488051081194825003a42d000454030503c0c1440c005075070004003180200b02e0103101520000d814800396030b25000f00002c40c0c07901c90804000709071500c0d50300c0d000684005004541050050b000000a05103515a28400d541c3d5031200c3c401940c560007401502c1c04180c00030301542c02603465061407030031700c024000c0484440304524048001160704e405500c40305d040d030000d4203042040e02400fa021244c2d000341c42d0820000d240c102800e6041c028143d103155802084400012010310940020501181c600001c40d = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 323975863 1250 323974613 323974639
    0x313030c0501021201121203060b0d05090129041404020105030f090f030f040501030f11180418030203031806071205130c0f05040b0f0a03080a1404060309110405070e040e0c 76
    0x1085d82c0398503106c1155088001494201400d1090044004072243c0c031180038106030007006d0308000740c00000c050202c19941c50364072444501c2c10002c1000282c4411200800c07141009061000352081807a541503980200414440181da000c401c0f6503020030101343d00440e030703141c1d20402410500282152405031101003414910140c5500040c4200c0c7c6090300c00b000740741074021000060780c3c010413850109207004d2001c030704400d0300c020711024403260003000000c0e2040000a0903002c0c0c8884001900180c0c8003104001d180502c100b880c00c105d00d1040000c0001d854161401042162480c551454098884e80400c2e40d4410303041c0c6c460000380e4000b810422080d01cad482c0c08104100c0a201d070f1031082d41003149071401e078203110103840c09a00024000807189820346e10b0f052100c0c2c0c8008040020400001e01c0031451402080c0600050aa160350104d681d607442e0400000d051049170324203109030303d05014810410381100c01802e06603000e440c042000c280ca000c01600b450084542c95410481141c0c80c5 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 323977113 1250 323975863 323975879
    0xe2205120904050f1b090607021809010b0d050303071d060c1b060708160c030f150c03020f1801023d060506070303050c0412050d020c060313030c0501021201 69
    0x601142101030324100400e9840d1300c2141c000c04001c1c0d45e07198400e500e550401600505502c010503040201510b01464181ca139030204000c45411880c149104140509009409000380901c1c1c1009500b180c40c10290712440e00d84603120320010b000a4103110010302c8098080c00002d55864005200400668507244850415a01c3ea540248a0040c4030101d910741e81d194600381080c1c8003100c0c1c10074403050503c94018242c600c904c2000d102551103807601034001000500e40e40300050700d940300b142045403040e40e521340b110a880300303540c01005060051001519408940d0107071a101c0c0e14200b03c0161f01008000143d04019030340038411600708642d00c80d58044110100c1c5180340039031046035448142000c03c04201264158003405600c000100486408203100740c0006800c00d25801846180503a520003800e404156080200c0e041e401c040b0290401e00d4050103003140c1d00ba01591020314518000003800c00c5820700d4072000b0b050002403007074802441800d5041e9820388c1e840010b0b8049550b107170101 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 323978363 1250 323977113 323977117
    0x1506050307180803040608040c050307080304170a0201080c070c210209091c050c0f1009030e010e090a0f09020301050405150c0a0e01030911030a030f030f02040e220512 74
    0x312400300c0c0b1142140b00c50300706010341c036104682c28800a1800d041c103041040310031200107401620024050980403400340e80a01060740213180d140000c0da0b555240414901000b030442a08580c2e50304007401840c0542d070000c40d1300d94440c00502490f965440c1a240c41e18290400350003101c1c84540c410010729944074020740242003140211b4907880d86955680a555543c00c08802903001e1000303940948003614003580140660b001e5210584031110540313819a0315100000390072070085a103648050b82490780040c10090600c100307183c1228802807000c089000c141014005020041d580c520924862080303522800da444d90060003881075040038280140d5601190003240d019071400c0cbc0101e2201c1e080f441c1100c8032111580c43e00d034003180c000c40064008000d0544181ea944100300c8140f061981e081c440d0a600600c45d458902c408191001c004003200c04205014070303481c0c4104800c1c0f040410710842140c0c01080c04481c0240d01043d08544010744c40302c41e5000b016440740e1140c4101e41810307500 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 323979613 1250 323978363 323978371
    0x17070305090c06040b0d0c1106190b060c0a200a0e010501080105030d0228050105101a090d0807111207061805010e010e03031c0501031103030702090a050a15060503 72
    0x200302c4480c44101c5040144a1090b4440c50718544d000300903131802201d25800404105409040c00c0f40c6500b0102c8802e4104001201c044500f403910007040205440507104944031000306a07503860a000d250303004d9603992030120b407010788101c3c0d90081546e01081154164400c90f5030141950b404a640d9280c85a95441c0078083c07540402d40d0b10380045150b0400040050032070000e540104002c0f01d020010900b0f828141c0303081c440026211190a02081c424040d075401100c241001b106005d150000b80803184031076020300b08075110200401017103559000c40100e83c00d604102e03002d5565915150002c000d251703d20050360000e206141044020102290000446440380c071140701030504800041e1079170a0074003d150110701c45802d10031203944510311507018a030028007283d142140e5401e200c42c082e0114030061a2043e01da00c0140b0400060040340c142d030150030f400450918015500040d500c5100400340040343d07684100045803901c41c0c2c0c014003044401c071203148031000c0c2c580d40006c14643c4203c13 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 323980863 1250 323979613 323979631
    0x21509040e0102190311070f02010219030519020f12090d0f0b090106290a11030c0a230d050a0509040501090c08090a050d0c03030b100908070b0301080304060f17070305 74
    0x4c4040e46280a401307601c1c2d0014410002030b16001940d0348004600c0410070080c0d0462042d02000a09029450741c0b072046c0c180242c49054070f83d0103d100c2e00c048052241284ca045410036659159122000221400c100200222180e158408000403640e11507206c0006448044401c04600c180a50066105e014008150003401556150000002c0f4140030b01f0340c3d00c0d045007012b01082c1c207511202e00503000420083c0741110a10354540d401501d10341120742c041819402a0070900b0401c461110080e01c1c010001c3c0304448500301c210b035020340300da41320391420060050020f800d0342d41d20710510848040d6600100108001e584504810004040c054041404184484045000010001550b2000b02d622200030720b180c0d850b0000884080c00d030000300b00c040c035444051490281c3c2d030b445001d8005090ba0ba965a001074074040407245884819844001c244000b0001440310341804402c07101550301c01d09120701001c2c00900110f5140c0014070381c1c000001041800c2c400fa0366810b40103203010710050 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 323982113 1250 323980863 323980897
    0xf14011205120a050405130b040603230a1505060a080607020c0906031f0b150304120f0f0207270c081828050102040807030303050603060a0b0607021509040e0102 71
    0x101e4080b81d41c4204211403003c564180010030107450812504141d8041525021420302203120105050f41c9081c0c00444a954981c00d250389404042404c0150540d1054000e10b264011904c804440c002c0844e81c403951581c603000000c4481e200c02c100b120051081c00d048410740c0ca8840341c001d46032180004614451441711020076014940041c002c2004e0752000e56800f6422407a61481d0f0003000c1d010030b01c5411503860508034041c0000c1001551003180100808140303c4a21000240050806414031b018400604601c02c281030740001d4110035030360002d4902500745a180101072248000070800e0310120305240b40d003041c10358407a034201d00031580140381c0785030701100300c00c2c980d00c90480d401205020518401c07900e010421180d800b0310260700403000140f0703081d03d8034440c1d070815134160415004a51a1b005111050404010841d4003034035051301001182004000030b902441680c401074032446181c0c807201c46440c5401c040360710080000b402000601030810b03000780030b500076060b034815400300 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 323983363 1250 323982113 323982133
    0x40302070506040b030a0c0905040e0f01050109050f040f081204121e140702060c2a0f010e010c0311011b12151503060906030b0103020306090703020f040f14011205 72
    0x202000f03030b80c10b84904d401c216017990b840070000802008030110644c2003248000b400682629a40326007580400e600001e0958481701d803003040e095680c1a4400640341c0c3c680b20070000038130f0304081d0094020ba4028030041c1c3c500204d0601002034040d0074503a0002e10000383c2840100001c0341803850f003100941d160f40d0341d41c442c0d120f44181480b01107080307031011460000485580768254801022564030003010305041c81c2100f18000d240411041c85507040c040e0208201007a0796010030040c040c05001c4880c507650805050000f88031722030040d0722505006184003400b04241c0100c4046804a84c0b0100070808400381302d8072802d841c02c0d60582400890040c1c00c01b03000321030490050030100d0b07403001c1940d030300c04e4600b44031081e524010b207080c0f03000c1550310305000c240c80341e903401490029801115504210350450040609016015050204641c480ca9080005844035040700020040c2210006400d83c0c2202c500c030060044000c200d0000d400200000c1084001c04605104050241c405c407207132150 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 323984613 1250 323983363 323983369
    0x4050a0915140714070f030e130c0c120c02040c020123011202240f031512070e090c030f1027080315061305011b0b0103020d0c0305060702060403020705 67
    0x1d40d608656002c64107600c00690224000c41e14600c1162042c020340746000f50340e4030746161035549002e00300c00107142080307481e80c54504000030603401c46075030a0802580b405c404020f451240000d01c02171030301c1034021074459040e00a001c0b80352182c1d0080c1c414082d202011a000b4001c1148150f4040a000454a080504810004018140c03000400c000c41303581a40e8003007023400c01607258600c002054030180d112042c000c040c06003102c0d004281c2030523180d003816a180c889046e04100d0701c901a10010305941703103400c0000340060440d100380745409600d4503102440c608000110403401d800d44035084039215800c000041c500d079011705440c0208406c402804e030b1040d0070055a004c411344100708e18004404070790364800840d08460314850b0040c2e980101400b2841039000f011000d60060031840d010000d65030460041c000303c000f046911545000c5580d900740d590501800007a0040b000003859404122004050201540d04803045810a1418080003559400222811801801015000100c0d41 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 323985863 1250 323984613 323984621
    0x80a0b090115030b041104110c0d0206010b0f030a0b030c0409030507020405090a08120702100606020607200a0303090c0b03010b040f050f1305340228021e04050a0915 73
    0xe0b604c003248403451740f00d603150b030448103c4200405612999400c0c50704080810345009001c51588100503144820030700d10084d0500c07005034000104800108403512940d5441c0007200d502c8201e904001030f00c20044400f09260415030f80c6c80941080c40d040541c002d150700200500300080c03003100c00b40044d980d00a0b2090315a04001d4009040003021320803401c1c003030311407414150b1150341841214207016041c101a01901d065078480005030708000c0a00029a601158010108000c1410701c06004000d22071541c3d18a5420409404c15944000310010801c007481618000c100121450381c80396120010701400b40d1161044c11441085c09038002070700e0a203d04410a0440002c02c1e29642c3e1620301d034824041c01d0000c4c0003004d00643d0301d12000b030510038000101d10030702e4000841608a0994200030b49030580400d00c24415545181c001c0c9040049101214a2141d041c0c1c1c105d0190311000103d1000b0a1030050050b9015080204004101d809a8408007107140150810105100340740e21000c02c803 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 323987113 1250 323985863 323985869
    0x40513030f0c030e0306250905011d030f100c2c01141b0102130501080624040f0303030f2f0a020307050a06060303030605030f1b01030204080a0b090115 67
    0x214000003030441c22240201c501c1e0141a0190400c1341c0d2000310100007a090070022107180e0301c01c018042c3d0550b5042c2c2900600c03880220309080110f105410040040c016110840c1c8031510040da406040d000d40d2414081381080d441800c049440160b07900301c0840151000100110000743e4429205034060079a403c00110540304512350319444000e200116000e610706030444020b01801c022928100c4581a920300310301c1d444100040c2c403000440c180c0104415240e00c01d5040003a0401409400c1c3d5030403d201e18800e559407010402100000c04000c01800b8075401100c802a03880030008c149500341e00504c1d860070410004000101e802c40c881c03000c0c2c64080e11210261083e070035011000c0300c03405000b404800e6041c011241044019039440f490240440c0080b01c905849580410825416004200181004601414251907141203036683c8035a169504c4400c031907144e0710b420040e40a64101c901401c40f1000751411440c2500303029074856002d40740002150b283c030b21a1051494400b80c04026 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 323988363 1250 323987113 323987117
    0xc251a1317030c040e130b1b03060d0f020d03020f0d0504060c0f020a180209030d020d08040f0c05131e0506060912120310030606090513021c0c08070504051303 70
    0x1024411000001060700b000b48a418010010000404c0000500201350b00c200351910440b6074490032480c0000000e900030f03040e0b80c00c504015840903001c960407010390b80e0040082d601001c2c41d00050410300400c0514101c06500484201c1480c4141076001c241600c0c100440c0085802014a0b0142247c5501c601e01c603040028004011990004003e54080024180020000e041040d1140f08020701c1c11114481d0030601a40040c00d107250342000c0c484440c1c035211500140c10f05548903e000703003070614018001084180503080410030007109056180c05440d005c2c200f2907100700c45049620007040078020240440c10840144180c06003240141446030a0103425903040c070401c2400c0c0001a48890b003086a5402440e914240320080c01c40603610030385401c5014180701c0c0c99030030810103c0b2088d07080581c007181424200b20071200340d42c201c8076040d64162008001b840e609030411100203036422000340351a080c04030010700c1100000300c1d00195081101c2c20419525101c1030301c001003200e4040200 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 323989613 1250 323988363 323988383
    0x141e120903030402100e0a170109020a0b071a0c0c030a05030a051006050d0903033201091103130203032a0c0f0d11061903061404020c060c251a13 64
    0x1d102c3d4442044189000c0c01501c87e941e100c88550f000103039590407112139699507144140130740c0f40c042d06520050140410741841c049050300c566945410686054500b002d080003c500d01840e1042200c19072151402030b00d1325004841c9004100354800d50300b1982c07060400b40030964110402e0182e400312092902c905140c04843c16480c40a02440441641410ba071900107216480c0c80c041e440ca400d607088407003050640400c81440a0040e01a00101d03030561418006142c00920a0201d03500180c51030320100300d01070240700003072441c4600211008102e00240011811100861010079103982c40d400b038604e005161000e00902e60f9880d594140c0c007601c00320080000c18180c0704900290320300900440c0c03030f008050012014540c2410305900000380e44400410414140103007544054504031401c0d480c12042e01d845a50300c1401801e1a065648001341c00c3c0d0000c40c40b00d8103180c240c421040b0910454040f414440300c0700c00e0310212490b1816201000605110329281000031981c0e206612030 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 323990863 1250 323989613 323989639
    0x60f0e0a05061e0a050d0f21090b0904020c030a030e010f02070201020307060b12060405030a090b0c030a1220090a060f090e060d0c081b03120406141e120903030402 72
    0x14034612032000b50700750820304c0018082103645803d000e40034007902401e0035541e00300043c9054140e921109201d1548040c04204005903107a000c0c6205084030b220185061b00c40051a0004009203d07000840b030603440002000800c040e0190003203030740030301060000c1041c0140041d80c40c081c0c4c80340e000000c0c0180c00c10003e0705c002400306c4d1b22080c10401d004d0000345d0300d003076800700d100d2030008152415181d40d03001007070b07030056140d0040c806d1002d400d080f21490309041c4a92101d680e2409103102e145e05011100034808840d0301190300840d0000c016400302e0000c41d0003c1c1e41d0703451a5200d0300784107004a203800008a074840c040c42c940c81e07503a0803554824031440e00d80107884181c880050816903108c1085411100030492000c0c03540c015040f403201030400b00c3c200c452025191148040c8540c040d400c40341e50305e1054400182a60220382d4a41840107403030b0800720240c4824414040081181800344050744810b40c01180507007002c4035001122051134135562200c5a0740c1c00100e900030743c44100c0d08900 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 323992113 1250 323990863 323990899
    0x60b0f0a03080319060b070c150509060703020f010518070504061a03100503060f070221031501090305150403090b090d060f0b120c0f06030f01050103090302030d060f0e0a0506 77
    0x2144d00c042c00b0a800800c0b009202c80a0007034480c030742d00c511114040860345406024004160ba4002c164013400a0340c04803901c00701520034050b4030506e038400d00380403559509050080c0400703280315410030020403482ca071945101e100750000035110714031849282004901810180f24220a40e0700240b00c1100c120b009045a4159030f04c02014452030355115100080c3c1910f0410040e4080d81107030307114003400c2c907180500a2520742d00111168102c40842030420801c03489204594006820100c0301d6540121f103801a81c81c1d001c0f5a00c02813081c0704001100800c900c80c070401c28043c510036900c4243d0341c0c5d0359201806980c010300208a80c841000e50f40f04000400b190701183c0b0740d0704411001b0554007110310014040f1050800020306603003089000d440c807072504001c80200d50724102c80003400c40c00e00003030010100b141401041d051641d241524800d00d4002c10603107413010524030040c030680740c413101c080480758624880c1045404080d00070542c401030070301900340b140c4405030007110300e0084d098034 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 323993363 1250 323992113 323992117
    0x16060905120403080403170304021003020307110601080616110c0105070f150504020f030a150e03090a03150c03060e060f060d0e0604140115060e0301020d18060b0f0a0308 75
    0x104490512404005920204481d8040c01c002d60003884010780326403031802c0c60108582c1b1000416031080d010402c1000590703950710003081500d1245001a240d40d6441401d540b0b648241c100700c10540305940000500c4800002c40c94800c0305035074010585902e09030700985460990464001103030b0032443c400c00305540300d81e002c2e0800764081e0002d040d10009035103d40343c02550442c210300030300b5100e2041205505002c007844041c0075064000b450410050789a1a41005a51000000305501c03020900c0031060100161b03a0030181c01060702c916950342c0d1808040100d47d004420043c24203200030b180c2c0c600d01900c990030071104192141c500a039224020418480300302480240d0224040c0440e0314881101e101e10302d00c0c510200010301c00350900381080580590902000246a07040124000000c03085d00d402104031030309410b2801c800f40c10b01c00041d0281c0145c04503401c0307041c0741c00120403800341c0100208100500030381c1c0070044507036180b0900c0070013400303541c165811180b4110100006030fa0480 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 323994613 1250 323993363 323993381
    0x5060306131104020c0d021b060f030c21160206070c08090406091d010b0604081504030c051b240406051b1006061404060909050402030a050d02100e031606 68
    0xd044a144007803080003c040b41c12440c1d44883c1680100c030b04080898042002c0c001d8103c600d2840361341151510001170380780c0300d280107c071b4000d000400801d0704288103105503888000444034018108100821341981490121007194141c00200d41503060b02c0d0010400c54020825652416504021600c660b00c45511500000b0f400643e642400170b415401c62082d98508102007504084010b07042d41b6a5081d00c907065003091251100300300c100b0240000103a42c0001030000c0ca040c004a0b650307410150b03600850031038040c1050169904090440d812a0100b10b20250201d03201c5c00f0000074090651203000441d070304502c20b0002008180000c40c001c030050144d812040004480c0500e4181311141400c140d050402d1000c0c0c0c1340e02c0d00780300e1150405070b055104080241524180703490400e0003850420b851040b18001690b5802080039034030180401d516040d0007204a50301d070b01803032000940c1c03000e02c2070f10118104d207095412142888003004079801403804068220800d405038842400401d0160 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 323995863 1250 323994613 323994623
    0x9210302031e150f18090304090b0a080d032c031c0e060406150308040b040515070507090c0e060a08010509070507200301090506130302100b3a050a0212010506030613 73
    0x41498500d8403c8003000710f03c6410041e004d1f685035843d1401e0502699080040d20b8880c00349a81c00b4090304bd000030700e059071081142750100b4002143c9240144820a014200005a0490410240303585000000303101a6034602584101c0c0d1712031080410440e9844600e020307441e000240800c001c18031a4100c3d0300b007212071381e400c4080c00d980c036500e90400f40d101d648500281140841c5c108000d10b0071140a017241c001c903905891414040395200342d00d0342e03c14020035440d6035444802c0c807030243c881d0100b883c0c50180030382a00d94480d41080d010784a01d03024840c4504c00c0c030302040091001403050058079030b05580300398200414600110080e444004a0301020380640d0b94046600c04a142002040c1c06a1600c0c41c0766213001005060081c1092101c45200d5000c41c28511400c1040c0c503480804c500c00800d4480250b43d081030500c000f0020711600d900f5601c01d5229042000612101042000085100321100da14810030400100d081c0c072000c6444a615400000000b2060b071440040503420070b12034 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 323997113 1250 323995863 323995879
    0x1c0605060d150b12100b09030619060f0b030901050117030a05030c13030f0b060108160507051c09211a090a02031e0105091203010909210302031e150f 66
    0x100c41043c0310340c02c4a8010f086954843c0107100c8104044082040034101c2c1c0c0022924004940c4080b0303560354005041d402d1403040c0c10000c01075100c03807540f0940c060248084031001c003640e41c45401150f0741040e9910a010b5103020b0000034000180e0140202011440024500f0090240010381c0d45810040001c0001d05081108170a140303220310f4088091482444408012055400d09441c410401040313035050000700340500844422414045400725210b281c131569620301445c1160a150944003c0a01e04043c01a02e00110ba0092240c0303040e1601541000d11203001c0c0a0202010000301d14003038040090155064407400b0054071280c1e010b26034a040b500d4801c11540464905071101507100e20300a0060401065031201b8001c003600540140024401d1030821816040c0703d103c18418581460303902e00044e81084601c0d0707504e041a146580c09620340f4049090302402039032040b54091480f58065031121410601c2656440c080c03901800502c406d001010240064604c0c0f0400743e0354400c1d40c3e = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 323998363 1250 323997113 323997119
    0x204060306050907120c0909081e04080d0930171e090109060e0118120c0e01080a02090406020f03040f03090501110307260408031c0605060d15 63
    0x518014200103600c9010005024079003810340700d0510105400130445400c1e60240170003c55a01802c003000d0320084100010f20a0144c905070303480d4802d20310301501c6003000c492801c80c50504032001e0003c4620100c04e0329010a10204203e595580d00d0190001d191100c4040d03406901055074102024011500307580030f00225900c40e00075a0400141e002c010780000181440c0b0f41014031a03004016500400c0d260411060f0310010341414100c1c0100350401c2a00880300c540c50b07101d101e91006004600d0b040110340e94440d003060100c440c12050998407031910000005100d21480301d038604951040300a801c41d5000c90b4200500d1800151060300c03459000e000a940b01d16110005500451058021a410b1842407602134078000080c4c4c021818803c2030031209501c07000102c1140c2c1c0300399022034403c04034060100ca4070f1070149070701c1c0f00e51041d1b1404200800e10190010003000c240301141100000400c0c80010b04040da81e00d40101034000905000c01c04c1c11034016045017106034040c0944041d060f803 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 323999613 1250 323998363 323998369
    0x308010515045102010c0504230616030e030f070602120901050d0c081503010501050112050604060f0b030f15100c020307030501150e0117060c2b0c11160b0f0702 71
    0x5420f8680c50021949030050741c103010b030244a92000e448082c01c001742014901107042200003190031100e0000040400000072566908003201c410207148106400d02d84558200140204003003680740d4041d2040c004c89511411000600000f1a060355004085103080c04c6681c51464200007800c0d41402414000f08543d80118018000110403583e1501d486241001003e10004c6040300464084e0745000014051660700900d4444928040d0b000840c1c00d8031008085002000e4690103407131148407292001c1101c0031660300a600030700d0001c1411980341c03101d012402c0140141480701c5d038031402c01044100102e015141480c1c40d50300080641c0c0d4a256039031207041c250f0782d02101140c1d601d103100005001803402c1c0d52a65000d0a10149501c84035103800c002d080e0364640c0030b803a040c46d8880205802e056150050801c075030310145404c50300e00c00d403090040500036010807503052020850403214080c0f4a14006100c6001c6800341e40341d44106031500000381c0c81c41c0d0000c2c0d10241101010800c0c1c00140e2 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 324000863 1250 323999613 323999729
    0x70212030702041e0c090501270b070c2d0e040f06050c130f1202090c042c06010f080417090a260712060203060a080a030801051504 58
    0x2d0780400c5065207420008405104a880764170400061140501c0c0034059031345c1c482d1300e0f1300d81e0744003903089035010745100401348008800980c0100d0380001d0001d02c0c80208002d4402860460703020020b40c1c24028040d460070442c046c540980e401038050300540802c030400c08481c00c4d03500329000389031000316039040d5221036084c2d8000b15028030642100103180300d80032149050300001404280700c00380c0880d050082c041b031440b0328640c02910520290740401e41c2082c80b0422200188808110b40303115400d581c4508405401100c1180020b129500001d4155401401a1564924196519015030f50f840c1d59140084108444100050209001891280e00c42107002c1c000742000d514007140030340900e0180702c0d61590f8101030030b4407600416001c10400c5078a8000d9400c15034004005a21303a50381402040d4401c007160b005003050301c6103136005424940c02c646124162682542c107803040c0d28030052049054402c40c40b401e130420b071244c514121380740301d087e642001d008410080520030328008251102d00e9 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 324002113 1250 324000863 324000881
    0x3031602030607030c080a0b061c27030f030e0f0a0507050a0f05090c0d020708030c09131e1a03030316081b04050405130212010b1503090307021203070204 68
    0x140102101a009518040000a41c03058051409214003d413600b0000c00b05400035200b0702003a5140c10380e2144540d504010b40e0501d0460348280303200c0341c518000400140020904035101c1c07102081d8244217905104100c003141c150140c540351b01c41801100308800a0625980c1a001d6000d12054140410410702c0b00c02e400e980143c00a1081340d003004204015000345900c45c03001c01c64010000c0010341c0b10064050f42c042c01c0034405507166504115954060310841c00b00409100000007008010785c040070181000010640b03c020508810b000c20208455160115042d40511201c03095800e2005800c05c102c07519050010010307428159002c0f80c03540c1c001390703510503202c1c0110100c000d101c0d41c420801680003528440078001441030464800040c8141c0c003c440c042c607201d4000032014103031012041c819650250215484020710740c2d480f4024014001010310403041d030780075425803441ea002980d01500314040518604506907080060058440d058a05940014044030025070b48920400d054 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 324003363 1250 324002113 324002137
    0x607020d030e19080307020f03010c0e1c1b060323010b0d11030c0702011b080703140c070803040611150606070c08030c060114010819050601030e071e0605040b0322020303 75
    0x103491b2244104016040344011441c0039a150020043c14164440703030500700c1100940315201041c1850340342e6a119004c910024251132855000c150740009040503400c211502682c081004001c010748802608400c22550800d140707a83c0011720842c0d1703421000f8580c1104284002501c42c085090070750719500101c5100ca407105011401c1c2080d960807880e0361826400001000004503e1951401c0d01c40c00340300405810000142d12200d201e80c9141c04850005c48903904840c0780c0343da070742c2007544c0d02e0f80103000381000139281441408081c1030024070301e01400c4104c42a0402680c0e004140300d5540c014900c251a19130543e640007030032020610092510301c8404002e4000d07507050640025012410111803070400100508201019505554024205103d1b20020403c0d13141c00d0300403006820a40c61701c0039180039500b000502203442c25840c518525465200e070801d542e840c1001d86e02d1380140e1003080007042c03023000000d4000078007100d07001e2850705480310000d0009068021a00e10740005000c850 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 324004613 1250 324003363 324003367
    0xe01030510050d0809120a0803160306030f0f0507080706021e151e0c0906030a090201180b07110d02030706120f090605040c15020c040b030a0212030a0305060607020d030e190803 78
    0x1007400c0840c07104006e9007101c4000d213003900e0341c2d40d2010701501c4002e1116010a400c000e0040c0014405d401078001540c00000c0c0a4150a05003003603421110618011203203071107600e10001d82c410000c1405801c4420503000761498a02c190741242401061445461150190340121036100c104440380d6805640000306140d0f1084040030301421280b00500107981c003c01c00d00681c0081c2d078903502125804400101c0c0447d08a02d10300c016903610b80c40400b4580c0003440f40d803021801400280c090b04009002d101c0c4030300c1a202043c1841407200039940d001c0c2d0580c0001d9018042940110700d885039802c2020b000081c1e4045034140d0004444a01408840250310390060005002c0e4009049002c2d0201200b140701e030f41d20100700a1740d40c49404a18601030b540390042c850705960180710752400690040d001283c48008a81980d80781c5d07102c0009000804d00d05408191760b0304081d0151951503501800785042d40125803429140e80c0810f43c89030754400e802c541e1809080c034803a000040100702ea800116 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 324005863 1250 324004613 324004627
    0xc070b1609080703080403020d0c030b0109090510050702060606130503070902090f031b210102030c070c120201021e0109020a0b181e0607081231030e01030510050d08 73
    0x3840d8401c1c03584440b160782e00c020014404120031000710f0301103940c11110000000014540110106515030000e42911f020000020342a420343d0403a0406520a00036102ca03043c264000104464080e1180001039118000262003402c1000c01400d022002c8402000c9040d500c0c0000b07440c002c5180c102d40011600800c181c040313802c2039080514105400c80c00350600700301c2c001200d41c007001b8150800d4810690a44410710540d03003154150700f6818000000d6540e440c0610900b00c10740d02240d400c64101c1c0c0485000528980c0c0c854040014980c141d000d41a014810a81516401480c96204040e9503a468600005a5420096000030030380c14007140c0d12010509400380100f45000c9c4502e010b0944060303480e0130400c003c005202652030440b840c80d214000c0b800e01889034002d2541000c0702100c480c084c806040e09000304800c080e036000000055849004e00c2a010301d0074103c0e03004021902005004840c4e40c02038003c503900c00100583e0503021590780001410015030b40700c0c151951407000440d1 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 324007113 1250 324005863 324005867
    0x40506010219150e030a0c06021309060914010806041208060a1503063611041a0403110d051c051608190f02062d0f0901240605030c070b16 61
    0x1010f04c03481c030025509140040c103010300b00000290000f041d80b9400110951624080ca42000c09060b000030100501601da00c3c0b080e00400b41c4a1800c0e0b070b0714140d03a0000030030840009046120350752240502141d954401d01c1521840c0780503101960103040d0501c08240300c8800560071903140210b650205a482c036224040e10f004011660303500b0381c0182030b03451501c0701020010094203015414800580c00403245241011801140c00c5180500c09030401030405514071009442900d00401103c070317003d200d0364100018000da19a00400f150082d070300d03c9481d8894007000018071a41410400c1c41d19180740a58244050410801c450440000c035108008981981200c0808102400c1040c0c030003040000103580d41000500685032101e840000d0b1a03440310480d41c008004080c2070740e00c03405040400d0300c03070052942121183c52540c608201040142d14625011001c901c0c1c11688030b001c40d003030103000c442c1607100414204807140100a100f000500e0108814810b001455076040c1c4180000e0300 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 324008363 1250 324007113 324007121
    0xf0e03150a02180103111c0212090f010c02010515090711010f02040801061401020a14030702030d120b09060a0b07030e0d0c030c0e07050f0309010e0a03051b071404050601021915 78
    0x40f14101441c00001c0601d1078004012515000d1030300d402c0400c0041e481c1c1c40304010f4454084542c00f042c07060b01c140141c03403500145122a240340c2d000207014a224049040b0b003200d4003119240010300740124828110304103850800d8121065280050040c140d030103030307103081d502da00b061244402d5000804100e0710f4400c1c41a00701401440c40c2c0a0820141080005d45c2c0314800d40b400b800001014181c1000050304008039840254040c041d00c4d290584104040c0421002c0c80d203902c0a030707040c0900100245000a902031003954000c0124054505000625600344c00485044043c40b000e240041515581c0506405d40c00f40b00300c010030b0300541075140c40c5000109a91120400c00c0d500010302c604075030404140d03812600c0501d060b82c0c17680c3c1c90742c00c054054429220390407040c0c050441c02c0d20601d40c1c80340003415600c90201d02c404141c11041c1126586813854442c5460100610080041c5840c09030485600a00140f044900d01104a5075090ba40440c400c8100c4440300e00f0014100c0030401402 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 324009613 1250 324008363 324008407
    0x307021005092403040b09070f0303020706110313140414010909021c03020a0b0c0405060c010501080c03071805070c0c080a06140402090f041514060a0806070f0e03150a02 75
    0xf4459880a035809400c1d808003400050038600200c1c0003512800381000110000c01ca070a071401c5016659040280d1100c8c0e9074050440042c0b2407180240301c04200108403050840c4504501c6003152800c4500d07040358503c0c00040e40d215803610401c0444401842040d406070144440005400040d88100301c0380350400c400303100d408000100348001094001c030b01e10410759008000782c4c0080d91155007000c15881260030040d03108201040f6034028060540c040d60580f5840c508560b510b00c000c0b820180d55030348070320580e0b00546401c9030754070f04108542c01680c0c001c2d0740b608107140c0c000b0b241d07901c640c0c1214107a00110b4041d400300e00588240447d0380103003a42c00c440e010001d010350600c0d030045501c641000702042624142040410200f02502c0b080c1100c06141030010011881100c600110030704090b6180d506c01c05a180000c01e401002243c0c160094034162079910000e14440c90941d00001c4c035420710741d4507015402c040d04152160f04181442486840030041e51800782da0243c0042ca140c01d2 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 324010863 1250 324009613 324009649
    0x605061c15180506060904020708271003020913020c030a08010902160201050a1107060f14040605041707051f0810060f050c030c070b1902060c03130203030702100509 73
    0x2240030858591040755104520b8240720010074140e03106000304003d48225069150460310018001040c0203541010b03100c25810710034010713000740c00082c018860825400072650710048504410240c0c0303010398000c107980e5501920b1029082c00b048100d00c100d8025136074000098100040d41c600c015400002180503141d0240b04608050b2007070010451341d85441030081c18454006403840e02d0f10700514100d1040002942181d00041c2c0354103000740410745203000540070484480c0962001111502941d080c1c914035039610b41002e20f000400c04a900300d11000148a000c0d211003c50240c4038a940b0202000450881d2810014030360001000740700000c04501c50048000d50030b00007250300c800011902801840d10640703941100142e281148144120b0b0134952041d03540020721040d508016101c600e1180f241ca9220040030b80003640c681804132052580c00c20b040000440e01c0c0420385000744e5240c00902140c3c1010100c0d80400e001c03400c4020a10081140442e03e040309191185090142544075 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 324012113 1250 324010863 324010901
    0x31101020403050307020f0303121602010c0503060f040510080f010204060f030b0d061a04051003110105030709260607200a0c0302040203061207060315090506030a02040e010605061c 80
    0x544943e500c07070044100013417050004004100d040d590030001d6070300c20105100141030b10709001c07100141030b1280d12550300141d428620601c0d111070041055a1288601070b0000100ca00c005003000000c3c80c00400591a880f20300b007012681400802401c04051200d07400182d60380c0c142940640740c0044011440100741c10016030403d02c2d16020f0310f10401c81e5100c68007181c05250f401d03080c03030000014a0381c2600607107803104200f601d041264070302040b00d02030b10454a03400004001103e891004588001c046080c100d0b00b0044600c10303102071002c030310b420f0f03046d40030150402c4081c500748a401d82c1ca02e4006041449200b83c1e20030794241d59000c44c01c40900600c1610501c1d03a40720401c0c00680f03c041c0c415a0b011000846030384070101a1603d1801490588a00075219640600201040c2604a644a4950f170001c174a20300240b0400d801004003c004203502521a401c20000e015510280d001030354031500001101e45952018041124507401c803581e000c10000c051008440b003000100f2100900307 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 324013363 1250 324012113 324012119
    0x15040201020a060c0509060a0201020403020a060c0b0f0403020309210d110705090411040509150109050408030a0903031d030703022401060c080f07200114091002070509040f0311010204 81
    0x5402d2441e690161000c180c4100480c81a03c4d1801910040380d00940300041710040607074194002d00540303200302c0340101440d444001c02c60f04501d582100810007526140861005000d45404650241c0309204a900c0c02000001003120780102460b02000c14079500940c41070410b0910903079881d1041854800b03c441a031500d065606d0840f403061030701518824001c00c09000c418110074554140c080e000303101500301110343c0d0355030b0384004603807101e924541d5002140300b01d440e0203401d000700d800421041c11521a06c481500615114204500341a526803840da00301d00c4505001a40b100000040c5444d400c8a082c040e00b084c00c0600b24444018145c001c1e02c2c946915110882d0664109103000034100c00d55140040b5184124441c01a14090100f882010010391803400303c04407261030010380c0c421469074019540441c100460a0600308180500d403014100600a070503042098411a00103d954901140140c1c034261000d540b41041200858103140e0085018040540605c1c02107150bd85 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 324014613 1250 324013363 324013367
    0xd03021c020c03030406082e050f041d1e070e04030c020d0510091e05060105090903040302120606120601030b0415020d0f06060905060a0c170c1006050315040201 71
    0x12402210030594900c601803150514420020314100d540050122980c56031200d2020b00342c0b40e42180c000c41d058000c2d0b505180000d001e0a40c9000302148602446079190608042003050709040307401c580c0160307481440c02c04000d07c905007100c0c40c06048015103a01400546203000513500c2440740c0f003460703115034010051981800c8501c0c0e40706404d4030300106012006c1c4001051415400d4002c0c0052103004d0140781d00f56015407007218890b1061003004242800000301f0100050107030805411904610010000703814401103e95004c203244040e0391800e503e07640016480550248030000030303404401004414204107000105001503803004050661640c1d6860000b040000c20044c950700107442810368100017034040d00c104052890302884083c1802d04040010700c3c007807151400144407000d00040c103082c1a0f04880d60f6051540d10000d4040e00c40e02c800300303180c0c220b10741d03c590b00c01d003004000054101844810403180485c00e01080c0c1e1032400040624100300400320342500702903841408010317a = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 324015863 1250 324014613 324014623
    0x170a0c0524012705040317010807050f040e030d1a1005041404110d090804030b040b04060507032028090f090c1209170d1508030901021513020a03060203070305060d0302 74
    0x802034000c04941c5540c3c1b403030110349030b403c1048248110008500007007a0003902045240903100c0603100c12004001c0c1d4810001510030001030b000d441d4004004420654885401c0040000401c554401c03810b03001c1c001090304244036016400c00194089420310402c9884900340402c1001241e0074000045220712040142c46a240c86805169a540710342007040180020342d802075400410720515480c0c41c0c1059001c403d82150304a400500c0c103000951202d000b0b2080d8818140542d8580c42c0d5115a40751303d6840398040604140318410084074542100844c2800c085040841e40e078000c142c9141c2000302d180100c840e00070750845c50624441300d07400c41d84410b030300f10369500d807050101c0c4521981c20302e1505c5010640d641076550030005804c5041d14815045459200e200c00703621604e00b0340c0c54801a4903401340c540c0890050708440700c500302e030141008a440e008044611180e49554036540001c01204003a4000c0341c6c1c0039004005c2081040e014800c080e44044152101e021200c100c0d80c3c02500d807 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 324017113 1250 324015863 324015929
    0xc040e250315122a0b07060204030b090109170703020a080307020f071403100b06070b0901021c050f010303051b03041206060b1813020d02070f1e170a0c052401 70
    0x4c030903090080341480041034124000c00392800c80d10b0390303100e039424000c010798800d01069401e01d030414003103080c81805205642c202c42c1c2162100760701414544c440390850b07100d164240d00318411f01e0049400b003110140118010841500200383e644002d598040c101200f85d80640c40305006901c0c40c0c03116803804211481c2084d030744940026210b82003000114240205200a8481e45900c03040081604055004040d40c0aa0344125018405404084400d881c0700703d421000c4081000010000280220084c058680102c040052801c0c0041c900b1840c541081c2d029080b00039181640b10306004c92032088901900da00c6c6007aa01c0e014a14005408940c0c80103c03181c010a1059413000d40f844065040d02c5075003603011025950b030726290030006880031107888252541e800703d00009503c0c0340d0644540c209132b9440101c019001c0815021070b419900003240395001d000c100080078001420601c00030030440421203500122100c15803c0c102c62010580013840c0c01003511b0140d10050345031000100310 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 324018363 1250 324017113 324017153
    0x21c05060306090d120b151305040501081207060c02030405190312051215030f1b0405061c030c03020c060721030608100b061e070b0f0c040e25031512 66
    0x20182901012507c3d143d6601129122210b01045403a01d0b080440002e404a4070100c2d0113001e1662940b5145486507100e0140311142c1c08d08102000005110740c000441080690040d282440e60b2000864851003003407860700c0743d820713103200244104502c1104410308071010f4581503040021070040380404810103460491070300704040c40c482c1d450f40c00304076481101c1c52000c207032802010b54100310445c040c8402c5001c3c0c4150708260000340c080c1040c0b407410841d0039103215890080000f40d10155441c0841c03d05c241e085009007429440b0541f41d0100034071781e00c3e00c1500881d81c050a482d01a1003a0030034808190205800c01c0d03400c122070300d800210030000c00100310300001d4092444000445510541c0d070702d400c0055800403154038118648010300048e130b0051419101a54a5000100f500081101d12407050030090201b4002010891500386d407007007a1048280140012551300c40004040c0c0c2d00150010f521081c58800d843d00c1c80100c203006041202e981d2048880942e1513540c00001e080003851 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 324019613 1250 324018363 324018371
    0xe0a03022b0807080901060b190e0409110603191404120315181b020106170a02090412050909040804090e060408040608130c030303060906051906030c0201021c05060306090d12 77
    0x217420083d030004004001c112081a645c4416000304100c80015208050204103c0b5082ca0300900b054004c0740211a480441500849404820002c0301c0d04040d00d03000c81e11004000d110740d8084c56228255258803029220440c61030949020000d02084091007020141030408602c0400c0c0d413510700d0310554800503110740e034114280ca486030003003071311109111003800300111060700131f90194803101c00d540905122000010120b8403059403080307154002508500c51500040c00309540c4140e48245100700e2400c94605550840010340c0c881d429582070350346000004040090040c01e101c0d0202c040e6150703024064503e010f48601c291401540b155805007c45000000d001d0380d9544146110b20340d0001043e00d100b604ca003802001015203018901d0241e02d4158041500e10340072141d0242c42c0740c00d00600b0801c1d030a000b4200d001d4103007401e0381002d540d000e0010030030341d010065032030360001d5189400040903d420703000c1614021014040403800c0d00002c0d03004041c242c0c890b030707500340e0b0381c0e19200042 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 324020863 1250 324019613 324019621
    0x3170702030a06022d1218030901050904060e0a06080601050307030809060a02010e030c03030103050c01080108030d0b01120617011d190c0302040608010c11070f03150e0a03022b080708 81
    0x82070a80c454031041007000c104000c0c21740700c0303001c0c14007500001603452000d4056a5801680d01002078003d18441420b40c03080c801046290b100c1d030010101d282000d000482c0c2c565488072045e080b940700380e404400b52515098180321445c01000084e0060000310300501c900e51460b25118001c2c03252071402c078000c050018211003030a000750003c2844000480031243d030b4803440d82d403640e120f40003800100c0c0c5601496110361061741c070403892075040e41d0750280a5807a124100424030028800c1d105a18140b1070307c90100300240c100c0d4030641004000a418403070182c0d190144542c215000394035480d0100c804200680001d800015078111462941042074510040e00d04010a1141d000d900080d480750030000c7c003065000d010f400c4044424042e4580c089d2032080d104d102921580140a001181c0101801c00c2000c41d051149240c1307100314071080082c01c0c07038410f08018202040010241d015a1004c8241100e040032800700400030700b03a5121a5840c409010300007804403d001c2c24080030010a04041 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 324022113 1250 324020863 324020887
    0x140f0409020d1104030b040b16050d022d0c0115060915050906270d02090a0f02070602040b0901080f0610080702010e0706030b010e01020318040507210603170702030a0602 75
    0x80904403d020030b4950303c440d0349107030103000140e0890342241d0845540e00424421240c1511084008c201a20342c942001d450700b0440c4002e40003d46403049609105041b540000002c03030a4108580c101001a0380d92100b030020542515100303404e402848120080402c0015072104245098074030000c0c4e41402c441003907804407031301c1c0030340140b007580035000150b1040c80b2905155200c249404d03480741d68242c503d8032010005812800f480c003a401c130b2542c0700007590741603c1d031f848440c3c4040207403c014100f0220381c07070390300c2240c015401c448920303980043e5807540c1d0f40e00000307007030751082080d0b0f55414249462408150a551a21482c0e0300f408084404206814002e412400c000c002c0d40046403491aa149001000740080c000c1c614007040003004900015403000c0201e03508440c06807070800482901c2403e000c024000144801c041106087c0045642c00071007024103e10313001c11002140e5541141089611281d081d018065090300411020f001a10040b803100d80c0181c00000068031282d10707600c0 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 324023363 1250 324022113 324022121
    0x2090d0503161103030903101503230c240a030209130501090b0d0c030f11060406080a050c0403051f020d0908030108011409060f0c040321140f0409020d 67
    0x6140e0301012078441411110a000782006500a034091215080d258091688910460300d100c0e030103420440c0585c003042066002902d8410b0a401d428150b035a5030345a0310990005c990400308180b40345090441d00840812440e40200d1080301d001c500108829607401c6004403c0b81d01c129031441c040b5051039407500036415604401c5003d0300a4030755414020748400186024041c0c1c281591810308603602c0740c01c105005d050069808440c64481c40c2c00c42c2c070b03048003455980320211140c2001d549103496544814001d00020309031620360300124140095284103417040103011002d503200c140300c2000850340c0010b442c5103000c0c40340c0401c0b211442d00d1010601911642c421248100d0030911030a04104030788000354100c03401d10000b04010f60100300c036041154415240c0321015070064010131b4a106492030100e401c4130003070111624042e5030755903840e070301100c00d4000030051307100c140b0b4001c4907034101d6281041049541200d900d460000440210700e805280103110b00b42c1e60104140c40c024400f944 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 324024613 1250 324023363 324023389
    0x71206050405070e0a0f050703060b1213080705030301080105150109060503070c050316031211030c0a0512071d181512070308040614160b040f060504080901090e0108030301090209 79
    0x401303a581468040030000c00b4104866440030402d00d48030000d95003605c240b00d0031b0180c0b09058203162900c250001f1901515070003030040301c007081c80500d03c0d0000039150402069000c2c0b16030043d50b01d0390701d42a452070840d400280300010044d040300072102e0070f0f0303805070a0b0803d59080707041c40d07074807900da5440840d4040c0700500002e200f031000141042000d1280914010300e0b40c400d0303581c034821000025130803048e42e84080b0841d8841c5012b00100c5e0120000c0005020b09205901d081400d082d000140c1d8083e20398162007140100e20450036032030780018862010503203040d040e1840501024080e030a43c48681000b0034019200346600c0f44111740b592001188590107403007808580704281c030380c201001c0c290b20511840021440c844049a00e20b0701c5141503842d0b40c18414540804400f03248c4880400740300090040741c84c40c9410003484000383c624800c0c14080c1d40958070340b80d202c15180001600600c038640040ca40041d00e50010482c00400000300d9042d20700c1c032030015890710505800708160b00d5800c1 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 324025863 1250 324024613 324024629
    0x90f06031302031f0f1509051e01090c090e0405072601020d02040501181404050402060d0c08060906010e0f281202030106050619080903040b040e0402040e07120605040507 75
    0x80c00d102c80c526001c4005003203400408504101a10031441c16004950303000041c50440c6c9201d4908002803031450b40019030000124006006030840c0354041034201b28244c111041e215a290032000000381d01c613001c0e0014160300b80c02e01c00d00e4141074031081d43d103001502c03901808041c1c003092844480d034512008090302c00c02e80029511502d50024690203904139006d038a0015140c2c4800390000c03005440e84c4802ca03044941007541b500080c206210191070020000c1c0c0e0040d00400c000128030f4400d1081c0b03110f468031644d403c5110304011b07040014000c00608500c0c10040403030604181580c821824000e404000c55807400a07100307849410302d042c2c00031000b1040c101019180040c0003061800041100c1b84210f000304491030300d80b020001c80e40241d0a80070400c41041a0040d64903009804503038001c080901160b04059640c5100062039006400051480e44610305200440c2080c1c010019658940000781c10424103140c40c101e1200c43d001805040141c6500100d030034000e041c45250050840a = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 324027113 1250 324025863 324025873
    0x20d151508161d0f03011d0c01091805060d080703030507200d05180301022a0303040312020a03060807080d03050a0902100c0f1e0308070306150e010905090f0615090f0603130203 78
    0x7c80c10000e4001842d641540e031409040074034150f07036101c0c000c484165440854040f0f4002c54501e29003000308402064150131100480b4500702041c008000b600708a0b00c6aa001319440c5004072004240c54102051682c2182c1c520220951a00010a00e03404a51080c030702940c940780c080b8580c04003041241c15050709035100181e20150081c1e48200c80d130b80010100761000b00d0301e010301181d550f01e200c200c5019001500c80410141040e0140c4c00a1a00c1001486d01140305500c4243c01410301300d16a01020075a80b0918a006586406008656000316201d40800400c010786e00440d01c0d8040c0484d40c40200403200450004110100d500120b805405c140f0100c030b5100b01c15030021064020000c140c001c1168039001a104034400c0c010700b4190b40c3c842d40038482d0440f07001c0d0240d070602c018a2500303040c410f4440010615071590208141308044403216103003036040c945d013401502c11407010f01812200d400c01c41154540c0700c40d440101029019550643d43c0d039941c10b45049440d000580003981400b030 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 324028363 1250 324027113 324027131
    0x12020307092a020307080406262a04050303031b040306020408030304170c1506030a060f050103031806093f06150501080604020d151508161d0f0301 65
    0x566400c5a0041500c00300b01c000c04018484140d0756401410303170051450001300400c1c041203124204400d80003600b02481080d0282c40c01c524048260304840300805a110f001e00110440c0080c003598022075181c0710f2241c9050309200c0407980305d201c01070801d44000155801c0310400d03e0100e044400540e0411021500c4603125100e4a40303e500545007580e01f403181d5041c070030300c020500d0101c859640110300104180003140d004101d02110042c24150701d4015040104045441801000000c41d200e84000446606501e406020103031091283d01d4108080c00d800d0149640000c0900c060720f44204c421000394400510300c1080400c078184c2c2500c0c2480d404d061341d603031310800c185e1410814407441040c0403000c00c2e4034040750004502c0c030031240000c41060114a0f9800c15900400440d6996a400b00e5444014605400c10111540c00310818058648040071419440041a6040081d012610755040b0b02c1042c002c19000c3c0000c100c2c0c0c9440070a840d15600f6030760711101107410103000780c020b0111000d = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 324029613 1250 324028363 324028391
    0x91e0604050d08030f061f030902030c030712020a0e010f0e090a0f0f170310060518100f111b04020a09050301050114090f160507050a020d080d0b090403091202030709 73
    0xf003a40d55820035020345006c6402880c00710a500b0802a80c1c40600b5100911603004502400710704500741d030140901d0202001e0f603201801440003801040c07134200c043d96014810300c0035905003540f000265043c40001444508044e0801508603104013030904000c0d00e805c2c001ea030420540c0d480007801c04a0040d20542049014400144114020000703c20158009180206a403004440c83c100303c42c1070660078044140224083c0c030031403c7c50201d86c0090740c50100880c01d006d41010450011503049051601c2899120203090884005d800160078903a071140d103200c24003400340f10301502c00c68002c0b8040c41c140e4410007005004000c014001d0089581d102140710b040c3d90301040e80350040024100040882c030220681c940101c0c14040d080805001d5034004852680142078101c40750f000f007440031402b694500000740255400703020450759405000e5000e5049400c00d01f0210b000786000c1e0208800320340c020400100b10f9401d1014200c1c103440318070010b41803942c60707084849468908001200c00c07071 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 324030863 1250 324029613 324029617
    0x2150d05100519050a06210501080604150603050a0807060f14070311030c0409020304170f0a110d0c141203100501090b270f040c110111091e0604050d08 67
    0x103201519540324207900f0407040e001c2c001d000c2c0500e03600504400e000308020b0307104048080d43d40c2c20440d000040714038219140c0c400c1c0c0f0002c0c3e10803002c0398401c800340002e00040c0701e0801a6101060740400c0103604e0f69a40c0c03030302c840c00e030400034015103408120f4409001040d00031a445c200c0c010000c2040c11041e5a480c0500d8005a90100002b40f0b496035414012400e00c08807400b614002915909040c64480720402179400208110344945610b5040540000050060b0003051410304000c0c0c0c8802c50b4450040100b111541c030b482c0d007540615400300946400002c03040405801802040b40301c0d0510100b0340c50a00507516012807400b000042180740d0420b81206429103a0982c0c03440c50395a591584240a40512070810b41c0803514505070a000f14003405214503080c0300502002180c140b204000b90465000b5108500032400d44110010a22420f1045640c801c60b038400b082c3c1000d98507c04101600c85610310012809000ca00c1016a030355010141c600030701e00144200c0380d6698500d003500381a = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 324032113 1250 324030863 324030869
    0x703140f040312060e0a09020607020a0b030103060b0607030512040309050a060e10020705010203032404022d0c0c010305061f020a12020607170703090804140f1c02150d0510 76
    0x95203081150442e001203002e030750b0403036003078400545171a00d520742c4050017081c00381801c80c1e03c424108554801611599a64001042c001c40415103c0d807460402d6004c0d211280710300e500c1a182007045c4000a0742100a844803a20700c49002e61040c0d840389001d44580100d80c214541c0204081000140a940100b550341010001d6910300103002c0d0346d0b281641d0303a4a15004290240e001400043e0007021045039004055841d0350f204100c0c40d41b4031001c10300703da022081c02002e04100380150014210032a8025a29003041d00c101d9180440340c034000c0d9154511100142c1c10981c61300c01103102e43d6210305001c0c2c21040302490640000324094070180d51030300d03407400c101c032100303102c4501d141e0882c0007107001c1c2e11489941d114100080c8080320988219000200000709155442903035002060442001c0d1000d441d1105801d40301a04050802c5010030f0074620052080465980245180d480000c00d40034482e0305503104c0d4020340b038a400000b154040c040c800c0602c40d103484104840481410024012 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 324033363 1250 324032113 324032117
    0x30313061205040201020601030b070c061a01170105090109150e010b190212040308031f080c0a051c080903070b1c0507020313060e040f020c010609151d0703140f0403 73
    0x1001c03200e80d01039025180c0c02c88010b03015030026401040401c11490300e441d070003201c034039014624500540d00e40007110703804442c2080888505c00c02100340d5030010004008280c4250b2040001c0d0304d400002103900405000c0d11004a0722048401118401d0204c0c0102501d81d10b40b40756103075070f16500d441c95950420ba581c1e03048240c000c140704940c02e001055040460386000c6000b880c250950f140e41c62164070284c8643c0d058980d0ba2100541240c42607030030b1002e00202409005603101c40c0c810800d4405040e08403d105072130050f00c09411012032004003401c16440b01000c1c0d220b000d0640041d044c4440c66201c9201ea44000821440c00800350f25907023060000e0181c00c1002d615001000ca82d40e0081d21a51680810024000d00040f4014085601800b00051010031510a0400784c0003c0e80c2040303d1005d02d0b82e4603090140071f80d030110700840302001ca4441d1003002861070040f12800c021040d100c0b01d42d500c8001c0b00484c428900c01c2c4c002da40006400074019405040510300445011000c49080e00 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 324034613 1250 324033363 324033377
    0x23040e06041b1b020609090412020607180302130b0907170f010303020606131d01060821041e05040e0303040309080606280509041b14010503041104060503031306 71
    0x44401181d403030484003552559604600b040f8050300300b49060f54225016648a0414030a0180c295150307072160380325603c6144100c1414800c2400030380b4045000c1e00e42001c1c03003030010100b540d18604005020449030102c07060601105400c030751000401d03100300f80b04e8022910702d013040b4049411500080d2281703800e202141c1c1c6681c13004103e0940700c1080c000100140c11030b00206855147c00c0e140c48464404840c00040ca0b248013207038448411400065456899448240030800744000f403100e03501801c19505031070700c00541c00b100c00048d4400c5015403110040d1240c9640c00d0800c0c244a02405003030090700410500c0900141141d40782c2080710202c002078041e410111300300a01044a034000c030405800082e140c05003084504010100030f038444420342c0c06510000700d6681d441a240c1c0654040c41c682c0040f00810016180000000d801c00044031488104034000da9a006003240d0f1b009802070044074007001ca00c400140a40f215a00c6a44d2511011800005140107442c040044498a0321000 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 324035863 1250 324034613 324034631
    0xa030f02061006050c0f010c0329060433030605040b1504050607020d06050414150702070b0904150303110c220209150304061401050102010504050d23040e0604 70
    0xda4400e0101c4042c07107444180c5004100c62030107000500b488280d04c030700361090441420501401c5031044006040000c3d1694000c1d08000031041c1680c60001f0300d02d060341055225800411890f00ca640b0a002b010340040a101355019109031039400d0f00c0389035903034140d1809903d0400501400c03440c02514881c61521521040920b400c603400329051b10415141802c0a10f00400c100540d0001ca0050341c1000881050100040c40e81c170540b84600e00c40c1038171091801c00da5034001d1415480d000d14407110b1400ea01400075090300000c81c4030031505444002c80d950318203503011801610f094240c0c031000c150741480110400d0b030032128004042415074102c42c100380390075040203a00201681840712404048200d1a50380c88540c0042a48500141107580d0000d246407a1200c80d81c411035082da44160b03501182044000040002801000c0920080c0f00c6424141c1700c00d51500714461004d028010070210318010010701282d00c94081c48180c440b0394a4590390312450071212412205107115624200080c = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 324037113 1250 324035863 324035867
    0x30c090e060f06060d090512030103050705030f03030f0406140a090b13110402070c1a0903060f070203161707060e01050105040e030414010311070f02040c02071202061b0706020a030f 80
    0x402e1003a194110403030b05944651041c061194081400c10b01701d00d440c1d40201c408140104183c0625040541406540750314606010341030612541100b40b09401070840d29003000380000c2071707903004101039800140c2da8a483ca00071006260821441400440250030810b4020003940103d1610303008640e0a0700c6540c55418030351403001e403190010600c0b0101c0414024a041c41e5004c0d1144a10442b0319482e2035031100c10144001c3c0300c40c0500c03030307002c100001e02840750f007014003c0942044440502482c10b0515040194803801907421a10182d0b0700900001c00b48100c1c244e26405000d08032007100e070354a5150070004040c2140e00750b00410f560a01300006044d06091040c000c07118071080146040c01e0404403180c128141d4600f01c141056111011607441404610081200f10310034100044100314510512054841710f02400080d9004250200902c03200048040030b6a03074103d0b034103070351205250b413a0702040381000ca903526640b184400c0442c5d030a8000510700340f01c0b400b0792590f400428801e501 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 324038363 1250 324037113 324037123
    0x1b0f0905091306020304080c01090c030c062a0614091608121c0605040f0b091f0b1b0102070b0108070f0303050a140c1c0e03121207021501030c090e 65
    0x2002c07107210311008401280540d406180c21a10404e00d01c0c2c5098000c01d5601c1c00c2d5030400b42c080d540c041c00c40300d08004024800803044001c1205041c51150f00054684c0386460000c403549025444403184002001c100041d400b011007425101c21200b007034100303860b00540e544c20041d5524a8221581d43c04075441e80005007a081c100d07080d4010310714100030780c100c0143d0000b080c081c80c841c42d51241804201d40c2e030340c2d00031030900505001e00080d00051034810081e80140c040c04034800312100c000712440d5101000384641c2590038020b0880d030b4903403180391081c3d12076560a84100003544045100010821034001302c50403924904212404c41303407a00025070084140d0710008020450810001c1080703400703140f004074a034510034801400c020000b44410b007080c00d902e0420003802200c03000e0010003508800e504841c51015001030002c00309082c2d58044038842c2100a40d030107048000003130710b250320070844100d02151b0b1560050345540d581c0b5003503620030b41d10b028240c4000e050090b03a105001c00040c5c = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 324039613 1250 324038363 324038371
    0x31b17041d15040207230d09050105090d020f030328111b1e0d030807030606090609030b0624030901180506180717030408071410030f1b0f090509 64
    0x40ba040c41d00c0b4000c04000003540300c0001150701c0c2c05541c9000c05905804031181e0b40344c00d019000341031034400841c8000d01001880d08000d0601200380708500490303e07800c1032801e0340c41d4160742120300140840d0000389103002e0799520341c506030004102c004540001018191213100540c5074038041c9062038000303541714045a005c80e509056960032981151606804190481c1103640c8a01c51144228012901c5040c0301103043d030202e81000103004800c2e40c140f155100400140c40c1c0501440c0c18090020840d028070322000e081e01034070001113042c60b40e99108800f1000100907610380d1803401c11071045980c1d04111044c018652030030040804110b1580c0340c8586255008000d848140d03070b4208441803500d188c126061051051b0f60300426030054160350000c010700400c00071074842c2c1c42d100a29260502ca50000d02011501200c0b001c1c07607484094a0080546072070801180107034510451100038556518200d82c1800d00001c080003545d0003c604640000e0140c3e1807150041d00d5009001240f84169 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 324040863 1250 324039613 324039631
    0x608130f03050708030c120709060c2418030324030210110d18050a1d09030d0501030c090b040c02060703090501150617090c0d031b17041d 61
    0x84200000518180d915580d03540c4a428068100ba110b602c40341801d41088451410300400054074004003074800d81d0043d0f104010f071415428050801c0707402450f194564a000300300c0c1d010005518045c01d100c1d60809426400740394100f00c1c1c0514000464900c5080410030707004030b80b0703000100d444206540c0102c5c103501c6a5004c40d2007500d00d140d003400410584a0074030401c000200e20500c00f003500c180310f116440c00f403e5513400e4042841800c03008002d07416502c91881103c0c00142004070301d01c00000b41c4176200c10007c240c0040c4d40d50403000c1d03085200c0c845004840d90b00e000b001004100b9040c0800003a20014402000f4203014017082c0002c54610712619800b40c1d101100264a0700d00c00d411012102d0710490010070080004640c45444000b01c1e007240001c82d0b4541c01c110301541da200ba01650284110004004405016010842e80c00304e00801800b044580016a13589001441044070340d03e034400550243d90007030311050f240c541c0160140c00700302c010055680c003807058841c07200e5001c1c981c51 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 324042113 1250 324040863 324040891
    0x1506051008091501090501060e0d110d03020a0f0302031201050d02010c08130b0403060203070807020a12080a09151a0402040b161103030325030504051906060f030503130608 76
    0xc040c240e6001d0801001c00440d80700f10f5030480404600c90001d28020a13003a0303000314003541003490142c070313052030b1a274131074000e010100308000030a00101c9800c1a880342500c5c9151401100c4c14200d00301101d07000083c154000c07001c245402c241c1d0006c0202449003094055a05036626035081103c0c2084401020f0b00040095800ca0040b81e0380600814480e142036111001041e519411421079400590080c0c0d88240d0200402c94840e0f084107403107921800e00c0c03002e425100515690424468800d44801c810020b500001541e040c41641c0302001e01900490001c41c0c00401001301000f4026030415180a6064174082c030009080c1402920190f91001e6800341c1071900e03074120109104600107059840b61140070394503c09840034070086001e503510b0a0101c01d5a00340310900e03251a0303589001d001c20103103840c0420001c204045444200f400b20002d4001c007041303590030800007401040d040382e0a5495403820002c00c00c01d001005005039004014400b0351542d032041c003a0380040c01290340954820382 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 324043363 1250 324042113 324042139
    0x20c06030f1504061a0c160503071502010209060c01200301061205041104051e06060a09090b030a1704080105010b0325110105040b010e060d050c0d021804030804150605 74
    0x5030382002ca00390007000d080040d05595500d00000030700042e40f00320401c00c10004640e0b0604409100e051100013080c030003000c060349441c0109a0b0380f8940c3c070445460001402103a40250720070b40499803003160040c000c2d84c40b41d4100141038002e106401d8840c0c001240c684000d00482d440c8006d4a04840581d00e0b030007207d420030101c0c8809003400070000c803803d2034103a8080c80d40c2c2e40d40d48500c60140110124500e5411020b00e603034a4024000f400b554031541043c0011841154400100030a9074102600810030070070a8000c24a06160004003c4c9104038007500704151041c1800a001101d0861001b400540d9840d43c0f4183c0c03510064a1b0392855000c0b20041d83c100c0c203e208003162916000c1c0c80e07d40010984e14080608490080d0703011145144010010071403986441c821681164088448806464455544a90791302c20f81c0e00381405101c0b00d404500c10766840c1c841540c24003944441d0a42c1c80c1c902450010000350007101d048070110005401c040d09480e81c6c2c400e040540b08003030200340300940 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 324044613 1250 324043363 324043381
    0x6020d0e0102330114010f021b010f03090b09030d0b0f030d0f090806010e0114100801030b060604050d05010c170405070915090c09060905010212070807020d0803090d020c06030f 78
    0x61500c40800400071016140b541e42ca07500f407449030007400c3c8450180d600d02140301c0014451050400035404640c000c1a082c44007514010800d40c4580003405c14085d8101c50407016805481c000001401445500c410002c20241c0480209041e02c2501c9080240c000c0e02000c00401c0c00c8069540e50f0540c0c00403207400600e40c000c03034001c0c4010304ca508000010a54440400d03140540c01d8000d40803500504c00104224189005e0101029800320381e0710000a42082c0028142401448060b0541d544000803481d81d440c0c07001218041c22025251031084500c50900c00d01030030003454035800040402540b030b5081c02143e401503020310381c0600985861842c041c80d080180c55840d9004040051100001030003a409204403a494031080e00d6244a0620b490b13000f0b030000d0072a038405415504000c00300000c0301909000c88802c160301441321a1074a0071800803402050051030000e144070710000c00d0120b090b80001d2891350840007a400c035419500b100041c4143c81c0020f03100527011060b03650126033100 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 324045863 1250 324044613 324044653
    0x21011031801150306150b070b0601031e02040906032003030403061a2115090c01030f09080a050d05150d08070501140106030f05101a030a090c09050106020d0e0102 72
    0x30060000c50b10089400c40710f040501964400c0340e90350754801d05441c120002248850040460448403424016a0740f510803000c800101303c10b04150b92800c000141c000c2c02c1c100305e40701003040300c2d0440d26aa00c503070841c0000c00060000740c892041d42070414420019450012059001c050060344c24649503035034440150218045201c0e10009443d04400c09458010213550311041a1350405c15641c0d56003c51800c040400c5141041138443c0410000803040009904149440c286000545052034091202c0141214030006009010015817030413034a60120203480075503000301c0c0421003034403401040700261050420f040d410403c1041000b02203000c100140c00301c3e9010b4000070840349610f5400445d091426001100445d5407044c0610510800344a001d521134102c0c60350003000e60038101c06c158002280c01a41071411000130001c0d40c80b1099030010108150711095100d0303c2d98407101c80710081c2000340144401403141402140000e840b0304540264424107030050000740018003d02d00c410 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 324047113 1250 324045863 324045901
    0x4180b030a20030a060b10110601140a08071e060c02010c0b0613060603051f08060610021006032009060904020411090d0c050901060c05030a0f09030203010e0d02101103 74
    0x12034501c802d80c580c506000050102c1c0c440d0b80c000a07190918000c101d0210b4820342800b0401104401a81100c80002501360550356404d4203403407609030200010b080106039400c0140300340604140000c00e001008925801c0180600c91109038a4551400311100c01c40d03d0000703030005e207402070800040f406a4903680d0f0404406826586c4c0c481ca20306481c426200705038004400030b580c820400440741c900104083e0078401489800840c18a80710030035695040103414544070300b900400c240100b41c000c10036100701076101d11007448110ba507410003280440810300450710000b1140326001c81454507090340ba105900040c01800107465640a010051900007460070012038100403400e060b41d202c0c6404034a0511400070300d4045030912060003802a410b07442a4144a14180b400f000587c1c08400e032406440c0c1c5151420b05612090021903000842c1d0340041e40551800040c041720380c41c081100340012030240c00f25411103180301c03103103402c8503062802809110014004151000100714003400c0c0 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 324048363 1250 324047113 324047153
    0x80f0c070f050d020a140c01021203070201060302090f010305011d10110c0304030f1a0705030a0c0e3003030702031204020409021804030905010e100e031204080304180b030a 76
    0x8160b555294500301094000c2c002580c4444040f50800008100a002c2c0208090141c69101245400030b540e402450038100000c04001c000600018800d500c808000c580041c412504c500b8114808040d10500303001c265100e5007410180700700308060151180b28070b5400002080260410040000140300f0305a0074825101308000380c0014074003c00c040c0c0041d40c000c00705034104001520f049040341c800b102900c41d001600380c0130881c0c0070b604070041d2980100c030360303030045051078030941c1c100c45140c140341c90340d03510500c0b035980f440a440541e0400300810300550220802d11540c403c0e9650342e8042203c03c040160700800ca680500281c600125030000d101910208140700c0503800201c10040d42c5425010070784218040200341980702d02140020328084c2000030b241040c0d03001203042c0f000207070100410322809110000554904014001c1d81f8860f158004c3d485540724192140c996002d8850710802185000d1005203141c00d0707218510700ea040040040c5072a5006a8500702c500840119280d0 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 324049613 1250 324048363 324048383
    0xb060108090a060f240b03010303050d0902040203130210090f18180303020a090603050c0904020a020c130203090d050c0a06110c01061e060305130209090a0602190807080f0c07 77
    0x100080c00d0740154651131800b07010204451902c90100d18000051034061000b905280c94104091300b0a0f40c02c4078192901031038481c0c0d0b47c0280f108014003511451000075000340c800400c01070003007140c03003e54064a100b15680c01100c0e0300c4070821030791701c03803240120341000401c0402000011050001c0d80174041c00300a010a05400d00540c554110138044019808a80c00046130315403980c1c001c001d5405045141001c011904210103003500c10301942c10a140900d500040c001c400718020081c250150800070309082d4118040e1a000c4040d410540384800e85206410140001c980580284c540030f0705000010038501030161121809402d00c0c6c5a460303040c1e0300820404014103804e00950000d4007000116001c850004618404003112070b6115030101f501c0c0c44180100710b51003580310051240c0440c0d0001c02901e800c40781a0400d0188640103103010300c00515020b03080300704900c58040d03003403e4a81c4072003039a84a10542d80c0150443d040303050103590030b0000b5035181070389018001143c051007580c0 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 324050863 1250 324049613 324049633
    0x506010510020f011503030f050a02030a03020a0c0f110a0b07021302250303020301030c0e0c070210030f06080105010f080c030a0611130e090601050a050114030a1803050a140301030b06010809 84
    0x242140c00717150000300d030020035403010b2044c10b80111049180c000030749441403034035052041c02922030140c00340160405030006942c0060f01d1183e0303008900710350080c2034074607405514034100c80d451200d5040702d030081c880c1d0580015030080c07010030383d0820ba402500001030125070801d039000961006003078a0b000409807221041010394040d0640b45103201303441c0181d42c2d505500380245404815840811143d804070308000403044000159034603117034150740e40051203025440039806007008642e003a0295140040008040d003054200c035049403c0603c401c4003007504c402030240c4801c0006643c9401d41e211000740000940c43c0d500002c1c4502000480c141000d0403900d440e0304805050307016019040301c4805001e0348040c24040180145021203074076940c1860840045c1114042d00341c1507041d8440440040c5606945030014008c07d040003240c0c0e0701c04041854040c0050f000741022100080c0c9180510510300c20030b9003200d0507650000d041d600f030799884100442d40850300a102a529000c0d0013030710307 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 324052113 1250 324050863 324050893
    0xf0a09020423030706050715060b1606060e070512040812190b220c090302040f0c08010e060922050105010e1f0b031303020a051b090112050601051002 66
    0x1030300141500001c100501a01842d10b02c03490b4088200741c92094101420400c6146c3d08030044a6845500c0000070180071210b00400004010170b0380031440180340043d81030021440103200c0440513114450401030191201140c000f441c2c803c4500724007141003000002e040d07180000b00180d10078498a82c903845c24842001102010501b40c820302000c00704181d1141086d244ca002c0d4442c106070650340c00220a64281c20000b04c103c84041400704241da4512101410703124505c1d95019580162050024403509101140101141c011401c00100740600124144401c26042401900000c09149039601c4615010b1005078030481d00c140c0c0031400c022070f100020310a0080704d009221141c101380302481d00181252025881103000000c0100b0b5840900141c588001900c0d00030b51040031a80b0a82801d00d030503481c200c50300358007801c107114040c0000040340611010136018002681c02d240d00340d0381e80b042601201054840100240c00582c010301150410311058040f403e9180b04550382c0300c0b549506 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 324053363 1250 324052113 324052117
    0x13090206250611070506041217040c0e060a06090e13200102060a0b0607060b0102070b030906091011090112150f080d111203091e030c010e0102090f0f0a0902 69
    0x40c1ca4407003a203006040620466102d0742074451542c0508070301e003036120341d55140c441da4018801445c08881d40060143c10f48140045641c80800b421024030500f814180140c0002043c0300c0c000190050034005940c6080454110040342c00030f0f203407898040c0c10702440c071070310610050610170070000c40b0040718041451800c00151001d042c0b016406800c503003000080c00c01800401800e1010b042032801000350701c075017044510660f0402000600441d0184c0100c0c1000100c1c1d00202d1401c0300841441031030200810018010010001114655102c5001960903030b4000d4003082042101401020815400398450780c0250409940001e00f0070303003060488100402e5500410110707540c0450034040c000c0d0801814041100d1818940400d100c0d0310607942c1e6510903030140e901d8000340840800e4103003200b0480390602400000083c0710b50034046400d160381ea00040c5e2100700715030a2074940410900184200c42c0c46c800040d0000e201d4402c803c3c1806581c00c0407040320b0f07070481550000004d41c02c0071880 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 324054613 1250 324053363 324053407
    0x506150109030627233412050709051509150a0305030c0a0b0f130f03020a0b010311131517031b06060108011d0703051504091b0e0613090206 62
    0x80117840720403800d00d85403005c0c0c401070401d1002c3c4c1c030200e05801c0154010b4480f5090056802090141072103210601c0382c01481d6502600e0040012201c6034104a4045005070035501d1580c020403682c1c3c2c403110740c08841c944d9030320303545d400503140c43c0820200100003880711000300b8050217140c0c0160f0341c1c0d0340325851030788485440301c0c5c150080800d181c1080390b00314241e904440800400b1001741003622080c445180609001410500800021005c141c000d2041010183d003200384103080d50703580c1c240600403490b00c4070f1043c0700c0d00c180c401031403c9443c24410282500410b1951000c9139050000140b42c81000394040111480b060002c1913103002c1001360505103c0320040070b000c680c10720344c00140c80c01c0e10680154050729000c0d4400340c03500e2140404030350b00c00001d26020500751144242044450300907445940c00c14142810a401e0242304010280c0c0d41d0140c9031402c040d540e580c1c0d0b021002010503184140d2014110040c5050703800356802136200d150005003801d15141104c0c002c1c449a0003440f07 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 324055863 1250 324054613 324054623
    0x507030201090515070f14040b071e0f020a0801020a0806090601090b07060f0b010507080d02030a020c0f06010320030a12050408030408010c0311091309060e12070506150109030627 79
    0x40c1c1000b205c580d110030f26099440040c2010808400064010307100740c02240a24042c2d90008500c52052090b80030300760151400c600ca000c120899035040001251a090780305078022012042c2c001506a81442103c100304066902d0040d1a1a0601000007200002e00500d04000b100384010801004850041a0308c0f4862180003032040440c143c1c280684114501003410b10100f400482c0210f52168229024132205840040c1e4940e80c042081e4000d01411b512000a80304510107410b0081e0f0006030b09060744e00802c6181e01c0300d0710013401602c4003020707002030a400d030300004550300001d000502a0b0700030208034203200d401c1035140c1c4100c074a95042688079040c241e440344135002001b5014460b82442c00b41d017011007450404001d000c0b4801c40d6480801312006a03a036a1400d040c0140b50780489944100d500a031f030100031703900c000c100090b040400c0680d103601510340401c1c41c00134103c0c50342050310010f071034a00c2010b02d1500e51400030a074a00303c2407140440c440303242010000c61000c203201c4c203104d1 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 324057113 1250 324055863 324055903
    0x7060f08190e33040c0614130b030708011e060e030a060524090106050306010c02210705010905031b1003150f17070609090b0607020402131d0708060105070302010905 73
    0x544210f0344009109040020004212010b110100d03111200e01d00c1510f0490411141203010000c0e49902c41c4540c456070b000c02d03820500003140508410000303500483c0580e4410080ea43ca561405220300907a8100516604d4502070400200b030150300310050740361006003070752000141c584960055500407107200c0015548103100302440d42d0404400c449216065440808540c10319502508510014200c5410300c01050307004821561140c001c1c034004400040705044032014050b0ba182d407950729000320342c080740600710003060703505000a1140b04035460007090805c2c407441c00c0a000030041098146010103440700d0743c011007511080708503002044158440302c1d0729403800c81c0680039031181c044040d0b542d402c402c804200040e03115024100340e0f0142c403c001b0b404642c483c0000c60f40e101d1000001c1d006400481c50020240080c07011710200c4082c03480d80d803098401c0130180d000903001101c00001040c0103e0104265502c140003401c40b003072107400005400c0809496440c80c1550b017025a45240d065 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 324058363 1250 324057113 324057163
    0x4050a06150302090109210609081c11070803040201051e0409111207110114010e04031b0b0a020306040e150907060c05030d0911060c010e07060f08190e 67
    0x24108070342140708041d140460401c200035000802880861107480c00e0903500001c60002c0e4848280152056079205030100f2822a071803522942c96003003052503070072101150420003149140b50180e041c1003c12200c7c054039100070755541a0301e5070000f80099041040c1403240c099007130f1404080070301102c0d01146040d126131502800100343c852a02c040c1c40d80c90400c1c414840c8072901c10030080c2d0004c0c0142040e0404000e090300035401020200b10025102c080040000f400c0c400840c10180158000e96907a009001204c0d540203070003096980041042d0550300c00101c540d1415030141d904004000c20125036042c0e4441811728208014020f44442c0c2000e02c00c1c4800c1e803801b00242030080405044c41016840d43c0d407101fa0b02c07801040b04c070f4010213031902c64003020064508a48091544000c29190f10f6584a1040300c1c000c007440031020010b031003401c0c0085400d07030281d80b20850b010250b940380c001c19901c010032030a89a61540915a0654072144101c243c1141406401301d08010784514501440c0 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 324059613 1250 324058363 324058379
    0xc090509210313150207060b0907050c07060c020103060b03040b190509120d021e03010602070f0f0b0c120406050d0609050405122203080d0b040e1c0203040504050a06 73
    0x80c5141c40c5003020503284103121100381d5001c29079030b010410a001910a00d92410031340804207a01124008080c400629542006055031020031042c070192103200a9a031540401e0f01e00e4802c4100c201001c3c1c0c8441780c104040c6208040304600031b4810700d0045503a0b07a452080d000c0c550815942180d9184c186c80c00c200c00d0052a054030081e90405220038807003400c04946440e141c06003374cc441201c0c4200020107161200c080c2d011100d007040104a01030685031351505007411030f0800e024010050240321800101c00d0172400284064441718505407440b01d00c1c010f591034056114035030380006401580c503401780c104800d1024100500d21a102c4568501420700f0101c02ca600540140d05100d00e090140000700b032002400810000540e065641c0d074069051100c0440f40c81b9140203c1e01140100c0301104026100e00035042400350580288a000300c0c040400c416030749480070425050340402005040b071817039000c2c5e00c1c1c1d035043c140c01501d20705a03c2e0004a800e0b2141110b091029503201c080810400c4 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 324060863 1250 324059613 324059623
    0x7080603011514060901050f0f03090f01051e2e0914160c02130603060f0b03010912080a02090405100509070f09140a080604050a0c080c06030c03130c090509 69
    0x80b01050108520740c18180c03060962034042c21864002c000c003080b5244264041d000310740b07513005240c402c0c5480b80101d4440d98203551040390b81c40c840c1d00507124900da000105000e402d0280321220303090904181907000c039108000004140381481c01445500c941032a4090244403040c00c4a8100010300508000c08001a03c40000003924405822130030451104036290341c03004900c17a2443c0c03001e28081d40d0300014220080c00000858010301d0480004100200c66000716490314180d0400d00807181c0c107000301401c0381c01380070001d0301840398403c21010311751061100c140d00c107444c21801410a40b4040110707040310400c40b244490452951024042c0c0c1c40c010040702c1c3d0140c0149400c502c074050b0f0060040c081d1901d84260381c0d214503c800780c42c416544210034107010b0020b100031207040d0f24040c14801d03604c1d6001d40b01076462441324880825062000300c0c0e000780012000d0851407841e101d092a511059000601e0030308020300190300600060554817284006181d00d18002c81e0b2810407400c614104 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 324062113 1250 324060863 324060881
    0xe130218090702070f05041d1f060b18040f18053004060c0203010207020603070309020f04050c0a080a0e07060c0501050106050310090f0b040501090207210905091e0708060301 77
    0x1560000d034003041008640050181a280c041d80c021030320804248a23959030228170030640c003050050520b80581946200c0140003541c001142c2401603a9a40035006e20900c9400403480c0f010300301d0025203607581816000b2521b00c088900b400920711140070341c10b5141e100840c0f4101d03046c0d086503900780f4032946180c100806105030b05d160140660081802056580305520a6409000e026000300c0250f40d07080d4140d0343c00503006041d80780d8a140801c00140244298102240309020600f03400c0f80300e0500340306030b600c40d01054140c01c3c50507a00c88401c1d10b40c95401442000c4c4281c0701c020b0365002000c1801104028006900c41c021001403928046094410582001e82007105c1403042250302004202c4600840d1140c3e074000440b000380410b0f140c050804141c9181d003040c18400006816940340e801080d08038007800c08621001065a1412008468410364000003010814180481d14040440e2070300000c00c442c0810311007020041066a0510440704400414200003c1100c2420207001c1c454407 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 324063363 1250 324062113 324062117
    0x270305060f070206070f0306030615030219030305090609060c030d050f151005031509070e15030c07062307050702011103070c0b22030c031e050604030e1302180907 72
    0x480e02e000c1c0c000a6546000602d03950070480c0546051480130b020783d00ca8009907800240501001040040044044502d440708901480159030b00341020501009000162a8566202c0b860300e00340d0010006a40c0240c01c03170700e0380200d0410881c44d05500800007085015202000819280740c5054146040e00e00100490201d09400c50a44101d07034456244003140d85080c1041904d0780ca910b50900030321100500455000b4400005100e019a081900156031403400c54022032052460424040c550005442c9203241c035100303204150002d240c6d6004002840c50300100d0304040d8214080d401110748050340c6413804070340b00045c00015940d00000083e00880003400440c81c2040594881109103d280310304505044041417807828180c005800421a00e2464201d52840e904e031304150f000b0003031611040394103240d01510b04803010b400c4802c6030206a04078029101c103030f07100d46095683c0e102619010b40d0010002c030b001a4034210340d101034203992107800c0400211014440500047c0c200103002a81 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 324064613 1250 324063363 324063391
    0x903090e04050a0204020a17041a010617150103180f0506010f060f03050726090607020a080a0f050418090308150a0611070302120f0d0e0d02090727030506 68
    0x20101e90b00240800318140c0c16500169901201c47c811101c402500c2400c81c0d160502605100511841561080419076074020b0380189036618407064a01580310955181302840d0100064955440047ea454082806040224002030124800040c40e404448100c5070305c6202c440001c02d00030f0800000f800f6049840c900a6581c0c14001c000d090340008030005010180caa00004c0e0016202c1c13041c3c000c007182400950060840819541804000100c0f24005a403203480300007031f601880080c1d4a8000c58100c041c452800c2110142255103d01c0d00d45444244a01084005418030001c4080d8001c1c024944001620541c149401401d21001600e0f1026180c11201c0074180c955461806104440117810300910404a101d0301d141010680d5101a52011049513083c1240d2400700c0c0b186d0511000030169041e15191711020b480001d0382c1e60109803c4058040128014180300c41203a0f001182d5003403c0000034100c43c00900300401d01c8082c007000201c0b0342000c01c01c202041021540100070148121 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 324065863 1250 324064613 324064621
    0x1312060b061c09051e03091e0907050c070506030c120901090c050f0a0317040501090f120308060607330b03120a18030b150103093302030a0903090e 65
    0x5090b0586980705111001d5588203140100182044442640d140b080c0d102543c0c555800381c42c80d100d40000040c03034010043d070103808807030f00c281c4100751905240c01850101c140c0c0792294100c0c1d041e0424124001603108540010500c0c1d51144050351080d144104030b95641e010340e81c40182d00c0d403806400d002c441c0e07050003440310000e042c800044c4150f1f0001d41d65076943c10120000518141810391000e0a214101c100d445079040c0041d0061054600a0301d40a0080741d03a101040241451442424003a00c4c202c000f100c00684600700720354100400070078050501541d42c41e04402c2e014100070004e2500d52204407010b40e90312900f00c4410406824104102c10001c01000c65202c00f192070760351035400ca001400340002800b4604c03944000968400c42d107140340d00da1500105410381070720381c91124070312641002642c3d882800743c01d0489600a82d032030100c07003190a00e1702c8900f08041c10803e030030008200b550810046840903501c5000b2a040220310003120303040107094a026500451a20740002c1c00300 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 324067113 1250 324065863 324065887
    0x108030702122d030f0d0e1c1b1415010906120302120307090b03010b091503130f02121219030209031c1808010506031608070b030a021312060b06 64
    0x19070301c50340129001070080c031082d000504600c01e020050300c501c500400c1e1807801c9910fa500c001e20700181841100e60080318411065050b05850719403000080134030309c075a03801c554506800c50020b4420103002c007003a14070418250504d20400b014503000c1581c41c2c01044104000d0095100920300c8049070108800035841c02074036000d00e00a000a000c000002040310548520300d0803000308000d48138544c4958613803c0c0f00368654840070040380300b082c21040311680c0c00c803c1130031079015034a510601444d1000741e6591415900c5891002c1c1d03884800000c01c9000180d044c0100d00c0200d6420296070b95800b0a000700b5084020924024820148188081d203d1f60720002604c0389841000c11111084201140080b14010245102b8004140a03600c0014850b50150001030294108905032881c3c10340c0c41c1e542003074000701c61180315043c2c0d00c100d20400c0541d000c0e400441d0801c00d0720b00054588911107800c0c200c81c6a03c0da0165101c100c20722488001c0c401640b0030004082403c030f8415160540710148 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 324068363 1250 324067113 324067153
    0x11409070611070e07050d05010504060609030b0907080303070905041d07170c0d1a15090112050319080115170a0e0a050d0806150705030d0b18010803070212 69
    0x340790a1110001408210740000c201070001001e030b8041c503e086140906009007a500541e1050003241e00b44070021450f840d0501500003520740d1655402c803954607640b1800b60004000c2c2541429004261011030304110034070085204643c02c0d1103529289250106002c04c031071021413245101076641172031042d01130001c03402404841e581450041000c2030038100c90f04103004084050341c82016175444908104041c0c0842804916074200381030107a80d40e2100e444c50000c0401065032000d80c07000107000108410221007100c3e4010400c0300c2c01c2c40403102000d1000c2c401c07507c4650200b9407800041242480d84040c80e01d0b100501d16102e264a00c1700081c078194050003070b0280c040551a50640700d412501040080001a00a406c907501d4184c40c000140494400340c420741d018100c09e080d41c8a0b00780b08541107036200c0394480001c5146c00c41c0d18120b030004008000081e41c0c400e0306021903040d0144842d0b0700501070000280519510707031051040150320580035514050310780144886103004072a03918 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 324069613 1250 324068363 324068369
    0x1006030218102006070801050108070f0503150d05070306061208191e0807080606070503030105130e06070e090601030603051903050d0c1d010801051c1b090504020301140907 76
    0x50200302c0b060548000d441001c000e49118060310700003101c400f400e8400145181c0541520b8072403865690321a401111000801c17240000482c16911510381941e22440c02142e00090b9103241d05c00c805520000165003009444003902c036640003640c00c3c001c0c00510311a840003881c845207071805079405e640e80d00c0c1d5103003e003d50680390344004000c01026103000e104402c81c032804101d0080300242c0c06a502034400da40070794110000035000780001d00c01d8245001280c03a0150818004c2d411a031802041103209902c100d001e1641ea1b807070300c0104025802c10003c2c9401040c603a212003ca44124005000c0c101c10000c101c07504250421208001151003c01d40d0400e20342c0c1b01cad60f104d50003942c5003025929841034040f099805403401800c905060761004420900011200c4e00b202004a4074004403004034080c0981c0c2e0b4010110500b100403c40c10b40b4154040c00e229217440030f140c0b0b4410b40250781e003640543c03140700642c0d204e004220851038284174203202c004d000790216000781409c1c0d13041641c446d0240 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 324070863 1250 324069613 324069619
    0xc060f041a060406050405070f030e070521120714211b0c3109030503010b1c05010311090f15190e011d1605090d0201050d0609051006030218 62
    0x102c1c0040d2a984c0145002d824060000c0c4080d041c0590000c000100341d000000029180807624411404e000c914102110401820303000003a04908138260303203501c03958048007148528000c4140d026481c1d0094000d81d4080c6441900f0406001c00031404c004100c035580c0ca030100d8500460080d4207001068800340d141c89401c0e003055044880185181c10b8480720b0f282ea02000e00da1186040840350b80c0941e2800101510a0140c0c03c0c4200d101030913035600c80340c0100450000d000500061054401400c02e03070025240403640d050681400600300c903001c1e0415036461084110403000342c10001d02d0503401040d05140030b050b81c035040403519211480c070703401e50348684c1c2504040ca0701d41c80070307054008c0604071606114416507074802c40441c1d4030055250030f41e04070b244480080c1c2c3c03210400403144101c40b02c0e51101480c0c003d4800c10025548030110f0101c0c140300c01070052030340804036489400041c0c101944001954101050140d00d0170b400d0394001d204240c0104207140d5039860480e4881c01c0d0003829 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 324072113 1250 324070863 324070913
    0x602070303030e0a0b01230114040504051b0403121b05072d0b030108120a0c260a1823040207140a0f0c060323090c030d050c060f04 58
    0x40c080382050913280c4060240c00c98031001044030000d44c82c0004881d0b5101940000315621000151400d40540c000001c0000303040c44100842d04081e0405944020001760102031018a00d041c00c030180c00c03980003a1880341005940410042c0c001d24074005403200490144c85145060783d800f0303603864190250314004803600c0c543d503541404d075000301946410b0700c48002020988030503200700170340c02c05d114840161240000783e50110361a04c00300c0c1c45010040c0d80d40c0341c2800141c2c40d0380084100e84441c1d0084100c41284000340c13414030b00090500d50240781d41e12100251070ba4401c5030b103c0016004503440f41503c446406404e4400008285403c00685015841d4021400c6c203011201841d8042d440d507018280c0700f4020800005c0740b429800d48a10601c28260b038540700100c0468514404001c22400c0000c0070074104030b400d610340c0340e003c03401c2d03c2140e95075080310012a003040001852280802d0010030071001d492418001c841c2d111803426400c00700c900d000d80360b00b6403200d0b81200b008400c01c58 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 324073363 1250 324072113 324072131
    0x70b1c1d0a050109020301060b07050d0f020a020a0e1801020a0203160822030b010902072012010e0a061406030616052106040b03010504050d0f02160602010608060907060207030303 79
    0x11111141125503000303400d0711140c0c2094108240a0318160790704074429442c04c88007090540301c0d1001d54601980040040a003110903000544000b130708042035030306521031725212100595504e0101d201030080c0c18810045401c00800002c42e03011000304442c1720340d0042c00f0f6610080da0020541ea5400c11128910103118024101102d0902c100b4404041a10501c16110a1204801e04050859114544510f12a81c0c2c8404034812801128070007030903804040d803140560921300c000c04155010013003800c010b078402e03080300a00f114900e40084450b0307044190210b0621005204003a0b5076800e40010340800d1400c03400007512528001c181002a0b00c0c8241001c803210f00c01e000b550005c0c1c10f254603450300e1502c01c1e031f599180244111401d612850801504000e182030600075035000301c1c0c1c4400104125042d8070010703200000a01c850384114840c410900b0784140da940c003042c0040800c3c0d00001009420044554108000105201c00941c13006404011559001408000320380d090315000840e552 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 324074613 1250 324073363 324073391
    0x16030903050105040302031c020a120908090901031101021b031507091502010506270708130c0e090d091409150d110901120f12110604050105040302070b1c 68
    0x6800141c40c941c030386010001016000801061205040c2e131042199200200a6400f0b0384692090351000489a0007601403406454100c42c0b0191320502c0e03600c2c00e0402d04000f098401c0c45c03d81c0240c4904060b03000c102c0965805002c1e6036050b102000c800491500d050011a0f80d81c089c00180c0380308241c02600244081d4480c0005102400c000d40541205041c0960000d010300340c140e6485110f42004002442c401545911404524410746685d0341170340c0da1000f0980f032650005101c0652510391942c1540010760440300ca40c013500da0740114058505101e1076151421080b40070000c14440f0240050201400400882c44054000c0742c0c1e00045030388420220b0ac0303100103180e405402c2161450400100301c0c3c40d10486400007426039070038120b0fa07a50f00034400790182d866405072441101c212114041000702845080c5c40f0560b080802c44403024080d2180362480450b410384e0b40d6550780060000301a41804444000c1c509040c1c0e6506103a000c04d000c01001030000001000e2582e02e20007565000 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 324075863 1250 324074613 324074627
    0xb1c020d0f0507060207030308011d1602070f030b011403030a0c0807151a1008150d17030c1206010806090f09011506020d11010612030c2a030b0703111603 68
    0x169124043d0381586648007406595501503000480c0410301540001c540c85100f0306a58003110f020041c0300b44280c48030b41d0210400c0381185010310440c0255000812100c280d07070b01d04001548200d04039496989000040450307061814a030313502c40d03041006020741d103d50100010681d240c00c800c00c25561541d41c98404417000f185010650102c2c200a100c1c405e80342e26000070040040182d407c10048030b01b6020071140e80320101c48424542010202000b0170b0f04200c41d060545601c00d500d6480345e42c00d64505010300350400c50f9142c459000018802d480c60503900f1985400010a0918070040d003010b90006261140040c548100c5803030800001d0701c080d409401802c90010743e00b000d04406030707d0300c0f0001e440c0c2ca034040c8507401044910641c00980d074014400c5200301d1300c1508100800c0c00a46d5022140c402c030146080d15800211189410450030401d034400c0090100d06071013001901d5454203070204070b00100b080c424140780152a100002184040700d0010002d03200701600c0190503e01070f120300d = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 324077113 1250 324075863 324075893
    0x15092b02030d03021209010608072108040b040807080609060f04150c02030a020706020a0f0303050c12090a0c05030604030c020f011412041a092a040e0c040b1c020d 72
    0x361241c00c00e02c520054150380206000125504c120f1041d80c1c0c0c50048500361070152013140150340c00388404104605082038031500c14043c10340ca0614840403030301c03050700c00e0704075400c4806980e400007400c1001400400c5903000a00c9400c0c003a060354a000b0707000d03d84510000344408414085540040c041184000c0d182650603001003003080220407089009640340c100f42c11600c0907206050020684a00015100c014681d0104a031050030741c199400b200a000040d1950564035410b0003c00040b101201c4120301c101c0103480106152000c0b402c2034440c0d219294001030007508800d090002081d44501c0c1780c01e5454060301c120b0800d0003c480100c400c480c0908008111100215102c0300f24030442d014103004601541001c1d803a40583d240c410316502007913980d01d080f07610405145110722405590020204060300c6900d00855942000c901642c09003600102190048000c040c01407910b4450468040c0c2c0645606482610b1a028180281e000002c060300c46d6034400041c50030403066154460722 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 324078363 1250 324077113 324077119
    0xc0a1d06070302010b041d061303090510050306040c0306050306150a0f09020705010e0c0127030c0b032406090103090f1703040b0708060f041a0406060e15092b02 71
    0x1d14001800c0c000d000300150401c152085040041c4000200e41503401c40040c2849007001d0405511420411181441d03200c40803420b0048118000401e5502c005004500400c5501c507542d4078a80711042008444805424409052408805215903100010010391004421139400003180ca818006074018100391b0101c0e041950114011407840001d03009403040c0d5104400074002d4031218404503881e015060000c3e800160381c08a0000c010204c5100910009010800019015200c0e100c2c0d0401c000c0c1c5400c403040c0403600005000d1844100440c030b004245140702e00c078400e6004c040000f00c01d8400d07208114100b5443e00009024040324240850003598040501c200d190710a04044089030821202510f07000e51003400a46983d001e4808144030310b000404004041c441401003000034030091902ca180c0c401e8801c6541c50a03180c40c40b4100c040c181580300d54182d0b4910104100c2080d06254071542491420310102099440d2181e4001110503460100310a0805000f0240303142000c91201070740c = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 324079613 1250 324078363 324078367
    0x603041a07090b0a03061a0301120f0c08190209150603011509080d020705011b0206030c3006030c0609150306030313090203071d090403030c05090909010614090c0a1d06 74
    0x13104c1c580541c003201c00c50748000b05055420400340c46001c50f6020900c28a04092412003484000902e240421420070f8464003998481c16103400c0018605000408403200014038403c7c2d1b0300035450f2400e07419a0252054900301100d26088022404130f00041c413450000e20304600d180390728035021700002d4029100b1042100e01c030702030f010f078000c0d07440d206841094007145800c50125104d01e00000100c801e29006000310f4555211085215203940c00324560002c844a83c2d010403102100b012091003810b00b4030842210282840420075041401c0d1030300403442940304001035000380c0c443c9940c543d440c07101c80c24042e403a0350b24103002c6801c622032540c400700c40e0300c50a4008506190306a001e54003400081e0f5520000507103240388400004101d10700d450340000204005000030384680c02081403014149840d074100101000450307100c0c2c100b540c420303d5903519980180250483c9141d07840941004594200c10390900e21000071a503c07810800e0300400c20001e4401300c20142da41402907002c040500790700d03 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 324080863 1250 324079613 324079627
    0x6051302071106030a0207350f0901050a030e06070c05010605240d060308030c0d0c050304081e09060c07080f030703051206030a0213140a1b1b020405070512060603041a07090b 77
    0x3600004540203100300e40100401c0107a03482341c011041d01c80405640c3da0b0540b900041e4401552160890090281095107a982e02c0ca803614040c4100c0d030003240d8540311f6100d213407140c0c64907500b074a80c260086401032a003100030000e0101c44804013a02e1940100d5141e40e03904d0040b4a01e0081c11042c0c20180c4401c4c000000c1c420342c01100c0700284583c46441c4400c1000704507003001190f541c0320a0310b01400e03880c01480140400c800c241c120304041d40700d005445281c00e405030301181054001d01c0130404c0d160414041003041c00d078103100c0e900d801801e0720b0103145012182d03034001d810340c02030044d50f55006010000062068504111240045030000c00b007a0802142142e904040d01d09104001314448014001c0b038090b800c82e029a901d01111000302c920307950b404940494442041044801261f000007240f000980c84030300c10f0a002d030381d00303035121941c41c52003251100c1040000707000c01d80030319020010080818400c5900001504006c088003e00d0380300d0ba002201e000015821040c0c1d06600003a4030 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 324082113 1250 324080863 324080903
    0x609040216050f0f06040206030c0d0b0a090902090c040e0123090411030f0a02060301090e070f03061524080c0705010606030c0210060321110a0606051302071106030a0207 75
    0x40a42842180440e6810807031548910f0705e94400b590000c0d04840c081c4081039000400c040a031070100c54031100000c8180c0d040c400104240610741c41a520036658900da5015802c0c1560f4491b0f201c030500500f18a49440c04d4040e60340003c0c14072440c3c50141c4640030030106150001c0c0d50400010307006044602904207801c00b846a000d5030550329100b4420340200540c81107000c5206003150313800614150443e0704c0c1c24261b078041d024210032007166020b051000f1805829810140010b503020b035400003001041085c203044000082c1c0c1011500c1c0c00100030349070381c1d260600442c2000341c05030b14000d5816290740320360080314043d03040002c00325400d02d2000300c1c100341d0580c041c41c0e10a004e17908850150624444100444256001c0540bd060b20180c1e1f0300801d900d804041103c412040c40c006100e203460302201414010340040454003180c039503400300840e140ca6212080003200400d0214900151540d902000c1112440e180780501d40c0480024500d485950540f5041c0f500701011105420152000e = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 324083363 1250 324082113 324082123
    0x90a08072901090501061b030f0903050307050304140102030325210b010207151b0804030203070906090b0f030307030806011206090915050105100e060421020a08030a0e060904021605 80
    0x1440820510713000000442038441c2150b103ca006502400f1490200d03130f40c0742190350040c0c801c0c0c00700502c4412140040018000c0000f011103600540140d030f102c03400e240200c10034040014000341154024014020301c1c0130044403032014805094079003a113220b40010240c2e00c84110740ea02c10784a031148511000c0040c0075400c4080700c0c28003642641ea44984451441a2200300048400002280260106840c148505101050a00a140c51800d080d505c0c1e0001e4542010f5070000a101038030b4030404c00c0340d40501d0090302d0b059107045400000b0440362a02181c1d49018584002e420040084085062640980113032500d11000d04024400b10f603c03900310300003600944074121400312600c40480303101c00680c4203081c140c4500507c902050341000d142140c030504045242d55000100300000035070309c6404e034074148000d242c080c107400b02d0014600410201e00155400020107400c1001181e900d070b940b0400c40c003000314085034544e07243e0485501040080c011646501040759407400007400384240094 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 324084613 1250 324083363 324083369
    0x12050a020909160e0f0402070b100e010e040b150409052a040509070e0a0e060411010f0f0e010f05040509130c080d0206070507291008010203090a08072901 68
    0x95105890f031070360080440c40d00c90203240c0740009058501d180a9910385100c6610b180200148003500303102680d122460b00350029181c00e14000100002084000e50800b180c0d40104510070202c50281b50a450300654140010300f840342822800d020715030030f40c2da180d100c1300310b840d0007000311460509621852100b2503082c000c03c0321100440791402c0d016180038012184112150b001a010103440e008002600900c064288000140c441001c0010440200074407449140a0284002208070000026100020300901102044510705800f500e0320380112298001d40400e183c891400d282200084503603000c1d0340c100070361000d01c501c184141141c000145c0030915009040d6000350903620326110380c2c0d0361903451410016801c01e000140c0d0741c60152015041d0540100c101062824820541c090402114809005c08490300d030148085004509491006040c00000031859800c00c20451990341c181e10000424141c00001c1c141c007086000803c00e040c01705241a07003c88440382c80d60808840780c00740 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 324085863 1250 324084613 324084619
    0xb091e03041e1503020c10141005090f040b070203040504020f09090610140906070f050706030c03020403020f09040512030a24060c060f0e0a05150106020705031002070312050a0209 79
    0x216186080034030700900c60468121001c110b400014030f180a4020390050007a28000340101c1815928000b190f0081840c60740142c040d460407480c0c030140c180301d4010300da004a40920a04010402100140036040d604107802000c5440755964041e4100d1441c490354005540150001c141c03c07001000728400303010486001c40c6c1141072581c501701800b01005c4880a41b000095410f500c070000110110000d184c1190043c0400e03181c0b2080b034440204055104100b2160340d4030007901001503a601d8491000398a54501c1c0035840c0500d150005450400c1051717240c1c2c841c40c1c103940801c0400c40c0400c080a40280c0c4405a42c2e164503124079000014607844401c41c403030303401040354104c00650304000082034421a4540b20703030342c5070240c03650401401c03c00740e40c220042c0d580462468404c000c224a0740a188914001e028501800312031031428141030384180f007950300926082c000d59802203401c10704132422200050700c880007130404a410018094400f01d07410328020903c2568401c3e0f4004080c4404d0503 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 324087113 1250 324085863 324085889
    0xc03121803030a0b0310060b12010f18270c031103150f090709110a090f0501020706120b0904030e011d010f120603121e02030301120b091e0304 63
    0x6840c880c1a400500580210385030401c00005070040596400305044410180c00c90380300a0181c0b0404c01100c1e203a4014900d02c440200d0702144070707080c01c48520302621542c8107071106c10307140c5504880c10078180660070000a4841140f80d03c280c6d0070403444110200c0440c80c60480922608020419003030fa40011313141120300c03440f6407445082c000782c41c40b0b02440c1040240c0f110b40c0c44140a0701c081d200640040101e01405030006207031003a6024207071401400580c002c1d5103070090440034140d540283d0005842048480c2d0811107682c010811404032401e5085c40d5166156290302c9100616000d410580d00c07405c08400e02c0705059119100000411082e2107550040040c805443c210030f000584290003e101e02c12401c0d54103200303510080705040707003640224005449549000c18001c5041400c000603003944841e81c2c40d0b4902c00e82c48690804680040d43c5075504107100e02002540705207010381522001c601150380801c5c02c00295845030200c0824110300010011900e451b580107102c1e400c09116a = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 324088363 1250 324087113 324087121
    0x108090109030f140c0a050106050a060c0f03230406030501050414040b1915080f0d090311060708070506070c05071d01050d03200f1902130902060f0c0312 68
    0x14454450034a402d91180103c1d281c0b001421106010325022124041c10141302d4800101010080c1b40344480c03141d000441d065042c00107100000d4929400708081040581c0c041020652a060f80c150700358042c0303444054056000c641114070300c20000c05200201000400260050b8907611181c103a4504031018440c41c40707407507a0841c1c0710070290340182c090b00426010540ba6004500c484254030064607010407a1b03c00382e01200720302d448030b40c00100355800078200080758410070700035002c804003c0d00b804207038603041d034031003105030000e4054980c01440c0c00201c00c3c050152a0040d50310041c3d000c0111841b82c81c040030003c00e05c1001c424200c4140c45840d0011419074099010b008d88a254540d02e014140c1c6800c2c1000b0f41c141c1c40c0c020541c00e02c0303c250741407041c25000141c8403803c016100e008080d03c40c1c01e81900d600e40000c20071484041c1811582d40740050795140010903c1c00c2c803120307000c50407000c64000143c061081c6208199291800142c80f0318002012024103803030030b2030340c00a421981d5 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 324089613 1250 324088363 324088381
    0x10305070519030b120a110a1d070804060908030903070c09111e070204060e0103030f0f140a02150a0b04110304020907230a17072c240304020108 64
    0x7580b03402c0e0b82c1d80804504a034181032107544015560140105a040304191003034145082c00f0501c481910b0100d400310b121202400c00c01500c6000700a0100d43c0010030948032980d000c1e40101409035010003c0f5080440c05001c2140c010400458000780c1c0319a9900744914442e507603601480040f00c2d61a070f902d8001408561713920500d4440d00b0100b00703041c5080e80481e480d03000300e10b103040c0081402d1002d03c400409602e8a00c03c81c8041c003a242100141035056050107031019244040d120204002d030550207001690100020840400022155803101d50001090b414180c4000d06810702c1d84101080212140d1190441c80e1041c3c1d080d01e0400202ca42401c0040c0076100c02c44000c0e42299001001c1f400903031254104002250002c003110044031400010458558044c45c10345001840f0400030b4503118220f11441c50b000800303400c1c6200d10f0303003c0305441e1840f807820030004510810082c14204150f00c6a0300c44a540b91241680c480200c103095141200a07001039409900082ca001d0000361886 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 324090863 1250 324089613 324089617
    0x9080d09080606150408030d1d010504020d03050901050d1e06120b070e06190203120702150103060203100e011205070816090b06070203031305040e0a031e020712030c020103050705 79
    0x15601902601d00c035520841070101c02a40013441c0140403408001c0003e00c3c0c0c0b03052016148540c4006030120381034082c000d890451100708206090700c3d03403404090100603030b00d90000c0c11501c1d5060404903101c120302001a90a409103024158100381480c6144084280501e5128040910708904005c00c43d00e80310000c200240101d00101181b89500107e50300398020111340300180d10060030b1614100106c499050803113140300c415400f580c030101e2103511248000800c158040424402851045901503528214040611004c1e0402d44e000002c242540034101141c0007510200c60101840d594a10540007050340c0908140c456000304100410a80000f03d0320b08001d104045403100ca45081408503c010b05a5645080d4845004c00c844401038805201a20080165040c448001468113003070005480c0011100b01d41c580000d42d041d00040c0c0c02464100103001004801a01d00c40c010303100364078050142d0010001e2101140102c010107600c11026543c0c01c0c0300b03030380c10b002c5502d442c082a03a0724 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 324092113 1250 324090863 324090869
    0x60507050c0906040603143a030504030e0301090305120c040f06050f070204050c030610050f070b0a090b040b0907050f010c0f0317101403030f092202040609080d09 72
    0x941052242101e64904042c1058005500410000d1041d9a0381da50b0580440c40e80c1d070321051600520460410f69048066038203010310f216002d040c1031040b00c00c401003084041251071040c56501c1001c80c0c2850310983e0796000081d0050020420a056400e0103022034004d40b50701d006100c14000044c40c0e220700d11081e28126005800c144200300d0601900b079465400902c0c04020a600902154025a440d030040c18040d024003100103640c4c1c20102e05022445c6a00c0d28100184002040500501e448407401c0300c1c40c15803c080b1441864407030341c604002070b011009000d08510422414081808440c50645016840700f0080343c03103a9986009016000c4482e10965000c40d41006007500818110b10b01d80800320703c6480c1800d6002d0317407000c08600d46903042d540c000c900681820140800c194440385504031002c11001103040400d1400d221030184502020107004940c4003032018450a42403140034801022441c00713549803070310355400601e070318a64480d4140c0d901c200c1c0303404201d03e8024204842a = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 324093363 1250 324092113 324092123
    0x5030606030d0f080c070602040f05010f08010302130b1c050312010806041a04061e0e0c0603010315020a0c05011a011713080c0703061503060b120703021c02041a0307060507 76
    0x122030f800c0842031314180b400810001d045403080000c800010a64401080034141010584001500f850001400c200c001c8201000b4884820018009a0307a8240c24030407092090b20003103440369030300c408100e8182c9581d41c844240100120303010100200800a01100c600784510141c0680ea038546442c0d8400050318090302900b9801500c5026200034828983d11601408001c80ea100d1a0180720082c010410300c13600c01c09136910502c6464481c00c2c0121070f009101110b045c1c1c1194110b48400400e6070404007010890365001448224403030141403c010340503002002002a1285c01071840c10b00108441c148d4005080c1d0b0f02400540c00503800054060400d01c0c4034082c030042da42d41d88181551040003403481612440200000152141c043c0880c580d07024240184034628520f411020b40313841c0d01c030301ca11800c190a17240c005040d0005444e81107a40403a9080a803512503d42d00307144494046000e90010f00b0500e42c0d010b041500d2010425070941135040390319240c2e07070b4041240c15010355000104 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 324094613 1250 324093363 324093377
    0x2606120a0b01061d0915130606120b1503010b03010f0603020c06062e0903170405010507030f140c03090a0b1c090c080d2001060e0f0403030e060a0605030606030d 71
    0x141912071303410181c00303000b0612007400303504500c070000710104011140802d1092440007000b01b5414204c5a058400148003002d002d0309080100c080d0603000030303003000a6010f540b50b14031401d0b81c3e205454011500074062000340d481d61100044801580240500036240ca51002c0c0060360714030900c2100c5402c0c5600d40640b1540c1c03904c404100c040503195210b100c0031110080884500d491070010f01012500e00d4980a0302e192071403500103184000d0094200e40c81e4024001000666045400c403218264146014202c02e94100300c103441030504240c0009140001203450030701010000000d0086a908403685001107540d003e030540a07200380f030802851b4201c4540030018201598000c0700c20700b0702c2075194a081c00e84075001c5918103044000818001039030001741302c0540c892051114004914032000b44695402c001c40e400318140c0141a055030a40600700240501d84258840414400c8980a850f024106031150300d018001502841303102e802120040380341d0b4900051244940c08064580003 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 324095863 1250 324094613 324094619
    0x140612160f08151c02150703030e190206030a060b0304200f1c030c0609030302031012210203070f05030406120204050f21030408210705100c2606120a0b01 68
    0x44800c0e0011311400c110043e50908020060361848074000709110513040d17860301c0300351a040003400d6611810b1a40750b150401200817408251809003609907540550b40a0360300d444001c6205d00805080d4081f00b400300c0003105000c2080b80740c103c050715400031226600302d03c1088000f00f002244220720501e40c8618441024511040074102d00765400e402410012409800780c1c441100740c0d0300d800750450020f80c1c0001041200040c2c60394650180030200110540d2180c5580e0714000c801e000480694650fa441c0c524100451080041f11829940f04c0c1e0a655044641c0c03070940d0b9260000d0041001140032842a03003901d122034400d0310101c4100920404016000d2410f00c4110020640401d103c08502d5440950041c1d04000078401820840c000b001c01c548010200055841d801132202e440b48410041500840c02c00500f05e059040d00e000006181103c1e8041075608540740c00350950b02003004081c8034500701082034024810442a24004c5518034450900c85d2101c0004100612000c0c01030018 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 324097113 1250 324095863 324095869
    0xf0516110301090804031104050c0f0d0f0612060603060c020307021324080a0303140402010804120203090a0e010e0a0219080a06050411090f01020d09140612160f0815 73
    0x400e04405016000041c8400d05403100b003081d6005400c1170700c0406000d401206281024481c00e54071003c01e01f002c0f42081d2034428081700714440d01d103c23280421745800500203d8241a40f02d500108880600852800d4541c40d0060103040b151006586003441c000103410500e00100c01c4406582c1d006040c000881100346000b801844819034106a00c1104d8102e094000300380c011a1021742010780090220104034940107041c1c4080c403010000d00c4100d2024040140d81041400782c00c80d0b07105d1034070600c200d04040c00700e2840c041c8155070b56100031074000000c3d091551580380e1b810380d007030128004020b5682d40c40560580c89180c511f040e00c0ca80920700ca0703010350700c036003445900701b100c000002c0303074481c1e40701d00080030b5640082468030720300800151140f951074448011010301d04c1c00c0c0043c010165000c14090038020300d034820030315101d107042c0305000295220011030784980301002e1006102d00b031021011324405003e005030750104680c0000c000b01c05019040c528440e122108018400815140038 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 324098363 1250 324097113 324097133
    0x509030d1a0a180f020f0301150e150d1107020d08030a02040305030d0b01030f0e06130201021e06040506091c0e12010f0507091403060106270303050a0f0516 69
    0x34040800003881c80c152002e40e9800d07904401055401191080c00d41c1482a002c00c4a4a40040314001c0d8410021010320f500004103030b82c1152019070a00b0002c1814140580784400008800303940544024030803030032000c01d900a4640c54040703001c1040110410b0280320868071803400003070342c050b04143d15100054401c4009503840b00481c80050300341179a076500d0070b283d03402c07804403c5441525203401200659052060700c0d0030028642c01402a1909140001e803940c80160101240c5490003415000350b90080000d01c8003e000b2a0f8040084d2a140a80e030313469038025076040340c442c0a202e020806500e000074400a04c03508520b8510440d080803801616256652680c00d90020121050030340c07102d13800c0c0708407604905002800310b82c51402c402c000b00b50b04040d41210140c900341e090111110346000501c03505445050902d0540c1ca14100380782c20964440141002641100a0010082590200280075002c1407174807900d0fa40d0118000540d068000c11030410130f1180b504031508045210050 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 324099613 1250 324098363 324098381
    0x427290f130c180f0c1b0303021e07110f061801031d06250207030803130f021918060608070e06040f0608060315043c03080a0b03010509030d 62
    0x980010b41e980d191000c48500000b03008000e01c0c00e940d40c1d40310036210030b80c1c010403800d403000d8500468900304541c025655064140c0c0043c08040e80403605400c1d550601a24110b100c2407400c520703403200003502c5c262034050034007030080d030088072540000c01c018100075056441021401c03600e100070461400c0114010300c00d08031039603950445203d901140d400c01344001801070005022400c591b075542031700c5201c484400407042e170455200240410101e140841640e40003403800c00404049600b070305160350081e4540901039800130281c01d0100d844410190401e0854800580f014425007112070380c0c90840746a845818007058010001480c421f00c0b512622242081c02001c0c181051344545c100e0070003610f1500060041814207041c8105850200142c07a81c03003a0342060701c0e103246099038032140801c030300f031510402181d0903c1d886131700c03640740004a06400b11705400a12890541d410300800c50041a10142c80092501c03040551a040600a0900ca80c40d008011403519111300808001040004 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 324100719 1106 324099613 324099623
    0xc02010e011407031b02030304080a0302100b13020c15010f050a05060304030f051c09030c1442090703051b0904020427290f13 56
    0x8812a8a0b1031351614090b0380c0581448001040108038940c025410701006c500442c00c460b0009600e158503019508030382d044e5031170740107101c2241d03001c0601c1a0000340b03810071140c0c1c07074419800070f2a40710b100800b1102da03440e01e10781c0d50b5109002a040f1200e4a548803100300308901d4880c8000014100454405186081a036800b400000b0040701071800d001021034003042d450302014554604290400d400c0c8400e44180c0f03401003075500400c0040b40c603000a0030341c41f02c00c07400c0003c00c6150803040b4000300300088086000035024503909600000c0702031121161304131894091034154001c06111000380441c504504e003030b40c1810303034904019082020700d000f1180e080d43c1e181882c8d0b030065010f0318001001000c880d1a55107a08080058a0107850a040110100584000e961007994018200082180811000c020220714180c525119101c03421020070140d155040d00040c80510803 = true := by decide +kernel

theorem cover : BRFrame.Cov 323920863 324100719 := by
  have h0 := BRFrame.cov_init 323920863
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 323920863 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 323920863 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 323920863 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 323920863 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 323920863 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 323920863 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 323920863 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 323920863 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 323920863 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 323920863 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 323920863 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 323920863 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 323920863 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 323920863 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 323920863 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 323920863 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 323920863 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 323920863 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 323920863 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 323920863 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 323920863 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 323920863 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 323920863 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 323920863 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 323920863 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 323920863 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 323920863 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 323920863 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 323920863 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 323920863 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 323920863 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 323920863 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 323920863 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 323920863 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 323920863 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 323920863 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 323920863 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 323920863 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 323920863 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 323920863 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 323920863 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 323920863 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 323920863 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 323920863 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 323920863 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 323920863 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 323920863 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 323920863 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 323920863 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 323920863 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 323920863 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 323920863 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 323920863 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 323920863 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 323920863 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 323920863 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 323920863 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 323920863 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 323920863 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 323920863 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 323920863 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 323920863 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 323920863 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 323920863 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 323920863 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 323920863 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 323920863 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 323920863 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 323920863 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 323920863 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 323920863 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 323920863 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 323920863 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 323920863 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 323920863 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 323920863 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 323920863 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 323920863 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 323920863 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 323920863 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 323920863 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 323920863 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 323920863 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 323920863 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 323920863 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 323920863 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 323920863 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 323920863 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 323920863 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 323920863 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 323920863 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 323920863 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 323920863 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 323920863 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 323920863 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 323920863 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 323920863 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 323920863 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 323920863 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 323920863 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 323920863 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 323920863 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 323920863 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 323920863 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 323920863 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 323920863 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 323920863 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 323920863 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 323920863 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 323920863 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 323920863 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 323920863 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 323920863 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 323920863 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 323920863 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 323920863 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 323920863 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 323920863 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 323920863 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 323920863 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 323920863 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 323920863 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 323920863 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 323920863 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 323920863 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 323920863 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 323920863 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 323920863 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 323920863 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 323920863 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 323920863 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 323920863 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 323920863 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 323920863 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 323920863 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 323920863 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 323920863 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 323920863 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 323920863 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 323920863 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 323920863 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 323920863 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 323920863 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 323920863 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 323920863 ≤ n) (h2 : n < 324100719) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
