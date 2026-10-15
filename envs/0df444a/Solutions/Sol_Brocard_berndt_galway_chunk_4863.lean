-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_4863
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T13:59:04.955893+00:00
-- url     : https://prove2.me/submissions/34645c35-808e-4963-8ef0-7b192132397e

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 874460431 ≤ n < 874640287 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 874461681 1250 874460431 874460441
    0x1d06091b070309061103130501140c19021c171c0f05010f05030f1b03030f040305031914120c0904150312050304020604090c050706090b0a0509072d0306 67
    0x107600044900c48148000c40d48001900d00e541d00445c0203604019204180801c2481035120307581c1401035a04c680d18907262504207032031105a07814146c074048403500140d5208440d004000b00d10601c82c0101c100c10740850500810082d41c0c01010302c0c5105800d05042c94060ba1040c80b84c0e0000300004510b0000c00310381d0703004074480030417034020214003949422586500300040c1e4000e548281c0100380405980c0c02c000078150010300145541909001410011a0039840390384070843c6600c800180100500000000408070f102815015024801c40c00a086800c14000214240500c9003004040b81d0125040d040c9a004038004038154070384009100000c08440c144c0e05003050395007200f20200300307208041e144104655014100a80ba5281590000d2054491801200803495550000c902034511483c285c0d4225948008104200d4449041502442808413144170360300d41480c002900d501030100d40030085031001092204008083e07a0b44405941e4a5507500c049926440000401314400e8060 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 874462931 1250 874461681 874461683
    0xf0203250302060c030c0f090f03071d0a02040f14041d0d11010b06030105010507060f050411040b0f0609240f040609170d030509010207150609061d06091b07 69
    0x1410840300d82850081e0510800501100d01a0014000c100c41001032608035074440070000c0c13a45650f400c8510018180302c0404000a07050701c240d413000f182ca2900c1c03d10302085a101e84040b03e045541c2c180303841c0e003a0f21443c011410380010f03820b010458000144492042e101e4000d201080c0c80c0302d80091803041a562110380201503000c41c2c880d0400c0740c0c0003009881c24400d240c00034401590304901242d414441807003540d0400000055440a01c1046ea00c940800c07440c21105014604040c14910036080117580c4a17071160b0700e007244290407440c14221400312004003070001420f203004803041161801e501c5002c590b2280044c0465031520100c00024980d003100108533035101d0341011002088005560480815940310031524044134500080350a0945410300d808034560782c0e10346445000e0702460f0ba00401060b9908428440b4441c690401011744221960401a580e81c604042c100c5422403115005110309107070100c3d1807410040c00c0d55900102124049901001201e0415140d90090340 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 874464181 1250 874462931 874462987
    0xb0409031e0203030f0402010c02031f09060605060307080c13080601080a030219030e0919090c0e100e06040c030605090c040306110a020d030b220f050a0212070f0203 73
    0x1240c0481a14014944116481180700031130440c0380040ca80f405d004006040a814841407003850400c541d02004645590a0b02180c103048202c0d00f022540e0140c081c04804451013810404e0104181c14090146da00c11905a910300140e626225075218041c1d1201d050aa6120440d0402103248101007150318003c1407081c000302a03030301d45030800909082401204440c04001402c420000c04d901004480a030b50049548004c40c0e102c0781501040d02e0900e5114807404c07814903501c90144642c501e40e040468200c01d8510000381d030360999242d5008154060f124880c48010046490350400f80e0050040503080d01300015503644450001c1d601c140211203540c2810340000d0144100210b5010310740d0200342d2041ca842c02c0280450019442c0c2c040420b441d02010358500c060801c43e960751403525000003114401c083d02e42d108007401d501a0403001c440483c0c040c142000f080d0f070082284200d41c40781030b8484070714849413110082166150300c041c03e1101144410b029081d4010b011020a44a04408007 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 874465431 1250 874464181 874464197
    0xe15010804261209061b0904020904180b0106092303030405041404060b0411070312090c0f17070f1815140108060d12030c0c0c06090e1302011b02040b040903 69
    0x1103008143c0c81c200034004083e54200500780705c0d071071480c21619aa10340004241c541c4a41440c40860020f00079403070200d034454140203000785060280e1808a83c5036024540b100080d03030701e82505850700e9189210b42e0215843c0801003100c180c9201c03651000ba680024103032407a007542d4400240c25074045c040e144140f2603c10b028041000201e1143d400080000e032024000c0d5000d43c0e1003051b0074010340700082e05000e203c4103c2c032251803040d4003070580d041c0e2080c00c180305103440c2c1000100c404d01c0d40c00740321481d121040e50070070042c00009801080b076840c80d51049601c1d00306900c551011460301e070900d644a40711100c0044002d648109040034040c00031281c447c608408000506100e4041c107000e00811940000c400420744d0764402c03035180412400c000c034a105030f98808503140c08038a180a00041c4c030400740481e26541c451000011a1501c00291034a5164a8442000085202c0000b4003145012507001d00f6a0503100c51490400c0c0018400149460360401040540700340709401ca001850030 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 874466681 1250 874465431 874465447
    0x1b0a05040f060207150c02011223190f09050c190e01090b010f031812050702030609060709081c0e0a051009030605071107090b0301020903030406020601030b010e1501080426 76
    0x4881400c0c80617003034130300701070403140075000030b01020202004e6280b0980c9802c20b066100102c060f9100b20480b5000881d0724615028603242240c4180700344603902203041042c0415020718074040c001c941c54200016000c111006020002c02d031107011101413941c80740c1c0d000040e41c80304540c0514000c0031803540106d081c42040c0700040108200a58080c1894907061400e00c070101c040344041e81003580640304e81d00000100d50141da4500074480d000703516104000401c0200c03480400d10702d0089111f0340f50f02c4803d17625088140e46032822003c418401540146034800315912601c110300c4004005070440d04034a844074041001d15003d1410365011403940d09080040106520449078001118500080e40b519101e4255498000034410754040f103440d01c4110340150740c21350445d004084020200c980d034940c0d030303100039484400074030040d98070f602e030200000380605503110114401c200e003041c8600c415422200555841e18080c0c4140c421020440c07402c01004149106c0201800f885050b4a45442903 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 874467931 1250 874466681 874466699
    0x6180906010e1b09130e01090c1a07030815210d020f0d09031106210117010506010813030909060609082a010c03050903070e07030506091b0a05040f060207 68
    0x2900d114480c00650f10030741c01000085064900034001211a00340b604510711030304001c6c00050000d14155441c204013042000b101c0f801d07040403102e8903260b4001213218080d0210b0180105440a008100c0043c0051802d180942c171a04013480c0080500a203c26602d13a54903075000c5001c8851038580c4681660880181c04200d0b110700d80910400070400724156480082500c4214440201840921119041e5642e80d40d0184d6044a80800c0354503213100312403000c0401388100307104d0b4003c50f041e100c0d00c21400d40018000c152082c13106031038601c015140e0b0a0b9985c0e40b9007103050207030104500380740c020418261034001c62000706900d80e2259603c0d420070705160b0501201059000301d48080c2280c100301c500b282503401030410401d003881c0309001c840e0b040a458501c984404540d06015481e00852168540c13151580502010350302000241c0e256410300c450407005603a10320403501c03081d04208034440000000d1064000300e2425900b440d50760344040490110380d070000070141c0c111650900c09045 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 874469181 1250 874467931 874467959
    0x31e0c0c240d021e0703110102122202031f1d100209030a1401090308060609030604140a0b090703120c080d052d37050618090601 57
    0x100860704000d000403818441d100c181e440c1c2165024032000401c1c200054011076060360480c1004003002000c02c2035101c102d08441c0d014040403004945005880c0c02c0c01c280500c01c0e507120003402da5488207607442d124040042d159941140c3c3c06031005882c500001030b10188020129064840101ca081070300b2040c140c01030759040c1800d0402103901c900c22001094002980d665960001c1c080141d5541c144c02c04603090092200d00600240d00c0002ca41c1d40e869415400710341210302076079480302c298841504201481c401d00f4040c03903040c3d02000200303007c1410b910700002e280c5492000c859400340c080c0d0b2a5201c1420072a0105407540002e00b040040c08a00b01f917000c203050301450950300400e00f981d90354280b4080c100c02011495038500000700c490440820381101c80d501e040c10303428603207003440c0042d10460302242c4e2610441007501d00002c0c0c2254010f00e2920000800400c0340c02001000800c1c0000c0034000c0c402c40c0c2c01a181c445984502c075000c40f030140140105409030202d58100015010668 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 874470431 1250 874469181 874469203
    0x5040606080c13020703031b08090105151f05040909051e01140103110a03060f0b01020705060a090311150c06070806030a0b070c17040609060e03160506030405031e0c 73
    0xd0802d6001c44040d60703030a18540c0511840510043e120145418120020b002c61001c8c1841c0d081381c0c0b0320207682580c0101015100354102c00003030004e561841c0240c40c4180001e00101e41044054041403480100c040241000007075618081d400c080d91004294140e417240f01c0d003a00c1c1604844041c800c025400408903041809050091190f02d6590124803c210014030000e0584042804180c0e41540c4044440340110740110084c0801d008a11144000f480b40c81045409886800000542400c125068840c164030765160384117514619140d01b82150b05440020b544141c00b02d00104510403050040e101e040440b000801c003e14009602604d01503010b0280d6210781e1140342e0034400100046030003039020b00e4a1400b003065207490f241c030001010301b0a4504503c80c00108000c42c040e90300811182c1256040d603603501a5440704400d040d1039000d1030a603003541c0003051005204c03506104001710b4200748920112882c1036949080300313403140d01c50700084510100001c1da51a0102080044e040c1c40 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 874471681 1250 874470431 874470433
    0x6010f03020108041b08030715150302091611150f0f010f0b07021807020607141e0a050d0c211505090a06051e1203120403030f020f0d0504060608 64
    0x81815034001a184400040009141c0554020603480c801034280603c40140750550031a500d6140c039240440010f144048030300756040c41e1101315007000c00e00245d4001103e4014040b040e10b500d4000c00200c00d409410f407134101b485481c80d00e400c1e40c0303201040380748868400010f0000c140e0806000f440500b80c4082e02c40c803c901440c10060050088000c00710044961601e0202d0342c9010910106a50746e01c0001ca01e0314901d50301e001c111400340c0110301c41d403180c4403e03612301d05040380900050005000301c1c0704c1c002080d000d03c1203803c0a08040c0c2c1c0200580007042c00c00f24208584c5045c28800d481c440f00c0d50400140e0f543e024000075400740e035008424020340074400d00c042e03422103c000c15014440d00c915403244c0304400c0401d40b5808140d20250240802810380100d10502c2405040c1951540103c2801448a0017181c03402c11004804e84150745a2800d401c500c0b51941d803001c034042c2000441c0a001c43d9800c01144c03400081c5072000f0a0341c4140c0d208040b1f440d10389410000110382440d440f404103 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 874472931 1250 874471681 874471709
    0x3601140a0219050403051c0e090405060105030d02030a1d0f0603010305010e010f020403080d0506040e0f030309060f041e0305040e010e090d1409010c060f09150b010903030c06050702160b0702030601 87
    0x10f800810341c2250310300c004c2c07140807403c070714007030304880407132300b500c02c0a411200780c030140814080003003202d9042e036106508a500d280100f0000300c0c0d4038411400400000382c0e011403403181c2190300d51a00a043c0c0d0b4001c1074050b40700d80e54400200359503c02c0e032003112a80c0d0340d2058845401800e020b000d441001d500310840c1424a141c64400340d03071168030841c08078180c0d2400001d5081e07941c0c0d442050314002c19802c4420700c10850307503260340e69407054030303a00038500c11880015042c032482c8030a03078400c1c1d83c0400607006800403002c0c0380b00c002050304011002e1040510021442c0006050450700901d0000700b10350b0207007032040d2614101050400214200014011611040b5030900e040f6202e00d9020f05e4041031009050401e1002024050784110081c2d04201442c030501c082d14518580114107001c1c10440c5010b200c0064a000581e40f20040200f03ca11405d00302081c0241c1c012030703101455005540d25008107a4080305448041d0b00324055540003c01c41b40254101048018090b15140c183c60b54 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 874474181 1250 874472931 874472933
    0x411070b1b030f060d050709060f120c050d053a02010e0c0d05030f03150a120b0604020f090a06050c100506092e0f09053601140a0219050403 62
    0x2501c0c0c8401420010703144110320214010b500c4000b50607540325001800d65040382e07203a000a1016141c1e520896003410030700e450115412080c0140704054960000082d03074036615210502045404440b07003510a80591080c02a05861728103040c101c03003015002102c0d5580c2d5000b80d02403000480c0001c102160300d000c10900040c0000122205440012030304010041c003503140641c51032080910207902c01d407002c82840720000e0b000c845041ca41004651196001d43c40341502d020843c0040710203098008050045411030800d070b4001d0410b9030001075a00d1500303c3d00c6011401c441d56070b9120b000001c0000a8428000005000011040c4d20449081c0044d0402c60000b0710482405012181030b100418000c00a16000003d008500742c03034188064085035484a180601075140d100e060381039410140040d002c2c2441101e84249465a60600501500405114a5040e00380c60004000d596a42c00007400410f800340550f00c9500211000341e60f0b8144030800d80c15844103160311805204080c04144 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 874475431 1250 874474181 874474231
    0x120c0f0d1e09021833100c0b040809011b050a05010b0a06090302060a1701060306050414040b04110a090e060603011508100507030f060b0d0c02030913050c07020411070b 74
    0xc4407520071030b94094010386071250608a80c256504080340040911446805c6020030303002800c562060448202c1c00c0e0300742c2450180e5130040c003c0b030000c0c0203203101300000300018001409019034a0040c0b40c80c0780520309101290700b04402d6044e081d40d156124040319000c10000740591004804140c2e80000308629051005c1d1120016000080c801e040c08100708450a00c2501c18840c00b0200b07000b001025690707401c0103402400c1502030f40d4040c90400f01ea603d807058026201c00d0003203a12800f2107080b9515500c0750a45405034000e4150b1001074002c0000304120b003402541c3c1e0707500151018128a080003410142110031000d440d041d400d03000c0f44200200d69001c03074402d45c101c10701980400c4541d02c4220450081a100384010302040c6040c00104899100f103018011640243c2c2c000c0014000d4100142e0b56401082e040307561150002c1c0c03951040412980116802c101c00260007070038901243e001805503003402e400001c03503410115103102807041d0110065008140c02c2c180005551042500c9 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 874476681 1250 874475431 874475449
    0x51f03020d15030b0106110607090605030a0e060c13120c03020d080904091101020f060c0a030207171605060703060308250b0f1b030c120c0f0d1e0902 66
    0x1405040e404580034284180380d82204100303214920340145055124030344940c402e1402c2c040e660020340b03000c1d60140300b0040006c0180c0510825107030b0404081c40d04070304440c15880100002000303a1120a104041c560800c021805a80c085448035140e522a01c00c40c4468210f0350f00c550440030040100e040400e008001110540c1d40548205e0000c07407990070511002d100d05c2402c56041840c2410040c2400a2040550a000c0003642590364803110381d0055991444185c4042d980014208412958640613500400c0400d200c3d24001d680d228021400c924103402c031902e94403801c80c0c0d8040c0841040002d0101d1170303008485040401016080d074440d0b028900139001240121030044200b05554841590a03000895000388032101c2444c110003442030004068034000001d07070035007010007100c07201803094a204228141c0c1d0300f030501c001000da000c6000400707001000640c10412100c2240c91100b4000c00c58803003452000f1554008c01c0e030000504035184a81d040e151403038811003030016600d000704 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 874477931 1250 874476681 874476739
    0xf030b150304141f0507080f070f140c06060a0501050f04091503050322080703080904150e0a0c021908070609031202180f0a291603030b03060105 64
    0x120030380340c2c0c0d0349242503244807192881c0b6a4461258524115000c55110a60640c5030b5a560040c4800c0d240d003901900c00b030b28107690800c003c1c940c0400060301c89214a41a01c0c082560b0700d0000000c83d84258100c00d642c0c041405a0950340190080111a080031242d0703034010f007c2860070b28940308031280300d140c0c0c03805140542e500d202c1e11442c020459044103031a00c00170310f4002e804c0c0c907540c1c001c0b440d40b5100a0300f20070100340049401440019012170120303408080340d8104020030b103483c55050810004100d020030340003a0055400c40407480030f0950000d684a043c03059000100220b01c2d2002a1030210202699100d50002403082030004000b901640c81040d480034010944500c071b450705603071643c0148100c0b0003052000c00c8144503032090200e601d0080c01c0039540c0090800040d0306101c001795060050010104070314134006801d219140c0c490041d820140802810100310240f0400b101803c904282d00194070798007140e99907c0d040c4451401810225550022a98002d20520320b01d404440 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 874479181 1250 874477931 874477969
    0x60d120c0c050907080a0e0705010903021306080f071706070f03020d09150f060b0f0a1206050d120810030c1e0e040803090f0c0904020f0f04060b03070f030b 69
    0x40040800c100c0452040141c503004000c9800f40c0b03044034000340105001c4541c4201039003080f1401c0e40780342001c60ba54055035010b9450181c501e0075602802005641030001c2109a13680f000700069800041c4801100d51154501900216140507003001300c0016000000c1c1854001006214800c1e81204958820150300d04025844d46c900000400080c05d105001a04480000d08a41644111a8000000c200c00c0240402070ba9440c5c52480f9007038051131450710310081040045c940c03054010b40d5000f2102d40b2080c0040391998440000c00d0707810101d880708071544010f13154007015141d00141034942c0050034402c00108a40307140c0303500082244c280b04401200c0c85404000741a005059205009824003040021050a00340f0b84102c0c5903004441030000c03400740d00c0b4840b07440c03200401c60001c442c3c402005d02c900b0752500e400f0441d004080c40061680007141210310101515603000d06e1000b000200303003403610707440c14450150031030140c1c40180041610381000c0224954a4100c00c81d40f20308418 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 874480431 1250 874479181 874479197
    0x45090a0b04060e0d0315120c1e08030a080402100813081c021c2d02090105070605040b070e030d0507080d0204030c090b0a091802041122030209060d12 66
    0x2040c80d03401002d0200818900d4040c0c000740d40f044d2901600701300f034070504122104111507660f0401c80407002d40050300501c203a5220004004142590001400b540039010513602103035a41d209080c03030343d80f200880c2004240c03200100070652804c030040c2220003001d800c1c04c940600e0120210350091a0305103004021500104000c038983d044080c180501e101041c804540e80c4402d01100042c204c4003145815811f824078640600d41607045800f06829990b00b1070240e010030dc042602c60194111454050400800b031180d280450114040e050080f402802041070fa81058a4010021400a480e0310700941c42a0035032090740782c0c07060458001c190402141030302c41c9401a0450081c0c0718a50010b001c0f411a013001041e90001680080340f150800c8403241c40c0b02e80e581395420250f440c443d015000c3c0c000d00040c100c02504260700541000c420340d4074460305d849c0242d07041401e500c0d41d0703405041c0c5800c0c40880510450421500309500803000315000c0d04030f4401359507a4200e9081800c2003104000e808 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 874481681 1250 874480431 874480433
    0x109030e0d08190302091e040c031e200a110609010e1510030b0903041d270c090a02181915110d03020c06061905060945090a0b04 57
    0x264161400406c0c02404a10502e0034809103c0300c0204a500c543e01c10392510780c816013194000c0c418a10010f801c2c042088219131356090040007401a01840c100c1001880d0079012a4000400185980176054446039000d254000c40d80d031401c80e0050000859a03d890a0400340907800240204004441d1172100305030b544042600d09807039410f510080848006506010740a40040060026078040f40501d1915000f0f05034090540c0c0b4003500c50b15004d8944001e0400e02d51400402c0440c81c0001408a034102d015490110350304034001c443c040c60240d40850410403840074085050000d0340d048600b50000c0711210100c8824517102d2103240e5008410414000b0a603004400034840303030135080d0641d10302000b89900034000c3d5001d0400b1084501850380040d00c9803030048100e8080d165002c8011041c2170a0406101d15503201c1d1140c640c0c0280d90300d0308003558800074200040e1300d406030944007c0307900d500d980381507a1480c0014148140c12022040000c0c0e1170300001d0b00030318550003040c041c1007a111 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 874482931 1250 874481681 874481687
    0xc09011a09032103041419150b0904080408120909010b0307020f03190f0f090b0c07081b0a05010801030b04030507020d050a0c0501090801021e070204061203020109030e0d0819 77
    0x41245822070030f510854105841c40c011001462199005009110b100340354200a0303901c8842282c44600d24428414240c40410303100840d081c180d850700680060500780100003e01f15260444040b02c810f000002d080c4030380a020f01c500b50030b898a0188403410304110750006004240e0501034000d400e007010000826451081242281c0c000311070b02901e50b50713980c02c60602d50150404101c10082181c040c20250303464810034050442200c1540c40e8806542030599210003540034442c007a00501c18500c001c40d00c81000e0016104100da01c4641c10240b02980c000d002a503500760380414180030460004002051710001815400350341880d006507140302130b100046009018400150140c8100d0310303140100b00004c2c1500301918000d0f00d0741180d06a4a0080c14207034030454203a070010b40d0821000c8043c50ba007074805080c145100a001045044d140c020040c2c07014440e40007a80140c1d1640703803036420716030804c0d10610203802c203842903800010151144005e520036000d80c4006160303102e00d00d283c1944 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 874484181 1250 874482931 874482943
    0x60916180911101d010807081501020c1801140d0201020a0b07121b0e1002191104020705100b0303040f03020f13060605040e0a0203160c1b090c020c09011a0903 70
    0xa009140f201c0c0300a4410000307014802d1180070300d4034049010f510055542c0146c2c4000c0c41440f441d55816100d40d00d4a0900e034030640390703c034000c2c15881428044022031f034500c0d80740401e83c5540510b904503903142a14140030001c40391030f0319000d50035400a0202507640864402c551580010719019181c4401c4c40c120f075080c48080d41c0e29540d0b0b20300200700118140e01d00341000d520b01541c0d00e0302d41480070803080015202048901c00c0c050b9100c45040c1e403204141c40b000442c00fa0041844c000c0c0c605442d0040780907680004001c495a40188002c03c00c808020700c81d18403c05d01c141c00460915080c000c00b5443c540c01404041e101d00003000d103039035072039a406079042841e0041c03c0d0709002583ea201805040f42e0424000c0f091a29844000240300d150a4030a4920800350030a00c0c204060290000340e90141d40c039941500c000501d03110491301105500c0c1c0b42c0c00140354a1100007600112200d000f03082c0b0040c074a620348140c8000004212211840c40c280c100303082085c0703807169101c0c2c40100183c5484 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 874485431 1250 874484181 874484213
    0x3020c0d080a0225141201023405030a050f09150309011107170c0a0515160507110f03240f091501030f080405030f0609161809 56
    0x40240c010420800144401814404859070221140c0002d29128050341c0e03100c1010b080e840303140202c0304000507204048007120000010780b121080d02581482ca5081e68042c1c129031100b9079844540d80c00f202030701e070350880340c4a9040c2180e80391440c2956487d030700d903c40c02114404100000c1544070001d992642181e00b4044014114003141c48800780c8085a0f0300704a4903090701d075103005172003859442c0d60002c8030a0b0b50b620030102c00c200d4013480d020303030340a402c103600e17000442c0b0a0300b203c500007400030450210891000c108540c403914107034a54802d4401d44170b24002c100a03041c00301c1e4000650b00c0500310000e400407920000e520b0034000210785084d00205010300300c004507513001e1345a0580ea0700e459002e12411904151700b6541c8003409030f52400030b0b44000c01c020a600e8010400701e01601881a100ca1258401074502607a800000785030003505240c0c0340c51900300c00c05001c00700d9000c100240c0480440c2044003021803030900b141240700103110740014181d03126044141040700c8615626498 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 874486681 1250 874485431 874485439
    0x60504020109051c0b07110c0405040f02180609130503031b1c0209090601140a0302030c04030c0801050906060307050f0d06020c0d050c01230112051e03091c0b06010c03020c 76
    0x45101342103282c0130341035481802c1d02d0a26a44000c100034500c82c85041e80141c0280340104101440d450034070000b4140100103881011601d511603005a03200052040c1d200301da2402e000076800c26008104a001000e04620040eaa100003c42d001880c003000b52940500d513420f48000c485400c0150049500c11281c12440740003219144a109194aa0217402900ea040c0c90740d400d10b80c0d690005580c105407000f01001000340030300c00381d52050b1080d002140d10541441d41a814180d907584c0350701c1d14807615000160682d448008011003000108141c030ba000c0c0d0103c005040c018070306030120342081d5a01c22240d006101550000b010320041e0b030102e5410000791011030301a8150307100300410b240c200310801c40084d402c0c40b26129a0390b80300c1c050169441c00c0b1042e00286a46042001b8012200c0c3c0c4c1000c4075140902418081c0140180c42005941e81c869000796039101c090004100c101d003405001e0550328680107031104089845180496400300b001e00b01080280050f0600340e1805070009106544 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 874487931 1250 874486681 874486699
    0x170703090b07030f06050d0b0f180307031e0801050a090b0d1505090d0201020712082d010f05041b08180601031b0e15150c0105010320150706050402010905 68
    0xc02e90684c0300508888a90000f00a52901e40040000307950801201619840f2031401041255461256007a040310703071140c2455036800307228605411500103610030b40c003040040c1540f10042c40d01080001f07076111107241012440d030410000030900e025074024003082c2c6a42d07145036203261303c1e482d000030811a000582c00c000c0c080d030543c000e0081e001c101c2d5080c240740101400b00a02c94014000e139090207521442c90184504184402c5810f040010240f4400680304641c1c000703034142c41c0c18480201b100b4201c003940c0ca58100b5801040480ca0f50380154016460482020940907100c2c02d0002680150315009403552501340c2180c85000e582080640580611800001041258412001c0600c07c8a00c1d98141d20341d18202c0c0b0040302022905c28000140c5242d02080900e8004611807200d03500401d02800c01c0c482505440c01c440c4243c2040340d41c58080d09802c5052441c455404500352070494184040f00400c08804000b4002c401009081e9030300c50000c24116801a034440015017006401410 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 874489181 1250 874487931 874487941
    0xc040f1512050624210705010906020613020a0305070603061e060f0f050c031201091103040f060203150424080d050a0c05010615020a050c060307170703090b 69
    0x4020004110311244084030418005a0301c91400360002069811501400244c0d0740d08071007280c5024a8800d26085200c20307486180c0f142d50703009101002d1090000044126001118482d1901d83e00e900480d061100d0322030200107440d80040c1c0a507200d0150009076410951510100704840480d0f04014068001e2000214a156040c0d101c0c43c216a40844031062940b40c0d40000c29040f5414040d580008240b54455aa01409038030003841036106031030314525028070b416507181150480c2ca0302c01005501c010041101462a010300703440f02061007070951441c04c050799151140003a00c003005090540101c00154590900744c04404c4110000e0824400e40172140c0c6620031aa40365580100765020b0303004045006000015104050185520303181d01d8101c56100c166034821031002c0440309503494403004590002c1103446900351140326001403064001074906241403031041581e5900403041807080001c6558800944030782e229014005c20750b030351101c9204601801d5280381c003900d0160302e041842 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 874490431 1250 874489181 874489211
    0x30a05030c0a0b130b0105040902010216080c18010b09010f0c05100b180603030a030207051e39120313060503150d080f130305121c2c0c04 61
    0x1a40d00c15050016079581d418108440c1a54138a40a080307075421a00602107810b0961041c94000e0050044440e2400a48012112200b2030f4100c2c90f5180c005000b45151170400e010013901491428400c480d266051020303400003405a035103580c0c108000015556800c3e4069603880f40a5500b060540e1000d24000c100d003005000000d10041c0076801c54140c030080c03240461546406682e008015600d0981002e400300d010350071188054841c0c2c040c080d0012a00c141540c1181050300c41c850207044501c0410605014104c40c1075a0310350488403880c000200d082c071240580c50000001c2b941564070829083e0b076a0314500420b400280c900c00200e001041d8140c2110155114071686000181c101c603109040c061810308900d0000d100f20018854070340a200001c01500e940e0844040380c8582a1781d030f4484515101c41d6940f0100b00d9800003071180c40c1d201c81180031840d9505010014001d0400381c1c40403803000590000941e00f204082034400d9034510060203401d20480c002441400022442c116003 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 874491681 1250 874490431 874490443
    0x210512010e18010e07090f06120c05030111031302060a0306090c0915020304080304090203130c1e051806040905010b04020424032d1d030307090b1603030b030a05030c 73
    0x30b10360034542c01d0003111503000d05009540240d108400034080c000c1c682062003001d040010b40c00b4480f2a164480896620390910403110b009000f01c0c40b60450b00c1c544414582151400c1c3c0301d5101c1c6150400030031071520000b01c04180c000d64169059a541e032a282411001407003d90451041d0703500b0703d11004405980012940c040e103828082c0101c8440d41c440e0203076564416442106070540080c00108200250760703000d19402600501c076040048402c1c0e076010410b850381d4100b1030b0000010f0031030f548003000305d001d580d001d0401540d116580300460701c0c221088500040210703118545035600d030f1781080300a4108441084000e0015925240c0340c1030b1b01c5816215001000b806641d140010900081c480d0240d5203403c26954044520000001102c00c04811003480919140e03440f4180003640c4011079a200442e0200c60340510b440741030001009003006860750000b214000c0a218840550b006054001072140c1e05041c00142c00c0e42030008a1f003001c0d440e10000d01640004110380c0e0000c540803540c = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 874492931 1250 874491681 874491691
    0xd060303030e061807060c0c1d0f0c0703140a0207050307180e0705300a0c03060e0a0209060d0606120c0611280218150f010309210512010e 61
    0x16200b2680d9904108048901d50440c40b138100c0e0f00c190004c0100c540125003a2146500400c01c1000e015150440c04001214140b541d41e105003030601003001c1007401000080c2c000c1700585905180c80410384005000540691042080c0c0f0000507a000c4d400d4002c2000e60020701c4083d007a1030056940b071400c3c140e1101c0481e100d803003260070302c00c0b40c1c281500c0124000c000e60b01d004144425082003240c60440c41c00054014108005524081d1031180c2020084e182c8070b5403045805010440c10b516020090342c0600300e5296669100c0b10310440180d58054030641c1c4904152007003694bc1503541442005440d050740807a0342044001d12035424030519040d11015075055807030380c065856604907040d54410208401002064a06503600e07001491115290301c154001020425403401d1808038800010042d42c5e2081595012080c5400b5800c01c2440000e0302c10090a0400030003035183c865180111044484841380035401e410020068003517400d494041d0070391386020031550f0312007210b9903071810306407a = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 874494181 1250 874492931 874492933
    0xd0e060708090f060f2842031401150305010c030510150f0e100c0201140a0e040203040503040b031003020103110702030d0e1f08040210030902091602030d060303030e 73
    0x40f814541280011118041c4131040e5044a1941e81d84030305003c031102c50781c02a5080d4415100d504811682406186000c07800380d4803201064501100c031449400c00031039110101646c189071944120916811a41240d402c44000d80030360901e06002401032221181003040c50040900200501c4415404510124940c0d18100302c0760315490900312041d04540308500107440c4000030440d0042c403500d5007405888040c2060040e01d401c0c1c000041d0343c000442c040030001181070b200c180030342da03004050180000300c0f1086249000c1101c50003c10151030b0803581802a07800201260070402c0c20000c40e0300602c0c0c4115141e442c1d0800720000c0d4824042031000381d00003418100034002104981c41150780c440d500500404d18005031000944400c940d000c501584905ca60404006c1c0809420040284880d00e64942a09241c28810030441460004480c01010f00d04801000107803111000160403c1c89403450300d50000303500804034514840e0034100b00311079041120000c01c2603019080004281c0200c4 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 874495431 1250 874494181 874494193
    0x90e150711030c070f080708060408090409020901060f02010c0801150c020d020306040b0a1104150315080303010909060501090c050412110a0e060907082418150a060e010f050d0e06070809 82
    0x9079045a651f00a80940c2489403c42004100061208401004c40001c094404600300c02c1030380000b40c6507042644107102189907a60300340f032041c4c1d0a20903403521500505182000f94100703040f42c0d40a854116040301801010302c2039000303642d14215088503090340203044518070b150900c1e0052500c1010303501c1c1c0c0343c0c203070070526401615a0400140c1d025982c4c0300305002d1000981880460152515038102c40001c23400c80400f04035070708244025806403000341d03800b18001405140043c11100140c0c40041c00614249281d455203501c0000c072800c82d00c4010301d56680302510700307188041850010545600840e07540000801e0200540800d200b50002c86006449a469803000c2d80d090404803480243c03160544001060300c03454100355855138901a003084c2032040d4946005000840941d50190b1003a002c807800e1600c8d2400b40780c00c1000c1d1101d8504002c0000c602000603113078801420901303050050218840c07441b01308035407040c1e51103203004044032018104420054175050050b581942180185 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 874496681 1250 874495431 874495439
    0x60e0a0305012d1b0305060d0b152b0b0403050d090515090c210c15030907060f05041401140a030b01180506030105040903110d0207050901090e150711030c070f 70
    0x30b04ca0310480310082d80307140c5400004060120014080188400d910050424004010503280404180304070414845240c00c21542010003164196446054a07190724004402c464240300f400c0c14002154801040c500b03503160303407800391854040d5681603004189062022428064000390700d104d00e07010103950481382d4451203e06074640c10301d0f0101e40d401c043c2c7e18245070042c0301c07468040e5001c0781e400e106031044000d00400054071040c90501042c0e4020020052200c000d00c03d0044c58000e241c03e0405009240f80c0620103400e6020720704c559844070501501c0350042e64010340100c5008401c0c46600c03556800911000390040080401603070014404d810f01c900303804c02d1070b00513400340c031401003103107003168a8041040050001204200c041050340300c0242504401000000e1103da01a0040d00d2018244400e112032560141d00a030b1015041908007940fa00000c01c0740300310100341c079010116035a11421300f40d41405022410070340d5480005180c250807440414840c0a8815500071440440d0751 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 874497931 1250 874496681 874496771
    0x70801060f050a0c05010b0a030303020712050405030a030e041518050a0b010c080d091b060e0301050f04120207080f030c0f010b06030f100f090501032901060e0a030501 74
    0x1d000500010500c1084404031080c01000350001152181c2c0000c90128100c0c0c000c60204600c5d40d0040340440d0f000700b070f40010014100100c09450000346001400c1a286c0f8002a0b51070440503800740604c20400c651554640b2180c000e034043c00c000050400449035a03030740c640388540c848110f0080144ca0400452035000082c0107005800105030f43d06c2040149039229210150b1014154202c0c0558a030000c4000920030458045101401020340244501d403c40240203da803214000c1d10036407521042000d03e08030f001601d0341084d000031100c415000204030981c549801c0e9084541c8a10955a108070003e6000004240801c090340070740300b00410b04071000342a1020603d82d29032083c010f20004803140303a43c0c0d00d91980010302022014000380e0340c07400e00040c2100341e040451100e4440006205002c3c0c69034000c088458501c2070882e408240354000d803403010060040c802004040400760245a07a4141000091504007000304599880c1d16601052030a0b03603004041036a111682005503180 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 874499181 1250 874497931 874497947
    0x807090602030d0c171608010e01051c03051216021203040c0311130f050a240311060c031801081008030f13180914030f0f131d07080106 60
    0x24003500110b0402d0000401800600a040070313035020803006068000440c110400018001c0082840030000d012030220010030b044d80c160407020000d0341002c010040e603160384041810346c1c2c5083c07207c003441500c0c5140458030b62040c2500981d9081c25003007417002c1c5c07145180007510240c00540031601c4801c40c8404404041c04122b40c040e00c0c1c2c910041c800c002180d4561403c00700f51000909241d911042c50312800c04607524081d480d03105d256140d0400c020080d1a03c145043d44a1500100f0000384d221100d503542c00a0b41d0000400180a500302c04003161203441c02c2d50300501e000d030143c90720350900c1140d01c2d4082c0080420b03940096604008105c51036405058802501c40741740185107000500c403810340503a8041792074640340240040d030010301e80018000091001e010f445010a21f224503041405002c0c52240045005420400501903600c4c0c0c0c117000c49d4110031004c030300385071900780d11012444400c019174007442c0304894119602c505c28441c500101c2c82001284c0301c004003a40c0722002200c1e800717 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 874500431 1250 874499181 874499189
    0x20106080a02040e16031a06010e0d02010e010504090e01020915090d060903090b0c10050a0b010e090604111b010c03060e130c0305030f09030c04020915070f0b0f07080709 75
    0x30304440440700250606070042094265440c04039000c2500c4a11104600b885640c03066032040200c80c20354032002540080581c11940901c0c1c0b240624042800080d445107103190000d0500c8000580319039541d00034800c2d80c00900009000f0031075102804241400f0358050310840d445a00ca0b02101d4800c0f0307401030b09aa141800241105a03d00d40036a6244000d200405050b000d000c14070304006507003040314005050001c80309028041c402c5001d9079540a035100030704481d00c0d2504100c01c52030183d170b0200c81503a034103008032680d501c00e03200c10002c078004140210401c10145800120cc21518080c03210580b5003004141c001c0203c020b40001c00c9048600c180240d90a014035000482c0e03103143c1001e02480f919008403d0050070366640d6482e0303440c40d40483d903903024141001c40e1a80441c5070030b0190300602c04041c0e03010352034868030344005002c401c52101d41900c0c0707200201c0e44109000090015840090384503990030a0390034481c0c03840880c2070085a000d00080d21010006d0102c41c801d403841d01c221 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 874501681 1250 874500431 874500433
    0x7080606270702010e030310090e07030203300a03061a09130c05190201050108070e0c0306150403200a0b0a0f081e040803010503011b051e1215040c02010608 69
    0x4640340c40744804265802038034002c00c56407100c01300784c2c42e103100f400198019a10b14110000440c40d10f40000103643e211180c0e041d00d038000700b10401c01368401003400c040301d00d406000101080301305280c80c555030712403c410f00445480411000ca078141c16502002c00c0d594284500c25191551522205d51440380340303405a0000400f000d140001995034012a42d07074002c6003005810140c24000340c00700c00c8855005000142c0d100c0e0010440d02509200c40c101500b862880b0700464540420b0620796440301418203405070302c0310002e14130800f6040d402e40d40035541c402c00444180c92019074001c0420303900180c1c00c0c4900061040082da07440309008840d103000c584c1c1c540841c0d00c108280c095428040050152807030f8540b01c0600000d60030b0644c001e520561046101c0c50300ca504040525003110022100d002107410801003424585810209884401d507400d451659407148800b98a10140240414a20b4030f401a20a02101c4280ca254081c0030100540d4108a62080d0000c220309076105885400c0c01 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 874502931 1250 874501681 874501729
    0x3010605091e091e132001051e030613020a020d030f0618050103051c081303030f0e01020304020f030613110f09131109280b09010807080606 62
    0x2a07082698400340240c0070561140800074909001c1900c4410031502034446040140001a64442c02c01144c0d800c03803002e444800b048a0170b6600d00c10045c401b42d4100700f00c0c8a0600002904d03a202d43c045802d00c11200300200c910140301e908907038440d04180c880510500c51410741c0349440d02640f0944150000540c0241b041c02c6012605500410703d02e8207241e2015200c0f58003085508100c0c0301c0c24010614840001010b601d9420450b0400344d2510040101200e203100600207030b0b034012010341d00404d86402038010484a0300d002e400410100078205e092504101503e0b181d17880650107144a94000c0d114810442d096000f01600d40d00121591801c255029a02c0c40203e1006d0090b841c9491004d000b0451980e81c0710001520b005049503006540c02d1808a49801c004d03081031002e6901c0c4050703c03c401c5e1420b0040c140c507903007400050403c0003003011408941d0080b0258108000c1e80300c015150400a50311181010b880d0003007070080f0899481600089851800e24404011602d0802a482e0070303 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 874504181 1250 874502931 874502947
    0x6141309020309010908040b09030c04020c07053105220b0714070803090c13050f01030209091c090801060f0807031101110d120e030703170711100c0207080303010605 73
    0x4000d40000c0c001150b00d45d80d81000f2800585200024405414101019500c402c400b908151030b003180309140b540a14014410814a2000066044165041103504c1070518101450760540708584078100300b490301c0f00c0058148141100c4c1d02007070084400400c00300c20451400740803005401050f60060508d0301c58800503402903c6480503030403032440400311614000091f1030f0401c5a810031b5807410034541054100b4112445e20366145030f1017065410341030140c4d00d04144401c2400c507052202038061000240042e6448000744151024040c1c1114680356040110f10b004003120070074002d041c6103610707000c0007040315002c9805032801c540b50840200040c0d801c541da5038aaa01490302c602c1e0501c500400c680c805002c0c11321180d030b0021481d03039030144060100a40001590f802d01d0568031036800410880300800c0d403000f0703038820301c0c4048000885561101e40044540440e41d0315492183c0c041c1460010a00c441780c0c000803071111450382103941003078880c160b003612440700b03200d002c0110300c3c1000858 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 874505431 1250 874504181 874504199
    0x90212161103030a060608010501170f040201030905061006031a030c0d0203010227011701080c010815031e060a0501120b0919060b011106071205060307030219061413 73
    0x20144003071501000d40c0901030520381c5590420b039034290509485880a00c882d1707038071031441401881d0928100b54000803918400c031980d48040c007258210440000003034250390098100400050b4041c04507103043c50702191030351506a0a00494002074280300c80800205080002d0a100d282c00502408244000804114100005400c1244c00d55001e02114031541241242419481842c1c512241054482c8000410f07082200c0c000b03c030803032820303070042c440c8110010f44060a100282060741154030313600110844c0c04415070403540d140c4a2000c101c0082503da154403075900d580141280c6c029268288400d065070024062180700241c030a00c0c20020036440015140c11421a41c05d1b0b0b40f02da41d160a00350150000c8a2060718180c5c1c0313030711091840c1c0d64803c061050207104034000d4000c0381062000100038045000c46400c006480d0400b01e0035550b020703c0503000440c2d0003014110501582c440300c0104001130703c00c00317022611801c410158002c01508a03407004810000f1241d01500b001088 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 874506681 1250 874505431 874505461
    0x50603130204090c03030906090612050405070b0301081b041a0910051c14010506090a09030915111e0607110a05060420040e0309010f12060902040f090212 68
    0x40301000369041032920160b1a5442122000c6008094002c8060f0450402620740a0705600010400103800c100b00415988030003078982001d91154003060b2a12181009032419081d45c000390103000e03000000140f144030010f038803084078141c03c80085620031a0000c10080f0740c100603c5204a16a1039030b41c9400b46401c0e80300c15070205568481d2101180c4400c04104281009441385c0341e0407a100c40380100384101d9044a1a8444085000784542d00d02000803030143c00018140d1820944c48607006030806010f0900715024000b01d4040c640e200081401c010546002c54201c800d41c2e004a0008042e8000040c1907645c05803006401000e164640c00c1049856104800e25803c2e24050040702800190b42400b5490180b8001c4103055a01509c045d075111915026440c200d114914013112202525408415a1a80082420711500100b1100b900752501c0740300000e00b034282d40c9481d102055400b01c1364080c1c4107031080101c400c10030a4903422494120f1081e1208103a56180340400150440314010302 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 874507931 1250 874506681 874506691
    0x2030402180408120a0c09050f03012a030b010f05070209130f030314070228110a0b040f0e13060903050c0307140111032404230907060305090304050603 67
    0x1aa105116060035044005481070390b003143c5109002945030115028035000340c1c1c0204050314100440c00c4c10b25805490200f070b1b03100321406030a03000c60041603640d0a511505011201084402000c44118032030480344442c503a5400200b03203030481c0c1c5042944a4000d480706401070380c440e00d2074442e16070204000c2c10130040160104024140550340000c0d60780e45d0407039105109031404540445456407a18401100802d240111341c41011030281e000c1504120718690000ea444040c0c09070b1271802c28400030000c0b003c000c4e070054404000010201050700080c4102c80c418548010f5554032070300d500e42d02040640301d040303400360400c900ca404101207511000840b442030415074600141800c0c01ca080da04929010385040c3c00144045c14110f80a0240c014091100c3d6061071941c54211481c2c521120704921101d041c40a9250740803189c2c44540c002507130480c0c81501995a14110f840006904004540214050050a41c0018924080d004d158041d0f483e00005d9401c150a040600111b500300800d = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 874509181 1250 874507931 874507939
    0xc0712080a06170a020a080f15060a0f030b0403020d0311071101230904052d07171801181205071b030821130b04020f120102041707081002030402 64
    0x40020300c1025521840c1c072080025006130101503910f004018240409610000c0300307400c4541c1c003030005140403070200c2d0306035000310803104152140b0700860105130383c94200c0c11001d80c1410010050060762100103110b2031099013105c07a0f051851000701c0a86109024248a104c014070000000400b101d107000000305061415040c03c03007000a83e0314400440c148102c1203c200000c4d60300080c10180105644006404c5150740718428645126156201084d9031480000440c404144a03510920840c540284014405034040c20303d00540c4004026a0008801c150310340004e41d4001c0184c800840b01890704070100c04200180101e0503500c40d4000c070310880d0340c00c1622140d00c1740f05050f0718041c00954003444499403034003564800411051550410100441c011908108418003034101c0c034100583c0c00b411800464407244089076080010440c810340c014440055002000015405007040f5104450300100794107045503015140c42441c0140d44690700720100d8601c4500d00c42d001190440d10140c = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 874510431 1250 874509181 874509191
    0x703020c09062722081206210102180108040209010b0f0c011505010f02072d050904110109061b060c1806050d0f0b060d0c051c0608060c0712080a 64
    0x55096041c015843c4001128910704000c0c4100300721201410884503c1c04295208800050786900d1254090015801e803c606841c00198441d202ca0203103000c04050741d00c45000304440c240800f4081c0d000200b040703680c011010700755483c661060070f04a010b2500a04a0340059090429060499206071040e00c20408100000311402c0424459011000440701c0082c29881c1041c000410303000220001c40c04550000d002407141e0040e1003810007001002a0240d5458150044034500c41000c9510042c0d115006904100c2440480350012a00c5902662003401460b02d90714140c5010075494a40341c600b00c0d400e200b45c00003603c0e551241a21303012508040441140b200703400c1d403040c42280c0101c0e0004001040ea22200044c500640c905840450814080841c011022079041e000d0ba0340001009038945000c48172040c010012244171580140e400c2603104031100860010f01414414110301d48500360004074580403400507215402e62084805000d210344180440e02340300060102038180d0303507039 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 874511681 1250 874510431 874510459
    0x1d04021b03030906010f0f091802040903080f060a081b0a2705062751030d0f0e03010c0806130e0709110c030706051b0703020c0906 58
    0x406040559182000710341e01d14060224a040050603030080003844d410200500483c18074200130b0341600c0301400c1c00136149102003801080000080c402a4100e40340c20495800e142e84041140d21510f07500702000340580f00c00042c400c4003100d52003050f8250300100030300346050500030310880401000801080c0c1c0b144d1030702007000b928600c01c2010045902900716004c00330405000b8030794403200888050700f031512112044600e4527030030170a0700c1c0300000703800000c0d40381c522000e0b1509922004510301d09078000c46420810001060307100354100c1d05d81580608a21720f5000350b05041c4c1000240180501540611082d83c05805e04001e2030f091041c0c8000c0c81009460921a11040d040c0d10307519114030381440c1c81800700c0801011031010f0703941d003401c00c040c821800018240084a40050700000c03050003008400581e40036200d0ba040b101e00002942e0f20a00501b43c10031409493f8a00407084c4c0fa14484249102a11078654000c002d83c000040683d041e14001c8162130f80288003503c0681c41c0c10702 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 874512931 1250 874511681 874511707
    0x5280504050a021b0601030506040206031e040c09060b0f040306050702031c0506040c18170a0f0c060206010501050403050a080315090a0504030f05130b070f0b0702030d0b060a1d0402 80
    0x7089034075804156012580710400744002044c072410121240103001c2a5055807105034407694005c0c000380c0108030010100301c03a002907484000d1500c070964089222401d180c5010f55041d040d0b442500d25042c144040810f0030f017000011a1a0300030f490030624501032541c1e45107005044010410425030100748286105070807645000c100307070703403080030001407a2030071300c0c200f0048075079424290b0304014080411504c00f42400041345e0507140d0b01040031110a060b003110500c2c02800d564010518090004c0090420200c449010180c8039180c00b0356031248e0300c031001110b250240e488040d00583c44041c145c00420031580085400105800c103090182d180c0e840030074540181614050600d550b14001c20040c0756100500204041e0945081e900d4690209102c1000e00c0040c0100c180101c4000348000400c0f040750503a4045507880400510340f4a03001c3d0020b52a41c200141402613242010256065071502400b03c800605031034075a03103050b1020b2000701c1541c00429030740300d030403503801c000c0e4414a1314 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 874514181 1250 874512931 874512941
    0x5090a0e030d180c1820070212190f110303130902030a02040b03150a0501030b030c1c050105040c0906080c010c0618172505121309020a260105280504 66
    0x11800e03500b290000050314205c03044400c404010318040b0300e820b01042581950004603942c03250121100240d180d9801c26840c184441c1085103010071404c11111410000d00b1610f108c1c0042c0113038000c0c01d11020901c1815104d10810550303401c034103e440d4040c012004664040e641280348850018141600e07803c2d82061980245e0b52200d07807013240900c813543e5150080800c40540310230b02e000c1c80b504a4900100382e50300c40528017144130301c107a070303084003900402c0300132801c1c249030404002e2015040c10300300101146900d0240e5128207042c00c6010070301c2c604c00202c07003a4211040e9035454144070306413990b4005041c05d9601501007600b0505020104200c100c5480780846201119075030355800311000c00301010741465402241f1100140b2201085000ca150b070301c0054000000c035070b0703103000d200082903c0b0659009054107d2000c90901d1080b0f070b1101c0f4107034448030f0148040342801407800802403014000d104950380000b00086100c412855002c178090603c0c18480030912143c0ca0340d0004060325 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 874515431 1250 874514181 874514189
    0x81603153206100806120a0f0609030216030c152c240702010323010806191b0f090902120609100308030c07030c0203011505090a0e030d180c 62
    0x2444032425064102400c1200580001d001ca542950030f1202800c00340400900030099481031210008000c6007a80502400c1210782e88810189424005490010b0052064910540041c410b81c0c0b6403050402a6481800a030383c1c001c680044280d1405600c405075150550b01c00082100200c524800350001076000e0340390011514100d0325423860030041c007010001d076001c045825104582508420f03201d890485488580a180c0030502552000b8217189050803400e00007141d1201400024140340c0100b83d00b8001c40e48110380c1d13408103101140c400f0035a101d1a031040d08480c021101e4060182c05040d21451004190a052080f5584e41105c0d40480e0411005404001d549808201903881c001e859a5840100350301054551401d5813120348013400020500c0b0020380c0001180c5041c503010b1240544040e900038024070401683d611040181c80c131601c10a40200a1300c030104100c07031400c0c0910120089048010350030f001610303a142e0080c0408002c2c00810b200681044008aa12004164094 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 874516681 1250 874515431 874515491
    0x60a081f0608030307120c030207020105070b090c132903030313020a050a0b190212030403050d09020a060c03020d03020c15060d050115030510020301050f010302031b0a020a050708160315 82
    0x122048021b801510072140c90070041600c100f1681c4c0043c3e80020664a00c0c9800841030b403401d50714908281e180003460814035910400f81c0e003181d0b20f247c441c0d800a180c0484000c0003002d5500485241402400320100060360540050000400d141c1e502c4941078070003400100307050111607840c40030803400e2030950080108614005225098000d84030194140e0540c01c1c03004024004908210500c64000a4001410000005184094010380e81c03c10f042c4a0740061070000c0380d50303651402604116807583d00301c015016039410710010b80d00910a540118140354040c0004030402c032844007281000906542d0711541d00144040410400d100b00c0041490320b10503c2d100030708500f09903107440919242151503e0041005119030380300d9070035000420400703080140e12a101e040b461524a10414069040c141e0b02207801c41c180c550000c1c841c03106500131030649520f10b8980c080c144d111030005c40080400362002200b00700007501d01a2480103070f0100c030800195944114014030090400b10303148104 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 874517931 1250 874516681 874516697
    0x3020903060c0f121302041d150103050d0c02032b14130b03130b0405010f1103060604351f0506010e04020c030706020d060e060a081f0608030307 64
    0x299040401015402c0044002c400d4104100d60441d40d90700e224510662001a80d08408240c010144050110b0003a500070000e2141c0800340c1c4101d102d89502c0000322034580302d0070740900070040c61004002c2c140d81e00310300984882c0032030f603e0650b00301300c118208a80500c02c6541d0007010000c00b00c01800b02c07812040341d0450743d995212000f0850404d9182c4000d01803004c00c8044009501000c3c8070046a2682540c503460381d80e82032100126201d0220003030240b1301c26200708070800c103040d0302010400040c46000c00c5031001a40701005140001c0314044d401003070410007449545040030051100e41040f0800303001c4c000000000220b004803c40c1014065802a00003003c13040c2d190402c0908046804070030007032494841d00003410f910b43d54450702d00650b400940707081c00120900441d001e054000a055580d0916260351a004003903a110303000360514944045203803450b150314503008641d011002064410012905d0401016003452401c00300c9545010008200800381b016611485460300c030803907 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 874519181 1250 874517931 874517947
    0x315140a1a0f0d060608180a1e060c110f070e010308090a0b07080406020c0117040b040c17100e06040b07050309070f0b070c0f1503051017030a0f0e010903060b03010902100302 77
    0x102c5401c0147c40c4003055030121101c14801200002c1105109400c00d0407883e845511a1110042e495807190152102d42004810000680c02c070103500c102103403850440c0c410a020a603100e803604060b0003001c0d58824420010004205503001501c0300c0c10000744601071095031181800d03e5940079100c100c1c0e54000100e0100200c2e5014030004074140c90070700307000700384e401d10051040302c262005100030020401000800c00b4081040074500140c50310301c0c00c440f004c680700301700c8a0b41d6038004114003030130700e041903400c401100c004074186000381c1c0d100b4a113007915220b000054a0b1500001c1411107244601c2c140055207603000750003040100704080c0c10f15580c0c0e0b024200142c3e100c0c2c20350000206041d0402c0100040000e180c11420a2045894002100e0300c6904989a01460a0780b00c9079020b020701c10313045680c200100c0140703d1130720b454660007159007040c4002e407141d05004000c0ea002c80d4907030b103041011801503040190240030050000441111503400250080301848284c00043e5020032140 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 874520431 1250 874519181 874519187
    0xd09051c03050c0a0c060e012405030f151503010c0903060b190b0a0c02120705030601140d03030c030213030309090614060702040213150315140a1a0f0d0606 69
    0x14609503150602c85450841c01e010040d01c0781c00b072140104819804500c4c10700010f5401001c85001103402840745100e103841000d0031280451505440c84c0700e90340005003900d0001000703441088554040c00000052200e219500d02000707029034070303602e0b048001c01c105650a10075400d6605042d1a40c1d03900b2805c60030942c0480d041e4901407800f41c000c4010014151480040110465600504443d0361780c40490701101c018441400c029080a0840d160000d4800003042c90705c181c070002d6044941da81e998155148051590962141d0048142d5004101191103031300b02c14241b441606003d840c00d50398026407004003219910950010710074034002e1101c0034150103420001c181408103540800c4210000821034441c00d10002d2140d035002400c4080005401664001821071242d40c0c503080c0a00c150140140030415181255050860300101d0407403204101ca1980c050040d0500113040e041610201d041405050328030303038916040c0241010030305540000c000d2000f400c6d40202d130b9640743c40005 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 874521681 1250 874520431 874520473
    0x30a0806030c031005061908060103021503041a040f1505010f06052a010b030304060806010e01091410120e0109060f0c140711060a0203070c380d0905 66
    0x4144241c0010345070407040d0f41c0009034155591071a4030700007240d484680010300018070f40c2c00080c060410041c0d000811200106145040300c3c000c0c0c400c4030880210349074a00e41e901c0300706e41c01400100b110400000a9003580c82190b400f03807103404144030040030354681054074003808800ca0b101da03440d03800601c040703410740d0a000010491800c1c458200000705003441d9050507805485d43e0f00030541c0490954408c0250010b800080028003540d036038944492000704403103421147c1a002c90034000c1d50561035481010410704a84c884c540000085100b078040011541c040603080701080203500d1b021402c80007d03c11a407030440b03408000280904185000300c00c1c0c030004251004850714041c0d802070150f4001070390105d007039020000c26641e02c04602e02501070000b00304d94550008000720f59910000c2e0000000e01172140505410501140c0c0c1c2c20415001c0c50600006560455030b10250b407584940952b2000c920380c4099504c14245020040d4207011101c1c00081523401d40d0041f00c688031030502480c03403 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 874522931 1250 874521681 874521691
    0xb0702030309091630020d02040b030f01140d030c0b040f06050106050c01060e0709050111070f180e0a12030b03070e040506040b070c031d0d0b282f0c0f030a08 70
    0x5680c80107440410344c58100c6405c01e00c0888403500000c183c0720500c5282c0c1114058503181d401c40e5120700340302411008400007401404101134018050440901e0401003181029505580301311111070590f6403091008406082107c840002640c418001812409114064400303551410388078468140401e0030f44003140e01c940d5a44200000340003070107511402a009840080c20008502c0710901e0078280b61080c2c56000b9112100ba0080100701d000c00a1b25140899403003620134454112035601d820380711503264070700808103045030240b20441c1d4081d4110b1a16418001c0a0365461582d071861502403810841d4100c03440d40100007004204281940020341101d000c1c0f400c1c410400030380d034006c0e001c0d901d0240301052584ca5185409001e940f0b01d6030b080000c50b842402400142031420301e814a032017001040e82c00d44940c003a8441c1001025207e6401d00040701d5800088180710459015142c100b0f401c6560441c00c0100078103500180d0420010305010b401000955884064410003048050060300f = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 874524181 1250 874522931 874522967
    0xc0d0503090d050c060c0c030c1207030e01020d08072f0a05060f19150b1803010b040209150721021501050108090a03081513060503250b07020303090916 67
    0x3030303510901c2c400070303145c0d81c0074134400402596005031038101c034034500458000085520484a034018503d481d1005410b00034440e8441c0700681031070320016601c41d800080340d040014020400504010710498038405800f5003000601d60440c00603040c410142c2060b0441e82c441d074452180e5008001d020017500741d021040b40310503592420818900400314403001d80e521155912130703c502465060048924000346640d50b00c0b240d0312032400580407010807445614501c41d510708102592a81464000c507405003a00400d41c200010b40c00881800c160459502501c1e031f010340300201582100d40038000900003025070010450001c524642941482058111504001c41d040a0019100b40040c03244540d44e40b6081108032503854501d01c1300181d0540007000d40c841d403a4055240947d100c1da00c91000d41d00f084d030656205100803031280c80410903880d04c5404080c07041d80708125a400c0782d0050201141700500740e03460801c1c404006040d924094802c01c00d800c25860340d140c40103410028103151a41040 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 874525431 1250 874524181 874524187
    0xd150e090d0203030a0f062301020708010e1f0209090c04081b0f13090b07092d1e050d140d0212190e0901030302010605100203040e060d080c0d0503090d05 68
    0x500025101d000c0a000076101c503072507000d40c450407141600070788044c0128084104100c661038412300010280346904c0340c0580145100820380c41c0c011300038a01c0e14403c0d54002c14030044146003119104a001c02e01003940d0394240252003036a0388900c1041d00881d0b40403480e50701d03641801507460400e02c01d030f81c4000750140000b1240710384d0b44580800c9400b030a021900021241c41d0b421a9101034100f007000100307240e030b10b50204004180c002d0f2103202510750301082c41e601c1c1c0c01e590644c1f40c00e0341d581040426070f101020380700b003044048a09041c40d40c400e00c0d20291044035030340c0001c110844501042214148003010144076000010000d02101e140544010300e01da80002048014921030410414031030301c2c83c030b0740181090340103120042150201034411f01c40d5607502d0500038000e10160240511862020310004003d078400030907601550f00c044a07405094440703030200042d81000500413540070800344000300801c0360034014130701181810b4441582c2c1b45420040389007401c1c000544101800014 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 874526681 1250 874525431 874525453
    0xc130209090a0f0b10051b0105090a022206120b130b01091109130f11120a0209120f0604020a06110a021c050a060902011205011d040204020d150e09 65
    0x103040c01c640000d982d4000003122480d400055002d072542900a075001504180001c2d4001c0c0d002005010640c4444820100a00720000d850300303032802610460955401b04070050050701c0c001c20081d80d03c07400c5810b82031b40c4030200c28450055454603400114440d50038404507003030103002d400c495400000340c01c9040e2010801c1c0e6a2205a403418040c46c041d1654940e42c5016031401321003103c000c400003c0220044201050f110006040b580001020041c2031021003540c0076081c034141c4a1fa03a9070494800c40994500e2103440c002d4000e0715030554040380410321405900b000313020103a850000640909414500790051020701241a0710080c1046104210100992008035201c00c5040e41200c0c00c0e0030074211102d194201d020b1552015009002e00307080c1004000c0c460340640c070254401e80314a081030f16a94507501c00c583e400d2087c88883d4801e075211401404c0304502d060783c418801840103003000141c146000444408000303548141c100e003441440031110344410700e07038071103103185c02001d50280e9 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 874527931 1250 874526681 874526689
    0x6030d0801180e07050d081801090312050c150c0a0f052a0a06060f0806070f0e0108100e100f0504020915031008010f091407060f0e04020c030a020c130209 68
    0x105860489070303543c600740102c00b108244039190050500070119a494011400c24480d00d80c0040c50002c9945c0044070100e0041d4000c0300c00f40200d0f50003544c0526921112941940c07291b100e0380030040d96004508420083c0345a0520981c082c1c9605040c00c0e031200c0a6201c007074140c003100001c047c1488400e01404c10b200c1242d15883c01d6000c425048110f04880d00c0d0b40481c03601d00c040d031004101c1030805101094200050100e00c0481d0b070790303004a81e23140d103c030072081d036074004107101000000324400314103503155018a00c45604801861a00c05025503a4000ca02440501303803110395101040d0030003004803c0030740c1d035010701502c0c2c122011450401144002904c02d4164900308400070030100c001178803503c0490301e54004001c014002c1c015110512200002400e601c0c6c2d00300c4507099500900700701c1038000100300c0c0075104d00341c40310010180c151505513044081c6487d0154055020040c103800c0390424000390881000e02d80007452354078071034030412843c0316008840000c0d503031043c082c0046940e9 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 874529181 1250 874527931 874527959
    0x10b060f0c0304050604060c020a15050d0e03070b070e010e30030403080c0a150516030b042c12180d0606030203061f0b07200a0509090606030d0801 65
    0x444014416a91025841007509500403036012590008000c5800114941c2104401151510840301c0c0540707942c40d81d4030b5114030380c03e5958a80c0090b03000c0c0003c0310303803207119440030b000d154810b42101d04110007942c03103164904003103848100007088014075066650700521100320b0b0070b40c101c80008544804c500f54240100700c81e4402150303443c0983d040c88449609004031809150810600c658a42c805050141d454000740c4046440d8842003418034860102e40c80b40a000341817540d410040f106880300100c01400f0303540d203090f074003542d10300013600c00e2061420b80030007000002586141c4020110085810180341071034403800c8213410070210015040b0041510b900c07410480c0d040c00074a0150600744d000b004a60002501351082c8401d1040e01d81c240d10b1441c1850b401c20640f0b07029151201d018032003074080c0c0d4400900c41405c01d03900e50480380c205000005440310240080005541d913400050350441d080c1d850701c025801c018188100c502341404181c907001c809050110a0b5450402000c003c54 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 874530431 1250 874529181 874529197
    0x70504050d081809040606080601150e010804020f0a030605160c0f0303150902030702060f0601091208070206120123060304021804020111100b040b120c06031305060a020307020f010b06 81
    0x39800181083c003062032440881000b403000d0001c0075646058a01b400040a042c000c440300d6108100c00007481d01c0b0820101200300045a40b45d00b01910160300550703141c0ca01520881c0e0042c5404407400041c4c9814400c07100440c0a41d0000c55a81040301c1802800721020700c8004c2000f406600310808500d641105005003603251900080ca00e84030610580094103c2d00701c51013440c000030034032071090b9000076610300440b505100030415840307800064034416132034481d003e0131681c0c0d4004a00442c60382c1c0040c09045001401075413a00020705900c0c156244243c0051003a017042c90080d000b140103540c100848000146d44c680e180d82000d80004491800f50ba8660000d42d007038400007011640325900920700d0216031070403180c02d04c654900318000b03810549a024019464649440c0c0d03140340400300b52020503d81c20203020b00c00141000c0c002250320040102286240b001e25060003d50100503051240903000001600d13400d041e84000d00780b500485036510706a05025040d80c060f0340c5c000448001d2 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 874531681 1250 874530431 874530443
    0x11d060405150c060408030103120c0c1802070f1a0a0b0d08070812010306060614040308031501170a0f06080c010e01030b0f041509050106020f070b0d0605061c05070504050d 76
    0x21040c5407801ca01180704043c001c240d540030340000c0c04200309001c0040c0d4184c03803282e51260140016154129010b20400d240a00111428003040000c40d2404005140d040c2d81d240c0050302d464100d0320749600c008840c0350111210303a00802000611418641a660003923a400c000307101100c040c0c0000b0300e10000030f88000d00205d500103515010000e030f41742290aa011021090070244d80d42e07080500c018101031003184082854000301000c10340481d0101e40aa0340d1183e022811515010a00f0081300d04000c12141441022500007440248803107201c1e2080094501c081040010403100c001074640c0f59104410700d80c0801032560382e9a8001102003200035080c40c0006486840d03000082c84040740420385504136190058800d08000700f801c005040d28208442440300e0790b0380312003ca0391840400704074852904052010b0003c0c07461034006020700032081d800403c1c0c640d00e80c40040c61a5202c811040c443c410307003444d030052108850140d5540204181040c0c2d040c1440d00010540041480400810b8 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 874532931 1250 874531681 874531699
    0x2107060e1908032e0e0901020f121005060714100c02101e02131d040203060c0a17010e0a110a0e19170d031401050d0210030e030c010b011d060405 64
    0x4260a00140101860b8070880702500c0906242d0040e41d440318240101c5d100901c1000c0015200041402126405044018850700d4006030f14041e5204540c0584003072000c09101c2030000d400d5456501030020300b0701680b011860788c0c0721850080e150001e488901240c440c2000c001c00d030b9494011500d140c070141d250002140010810091005600220b501140b0031807001c00e440c07109030900e000f44401d580d00a07140590721003440c059406803840844000350301d40c2c800000a90361051500203854542518200b408040014580c4040b040f03c00741c100300300c08440d00c0104030300f90115008009002080d9211036141c029084801402c0300c00409499000b0b01f01c9000440c81d40c0401085407004107590600c9600605100150070785589048000302c00007414000c80b002042e1b0004181d5040743e81c0100b840313032954516800e0094803007000c5500c8081c1660381038076080180c010b0004140380d84011000103149007803100090300c41000d0403108007880d078850003051269260202240d060b21412542040 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 874534181 1250 874532931 874532941
    0x110f1306091d06041b0c020102060615040317192a0302071e0e0a09200f090c13060e10020313061b0807030e09060d0b040b07022107060e190803 63
    0xd0200c0c0400400c030120b5000526103030681c00322002515031f20036800d88542d80c544508206207100108801d850a1404100800c001002503a8a44900100710140ca0405054584091404142894420224403104c00780e103510342d030a240c0741075a1009402c010411703040c1030b1002541c5111902500480c50448c41070217658880d90444a0300800c0d101081e03c80314581107082002800b03004004031209110146207410b0904c03040c685540c8500041d20000070003005201700001200d01404100002000b080021030546007150148040d01154030742c46848e820000601c101030b10380c4403a0f0003c41d00140000e4075100100d406050450b003591403c017241650000c803020041c0f5940000906015000612504054005c448246080411121510559244414481c001c00440750060468400900003000210403000c1c0c1d641010381441110101b000d07104c4050007800740e00c004e00d030240b0781c0410b80508005060044101d54480580603056039550206800b103800f05400b4024811400480010 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 874535431 1250 874534181 874534189
    0x180b070903060608010b090919020f0d200f0a051f090e070801050406090c02030d0914120d05011202060301090f0f0c05071a0c09040b04110f1306091d06 67
    0x300180d40c100074104021552650075034020444072804500880100300000c0d101b00780402c10b24070001419044100005003642005640b8698118040d40314044500010100c0d0800d07240d01603408910f02e01d0424050964100706207034566820f16403007050045001d00142c1c54145c1101c24541c241802c109027145803220540342210181c03c100e118010034010840c0d040e512801da18101e0302d0580781089040d03122400d0038141c038400d00c40f01015a00401083c1000e1204c4e51054000b107010300c0ca2981c0b0044c0c181d00450400c0f808203542c845d82c01d808201c00842039001d10802d40104020520707000030f00c005038042880c9000501c103041445a40e40a0101c1441440d04074900901c07514034100101002c104001d0406d80080006590460140b0040e0700003410044026008290104085081c41e81580400020301460740078581c00c19124090301d4070308550390001d040f00c002c1c901d80694451105840c0641000c089502c42010880700c0c40c410400c0100343c0c42c03503401da04541003411010b40e81e040041 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 874536681 1250 874535431 874535447
    0x305061e130237080c1218070f06030e0616050304050c04090803180c01122406030b12011404021023040906090506031005090703061419180b07 63
    0x1d441d41000450307070000d11460854550030b040e21104098182580d403c102141c0f541030440701138007481d00403c4003000303a540b000041540165040c10400c10225480201404d07c490f643c0420030390f00d2158014090990140158112000326400505039494407049000c4a0413100c5000c0003409000400b107018000300340201040d00c0800b40c028003100c402498202410b44c400ca0b02c500446d420805000e10300000410040c9030368505a6400051244080c1c0c044020f0082070003526030030203403845505008500f080c1080082403d510000ba0f0f0340c02c07400078004030309260911f17402980d141404002c2900c03146480359030400d8059940710360030450030806440141270407401d0104c0d60700303030502c0c0b4119a105100030029111b25030400e01405980782d400c402600c0e0240d84055254001c035040200c101c040d548180e40c45642c1208486c0f5541c1c1e01e403551005c580281c0da0038064110060300300700212100c0d0400ba455240c4140d403c0200c40032000408008d07029035040108486c5c00c3e00040b41140344a5440 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 874537931 1250 874536681 874536697
    0x140a0b04021c0b150f1b0f0a030503060310050901022d160206120a0f0e1f0908090a092412060902040b1005071103060601020a03110a0c080a02010305061e1302 70
    0x704d2545c0d50100c40448003944c0020800c0300c01c0b049a201c66030b03055040892a5031030a5010b100034001d5400640c0c080e90f1f6508001c03c0302c0e4051084007081203500515004a600030400840016075550001414203402041800c01c1d11960070384000e4035607400003101c102e031071000080b103072000b07015860320004405e4801d6800103150f42810105022608405511030318280807005010410b510030800300326110740015080e07918211150b41d42c41c071a42400c1e00b21350001442010102d01d010708100c00154140f02e2038101d40b015550710700b001d8946d036412110b81c1240d40500c0603425101c51404007010045d030308070780004000c40d407240481d004540700e036002881c0c00c4400a082160f410507400b00142140c104440c159511601c0600380a82d504010813200d0040b10181e0286c8080704080c5c41c2070b10024200d6244404510580350307081c0104d82402c0c04030300a02029000f5041007403440c000141916006445140704a1241c56040c1300b040701440d15003038403501691a880d1445001c10300200070702403410 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 874539181 1250 874537931 874537969
    0x402040905010e0f1602070b090f030d0203030f090c060304112b151103070c0f050a230c03030a0e0f04020708040509011a0405010c05030d140a0b04021c0b 68
    0x100d0503c2e202d071285446411303404c504a0540e82d03407503004850310101c03040301c90168101003814880c04030b0702001007403042c0d40500034001000c03481c00402e14281c912903010006070804014420a20313220784680d5002103075000101040c0580c040020300a11010300000c2115007072180c400a01e40307503221030008002440016203240010f0280c46804404210310885031255070014000c00341d41948100b1200c1300c401c071851429952145019201000142e00c203950b4001c1e24480d04002480411180c44420700c507059500480700c0000041d88030b90314911388280990404c00300c01340e583d02c0000c01d5a0700f0710400d00c1c0c4000c424001c11b001c26030122054600700c2c0c10a0001400e0700c103100f5185d00410840e00280c40707a040303680e40c501c17072000b2a09180c03035103484481c410001040750390310441a00761172a004a040d01d2030012510303a40c00403220400c82c9007502c903106404000d50403404c2d21510640003801e40341585886a80c0c0b4035101500d106c13010b4007000659880840d2003a03244c212500030034400240c = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 874540431 1250 874539181 874539191
    0x30714032d0c03010213090b03070f030f030323060103150905010801061706130b25230a02100c0908030c0616091d0405241603140106050904020409 65
    0x6250074201d540d5903400708181c4214989031125040501c22110b036110200d0f0054035090503c1c124101030842440074540c14403c0f8040800c920400f408610700070751180080449403012450080c00b610002c84180c60744c20009a90041c0c0e00c114034581c0c607800340f02407070300060304d07100d0001289140078503404c40365804d4a401d00208201005510040503141c00385242d54040700c826903400e5075640110b59156104d2400e031800e01c001201710180d540c000012194604030030102c00d041210000200400c000091a0008601203c00e104a0070700e183c2c103400d00105140000036103001e566240d08100c01d00300e441c2e4030706100e17201900c190030380b0003d0800d01c000e499803005423040040e40c814082da511544d8400c941c01501000340280c00311400c44807030300701c1c0a026030400c02c400d10402c60020000d1700c140c0114880000d208800490701780c0c584207401c00c182d145091442040815034801d220f007a052515040c41229100c1c580001d003170441c1d05901e0a940d0300d28807940854003a000710303403114800900701 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 874541681 1250 874540431 874540483
    0x130905040b060607390b3121080f03061311090d0c030f05030703082a180901080d030b120606120313090501050102190804140109080a05031b03070203071403 69
    0x6c080142100500301495030401c0142c002c524615880d14409003a1580c4109030400034852824080b140102819100340c84100762521031510715030180c4005002d00000008110003490000056281c0440800c020840070a59043c03107180c91080c51555449a0203440205c0c003006504400c0c9000b56034028441040e00d15980307000c4ea034903086044110081400200000d000e489906601e9001c0880c048041c100c0072020a008a480c0c0d0110100b407d1242822030004900e0312030940080c000d141203c014404031401e410000c08403901480414800c1041c4220082d02000c0003400e6900036201325000d2100040a0b141240f441c490003800c0302914012140018030000c1c00d0348814101c40b400c0c1c080e62082a0740c4503151200e400750341d0000f08102000d01c03082c0b2101e002d07802d803003ca8003010f06041c1c004a44641030907185c581c2c40b9104440d44d9100083c42e146a401c450940320881840b08025424a0801d134002501c88243d03001d00080c82d13031108801b0ba40c503a002c211281440400d00450510302d050 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 874542931 1250 874541681 874541699
    0xc050f0316052506050a0216031b140a0b031801090503070201080106080709090b0a05060408010207120c080a0804082701080601170c0f130905040b06060739 69
    0x1240006440c43e0180040008070214042011004122810103100716a0b0074054191a80d422001c2544210302c40d941246161038901c081220246002c0c03099030141c448100e400d424000130607040800b506d0351a10845140d5202d0890310415030366195403180c0c69071788600c43e08002d5081641d40b000e981d0700b010b07100000c0c45404002440664000c1e0f98490b20703681c0729001524040b0044c0d40c03401c0000c128150070031040b00070b68400001403000030410400d00303031b4540024280b9005a00140c0d016540024404108603844240e5410f058103420b001d0807002481e210074005001d180c48035010301010034000b03004c202005084500302640d07080c03096041603009400003034102414103100d01107407541001c964258055091503c6014420780780c444903941c9e1915510094100010352200c008090284480114101c54250f02030020004005150f1805080c420014803000c3c00c40c90180408000302e0010a5440c02e42d00f41d032284038240b0034094006030b802d0f00c1e500900820503078400502154040343e0140 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 874544181 1250 874542931 874542967
    0x60b040b100c2112050901150b0418051009021606091b1e05040b1201050414061b030c0319060b180a0509070f02151501020d0305070504060c050f03 65
    0x201980f1040c0500b0000800070301e10700e128900c0e80b00490118644118801103e40125910045100006c204030252020101c0300e0b1015801131080464045000d202180c038078100c00f05c4401d5828000e0116040480345500411420300803002e16603000103005000c1003800f50a1420f20f1790089080110400c176040403140f072107107070030b0301d8924440103e0700042515484840b40c200c1d040303440110059914000811000780994141590491000340001289000c203121705032189019171750003600052856251401c0c2803004040701d00c221a040c1441040110510a8076480014441160b80e0ba45800d1300031103918005180b8500c4590510b01c000c44e040382d041c0003500b591030450441c1000e010f00ca0003000418501800740c15003003811000001d0000d8800c00e1042311021541c010b523030400e200103007885218902141c0c00c00d4100d081c2001c01500d56410811084881482c2c07408102c0c42c02c4c0213a004102e032180e0710a2004202d01b500303d000c103002c0c0900c0600503c019101c1141d82d50ba41c0140e05c101e08203 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 874545431 1250 874544181 874544183
    0x1603060c0e010309171809090109120903080301091a041a0102011503080a080606072015131502011401030b0109051609260a0c08011116060b040b100c 66
    0x39000400002055009000369883e840d8070090100f17200c501c464481100350040440100c0d00010b4800500e459120100c0d014020800840003144084142c20701c0441000c9030604d80040282904081012803030075400d036410f403142d0440220b42c111300380c11100c03847e040869406500a1809c80c2d92140030003030b83d041c480f0312282a0000d2200010844110b40d0380c40240c40b002e448130004000c11000395115000d450f91010b402440c15040000d19110a15140c81d4030788482e400d20004400080d207440c0080b4003201204500070716078a04000c2e010200107004d41ea210f0101c01c000c0b6409000c1c6e106000b908444105000108404155a56401c0c001c003200070038410640740ca0b180c0b60200c0d4603d91141d4400d0300c40b10030341c1c85240455140801200307180c5050440300c0c0342e151203001c0030341500105000d041420b40c05044008119403c00c64524212030310544101302c43c0e4800c004264000da007110009200e150045e2000070003030240000b0074040c0aa2650143e80480181c2c52941c0240d0442089aa40c0f = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 874546681 1250 874545431 874545437
    0xf01090c090b0a030609020d1a060a1202030c010e13020f03192a0c14010207030206060906010c1502070b0c0a090503010203060105030c13030606060e040f050c1b1603060c 75
    0x55507030301c44003011105038441c500c1e00080c4500b02413000c1602a0800e6844520103444850b400c030360350300c41100740008541c0c0e000610207080140001031928080042c043d08940c1c0600c108840ad95002907650b0700000269414403c0440061085948601d00c0d80f0441c02d514600f9540e814800c03a0350b086991040f940c1d00014181600049030440c403a204941c01f800a000600c0d9000800c0c080710005810b01501c59010000c4d1401744600050041403907805840d458000943c4440c03580c80c001c2d0030a240280528018440002081403c2e82d000410600042e008020b080d070b11070904840038007912402d079016002042f4441884400704c0d40c3e10080850140d00d030b13207800310941ca450400d8240d02c07094a160780054420303c081030503100c80700d000788940c5100c11485207100d581c9541d528103070303545544600c010414a000c4019982844d001705102c0c05100c40c001c018518006242e00003d003d0f410000342d038180080c0c500c9144141c1004514128101000010009030b544d00d46240941005184d080c00 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 874547931 1250 874546681 874546703
    0xc03020c010615021e1c0e2814040e0a050f150c1b010f06060906030b0415120212060c030105042403060b031203010b04080c03030c0c01031d0f0109 65
    0x70700c1e00c1200760700c218441d241e010b4601d00d003030702c3c41c1400b00413200340b17148805010b00505484400310003001000088680d03110520f007448181c041020761040e0101003141411440d01d2030507554142c12403803085d02d003c1c0c843ca2220480800100700101181d4041c05902c1c4a1007510105104001070030412800d0803004a642c404d801024149500c4021399a2410311342003404990404107500c0040002d403030a500000564540101030f10050700c1c40c560100b8041780b0350000034094642c0c540205881440d003070310244030401201c0640b44d0032100d603101d001800f02401022004541c2d51840c100310200d100300c104c50351400c202c080c14140d44d01c01c0c0718803440b661038000150440701010704a00c0d010459440c640000a1968645a0181685040f034a506015900c0446d440c2e02c400d42c013940c0644a00300c80c01d42c64600303285606150004038000c1038030a41c41030006030b11040c40060300c5a00e446c02880c002ca03e40c4401c1455111032051000791040600a10701c200b441d40714150710481c80e0b80e000d8441c88030 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 874549181 1250 874547931 874547939
    0x70b1317120402040c050c013801050f16080307030203160c1115042105071e03080c010204090f0e1e07061d0d030906090503161509090c03020c0106 65
    0x48584500c50700181c400104074009005403070150b010000018140c00c1051034618a01d0146007100c0e1a110405c2d9503001108409030f1402c0800c00c080350781024080c941400c0128800003800364007640340e4600d001d09c4005896030b10b0550243d0940e00d0981d02c0102203441b030811810181c043c0d042200d40340c4894000c080007044480c0300790340f5981181d800c0007450411035021814800b401d42040903100c2205402c0000160310010b11011248010300e00004042010721454a09e0030003a003030b805185030a0115003a000500074218100703003242d50082d909035039100301e01121030281c0a0356200f10034236464401420b03d0a46680c0100c0c203444108000c0d40c0124242c4c1c41d03800319892254200181e0b0ba0310100341800a0381c0594407103056074442c0b00011819605150000d551510b40e0b900c1200040c003080c82c104a590b8000070b4000c00b03004203e0182103a0408450020510710141c803440400c41ca030b484031701840500440800001c1d00d0100c0e8240151640d203040078001c2e40c02021216180d62800d00005 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 874550431 1250 874549181 874549223
    0x30c090c0302040b0a08091204260106211406011d060d03080c0702060405030105040c06080c1206010507140105010303051b07030209040b1e01080106091a0307090c0302070b13 77
    0x5821390354108045810045480d204940900c0700030980b400510420695480b10200280a44010308d0b80406450701c21494201400a42c3d241c2402062180c0c1010303014014001c840f480d001406004144440556440c3d041c03241c2d2000210f42d045070135018040001c540702034460b00c00e9080c921305070601c6400391201c20500040008000010b40003840d00c0000c0740114100c00000c044040c0028140c9042c07644990000742103070800e980c2202c03101440c2104100250700f0020a60380a000b0700407490030408100914160010020241030400000041c20403c002000110607a4500001c4c001c000c03541e105d140c0584070b0740c80044a03803a45090f800100c2c030000d41c0003d40e98103880d8003405030006c42c0c036a03548020325154042d1440345c00981e9600746400082d08030540500900c4480004508680340019000440d118441c1650203a01c004150700c0958400080b401c080700d910b600005104105454101d0013030042038401820000341e982401f9600e01c4956003401914002e100c03074101100ca0002c00 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 874551681 1250 874550431 874550437
    0x7030f0506060a23211212091b060307051c050919020139060c1e080f0907050a0b1308062403190803090c240d090804030c090c0302 58
    0x264085038070000c410b0801d801c110381c1d4a1a0710109025444005458200c0b4504200700da41064814800221f418008018007a01807034000c0d21420161642c0350380403000a1069040d0b08005004800c00070205030410b1003003040b01c1e04c4201c0e160b840b00c040500e0101c002c0140c04142e03078000240c400c00791210006d039100010700c142c41da07050712081140c0c5104038507442c0391044443c035541416015040e40d0141c2e100300320043d41c414841c10000070040c00c603400c0036001040020500300001d607801c00e0082c110703400041164110030340c41142030050740c0e1810114076140c6103401442c0c100007940c4001803082001005041035540d56a200c05040b601c1e11001350f52240e003226030030498480d400d00c2e0807450b40c9144100301020f074007800351544a24420031000c5811285502200e02c0d90001042080c118801d020262814800312000c80c0c1c1da40071030200303c590807421580c2800c00200001c60a064194944c0603058a590083c621900c66a41e400d10442103d40761050604841c20400b601501c2071180c821 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 874552931 1250 874551681 874551719
    0x1f020c13050108030a0c080910080106091505031f08011e05090609070513140f091b130c091a0406110313090209010203090901150f03110a03090507030f0506060a 71
    0xc1d400c1a1400404032507044c1300210507101f40380b0807c00420036454600c010040b140803034683c00c2141d490050010702c1c280c9154007481110402c601e4412100b0383c41011250800c110b400c00c80ca0358003111480c141c50789010b90100b03c00d50710300a02043c41546020b085042844081401c2000e03179546080e140e1a020100e546400f560072000d028000f80c5400a14903085203040c502c0041c01d0340c41031003100140d00050340c03134102288419041110812003000411141001c1912140410f10b001c004107070b420300c0b18102c08081948072415208210311885041d0001c1c0941c2e101c40303008140701002d05040341c0c0a4001c01e000940465074500c40142d00000f00c031030210b8840c1c0070441551805003038134029002072031040e046000070016011a9641d0300d01c014007078a10b132010b5204030021100050410700c821f0711141c2c00d050600100100e4010000300380c4202401608000c10250800e241c0b450800344103820040121003403840302c5003400310002d407041c4241c0301524034201c030300d4540e40480341e12204151 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 874554181 1250 874552931 874552933
    0x90d1101120b0913240504020f100c06020c030c011b0f1b020919020310050f01030c0512040201030e030304080a0f110a12030e121305010305090304141f020c13050108 73
    0x200350400600e010410130907005d03d41113140c4580080e481340410380c200354141d80807621001400254501034005400a4608446102500d40103d5000d0207000d6040c101816690b400300da03900c480301c0240101c1c1d400c001048000c00c10000c19901c43c0c0002041d814007480050190100c044040d4012410074540907101160700c0958170b00c9a0801c00201401400c4010f01581c40d28903a0f50b0758000d001030350160341c01c0001900443d050a040c000d402e00520480380c101400c10f54111355031a0810202c503461200d901ca08927003a070740c500040e03010703020046215846100c00010082480300c00c80c042d2801c02055030714041e000000d001c01f141c4240c0313403181082e07840d04201e140d540050080182d400c0982ea00d0700703020810444402c119030600002140c61510342400241404410152149410262609080400490404103850740d40c9000390300481801c80c0703521031480c2c038640d501c2d00070386076683c012003030150401c140550007910790a0403070354680200508444074101d8205800b035641680d0442d0 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 874555431 1250 874554181 874554199
    0x31b14090f060301090f03231914070b01170105011514071b0602010e010e0a1e08090405010308090117150120070602010b010f09060804080906090d1101120b 69
    0x800101441c0c405080258159030b5120306000103800c524140310a907020780c1704c1050000d001c1d03010107440c02041c5a10441e02c401040089411600304200380343c0514149800000c8139103083d151880c1c0d02c603040d4042e00c12500c0c9400004c0090401d00555070310003170300c1c0090182e030b40e842c2c040e480202c00c409401d4002c510642400440100d020740541003c6000d5403c2d40700002400065160b00ca201d60003410060b51546005030a50750240100708000c020b40009001c510384545130015040409502d801c111802d401c042c01c1400507042c00d0741d442d150010320400c0705594a2030114095880b441d400780c00b0840c000d803145d05002e80035050902c03070111882038550711101000116030128007c1c44420300441900e201114004042251101030040d60b000001c0b005c2d824000174000c582010452801c010080c1c00620401c0d40c0f240701c03d80c03c664010581a15040c0b804005081801030001302e940001c6156490428003103da03601c3c00c0002020380b18002000f188000c0d840554000e80da11641010040b = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 874556681 1250 874555431 874555441
    0xb0c03040c120b150402070b04060e15010b0a03020c1614102606150f130b03090a060c05070219060f0302040b0315010c1506050f0603010e27010204031b1409 69
    0xc0b1818904c003c0104010314002d92a55400c0003204291801e9030626900c602002d68803504001c0b0032001d0309000d41c110650340c501661203000344201a410410140c01245014400b403041003880c1d0318100c0c110300f1076038040d00c90b030721030b84000c4400b03125521440e42028114440303401000354044800d4490001409022500d2135640c400001501c440c0d040364620302c0c0304000c1c02c0380704060014aa2050780c0199a2401c16008064589041d001040948410414454100c07030010710b0540c1d0039882280030070b2100040300300355254000c4000194100400a8075600341d440c080310f034401a1469504c0d10511401000411800c9019500030700000203c10404900700c200564002e00b000041450920644d4009540e0071241541800d800c0c43c55a860744010304c03003450030403003240c000c075030503107120b41998900805c4405205000c0c10064019603441e1440524644000040303c014500c00000d55442d81d0703a14101c210620986034104003e521648003140c0686881c104825040d8028040c60310360b124 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 874557931 1250 874556681 874556701
    0x20301060e010c050f0d0302430c0e18100c090315020721171003060c11070605040521030304150e10050105100f0f05070606030b0c03040c120b 63
    0x142003c01d13a25485142a41411001e08024042010340790307580140c1c5580c0424074030b81c020030019040c03a08100c0104000c000096210610840c4600c102070007400101c281c0c100f20982c89401d80150021401880170030001c10360030520460b481c512901100e296042103240041211015510000042c003400000c002180e0329181620360762201c00c01c01440c0800540d07030307040e2078030000c0110403081600400340301c0c110fa00040d01d82e401880c0044004d140d46814090402030001700e01008090565071400c11203001d03c102c1404680740b03448011a0219522480060540c3d0072038480c0a20442c0044c00407840d000340390032182d01000308000114256121aa02c550041d00c5014a56400c035648003a20300000000f0019024404900f102c0000c440d41010144802c22000d50450024013202c100e1b100c1c2015445004414000c3e01e41c64815190246890440c0c050402948041c044c2513420040c0700c000d08800004500562040c580d5000c0310380c1d140c454030051891010301a082c402500c00150030921 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 874559181 1250 874557931 874557947
    0x5360412110f01060f0602062d0702191b14060d0c1101060b030703050106051608030615120f010f1d04031403090a0b010801060e0a0225051f020301060e01 68
    0x1c4290741c810305848125508454095000c4d50404200d0301003001903503010301800d07800c100c03240070403021000e90f5502000840c50007a10014005202c1e00040c0c5141e10900c03c0c075201c420902041a2041118145401c0800c4c00000360f85180c814400c00090780c40303001003900080003000c1c04039414454a000a00010000440c9a4082c40000444828120028450340c0068100c0c43c4034582c4905100354010200e030382c140c00400a0140800203a040900f501c2916030000707500040c030030358035030344da4020408980e4040203843e044c280c0480c0781c2505081c0c03140322600c01da14000304070700e0581ea40c00809403030003803a10070755282040492541482e00d0000c24400d511900a0900803c400d445002c0980c40354000c4411028541109072800d0400c180402c08500500394000248a02d504040c40440e0ba0080074041080550b4001109035100380403441d03001c10010105040340b001409424a10780741c070465103001d9080d650b0b01758240c2d0145058829a810ba9505a07501d44525060000550b1526 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 874560431 1250 874559181 874559207
    0x4141207030b0403020a05120a0215060f0d0b0405010c0203031e0709030c1502011127041d03040e06041b0507020406030507120c2c0a020405360412 65
    0x80566140400842c10300020180280e02c29402801000582e00f041414109503104d41480100108100900c00e40d0004070402c0681c41000c5040c11902c0c0d20000800e20798124400c40d800c0606d54900000780210181601c2c400c50043c40240901064010100d031244403c40d048590509807884414030320454006003684568030342405280c0030b40303e4854450301d01190b0f02c0100080d08083c500300d415a070a01510050350410640507041c03101131408070480400340c880c3c1f15003402c2028020003555481350048501c52400c280e04620001c010003519441c2d52190103030244140030a000305259081c42d2080c034550001c46071031125405d010460481d2550f002400503607000780c6030007020011400a000b49001049040000d4003601484c3c135000000d002150f00c00005100303400d8241120049201400001100c1e514540c07101d41d54104c4608000d01658222642040c1180c030f03002984240508800341d9103c40c2e02c7d1130141c05100ca000709201c42d4084400070004a8504101201c1c0390140e01c0d824058 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 874561681 1250 874560431 874560433
    0x50c040204210f020303070804060f1707030c020c0d0503270a0513140106020106060e01020304141c1a181929130b100b090d02010302090301090b06030f0102041412 72
    0xf882060300000d2940c0c101c2d5105640d1088006810000c441e0007000c00700481c03070142000100310500d2610040e8062006100a00f071689651342c0030021351003484160300b411390007030445003a00302c2401c10316075a8000814504100c0c003201c3c1082c0d068494541401907d4000614041070f80d804e200c180a2000c90b1017400d01112600c035002c12901503c0000e51501074419075000140030b40c68090000e0001041d8542103042d90420802446407101d5410f045140c600181c40f01110141044810380060010768005459020102a1012602d510000c0c40e405605880c86c60201c0e20300e000700e02c0e034503030300f0455031000699030200b81000024601c0c0000d87e110030b0034a000c007201c485814001484000f084407416812030202800008020907060525040a03854420303140d810708142d0224591b10603640c9051240000d1013418046a00c03d40480703008180240c000c1c49000d015190045d0400c80030765140d4403074003078211120212007051090744e007102c00d518506200080700da4140250000c0304c00d420205 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 874562931 1250 874561681 874561703
    0xa0921110105030903250f0501050702061e06040b1206150f04140a0902190602060406140405060408031b190f020c01090611070e070512060906011202280309050c04020421 75
    0x101f00340d0281c0680b07940c080c20001c80d4514000d00028100070005204104600c101c120700c0c00d1303040f003e0000c183d202c0c1e400c1d580010a0701c160800148a100c2c21075282110744201000c02c0009a1521004402064240c1d44403c0c494407040030081075030300c3da25900d01d69641c440c00041e06140a82c00222065001400da00340550040305460540c1c40c160b00514050fa04c0342c0103001c100402d070f1123030070308682d1440351040d41d9090a5950f107441b140050030140c54400044007058411403c0d10101c1062801d8000441d50307000c0041d1201480d890442001d004203964070345003c052070010800b104c032008140d4609010a0905034103940708044002d040c22140b150200100b071010524140720f004d40f4580d00d5071b54440602e0340c0207071003940d0010034160144a03e441030041e903903040740c0110300e07560600c8000b58036010641150286295143c0380304000d112003a0400080d50f40650001d2240760090b015103024008002c02c1c00280c1c4180d01c0781410304110002c2002001500c5070010000301c1c411481101 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 874564181 1250 874562931 874562933
    0x5070e1b0d020d0b041d241929030c180a0f09021302130f060e0108130f0b09011109061905040f0b040e07020604050c060a092111010503090325 63
    0x406c545c101c45541c0c10041403080c5810b0b85802c200080000301d071800012684211803046000c08003107015021000c2d410f003c44004a03842400d030044c08221800914100c0696039442c001d00845080900160086c000c0c48200502c1d410400c0e0940c081c20340852160029889604004000b0002000044085941c503024100141d9803482105060744a601c005a00d074901210140e290f10307040e510200c040e60401d0020010560000290300c8114001d0802c01c415583d015248a88041000001414800c4d1413610341d003041158041c41d4090300d640802000010f02c01e10f14a0170074415000c1e05944040d003071242c0d541c06803c81108141c140f802d4540241001e6030360305a14000303046034101d0b0900c0030300400d0070320608150f80c8038194800003d100410b807900b4983c6075103485a94041da002d0107410002250768081e4022515840140400c910100300501040c048502d1101130b04011984101e2142814020b0b62084059030b0003402c40c000950300d41741e41c1c2d50300e030780c210945200d0440c605032081c40420 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 874565431 1250 874564181 874564189
    0x131e020307030b06011b0b01030201140f1c180b16180b0301140405070c03030b0a0b0c10050a0c1e030612030e030c1512060301060b0705070e1b0d020d0b 67
    0x2070080d0320401003000503081090000d49240700d80034600007595480081e080c0400ca040501c4c40c116602801c140b05500300c81c1518034641d00c211412421100d00c00144011882c401a9031115151002d00040228880c140d46100c00c049940c07801500c080314100c00f154004414200c3e21030118010b080044503c20416546014108581c1c803078000e03000c1c0400104082c03a094281107406140480c0c0401a5103072003032024099001c0300c180a4205075a600301e04a41d921044608000b4101d083d48064940041c00d42060382ca0040c40001418a0308020209000b01c04e41d01030380791a0610740d01d80c090400d10b0341c4001030100000210391810544c0b60400064a00001720903413550034007940e0340c0c0c09041c9281082c18a01143c1403100ba0051620f100202c2100c2c0340a41070340c1c00200c5065481c1425250b000c0040d024045507000b1540c1c0b500001500b1042000c0001c00030201c410220741c1c4000b668407512462041c020340110425000d50803c90581d00f108240c1c010521410406000104003020b1400700d = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 874566681 1250 874565431 874565443
    0x601060206100506211008010e010b12031306211509200f070204020c0d03090210020102031308071e0305030114090903090d0c09051504050708131e0203 67
    0x240158111400707102d00380040380484005090150380c4507142403032142c0321000650000c0103290380055040003092210000070900030060444900034000740d400484594000c2c07651180140c810081c03a41c0c4000361300804003c0d01e0b080d103034164003805454a0144240c1e98500141095200f070181c9541010442e1441e1240c0c90011080801032441c01d801d105171201100c4128061407814000301243c40242c094410840310745e100340040c0c4c9a01d4610902c00309010740070341000c50096003d03141070130348540d5143c1c2c8030724813180c001c941c00e01001040042c00c0c0d082b4030013030b0758585046d06403802031004166078600034196640328000d521b2000c0070b809041701c40c0e410030600c100c000481c008010010080a25003c003804941210007500d60305042448a03980c1c41540507032401480840004420f0255409411006081c480700500c01c0345006001e068042c40804440c611a81c40d0502044d5814802c4800c60b1040184400c0d002c2c602c0f8880d1542c00380002030703010410f040385c3c0c0c0c42c81110068905010f0 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 874567931 1250 874566681 874566689
    0x504090903020a11040b0a031b090509010506031501060503070810080303070807030c2a06023f040308132112110316052d030403030b120c060d0b030601 67
    0x140035250f03907a01c0c0005444424405151089043c9045000d296403600b00e244201e0342c1c081d442d00c03004141e1500c001c0a000c0130f5400701d10220702e8001040402c5d0410b421840c841c40e0104d040c0d40b84240d484003c02520301c030a000b084005030b810310008245501071600d80d134001c10194092141555203041d00c625603032044808000080034507080c080e0140d054003c0c4201c2008a052078440010046010038101c000c403d001610f03d0302c10b100c1d0300d080c42010350480340b2041003400c0300c0c5111072000240080128282064004200e070b140035000e02081030700484ca000e913074182e49040050b11510751142c00560005819a030b11540b4800c1c1d1440e44900b101d84460080a584503c4682100c1c8020401101d10b034141400300003008100b041a5100f100c01c02e07803c40e450609100780c840199160651603074100042c909510130019003001c503804c01c044080e51103244607580a01442d0185418040c00703034002001ca5546620070000a102032a014019114500e66110001038011005001030b140080c2a40 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 874569181 1250 874567931 874567933
    0x3030207060515030a0201030209040f322509180902030c04090b06062206031a030703030e0402090301110d09020310020a02030702040b0105120702030a0f090503070b0703050409090302 81
    0x3010410080503000b10b40d4890402e000381e5421410203400f198443d00f140c0e0b0028105030340010101c00350b6035180d0001020001150082042c038a0154000002c041c0c0c0d004516801070321640b0b46004030a844240c40d228100300300c400c0c1e401042e0130301c61620305c2da0305a4403031081c08039848002c2805138010840f408000c3c180b41d40031a0030000750050500f406802158075000e107083c58662130100d041114002e0f0411400e81d1120b41d18090380f481f0700341d10540c0065900c1041c0ea411000604290b058020a02150001040382032034480801010703952419440000d000c1407041c01c13500020305c0d20741c1c054009440050004036004402c40101d003143da001b0308500082c01c3ea80c43c1614150b04041200c2122112000011440c014440b00080d540e8003d0500c001e2055071954000421641300d0415281202d801d016100b4181c06e01c00d401030340740e030481040d8000084074a8481d404c140e00c54508a412603c02801805a003410501804540d0340540020390a00100b004000f4010368144240c24405020303034 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 874570431 1250 874569181 874569187
    0xd0b060d0b090102130e0f1b0705030c06100503010e06060103151a0d060503031c150503030d0606020c0102120403110303040803072d080306210a1b05030703050706030f1503030302 79
    0x8003a07051009417900302c0c2544907000002c11281000d1f04c503105400911190f0f10303e1851000350f0032000781c0c0c452000d000b40140004140c840c018180005c0007070250380d40e4092407940f5511903090508a403481440f241c2942d2007480448c604e5402a44840107106141c42e42d043d07100c2c0c4400c01000d400c8003070f0380c030b4007640880020950140f0500e441014003500044001d103140410742c06005200d03010026014010030f94546507200580980c0d81c0d8040103110203019a0380b2402441d0741c51000700f89601ca51005401034045807030325584040f44c4141c2d00100218602d0030b00e829074039015081030018681c0741e0584010000814507890404c081c0895603c5442da00c03840d082074000c03405804010400c0498440c0c4560400e90008807202c0c1034030f46c0904203036910284106031940c103101442c0c241481100c50b000b01c2c5d0002c002d01c10450424036459054140300741c2d9041d0707103005055a98110303120103441074001c6030b418806240700340c000e08a492010500482c0d1007100c1c500050305040b466104802080d800 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 874571681 1250 874570431 874570447
    0x7410d03151e0302090a0509100c03230f060a06020a0b0603010605221a01090e04050c0402040b0a02011a0109120f0803010b0d0f06030201092c0c03070212090d0b060d0b090102 77
    0xc0c40c0e043c1c1c0c0802e030491b0500090070003404250755820011420031205071604c25240009200342c0c414001c0c0740712030614040700310b10240d455802880a584110a241c281d03c0020400c0c142450b00404032191030707008010140480e160440800c81c0030b00119815501e5500004007645e800c81f011400e031403002c05081c400300c00c0980000407542c1c4485103005856000c45c0f014226a00400c404040700c55100700000c00d0f40d55417901508041504855503401880810701003400e0325540007500000c049031f0000c00108038024401d00c844100c42441c2400121206002d200c4100c40311214505184103400d2145050090381c0d4269881d0000d03040710038012004134084050310850300034880e400f04115020049241103070002003840190380981a00a40400c40c024060214000303101c103400d20f41420410385060203409078996500a40d000300040c89105d0b010020050050101c908140c401081c04000383e0081d0398408c40b41000400595000f120b00a01002103010100107034415a41180010380d14018 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 874572931 1250 874571681 874571689
    0x12021207030b01020708010902030a0206071b1806080a110d140f061e060a090506060918041115070605070c12031b090803090402090607410d03151e0302 67
    0x8158020f0b00c21fa81000001d0000d23031408595261465011b031021680c444c0c1c941000700094200a490391280700d840d1400040c1c050400701104100c201d2030000340b010b1a0368450751551800042000f5080388141c503041d01c41c501d06488082c48040c801c450620f400300348c00c1c290750f0070a40075140c58002600039404220340800da0a00b00040c1c01110580350325a030030b1540105200030900d000300401c1c3c65440012420380c1c1e550700181ca241d40320080045078025400650003502d60b0702910205c030a200803030450340c40c03840c19072521000c046010083ca0b00344510b80d00e07060043c08001c0c02070700a00186070f103031902141e0b6881d00b003103512a26460207e0b80401c12404030100c00861301a5404012440200344059400402164034240d001c6901503100c800e01000074865100e9000010042404800d20780e04038010010450211490301074020020b0075400340704c28846444c040a02c00e190414404001c03d1800b95202c420031020343c0312114003054680c0d04400444140305100c0b0315090603400308104500e0 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 874574181 1250 874572931 874572943
    0x20d0803100504060b1206010e131a0901062102040302040203090318040510090905030c0616030b01180909060b13060e0c04080a0b07050f120105030c03150712021207030b0102 77
    0x2c425101000369503c2c1c0721044d00300b40109041000301d49020130100307000d6807044d0081320360b0581c000c01400d0b21310301041c10400100621a040c0d1014501005d00442c14900300501034104d48080d220301580803030101e0007030070f0001200c040400c841d43c02e10000c000341c0c6452020303510a003c41001543d40e606804a1030302c210850000300b6110700d00304400c12051294690702030382156058040462207800a1030010708500490783c01c01c156200700c5d010006002800c1c40e00740081c41243d1070820440e00e0000c01100c10405000f03100c041c610b07081c20300700704120460307000001c8079000744800904e19601a000411f42d83c451180d843c0c40c0f5403a40c1301404200d0500e1046604000b10902e09450140f410401c69154404400c02603c048501000208410300820888004104281d402030351107080415081c07510300c080c05902c1c000c0c85030b11400c0c689809c001440100c11044040620500e40d6041005c8414a181881014000e6000d102e401124100007110034082c20082c1c501041310f40346900024542a = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 874575431 1250 874574181 874574189
    0x403111c12050a09080d022508030115080f0c0a110d030f140f040f03020312091e010c02060c09040f560402220801060f080c1c020d080310 61
    0x50f2509040703100081780d050484240786400725000da1180ca00104042030f0307480040c00311010301c1403a440801007007000402103050340e45024140c1481c1c104070b08101c6060741c0480706800e1075007100012594040c0424003904207403a0710314010711815002c218440c142010007041c080820b84510004850703c1c418040c0001e82001d0790304070029880c03c0001004081c10240000d0144644000d007442458400d0040301c801d85526041e214140c101003200030740d10b00e131401880c2214142e070401c0048040b0180503e85c04124250700034182c4e62100c500342c41d482e6100a4060741c0c0a42d03115600d0300c115001703008100025100c601032544d05000c01440c0c003c400301041c1090004505455003600d620210411032040b000d42200c1442403030780e08004140240f15010400000f00c0900d0f030f42d44900310000140701d040c3c4040b0317002846a80d07540c4400e041c0b98010b070701807405960007a02c0601034604110385880b28000307155644501c0c01d04070f900414501c0317004010a1b540c103070740001048400c2400704800b000070 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 874576681 1250 874575431 874575451
    0x90e070507230316140c010302031515090d0b090105070e0d030e062b140105010903032d080711060f040f050721050616080403111c1205 60
    0x100d90a41d9942865418004000e2075070040b2451540046000700281c808144c01c0c2200f90704041d0444c1064407245d142c05401604a108120300305510f54400d0080c0d0740907492152685051240c00b07000c000746d0520b00641010300340414400c0c101035075680002c2e880a80e0194000c16040d0030035860880c2034640091408040c401880c44401040d110316080305105505490192200c0e030314480012035a2149220398405010444290003152100341402191840001400c0120f40071402d05210381c0c0d0380900c03e59012443c411800c1001c80e0160300e03484041428090642c4006c615611850007410043c1440d8000441c00c01c2008800764100041c1440d049041c8000d00c03907450704005004030820010801031140d01410000802c2140c1040804080d04500c8020302d4040a840d8040004400c2d10400b5a0b441c42440c01003003120101d000d80d040401459602c8000c0d681d142e4505440141d11049076404520801c6034441d042902e00080300c0d2002007903070700c1d101144106420042520740243c105194 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 874577931 1250 874576681 874576687
    0x41505070f0311071211011b0908160b09010c17070507030212032b0e010f05070e091603091e080301030605090c220b09010909020306071106040b04020f10090e0705 72
    0x1324004621000544a086c6449803944040140c198007410355407403e41100300c0070403407501081d0b4110340000207450440b011581d001186180151008081d48100c6030000c2c0c04000300041c55106000300703c2450301840034500c1c0501d0200031061360b507000c0b00058515402a039828070440c038280246201584a02c80203504003085034800381d1460524940000903817030806980e11003801260082102c10002030300030012020f54002240c007400c000c448c100002500e0310300700c003010b140080c4118010356100b4014100703140b14101c2a001041281d4094955041000352502220f9110080c0c900007031042061503203035459440c00009680000d0081c0040d030b08004440700700354948a6030b01845550250200000c02c9030390322004014542c030890a40c0100c0c0c80e80022448001c0c0da001a14214070aa080300d181d56070348401107510f4408075041e507205800940215001c5004102c0312a0800d000a00409180300100d001038204000807980802042440c4401c10a00d6241411540c0c011039504150785 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 874579181 1250 874577931 874577933
    0x1206151801120c0306020307120e010e070b09120f030a020c040c08070c030306080d0201050103120e0604092003070f0f180302091e13061112010b03041505070f031107 73
    0x3008800500600c044060304048041c207101103030400c40c000390b400020855880c10840e0004041c0005808031007080c0e82007000404209805114a841075021a000713010002c1c14050420002d600201005034020803011700110340b48020b110071040c10548100441e90b5140551010782061a42c003071b2988070710b2a184100600540007120203600103841c0c0f91560281c0d070ba5160650080010740c110b20028410450010380341501544454103890040e0b01c2c00e500348585002c21130740d040d00310761001e40010050000300810381c2260024600c1d00e041244905105013100f40510458008840c03010005010250010000303800c00001d401000d110707c0e202016803000200d0b9540718030070f8440203000d01e042c1000600c003007040c44810b0700c0106080c004001303d4180214402c03a00240d41100780c820528107649030825104080454140280340d540581842c0c2c80c101041ea0140c02c000e10a40d2520b44118841c000f01c1b002c0d10840b0700c035170700c2900c130303c2001000303c500107040f034408120b0444a81c0081203200 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 874580431 1250 874579181 874579219
    0x408100b06030c0a120e06070c020f040c02070b0d0212040b0a1b050f09031624050301060c0828050408070b0304230a0804230303071115040302120615 66
    0x1984180207400c051700d4200c9440146001081c086807032840c43d00640007448107042c0d01091980a15008031502d0800d00e040a040104442e02d8111641c05030740008401c1203d03680c400302a11914640301c0b001410000c038003559005808007200c0403600302a01038100310b5010114821507c00749c15104295103540701805002d400c41c410007003812001400480c03407030b44c669410488000385648070250880c2881da03a40d00705042d00410420040c1d4152110070b080c1b5554400d03010b5034102d0780c550b40d40308192410307921003145540c0540c1c800580c00408168801400010174016066a01e00380d0f216a981c9d40341011704c0341000b4598000743d20588041040c40007040716003400094564654034411841188150320b5864400303820340040002002160008000d10b200641c402d055443c1c40c2c4a007080031149082688900c20180c0c0203000d400b54090b88025800c105060401b0485840300da60318003a143d03000a009030030104c180208503880582004268036802100d0091700b5415201080b483d54009400 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 874581681 1250 874580431 874580437
    0x31201120c0b03100803040f060f080702060f040305071209030606060e0d060e01090c080114100e27011104170106030807060504150e06040b010803041d09010f020408100b06030c 78
    0x10b81d40040003001041d6815030381c551000007081280100e07a03859035101c0400f40405103901c540004521280c0704000c06a00a00001e88190f5007a800340a85d0b41e81c80d0003044c0103100c09132003901002014060200042c42001141d0b014041c2500c0f40d80a851a501e41031040e42c1854105400f04005042241070036102c0b81c00c48040c030b940c8560049100400c54250600500d44035601401496645800050000043d030101081c641c1d0400045c20564a541c4c1c041c00c4020a0f00c960082e07081448001101480c01e00c51501d507a02d00c1407182580c070748801e002c003802c0d81d03a400c0c00b58410350000202000120f10812030503840312040c00091015514680315203a8600841ea000b40c0380c2c64448001500b081000404c0414208511004020304003600c00c1c555901c3c0003c580490f0b60411810001c50950000815203080b80d41c3c4942d50b210148600d803c0501c2c060028244541d65900c0c0e2004807590402400904007605041008100c280e0581945009a442d104041c501400040090090380301400c1c0c11 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 874582931 1250 874581681 874581689
    0x2706021203130501050106050a03110306060919091b09211509150504050d020a02062a0601080303100b070c0509270309010908061323010905031201120c 67
    0x5a01c80c1d5031912103108441200100602d19443c013000480c465030000041d2104070410b60342001550000e90380c00400348429100e00d81c0c051410b01210505103040d00e800d880040a00c4401115aa960702d01901034458500c8403000001c48078105111a981c46a4800c3c010b16a010450811424142400d4201c0445c0d203000b502d03280003401d20840d1280560054180c4640c03215144120030010300c610801442e065408070384500076084840780c0244001180151542c006082d030346880c07030246291614180d45014100d0011552800c691498005c0c0132190080244201070340e6a450281da101d05484074540010403028010f12202000c640d0000c1610700b510000d46940c84562501c0512a500001c00d1343c8008612020701d101c00c0b10040040050302c0c481100780c0300c041d180d40e00e400714503446090803100d01e551242c0d0800303500b0215000c1c0c10f494a00c0501e80c14580d02c00307032001500d1400e49403038003001d0303c25074000a540d000e00004103d2060040012035550800913501d030f40d0b03000410384503104e = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 874584181 1250 874582931 874582963
    0x9040f020d170403061b090924090e010b120a0303050a0e06150a0b0a0c110630010e0603060a0c020c060a080603010501051807030e01020f0a270602 65
    0x641281151100302441e41a241c2005812003201e203000e041415690250004075581410b00c5c5030b401084e084007081001c0d403100c035101c85600c14203001c3c0e004028800002e000e540300c0380790003c110804c101801c01e02d010302004c21010400341520302e5040d00351903036115400e0046d1040d0070081070071440803600104007030741440c2c0810780340c6402c03050901920b404940c9040784e01500d014484a40151448c41c00031440c156800818103a13039980b004814043d140078000410019002c040002e03500f1030050b200e04000405042c10b20250482030b1060b0101500200041c0c0031381103627204412410307c07610740146800b402a0700d9520305540400d46a410107407500d5005900c070660b007800700c0e009103e01842c1e42710113070446c0c1d25458907250003071103428252a003030b01079460240003151500f0055010051160a0100d0000702d071658441107005110118003600a55800c1c4692014000f00000410340c02c03059070394261002d1070f9854800440921104850060009180100003a54010079030000c6402812 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 874585431 1250 874584181 874584203
    0x20c09010e0c1c0b090c03060103050a0b030a06110c190c0f030809010c050a0506090a03121a15040308030a1b0f090512120307051b1b040b01030e011a030c0f0904 71
    0x443c980d006003589400702c40d070000410041080c0d00384404003540c400c240c01d0741c040c0300c80d49805203290121502c51283c0c84d0142c01400e18800402d150b0f41015050060200ba41e92928414070240360030f0131036000e6910801402c881c4060280040030664a020b020300d13492003000d0502e0355548103c0741c4500705015041c002d40c2010b02e001e2000c14010b4219540d040415034420b444c280010310307200d00749200c084010501e14680841e44128610600c5190003440d0040e0303882689405c100103a5200550707501011480400c008800203841002960140c1e01040c004202e0400f02e22450300c65111090b42c2c4010490b40c0142003c51680c000c0300c03482211000d40300b4140c51003200d5040b5040000902180714800000030a002c030095100c401040f0150241c0030a0300f40c0d100500b981d54031691523036001a01c1503c1c5a0001d059490264080004c00605040018400300940c0d4641d0a64443c00c0745101c802e42e500850b00030320300302441081080c0c0c100326810f4080380c5c020000161481001b80002c2d04a030180 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 874586681 1250 874585431 874585477
    0x1060c02040e010e0d0207090e0a0228030606030611090f152503020105090f12030a06120501140106032309030913060302100309050d030509100903020c09010e0c 71
    0x641d0125265803070b9a00280001c02c0d40140060ba0b52101441c403100510070a000000e015600d031082c90703140c100340c0020b041e80e0045034003008003003000020001c40384822020710a403c0e0000d5008040250310446000c5260b03855400d2a404860300c03200d5070a101a401c00c207040c002e13541c503280e03044d20350f4040f102c01d0301d01e00901030311513154041e0030600340a1907004280004820041c07581084210310a6009002070360701c00c050a42c64960028040620358807070240844013801c2100990b510035012800000c14a40d1400503420384c00c022041990965560041300b4040c83c801003e040c0504040d00b81030211900200908210201c54002e450003600504089811004180100c540a020082c4803880011103032a1107001030035203103c102c0c802c056400c00c0b5920315009020758242650024040d14000c0303d5101c00ba00a010300030000c101030300400c560707990b28003680e110311021180031b60300800491102605101e00c050781a007044400202c0c0c10108041d50311328004495207040c414030441c00e42108 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 874587931 1250 874586681 874586689
    0x105030402010309030e0d1103280605040302150a0213140d080d060f0312030e01090b0402041503120906020705060c0a0312060906121208040b0c160605070509010908030a0801060c02 80
    0x10445250303500031007c4003c0c2040c400e0318102550884804c40646001d8a0003c02c0b142c00544192100b102c1a500c65400c680840e07895408254060302a0050f14650a2001101000b40d10122410503030554042031524614118002d980d02906c0750001d4161070020f0400000d940c05140d040003800540000303940345103100b040e002003004004d40900c10800a441c0d1030800e20941310b82c0b244e070000034908013001d01e400c0c80c140244028107402441c514825242c0760244000b424025141c60700c501c0c0e15100000008035030400010755501e442d0360307000c1c40c43d080040003402c01c0120745c8118890b420038820401b42e120045070301c1386a07a030726061802c1c0402d034541551001d0802c50384061825132422038000b03080302d5a8802100d03154400c00d188a042126000c09540341c1c4410365014002015540003d690740ca5205d0081640c031000101c2d0500300300c4180e581c0d40680d030701241c012000800126903a621541c101d860350740503041107005141407421583c0d0003414110140314a80c1005446954401075480d = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 874589181 1250 874587931 874587947
    0x30510180e0601091407170117011407050d06060809102f071a0f0f3c010e16051b0a0501060515040b03040f0218181b010503040201030903 61
    0x907080c0c05036486507a45060f990010400d02c0810350045071140f0001d03414a214402c0b2072560b140003c040398280c2d08181e40d08002c2c0088030300010042d980d038140072140c0504a007040e403094082c0c0d690340340d9400e903d091900644e801903000805100662088c400c0c04003005c140b117040d030381c40321200080d20aa5502c11075040c5038000300b24464881c3c0c1e0305d000c0402e008908002d00c8018015041c2c0309941454035501c0ba440c1c01c040716035140314204800400c050b041d061588540005408000010010300603081d8510200b92034601070454262180c0340207840800209103005145140d2620f58514140408002c0c40390807014980070000b002881c0902d03002c01f04c2c00c124000d0107a50031030700c40418034503201d4000d01050007101e00c221650031410706030369243e4007201d080d501d40e40030700d60071a2039076030351400810f0340744204907131015034644030840040e5625003040c440c2610041103076085090009050502c02c203a48041c011034140d03060030f0b0160341c2010403650401c5c3c1c20301c1c0c0014458418182100c2c850 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 874590431 1250 874589181 874589201
    0x10e1506090a140405010212011a09100917030301080c0102010c0504061b120f390f0b04050307150207021e15130602070909050d110309130906050703051018 69
    0x6901e03d810700c418401c0560191400c0403400c01041c00590301e60310304041d003c65100102c0303407099081082030860304004070031560b14112814061081e503254000741000703000141202d1011347c0044010800804d0130480c0e421401020f0000704540c51084800500c036101d98081c3e2424000c50324003008a0340d2441800340d086541069060000d011080c2004100030b4015440307034002946080702e03d400c8255554411f00c00c100c1c81c8205400b50b151070007541b10000c420301056802d03c011685e420081107005034070341d100b140f082c40650303a50551403809a04140080a50f84001403050241000513100c65550700c0c000122405444202402d00c0000f900750340500040582c0f1080100d446440c0e00400c401d1441a10042e0302601d51240d107804082c001c42e142031001501c1d80d8000c00180c0100e6000d00c001c0c5200d03d0800080da85001e510340d01082c2040d02c1d10072070b1320701c2c250346103000418003107140304250b000403681c0307014000390800c1d10382c800710070f4098054803100900341e1706001c80d10b01b00f17a80918804 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 874591681 1250 874590431 874590461
    0x311030c032a1c0506120319030906020f03010519030b010506160c030516081501090c0c0503030f04020a08150406020c0304080a11010305090d140a1b14010e1506090a 73
    0x1403240303043d1100001c0c20400344560854105400700d82c907464030441b1754581c2001c0c44025818000c111003070007038440e040c03040002495a180c88481c04030359240010040c03000d03c04070b0135669524000511210025000c0249200c2c0d078a20418000940c4101542d03046500032520302c2c0d02c40710f1181020b00702c0c020f1031400070820141c00f80000100500031030448070496110001307840e07841d584ea07411a1640b403c102019000340c1c64800600c50b203c0a0b0744010750003001c601c0c01c0c058055080e81ca552555100350b8900e000c900d250340800c411803501c000c0410145c5141c0e4040d21040c2c1000c12071040720040600014200303900480c450344020f13010420750b07004020480403a180c030040c1d8180580070064070b07807500d400642880001000b840000401c4141104a40e84d001c50948030003800d840d05400074241c140400071100507d0003070040c802c8030310a500d80a440c404000c060b81003400707821204030700707100c84203074010364602101c02007a2030b40d05a104606035050801d9a88400705c40c002010040210880 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 874592931 1250 874591681 874591687
    0x170f04090203090a050105180319020a0807060615090608060108071e0309020933011e0201051e09070603050415020309390121020313030311030c032a 66
    0x220f070400140c1c0c002960300640c02040355481e0f1b10100000c01740c100080782042c0e03004006802802082e001222904002481900c01580b541e907101c89541e80041f500b500c40c0f1b1b444090621603a280b14203040c140600504141e00d2082c6007000180541c1e500510f19414410120001251140030b11450122041c0300c4403135200c1c45040d5035000d0000e100103841a4010b01190700001c55410143c3c40d080030130404541102c141e030580c9505801c8a0124941342ca0400c420807002c1850b0b0f9030b800c0c3c2e0158410700990008543c519200c41000110302c030340512840d00011420a01036042c50100b0b49a06403440c0c1c1c42c001c640b0b9a6182404002400c2d40c110a000c1766200200b08a1040c0f800b0032601105103c100071a40c004001c020001c0c1420f001180350711009914040212456010b08104180c12020003d1800c9002c1d4460180f01240c2049440307801009240c006001010782c14881e0396001095800811304508014208001c14000245502a98860702501a030014484004420301e0200241c000e99 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 874594181 1250 874592931 874592941
    0x31407151d04061706101a16051b1c0803010603020906040b130315060b0a0804020d050703080a120203010f0311181e160c15110d020403110d170f04090203 68
    0x59160300425110035031701a00d404a60310070a12256102121402e26040b1009190f07908144600e600003613094543c8100510f18900040007400741c50501d40307030300f0b00030000107004d0801c0c0f00c106100e1900c00ca10002c010005240054921070580303065400c68900181c075900c912005ca081031046811902e412540413a074094090880704080c1c0c1903d05c00c0c24003010b6042c0001c401800d03281c05002d605521081806000c0311688901202648180010407584008203e034445a0400c1c83c1354206a580c203400044240015800c4000c4001c210321300041140f8540c2341a44581032414140402415411150350030b0b0f100381e4070041491510800b64103122640c0c1413600300c1c407210300c3c280c0300c01246040b0510b0001e0210f034400559200d03075924980f0f0300302c2c0d265031035a05d44000c0001a0f18903079500d41e0b0f0300214050101c0c914054038040c06039440c016500d07070450030503089184607902c4c042d115555080c034200000382203016040c0004592612031345c440700000b1898090f030150303402c41c0055500c0401081 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 874595431 1250 874594181 874594199
    0x30d0e0d0e030d02060a0b0f2e050a0e100309051c0306090501120b1902040b071a06010507032a03030b0109060e06160f06090b01031407151d0406 64
    0x2120840160700c9820040e0709600a05071103401c41e8800c2c00150700310030001019a68180c01c42d80c800781d030041038400c45003280c00010300d1810b40807038510207150031126800080300070625030b10341c07003241810f00e141085800d64004000c52080c0c100d0781c1c010f018602d46910118000d811012030385500c031040d01d2000030a000b001041c0d4440b44c0803840000d040134000954a2190b1066034180d40300101d0004c210102e0751190040340070003401a01180c8045007000703490409510140000e001c85010040d6600c48a00700001c031610101c443c091000204400c0c0a440e07a000011120450b6150a182d00d606404030781180c422040c01c010b0030b0103c65100b040760304040e030652018028250980354120303a540c444400f22007202804c0980c581140302007043c0359182048115003803190b48111a00042501070340e8541043c1c0c0c42c0600c003281e904850000600030070045041c000c420025800040007610703e00350070105415107400c0014140484504001000a810204144030341700c00350050103510303640c441c84 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 874596681 1250 874595431 874595443
    0x13110a030e240f0f0403080c0702030a08030c0702090a0203061f05090a0612051f051e06120906070c03080606160f0c0f0f050307050405092a15070201080a0509030d0e 73
    0x1042c100903c150015611021901402d0f000d03e40580d40c4c0b460b03503a25200c02000325032012000340da240c031442242c600040c04020080d03129a00301070480340c94041c6841485480c0030040c1c0354000c00c86c01402081f80603229040621080e207240401c803d0704040d4110141da680c0314444003141c0140034400040b50403034104440d4046810703684010031440d034545280380040e8002140107810304003403507401c2042c0c0c5001258000348605041001d5010a0300c200084d0590f4040c41c01311031024001000c1000c43c003024081e95601454a0400b85c040c940d06541c02005207100500c1d2520512001c02c00654004141380800c003c240d101c84807c10300e0081d4100240e4624591040d2415428004008140c80c400388a001007210405401060f0081c144810440540002440302c0b981e031041c0c0c030744442010f000b00b00b038544462103040a0703c00c46a0100512162000c46450000142400c00c0a200141d071b20058140c1d1041c90124001919180d0001ca1421441080c01e1481e045040c80e544480984c000701d11 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 874597931 1250 874596681 874596691
    0x5060a0b0f040b012001021c0506030f0a0c0b1e030a0b0a050d020a1203031e0605040f05010b07020d0c1701050901150b0d050901060504060b0913110a030e24 69
    0x60020001074004000a50700d5030f0142500003000e81404003d842d0160350170441a60300701c4005070900781d0341e207020321150010303a40007015161070700b0621181d8242030103c1015a0301c0003001d0f201d04117440c3c443d501008500d01c12000101c200003100001e1410824a41d1000c0e036180801c50781d01d0610242000107400d804c00002d1003034640c038400040c01c1c5454000380100e1239001d001c030100b240c500b4050031403540500805070281a110741c6002c2c000c0c2103601503120a04002c2c6e10000d011400c200511046841044601203203e1600d001407100c69070704000d8450a40d81112040c03102e529510304600d00c132030785902a5074050200f0308012100641034110b5445452203000810000d4401648003e0300c18641c8a40f00540c0e0080081e405100d02c0c68000c65031011150002081d015510f801040888613583c2c400361038100c000c42c01640d50316024850100c1100c3c01074041c4403100c24040030302014403031100d0040a1650b582c0f406a140e9500b44040c43d9181e58850000101d00b6a00000011440c0c084070 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 874599181 1250 874597931 874597939
    0xf030e090a06080d0809010b0415150e010903060c0c121706030a02210f0a0f14061b09010c060203091e030c0303010e0c22080714030d05031305060a0b 66
    0x3521401e068401c0404403810180101160040b000702a0344942d40070b40b5500d069500c5a6210406450381e00031a1100200c550102c4802403801d0410031806070070004000c100110f800344580c0c140c4e48070b0005030070341750820800585282c6800d000d840d4145840f00082001d050445c10b5a0429000508851f40203054148110160344807420035895444400000798000724407540c544010020781051040030f00e8080c00c5a001551403203405140843c600c40c01c0f10440f03440b4100204200308811482411969070b0700500850909003c0600d000d1000d076066007214001040d8902030341e01c10a01a07418a40103001195642000103111703890b0810449400840b00f000b01080f00b0362a800802c945094542401850551742040ba07981c010350000f42265040c005c081c0720000303c1c4654110650500d0360203185031407680f840d00f0750082c14800e00380c2c4002d481d1015200d0030030a585000c030302550380c00300b03d150a030f40c1c030798855071140040c02081038054120301c6442c08000601d1002e038031541222174111 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 874600431 1250 874599181 874599199
    0xf08150f24091e060703030509070308032d0708010302010815060d0f0c0504030c051905060a0906180602121e190210050405100b040e032212031e0302070f030e 70
    0x207454200040300c01c40f241c100f00200060b10200f44258020740d044140d54043e1489140d40b5141d83d20710380c209490b804010051119000d0003141703007a00000440d2441301000310325103055030015069410510001e41401007400005058034110701c0150400740d001040d007516000d02079100d8004150300541807508500d080c4841052902030402e86080303960103074461240a0420003809044026483c1007130f1400b08a0002040a5403030310040c1c40c8a00040c0d07101c1403640d1500400400308907a40d070100001560000003400f245074041038003821740c4001300c0708503914a40d900c584645618021203a0100324008205a04203048443ea12154118280d003114030082c6101741c80740494a0640b40185540d2000381c0b000c400c825035812201081c50001d00018200400a80c1141903a1183c0e1884c81c0441c5005c01e18000c0310b100300420130142441d5406880090b44981d40600076034250302010504140020f48400c00c9442901103510305c075482100c4410300c00052401600c2001c3c6c0300d40c0b441c4625540 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 874601681 1250 874600431 874600459
    0x1506020616020309061602060909150906040c02031b150906040c06080115112a0301140f070c0f170316030c0e060a0521070f08150f2409 60
    0x791350507100014400c501d4904540301c1c00e1024031845030100d8000b0310920410307081d9996403031882d1003016006c000c1c003504019030007040b12400d03001f0700c0e0f0351180380b502c405009403590000c1518074440b8915880070406071502e40d56450000d00c400f81c0d21101d0280d00800081c0e0401040e914011441031854040060701c50343c0a039210042406003400703c41101688803003141c4680c2c000400c00c200102524509042c900320015a1880600b01031487c115240c0c420030700382000d10440c810043d0442d402c8041c2d0410b201c541c0c44400014080c0d404028224489009024002148800560b4064032440c410030300141810143d400c119000303080f09200d06001840d0500074052039030b00705400e580d21820586030b5000c100050300000b445a08024050002004600c0c404080c0c00c0b9410022001840d42d291102004001c508200158401c02c105402400350139030320081e0780540440c04441c0024104540e0012428200a100e034560b1790754811991141c11205880082080403400d90396124030b02c800e = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 874602931 1250 874601681 874601683
    0x80706051309140c0711041a030c0d0b131410050a0c050307081902090303120a150b0a0c02060f16020316080712050109140102120a0507050a12150602061602 69
    0x1041c44050703050b4503000005602c919184005e0442a1080b503903a583c04101c03001142c1112200c503410703d00a4100038117401140350810810b0f9407a0001c440007001c055490b035400c4850031002d4840e0320342800c2c3c4003001003041600520b4500c4040034004592960402501240c09800180c42c2c0840340340c504050356103158425011a8400e004548505080d929034130380340115001624924901140c3c28446400c5956061004001c180080081d0f4200d5003003860141045905400100c5202d40780c0761010004a1201401d5032101101424400a01406800400c0c0d09200e07110840030b44450020700d40e90248a10312007402e98a0007602141e0788031040c5140e56040242d6401032075141e911941c8108005e030203016081d502d25206400201e11700ca800e940d01d000d02c80c11003c2420160f5004586526030b407070f65440d03540c3d0094002c0001d000307604000c0005001c52080040010030440342e50040e04103005903030400e8050094a0308a410401e030b0b10040203440b600140c80300110a08018201c0030201c1c8 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 874604181 1250 874602931 874602941
    0x70305060108063604110d02030a080a02030f0724153005061b16031206030c060e0312070302060112060608010212090d0c0506010506070606080706051309 68
    0x201a1200100354981508104880400d02014904c0e1203544402d110040d44c6540001c0312422009520119410540b0304004051112034800380034400c1e03041c68a01590b0000350704010035410962180c0c0c1d660000104030309610a0390b560840b03034440001c10030100041c1081c2e907031412015411003040080124458401d4510180d071040111034090030610000039600c200e55209d03007008011084800c1d00151060507900d00341e200707480b030f0f40001c420030000340724041c035080145143c0440e252030107101510410200302c0555000c0c040120200040c032401406602c204051900580e100ca10301d84c1d0b40c23030014440054109424000d009448000f41c8150040040d1410140d043d0003902c1c5c1d030380c05d208000700e0005203140142c544544030800014911070a10061000c889895a82109440c010040c20701d08109081d20104100c516020000402c03800f040e4181594000c030354483d55503d85080c404041e02c40f6803c949414000d002c00000c3c0c00317800c0001840c0d1640741800c4000748e540c0e55424682111 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 874605431 1250 874604181 874604191
    0x61801110d0801090b011b0b0f07050a0503160201091505090c0609031009020112150321120f090209090706031404031b03051b0f060108030c120a090509070e09070305 73
    0xa261500107109113075013504035200141c01031410341812419101d4161074000084400d5403205d042d4800e1040d03803810345260329800740c09414528a00800010300904900c00142150403600000d0b6140c0e00c114403e401868034503401911902030b0b540c00041c20002000300b44c500030000e00c103000300d2082c5803d0500a0b50800c0d00c006016003440301c00840c58038060008400100d040020400074800000d01c2880780d81c02207400b0201345002907041d8900405107004925103114801d100141000042d0307802104e619102c4480c0c0e40100c0c46208812030400034080300c14001303601414000401141500005025048a0003564288888030b14200a8018484c007550081c0c0090151111031351580030b8610000403d0784a031031305614002c1d80702d08000c0d54214481d03440c40980c0000701d202000c108200309183c007401c0c0b941d014514205802c031403141e036820079010800c5000c46c0400d040300d555015081c6940203180150288506d803400410041c552208010114800c031040030204190764440e11819200d0 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 874606681 1250 874605431 874605437
    0x20c120a08070201030b09090601050a0b190c15090302300a0f050409020403050a0210050a0e0d081201120515060d030e150a1d0306090604080c0c061801110d 69
    0x1500c90349038404141e00c00d110a034185a00c941942d0900c3e01c5150360036201d02c2d4454040d01081d410304040100603806944240030f03010b8180151081ca5885100c549040c81440c28020103070843d9182456100203c0284000b0481c40c05640d00700349500401d0301260071842904001030f25070000d6034228042040510b00c0c240c0b6030240a900780031402190420340088803070070300d02e0a00343d80d40d840c41c09903482a08100e8258100ca2240d00441c00e10f44121828001981046410311141010040c0800100e00c2d4103803090b60122240070a12a04c85c1c1264800351035044114120b60315612001c00f4500072000440c0d9510883e902009915400c10f10940240d00060284030f049e200c589040703944001294820740d05c030900300780d400c0840703a40348001c014041d4591038102c0b4041400e072070040c600d060012117a000b60001d80c2041303c1d2013030201d104d036030065210041948900c200b144071842c1401c410106034002d203000030820034040300148a142c1d60381090713898040400a0b80141da80b03d04a901800000c = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 874607931 1250 874606681 874606693
    0x40905090f070608090a020d080a02010f060b030c090d0b070216170601140112060303020714030106030b0c03070207230a090b010806060f070804030623010806041b0b0316020c12 78
    0x208a00c00c4613099041211134007152104500b680000e1284429100c04841143c00022244041ca0b028000c25000c201d01840c104140d510b4440444120b01c0300624003c14480d00156400c4165140c003204421560440f00310002841c0854010b03584a01c2444145066211110000307040c1e1031402c01c1001c0c0d40c0795280544000d034a88003464003e222090340c0181406100c02c02190000011710039040118080e60061404600c1c0030016107140e1248410b070b41c0030b070341010f80500100301c81d5101c01360400317003005000342d981d40c80000407410051280c000c52144103540c25000c04000800c0030319201c9100440b05444025660511a8200c480340706603c6c0c0414038000000b401e41c40c0c410b0103014502d250382089450301483d65218a40c56206820407114241c3d030b1003428030072130b121095228980402d403000ba0300300c0d418400e45036510f0100402c02080c14048246c42000d017100c1e400b176940148102c0c0311803920780c100714079013a43d20115001280f005204a41090303074540362124402c131941c100302e4051b01d0 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 874609181 1250 874607931 874607939
    0x12102040c0504050303071109070306051815060d050f070804020d020907051c0510061107031403041503051501020606010903080c1e0d081501090b03071e05040905090f07 75
    0x540841c4034404144501800700080c1a01d00780003c00300d09209102e00c203070004400040040000010301194201881c0110034051078851122550701c08110701c60720b403260b42d80c64510280004da14030084d03801600202780f43c2e105070059080700f13000751030402c070385a000d603180e44048076900c0e40ac950181d0700801c01c001c0c10000d801c21942054211030390746012031510340f0141401812502041ca0b0207121543d8504000900401ea100170b00909010b24040d040d1303515144100e075803250f07640030140035030b42d00f04140a40c080007001150001c2c02d0000350070301180000003001c3c00078807040341c00070320509008030203515961000c25080e100e018141c440c1008581142c1700c40d8215004085015907521500c9120100169082c02d460a0fa01c1940e0081007000d1503850010304511000c0c0000d02112550f5003110702580c1c1241c696810341d14044211522075403680c4044a100d122030070030310b407000c0c0d400103d0401d140d4044024015110140070504c4a0380350032590725503981c031003014840380e41c001e410140 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 874610431 1250 874609181 874609189
    0x3120a033204030c0507080d140a05040b030c0c010f0c0e0a03020102030415020a05010e06070f02010204060f27030c1d010e040206210106020a03030b100c0b0603190605060405012102 80
    0x368000e4000e25090030301c0340e813941c0d6440c0b4058031a003012000340e000381848804940e0040700c0498400452164030f04140320460086c0943c00740b80198140240d001c40054403001c0a442a1004083d11b54028040c030700140c4101802451841200c600290180300000c00324242802d80710f084903410390056141c54500b00300c0060600c50700b0b40740000c500070518000085074013401140115280c07407000d4807c0c0d0810940190500d840c4d040407030256401030008204054001000200c2d401850070611403d401516071944000d44034900204d0300d240d40c1d6404410310003903520320429114442c0e002c80e01005500030b4550130403030034031411140b5500da800080042c20840058078454a403003010404045c58651406468407098101d280181d11109460050551501a450b0031031025070303043c440546800001040600450000f42c22003000502190f082d032010400d06010122612081c0da4094040c50820040c0400752885840f035410000081440c1c0c658070f16449810480300342c0750003840a6a8284 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 874611681 1250 874610431 874610531
    0xc031b14090114120109050f0106080f06121e10110304020d05070f08030309070f030f020919090303020c06010e010b19020705090408071709010c1b0503120a03 70
    0x760400001d55480100c600e48400034003808000b9a440044560400c1419012294000c1145c000406a4801000503d81246032640c002ca20300614600c10f55071100810381c1d44000321511f04592048100024402420505145101d0842e070700341c90001c5e40d00388120003524015001c05440c6c920800c00310b40149040e05101c542d0302d114a0030b803048150b80360b810200e441101d40c07081296800010030410a540d0600c410780c00340a0702c405c0c11f807a184c10364488031020034441070001c0c0514940c03000f1403030790010311798044d04447c5000001e00c40b9000526004010350808140c09040d485060004902c105400403410305803146038494904103034191468803107444821210703d065001d480c0001c103164681c9102680b00d40d0140026aa903480c2ca46840c00507005444003900750440705124100181c0c0c0d0203c02c051505800485c0b100d0511000301070a06012a141d1000da414890340e00c07107030302309803d1002030807041c01d25403020428034000f128190f84002c08049090aa840c0890414800211000b08 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 874612931 1250 874611681 874611697
    0x40f0501030b0f030d050703080901090809190e130c2412060b03040b040b0a050403050a121e0501080d0315030f030509041e0b12060a0b13020a030c031b14 68
    0x1ca0340349030f11074400f082c14403019051280000e14005540b1092540044c0a01c2d0841409002004100c24580b0780001c2030080c0c1203054407404851411408060f102000c40c8090420703803100e41580e040101e0b40c040540f2210340704550020704040002100c1c1010002504010702131140e01c140f40780e40e0302045450ba01c03480300500c880c590300c1e10082042c2e081240030710301c1035114017406030003400c01d400e00c0401c6c510018040f0b2161804d02040000199002050314036a00300d90406095100300310340d480c0d000c1c20110b54811644200845104d20103002a00940d0480380408203071201c000521030105e007a228421881d81c603911144104100058036080110461030081c54002d08000f0f60348001016103000c4a43e0301c0744010b103900c03000c154002c1e81c0304201404501700d44034091030104d441c8054503408010704003050309607030798000d0742c207070b100c0781d00c0d807006541d42040465442c3e41c41440a00200012203403a0f0000b49000491003030103125202005e040062b64842c1c01201500c200105066031085203 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 874614181 1250 874612931 874612939
    0x1090b041a0a03112107061d100503060a030609110a06020d0e2e0c031101150b0c010603050a0f060b090712110904020c06061c170a0c0c06080f070302040f0501030b 72
    0x307035030213018185005c020700492140c0140601a2034030800070a180c130000b09003640401034800c41015a658410046070400c0503042141d00e0341c2d0b0b1000050000100e07944040d080341c1c100b10100c010405500091160f03c1403c44a4501107904d420302207a440014000e010049161202d4050503413420306507920169a04a014140c491510707030107407044601c52046c103c007082d4450400c80030980c10040c1000300a901d1002008403451005414800c0c191910903219030210000794013407140302c00c1d0800400f0f9504001210410385552402d0413a8009041041d180140790043c0c4000600c2d007401d400d03000300307015070303600b07400030b50b1680014014420010707103512403001007003003840c00d44881c001713080380041c504090718042c6800424006a00c00002c2c0c1000072070000400320300080c0c1003520001100c048005101c0d110440e003082940c0d0b58080030005072804c640d0b184002030669001d03c0c0c440c401d100401e45041540c503484001d80c00c0e40118003445d807201244003414451948250300a07074601e14010 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 874615431 1250 874614181 874614199
    0x501080f09030d0c211a060c0a0602121f14011b0c0609090506030604080f0309030409060b0a030f0e100b060f04140108071b030309081201090b041a0a0311 68
    0x80401c040f101340d041d040b000700300104a0028004640c280210030744c0c0c013212003405110480d94038204000360840149110b080081841562000c0c2001949041980540b0440d5100403649284080303013422524454245d80380c891240d1404980d042070002c17620900715030804c0411120040d1180140711071500c550041604500c80070401411440c4010032a54542d80540c6040003100c000790388008000d10300a6002005200c00070b10724078100e44001c1881c000054490301c44020740d0b4118806c80d400341c48a9030800b0b00c00b00c0d0a03221030008181c0c17130345107807810800b203011140c0706010383c3ca0b0480365081d00d030090b0080804251180e00450a001c400500c0300780f070540c044841041517041034000020700b000c90102070940c2d58010b00e41c90f40000031802e00409048841c502c082d1840c50f10040141016181e84040f4100b02c0714805a0b44000c0321242c400d031196031900d401500911401445d68403030303410809802400350380c60352408180701c406081c031140d0394219103541102407561841c2c030743c0285ca14 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 874616681 1250 874615431 874615447
    0xa0321020d0c03051e010305030403030804030219050c0a080115090c05160c060320031b0c030706090c120b04020d03170a0614060c0d030507110a030203091503010501080f0903 77
    0x161040b280700118075140001c242c100624a24a8170130a040d402603a54000001031022130350000c2070f41c0440f0380c1890003002030760301c1d40360480c18450480040804001001066020400e0210300100c0019040c2c0310301a41c182c2c1e4102e62801d03204c43c10200c0c1251180c110b818040c2441c00d070001340058640c0c2c20700500d80211340b03070642d01c826003800d03040e151050541014803665a06000c4d184401450740d005440504519040020b01c0c40068642d40100f14010743c0c141440320301d04180c444002c2100c05413a19902242032007409000c0060040392041400343c004120318103c280700a40498000c6080f482c0756844d6070a004440440040c1074040c440810a180c10b0705505070b843d140b00301c10007040030403000d1400009840080d9003003100d80c408d0700c0c1441074012041000030360390080c2e40342e850041400e856445080d1a4500c800007031ba8030502400c01c442d0140742e00000204440c0d802030303c074940c44d40000d0105400e107000a009641c0003590752004a4202e0182d0700c035260700040c0e6031064038030f40244 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 874617931 1250 874616681 874616707
    0x50c06430c03110a0b060f060a0f030e01060f060503100f080d1b0c08240f160c060528060324020c0a0c0315052206021209070f080a032102 61
    0x4d1102c101c419213085004c0102e64240104010f01c0580700f84c5900d424580725040242c1401c080e08003020415940c3d41c0b01c066002025041000101b42c49082c1126640e00d406004086910851792103a440040300b000080d4075039a076a60f00e040f904c4030300c064001c0d074415000850701404d0b00070060441300c480d00f2500707020130f45505a103c010b20601004201c40c00160a14140c441c030b031841c1142c465000c0104000101d0f0203442280d5100303804460320303c040d4600c2c2c00d00ba201c1100c0080c01074440e514020800690500c505a9011a01021182c01c130314001540e0650081d20001d0200800d24844803807810200310320501c80c90b1401114600250610180d0070f011442d0070ba002710b0585241010800400601144410300e1003801c2c00c1c001c0911041c07600ba41c8040d6003040000c070314240c5150b03030380018080c050f90b503055504603000d8140380781c0e0320b05081840301e96900180c05010030707030079140c140010003001c0019146091540340e11040c3c2d110049030307885030482828481d141e1040303401700460081031030 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 874619181 1250 874617931 874617943
    0x608010f0c0f0206070917030705010f020a02070f0308120c0c0a0605100b0304050d140d091a0f07090509040c050603100e0a140a020901050c06430c0311 67
    0x582020004080440450042c40144000d400b1800e540100050003100303a4049031510075a102c0101a0014803040035640d40b8621407904050f2042d480d160021806040c540c00400180540f642213400040e19a119200384400603c0700030002c01082000204488900304490b5110307660414503810328031118411401d24007801e000300e6103d0f5807601001a03404040e0042400752100b09405030940c90035650f250340c0c60400700985020300000031400c80d03000703817004102c1d00240d0003500c0900c05c8040c01c0c9051004841c1c0c005641c90554803000c00580d0030855070402c24407480e8981c2d0781e140203c0c9084140f00040758090400c1c7d88025000c1400320302c03500e40c80b005500809805600c00c030401d02d00302c800d543c031500c094503c55400d800c0c0078502e505e9190a4421940002030064016036804045c00162494480c840700c0d41700c01d020705002c001d6000d420501020740e040b14036a82c040103441d8030700c404000b6001001034088843d80f40c104040e00314418504100140e102c3d061000da0110540203c2e881c240c = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 874620431 1250 874619181 874619201
    0x19020111060108100c0806060a0e0301060530030a12050603120f0307080c130e430201022817090f0c0f0a051909050c1801181503060801 60
    0xa07100d40c11301400c220852007464140d0000380740c0403a01d03041c8100050b00602c01d4104070000c000b1010031140080e58217612030001044010480c070030174001c419546481841d861004000b900780345180300d2070b8140110498200c2c0b0315035501c0824403103000041c0801040003401994140c4101601003101e0426071000380f030064201010180c5a00c1d05540041072000014034440a041c428029015050010400300f010b031145c1007000085595840e1404046140c0d1540918110307094102c0100c0d1882e69a40450407849440d08001185e10084000c0e4241c2c030410580170303032039400407021401a440420b040d030007051161400490f1082c8079180c490749000287e81d00e0800381c100f400304c4072242c0340070040b184910b04e0607140060080c000c000003441c150700f1403103440d01804651340070800d9641c40101c080c000d4400c151040015082110040e000d0f5001343c42d43d400454601e8041c107629601603162803514500000500e4079071800e0010b08404815070900100506448240c0888c4e000b4081c0501c071341c1c0c4 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 874621681 1250 874620431 874620433
    0x312090302030c030d050427241e030303050601030914160e010308040501182111190b0f120c0c07061419140a080105130e19020111060108 61
    0x89045004140c10608042480792003a0302114088140903008810b44048445d030759402540e410500002001001d800104504403c1c0b8048200c140c03040300f04140503121001003c01d01c41c0584820311911410380f00ca241c66040c2506100400000f4883e8000591005e010316002c1107001081c0d8401c3c1c0d040d107040274041141d81007103600d4000d45000001c0b0710004c1c0802c0703405d501d080d403445d103824049200b107019150400101034140d500304501d491a074002842c010100c40710400031901c00100e01a8086022210f48559080d2210580b070203400c1c2d0242d00c1f86040d400d03001140340c542c0c3c400c0554014440106604801e211401280469490507880380094a4201e580c9220903450f481c2003074030580010303080c000e0301c3c0c5c20411a005244242c170b1540c1c0381104c030650000c001300000d40702d02c0c06c110305122201d40300003141c41c8042e6005241a04880d41620311000c800039448914041d140c500300300700b00c1c5500c4007d002c864030782001d10300b00e4580d0041c104507196070a40c2c09901d080c05070980040c415 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 874622931 1250 874621681 874621697
    0x5100507020d14060615160c1701022515090323031504020a0918110d0b121c080408090406080a050d020705090601120b040f090605130b060907090312 66
    0x2101d4002e214540e88640106c40300844030340c00d04030002c0c0d1800307030b541c0c0c454000c85002c01550030080036169090140280c50103805d50303141000401c9001c0e6101500c07014001800e0034080c640c0401d41c0110001c1903a0101d200c060034010003071400014a0f114005404000c03030900800d0081c0100100d5070321103140407004c940d980ca130246111044000d001c88881c026441000228003d5502103c040180e442895980b0315a41e0042001c10160003681141904041c0c009141c500e045643c2d800f0000c1c07400d06452103509003501d4822103480e1ba182e5400401015481002060150703c1061160f5202d07204920241c100000280490110b6902d500700040c503500400c50f8070180001000b104510544510041c4030303850401e000300700c5880740541078030f061000070740d008420b04c00903400c20b00b2091000381c8104402c00301001c00001510303500d0000d40ba000d241c6404603400400141da0079411541090f1840425241c0c0414000320910040c640300400000c0703a0044000382007081c41d40c60b4604280c0c0c464503 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 874624181 1250 874622931 874622963
    0x10f08071812050c0d0807080a050c03210601090e06010f18090203100806010501021507020c1002032d040501261005041409100203060424150c03020705100507020d 72
    0x413030031900100d0b4074842c0e8083d032491400504a1000c1720030b0250301c029072503110000d4580c141d80b04d0240d05019610b1340000300e91082c901e040540f04491103200c1d10384c03000058665400541b010030150003070380300c442402c5000030f425502844880751860810f240c00c5400c503c0141a4180b19081c603040581599000011302100c15600060b080c090485080603007200d5151400207551200890021940396003150002440c0c2802406041c5d05600007a2100e0500408900c00a4072548198042c8003080550418400844502c4a131100d12459a0407058074250400b401515801c500401c3c0007600221803079402448203140703002c18012201031405040b2a030525041000740d5000d103900344035140b080010407004cd41e00040c0c0d4505165a00c2005a8a86480000c180500b40c41400d81e5110280901e5518410043c0c1c041942101c0d81e480c41c60122060200040b07034219120a4060300592240c00148101c1c0303000c0c00811200c03420390800d030749400b00790341c04602242201e42007501d100d02c540d94910 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 874625431 1250 874624181 874624183
    0x909032703010c1407020f01050c0105040303061e0311090a0207080c07050f040902060a1107170309030f070b0a08090114131704060c0b041712010f14010f0807181205 73
    0xd010700b03d403400c2100041400180202040c050302401900c12401c169201030184d000d003080310841c0d41648002c0c0250301e0681800303001b6020340e105224442440342220b16010b00340340054801d80c1c3e800504c0c003034000400700802042c1d45014160500c42a400c2204900141c006d20041810644a1018142c0285443c04003d02402c101c0d890b24001d9040182d1040182d03076400440b40280c090b0300301043e1581c0c046060714078001858001020a850641c2c45400f16540040604089a012000c5030b00d01125045200e031144060710900201003c10b0100c010090300a008941d030040c10302000107050a140801c00b40b8282058810b00c03910043c2103c0b0f04284810412810000e4001d010b5182c500b621308400148180301d08007000e041c02486001181c10445001d151058548400480076101c03003d400b94400b00e83e200380f19083c3c10305031000d00060751702010048038040c0c4d54161180410000100015250200c004004c40204403601d042000c2019245124102a01d0541c03070580030554649401 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 874626681 1250 874625431 874625441
    0x1603030f1215090e010f110d051605070807110d0809121f020702180a021201120803071d030a080d0c03050408040603020702060d0f021c140105090903270301 69
    0x10500705060000040d002e5401c0b41122049800381e24000814040e041816030041140d0510180301c907080c02000c15220940c0e2000c2c103d80440030504005a4848021804051852a611001058042c030cd210040f44400f8003038890300c0c2c028450000417000d20f00000300c03121032a0b00100c1d03e00d040461540c040f0306169144290f460125801850002081045072402a03c80e00d84511910b0f00080d082c003c5407213a04513000c40d40701180700d000e05414090fa500010390031501c03282c0d1208e80c1403000020104070603404500341c141c09c1a90180f445d1181003007101c0d4008190800503405003c5090b00007945c4040242180e828010401e00d500c42011105c80000c0e90172101819080505100904c0f0204922904a800300c42640c100141d562413207201041c1e143c00307015181013075149420380145486200390028800000000d645020001c080d506e22002c441c40c0303905070b0f0001c0c880075005004900700a22516041440501200e041103c40c40e15160b43c00720b000302400c0345004281c00301c00d80b41424040c1c = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 874627931 1250 874626681 874626707
    0x303030b01050c060610020304080304120215040b030a09022110050a0b031f3c061d060f060a120501080604051f0906060611120c030f07051603030f 65
    0x403441c5814030102c1659138405010341103038441c4030790680c1000d04034001c20460b0018100d4106480e20f6942d10b400c81da90070304005609034001c011910545030203001d01c00449040e2183ca03200c070360a580710400440d00600c0c15800407038201d44132000702e003c0758020852900714199410014045100c803d81c81406891f40a0080902d140c10b0441020031560085983c1e1024030141d442444904100840138002d402080d05600d8811140747c069200170001815804030340035510610601001502c0102c1c00301c40350f41c0f007105041440719010044000380720400a0300040014000300c60324440400048155110707080040201320038441c02e003001d1600d805401e004280f42000b5140c42c0c0fa042d203c81d601e0300810190b01003070030503050281c00e1118107907000403010f50f00000c08010366512800050b00c4010320b1071004985114038600100c281003d00700301e41c0342440940c0a036040c83c2d001010401b0641000350121402d00940e07140c86020f100d00c0d00000000e6000e070391465100200001d0140080030030100d = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 874629181 1250 874627931 874627937
    0x90a080a0317061503090a0c0f0f08150c0a0c05010c09031104060614130f0b0409051b090f0121020310090203040f031b1a061207050d0b0c120a05010303030b01 70
    0xf0004541d43e0220a11428100008079954035030b188000c050401c41e01c3c20000b002ca507595600071800c0c240310040701007a200c1c165000f15800e601c0e01c1d840e50b9156070705c0e10f8a441080d0071000103041d4100c0380014104403c8a42480812401c2a0780c845096a00303400d000c00000d0803504d01003051000b6000c0b20b0280c00c00964082008508200c1c00410700ca50b014a41c254040c00000c5042c40d08500d604440300910b520300e0001c2415403248403c000d2a4003038030a05101c0d0341410007181ea000c011011003115903961403003c0e40f400700503005200200280d100c0c240e050007250700c0c2600c00010703003418811400186120068ee00e00d084c2ca4406074684e250781060165510500c208000140868034159945806041a50106c00045000c80c0610907140e001007000b401415110000226500e500d0301070340f401c54000880c40710940055640f4607003803085d1980700d0016010040400c48480010781c0000c3d00180d071502e0144281c1d002005850b0a4400210fa107589000420034550305101c0e4240c0308500346 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 874630431 1250 874629181 874629227
    0x102010f050906040308060604270c020105070c0605071206030c03020907050f160204060503010905010c0807170f06120d0503040b220605090309032d06010308031605090a080a03 78
    0x1041581d03d0a0042c0014144403c0d040810034541d5120107807070040c12007018219013207228040c4401407815840c0f60212030341c1844170300c0c500140103005144c41390b4800c1d82c1c2c2d001c1c0c0380500c2d03c54001170180600000f00740505110a1441c6400a00428021710b0080355261103061461052000d01c280c02407000c010810700b03110408284e08924100c6891852410703802c44030450754000030b0020709850384155859840c1c03880a0703003008010b405c044d03006221621040d100b40d07154030080c0c2d0824a0344040010380502900051100d6000d103400c41c0d0401d0307018048018201180004038500400940e698001ca0004002c200421400040055012402c8031801800784e8056411440e659595000200850303107400004400709800c10540741210401030856203d0031a1074007a07070044180419641403004d51a0ba400241080094103a0403658000c0603603156503580c401280080280b4002141040010001d5050551301e812650025103090300180c03042807500e28001c1c0168004803440c03114a4411 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 874631681 1250 874630431 874630441
    0x91b0b0903060a0b010909050414010605040b010e0103021b03070507170307020105071401090602040f050406150c020d0c051f0807090e070e01090b030c0301030201080c190c141b0102010f05 83
    0xb050040d000094803601044214219006035001542e07a00701c0c540781882c8c2020001401246040c1384440030b61140204080c0380c848080c4415210246400c40c04207411000310511944a51300a0102c030344080501021350940282040c1140c1c02103006072480c0d4005c1c481845410030381010844000492001103140103210f40c00a8164000d01ca0080c1c6100c44007018908000801c0d007040301d101e640440c0455481d41c8610a2400307980e00c90060074043d9280000c0400c403007101e1405042d41c084d0603105c0304a10001030b070070003011200e041821034443e000800000380300e480c1d0300f91246241d075509180c00701001105c81c009140c980c1c000c0900c4200213254104015000c000600a5000311051411000c140400d800680c0c401800d54811403034010000f0411a03041d0a260103541030360b200340d03583c00141d202e0060311080c0c0c1c05210650290555200c1c02520f086000d140500b9406100381c0303440aa40710b418055906200c100d055440c5140c058103400c251543c0c1c2841a0b408410f00488100824280 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 874632931 1250 874631681 874631683
    0xc0a1a1f0e0c07030e0405010b190903200d1e0308070f080705090a170106050906091006051804020a030e0613080405090903190f08130209070c0c09091b0b0903 70
    0x4050008030b00c111001801009041c4212400c2d40300c10790182c828411540d483d070f00381c41e843d406200075402c20202c1c0403c21040610541d8440c0481c0c0d00b0180a0804000004101080c2e8042e00e4000b030740941030144c4440010041c01500c8074000788a140a880c0c0c611904000c0d1800c0e10041c200400c102440580c502a03e8020f060580c100b0440d14006031190b6100c07011400401c400c0c1c01c121500c2a40c0d0720540f000103415000502654025100004c59807180001c0c040c2d010400d954180c0f80e0071582600f03010b07a5209401800c403d0354000d4062045851010100b0b040364403007102d1800090315100707040404141000f00d2a0440390200344108180c6084d00c0b20b096a0142d80980707031107108100b0104264490400990b2810301300d221008543da0245038000e04916144100d01c004120083c2c002043e42201c511030503021a009081c0090558905004680010034520b0840300c400400401240c0a02d16100301d100710791050351111000040703d6101c510741803256000210010f010403072a48280c030 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 874634181 1250 874632931 874632959
    0xc03010510230d0e010c0e03030f0c03040509150a0501021c03150801020415081b0711042c0f06060f0108130501050a1e0c0503010b0c0a1a1f 62
    0x314520306000c03020300700b02c22100103030701d000c840003070341c0b0030205608504000940c0300c02d0294203090001c000c1500409000e0398010411004280d05030802d01c010b003c890a0030f8000c1c42c016078420241c03071902d62205d000520f03462043e52440040d4081c1010804541070001a0720040c0400b40000d00300756001050b0044140d440d00034181c2010b4a03041000c40d04101a924880a0030604009544880e201d41e00303101644440401080041c8230000410542409848500d018072024400149082029180d01c088000d400d040c0c50340080c1c1c1c070b582c1b1070440600c141030050300d54001c041c2c0b421641c40e041c03c210300d410041c1803018115000300b410f028040c5c0c2c880c032218080c03400c2800c007820150744000108402111020000d8103550901e4104621006550300000703403c500e101c0ca0700d80ca083d5a4145504807201d0a00f9072012400400061103103440c0c0704041d1407648841e00c1190280951039031181410080308103466501d54410060090b01c880e41034907221502000c80306100180c0c40d08034140c2c0c58403 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 874635431 1250 874634181 874634209
    0xc1803020a1401030e011b09150210111b0d0207060306241116181e180807080a080c0a2312070c05070b0c07090c090e070e04050c030105 60
    0x103402d90300c412a034004d401641401019400170041500752034003403507070041100b400d0b1000804003440441c0c2003854030440d00e9100210b0340107145003a8903801c0c6000a05801035610001001441400101d039143e000c02050b040345c3c140540b289220f40000a031510201d0303000350051504000301171180c0320035040e10403002142c001c1800c1c0e003041c42a0f404e4a440240d844500014098944000e122040740e040c1d440450780111500000404003400580841d4100401502c00fa01c492180c2d1030300d20299003101e03007101c9048007000c2d08100d00743c0d240301e41688081d00841e030b02e4501144030200b440d0480c04066000c03003440041440c11159010040152500201c84500118030700010403030600000265100011060f03280001814000070107401b00b0a10041110342c0c0c07043c0c110118074141d8074410b071003000c9941ea00400c01c1d5800c0255030400b6001103644003040041030200007411100b210010ba00462040d207880303054070719443c00d10042d82d000600411410008100410040c2c4440c81842401 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 874636681 1250 874635431 874635449
    0x7030c1119021003060b0c07061b0b040b0c0d060303020f0d0306050d06020d150303020a060b01021603080c0a0803071e0903080708070c030501020d020d14010b070b0a0608100c1803020a 81
    0x603c00d0700001d50007000a60005820220042114481000700044200c10f41c1d2040e01c0d5298130100c2c08c14842440d102d2000010a440340600214000600d05000c0a40255042c000a410041e818008600300d5002c1e40c002c0d80107a100c4007640401c98030500c0710a90f6202245814400b80b801c2c0b03c04116a09000103000340131590000369001da4038040d51041d184440600d0000d2103950b43c90070000e6503a41044d60980741c5e10310385260f68000c4d6000182c1440350145100c036000301c691464035584140d410201c0003158501404002100003a0000001e612506150b110302c0306100340d800424040301015200001840707540b80c2c081c03000c24006002d840c041c0358082d1100340d4604407440c02c1c1020100c15403004003158008103110f200c241441c1c0141040c9444800108100c0325200f01780e050b07159080c411009020010404400407070b9032190050303403100c49040045034181c0e0b2031065500c1d00049100705d0402e00d0369104490358040d80101c1030f010620b0070f0f6504131307500d41c1180c001800d018501d105a500f4 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 874637931 1250 874636681 874636699
    0x10207060f03090609030309030806042a020a0b130c1e094a01050c0307110a0c14040c030527010b060304060608060708091005061807030c111902 64
    0x1c00d00c80d0f08400a440d9000005101000d11450060003a0250034011400324401c40001200c07410107218806050381c5401024101d101c034190b600340b48401c010310650441c0501e00e03141c0045404015400e000c1d180054010201c04a141451201190f05402041074005515119600c0d4000c0ca01541c0036a64240000200070705c0001c3c5102c0c84400c0d10901d61030f8429940c1c044400003444110a0503035041600596203840c84603800b5600302e130070031a08010780300000c0c404640303628820070120b550907031180e007140c441a031142c58070014000c4a500507404c02100303c0e1842c9050910740105a0000b144c1c0c2000c1c00300b820500308050600c034060303645107904202240b000c4520300c0d094004122060b0082c107160b60384d041c203040c0708003c0d00c03043c06103241c41d20500021030b10283c40380808503c1014488060904055070321044805420040e00090340300d51807100c0000c102c07030400394180c01020315032030006401d580140054450011081540321a81141c1d8201e029151680410341c06145d0407205154 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 874639181 1250 874637931 874637957
    0x301150819151203080117030915070c050315061813171e072901061103130e04060506100f120609020c0a031205012106060e09030a08090c01020706 65
    0x141c240030b240d008050307030001c500301c1d88149900002d810b810b031034000404074012100e10b00040e81c0ea01c00c40c085184c100300c42000045801d4001d030007400c03149124448000119580307100003450102c281302214141748014080c81203504c0c2c540e10254014240708140c480519141c070100d0989440c82c0c0000d40300c0c0310010803100d003407003041003100c1200c4030800040b1080c10394200215266001408125180d07203044407001c5181c0540b00001d41c1d02600e840c0840100d82c24148115006001d00c0d03000e0710180b00c10300048009190105107080646101e110026a40c40c15040c11405d41e00041c180354000c081800c1c0341040aa48540300612a207603030700304040c16040c0c201d40e41c402400c050380102903e910105454851900c041038035900795000f42d41c1c00710140d4845170b01004940b001e02c1210740c8503150000404001114035a001e003054012240000c495940d0380010818120441e0184150b400014044904540005801d600800710000130454400000c0001c1d550350322a006180c148005801516 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 874640287 1106 874639181 874639211
    0x5030c031204210206040905041a15040e0c041401230f0f04090b01090203091605030307030e0d08070503030f060909070306021312080301150819 64
    0x601c0e09103002c8800c0d00c2200385024903c01103034651408005139807540050300043c14002e034080340b1780c601490b0400e200c0b1a01d8418528006607003050049206003840300300211340b400d68001031121031420209181c0b01420078a0766000e414424003141d084407036503005048070418401b604540340c0500f03249204103180000b2581040b00407200301194a0117840c40120f0b0328029000103202202d9803264104410700341c00200320355400005020702c05408001c84049c0d02c07040c4110350491400c00000980707a1180b00c002804000548400007010759480c200e003107010b5440003035030340d4a0102c0d10b042a180d0f0400c40e02040c1100003a40082ea49003403100000d8440c1500b04098520141540e446000a40000b03031280c2c101c00c2440000308210064448480b820b0707019504003600d070f6150101075428951160a400200301840042c000d4101000e086199001c00b94100458103c00000000f = true := by decide +kernel

theorem cover : BRFrame.Cov 874460431 874640287 := by
  have h0 := BRFrame.cov_init 874460431
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 874460431 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 874460431 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 874460431 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 874460431 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 874460431 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 874460431 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 874460431 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 874460431 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 874460431 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 874460431 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 874460431 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 874460431 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 874460431 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 874460431 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 874460431 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 874460431 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 874460431 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 874460431 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 874460431 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 874460431 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 874460431 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 874460431 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 874460431 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 874460431 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 874460431 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 874460431 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 874460431 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 874460431 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 874460431 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 874460431 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 874460431 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 874460431 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 874460431 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 874460431 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 874460431 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 874460431 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 874460431 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 874460431 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 874460431 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 874460431 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 874460431 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 874460431 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 874460431 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 874460431 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 874460431 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 874460431 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 874460431 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 874460431 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 874460431 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 874460431 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 874460431 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 874460431 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 874460431 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 874460431 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 874460431 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 874460431 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 874460431 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 874460431 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 874460431 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 874460431 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 874460431 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 874460431 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 874460431 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 874460431 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 874460431 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 874460431 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 874460431 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 874460431 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 874460431 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 874460431 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 874460431 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 874460431 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 874460431 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 874460431 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 874460431 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 874460431 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 874460431 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 874460431 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 874460431 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 874460431 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 874460431 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 874460431 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 874460431 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 874460431 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 874460431 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 874460431 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 874460431 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 874460431 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 874460431 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 874460431 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 874460431 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 874460431 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 874460431 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 874460431 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 874460431 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 874460431 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 874460431 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 874460431 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 874460431 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 874460431 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 874460431 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 874460431 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 874460431 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 874460431 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 874460431 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 874460431 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 874460431 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 874460431 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 874460431 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 874460431 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 874460431 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 874460431 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 874460431 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 874460431 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 874460431 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 874460431 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 874460431 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 874460431 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 874460431 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 874460431 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 874460431 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 874460431 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 874460431 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 874460431 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 874460431 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 874460431 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 874460431 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 874460431 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 874460431 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 874460431 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 874460431 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 874460431 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 874460431 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 874460431 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 874460431 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 874460431 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 874460431 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 874460431 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 874460431 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 874460431 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 874460431 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 874460431 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 874460431 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 874460431 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 874460431 ≤ n) (h2 : n < 874640287) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
