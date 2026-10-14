-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_0702
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-13T21:13:40.066304+00:00
-- url     : https://prove2.me/submissions/4f0f4a44-da4b-4d98-85bc-8db33638a51d

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 126079136 ≤ n < 126258992 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 126080386 1250 126079136 126079159
    0x504060f0e0c0313150902040c090509060a03120f090b070c062d1214040303060f0602010e03160212010504080307120504050a23060408130b18060d02130b09030606 72
    0x80800740c802c0680244056142045d030180000d0603004601c07102c2d070007007080c401c0c035403001c00c0100342070201d11030180720b00c50304001b01b04c3e80d00300412510262031b0091040162001483e81c00d403130504030000d4450800c00401000204841c240740680310461080c0e4400b0352951928400034151004182c1c10140143d41d11908050000c2c9101d5040401805080040b46032501d80001c0c001400280140b00c00000880100400c25600da0310940c00d440310310560381015a00c9460807800c8412042c0c0d041680d40c010000c800a03051050042c404441c03009244081a8848041690a42c0c8094800b240d102c03101006011003150400080a0041001c0d0010001ca29045d2100c40ea00c0306200e4024000146940028600215288484424101640444520741800d1034200783c00e0f4041c614410690030524008900b00c0d038030408603001c030902540640c946644500c100002c0360702458055401e25420008030b50000c03a0800c0c1d48006100d841c540c2520b424941042c5801c003d8020811880307211940c01 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 126081636 1250 126080386 126080401
    0x8060a031506030213020a080c12010e040f060903020d0801060201150509040c0503060c0903010f06031208090715260601021908070602030a02130e010f0317040504060f0e0c03 77
    0x24021240c009448002122600801d50018645604040d4221100c040d4401c0c1541003a00148215100d0707035034020b490ba0f82c00c100040c00e07004d00b0340071070240408500100840d01c04810000e8019004043e800c40ca22416030300d00c01250361742da0044000da00702d095003c413210742081e4005d00510850000b48140d000a02c506984d01d00740d40a01c500c903900010226040c018460582c002921000e004c0310528105070100301165040850014482e6080139206181c00c6c0c1c040c0280300460f60301c001800382c211111035041c0c43c03a0744010041501803050000026140d01c107a0301240100d00251150f0031041c2955030200108141240d481c0204c80f000e00503c14581d9001945004800ca2845482494441880e0045003889802c001400d220300100a0010f004070981c01040303c00082c55000040695071150346941c0d078ac5c244913844da0385082c0c600800215054540200e64400031000c02c0d0302e040e8444c00010f0441d03402d03421104a1300590720050040161948890341c00140c0c04040c1c0e401e51500a5 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 126082886 1250 126081636 126081649
    0xb03010c0f02070b220f1e05090a0f0e0d090e060303030c030c0a0e03060a0c1805010801090908160c06090902040b0f160b0106030e161a0a1707021c0806 67
    0x7080d10007500c1c00240740701701c0e041c100c1800040640f9500c03208401035900d00d43c03409810502d001d601e1041d41e00c200610680000c0c2c0741c0c02012118041c6c440a00307030741d07030a10040c000d24114180e100016103840c586400d0340303024080b844940d00781e07846580300340307041c4210b50412000040c603c0d40240d00800c24090403015070030a4a41c1b12003072100e04c039907a407059a0100e4442c00c881d40c8075030300f5100e00c000740484a1440d401c0030f64500041d0303030760303101b000c40707010408611039164803c02d404541194018000c007801ca0f00702d288924041c603c0146040358100e45d00401210144041d42c020619000920100394401c2012004106c0f6840560800d402d0000503c030074405e1f4145031200c00b100003140303015940304410a803071040e0801040c2400d980d68000c00303000341298003c1345003140501c0b01155130400c00c00604205075100c101200c2c4240181d0345a04c45c503075110501c03c1d410f00c082502c040289020840f0703120322030207a41e4040c14001c890740804440502c800714205062085040c1045402d85400 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 126084136 1250 126082886 126082889
    0x515040912110622030203371b0b06040e0a05060105010e0102062203030603150f150609090e01090b040f020a060305070507020d11100509030f010902010912060b0907030b03010c0f0207 81
    0x41c213500b00d0380012440c059242d80305460724250b402071104230340d5940c58590b480b010700769180060917011a4089840459180281c688021070945001c01d81c40d0200340803100c0c40f6440031000d00005104a0141003c2e403800346030000032030b070b1944000018071641d64070402e0707028042c000303000421031814806650511203494820381d20350b00118000301014548a5007000c070055802001c0e69100d00c00081d0100040d001d080f82004210303062910f01800014100c0402d4215809951513526103414980003e018200c0c0c82840a41c564803030001c90f02080e041192680210300c540c80c09101d2150502c1400140000303540301d6414185400100040142c116040b29145036045401c0507040d881c0d03250007030203051014400c54004036101c1040800640003c0140f00f00d100880031106d168425441250981c0c02c000e100a0002c1e01c0360008000d80c0c8a800c061200544c0700314004525800c1c44008640700040440781e581c0042e40f038249108a03414280b007030151500c00e911b004407840c01e02c2c00d006584c0d0703901c5 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 126085386 1250 126084136 126084181
    0x60b0a1410030c031107050a0c050a08070603020f0408060c040f09110307120e010c0e01090e13080a050702040903030516090e2e03030801080d05090d020405150409121106 75
    0x443c40000d04441c070980c444d4080180d4010b107641c940c0c2590410f40d40da448910b90440e070001c4081c13408102c0f880c2801d0030500312445c1c4801070007543c0c1001400c8010b900002204654035a013407001013000501409014131600b031001510b0340311031408000c10b90040003a4030007440d9032310309076400c8032105600c82242e82c0044030342041c8805000320703011000107102100c1182015460308094014940e03010104440c03022090361005c0c180364451001a480c95415140d003646101c0040030170000400da0805410110b686090103070506030907402107029210000001c500080e514030401503002e480300d6240103a01410b14001d44071500f01004401c500c0d070050043ea032860540100c207207072000030b001c0c6c80c0c1c040a100200c021407580c0d40d00d0041c1c0954001c1c09440d8044c095001102c1e58a40302d08156501e94000a083c440714948a8003400002d1501409031075a4986004c408049900c95000c3d03000ca59104000581d070703040285100030070188040c80000140e4100e207090100000b0040c2500c03000100 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 126086636 1250 126085386 126085391
    0x7032a0c020d0311100506030c1c030804080d020409050711150105010503090703020a14010f0c05060f04150504030e0111011103010b0f04031401020c060105010e0102030a0e060412060b0a141003 85
    0x1020f080c255000c0d030b1100e0352082c0c03e109200c80300034040340300d8002c0341c000e1030254103d0b4103048103602003003041602c40d4899545441e07902c0d001c00c00300e0311036849a60003c0c000d0903814a0012403080b004181e0344240c01c1440740c05e403101c05000d5134070b5004410040f400d17055000342644000c194074840315940c043c032413541000004000302d95080070511605005640c01016103207040e60f2000c0001140300034404a50108100c01034003860540602c2d45401040da0007006001107a4481c07042e824450000303002694100600c0c20100c0d00340416108050003903000740c90700c0040c081904001000651025080c5006074140540200640700e050300f5a0f064944d10103005490310003003618801c2500540d40301814401c1c0c0320404000e005019401032490b03100c200c05441c032582c3c84900641d0850301041b40d140c01a481000940b000510601003558841070051960389825031700d0400109080c48010150303545655810440e010345880d010a200501d070080ca411502012040099946015400c0080c140343c1c = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 126087886 1250 126086636 126086659
    0x6011e150e03030906130326031f15020a061a03030a0c050f010c0c050601080309090f07140c030408061005240403020604030c0e070305060913020a03060507032a0c02 73
    0x10b5051003980c03158000135050985410b040c0740c2c6006003040c40c1c44240c94015242c10420035004031000c0c2d40003902c0d07040030404c2c919100c60a0f95402d080900300d906112104a510104009030064068284e92503107038014462800c080c2030004c12142c2d1032105078441300041e010050b03540c03004016548509898205103400d030002e42845418001001c10b903d031903520f4040801e49690300003030f9541d800b034001c40c102c8d4401c0c1c0c0c0b1507483e1030703036803185040c0c2940c40a0300200181d40d8034203155010780e000320b02d440c010040400c140d10100e825000100312080c4d541010406105401003042440d600079104101c481d00c183ca000c020500300401c000f2540782e0f00d58500090361031200040e0440307000b1a030260402e95115500d04010703034803810034052a040320001d1400302e01ca051103401078900070383d0b008192130039503100d00b182e40c1000205140201d0f0070503440c03c1c0000105d0710b144259482110389440101c6e5051000a610844030300d540c5d002c1481024002c000c620240e070140c46e03041d0313060381502d01c0c41088 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 126089136 1250 126087886 126087889
    0xd020108011a13060908100501050a0308090402070c0603020919141915050d140717070903080705160503030406021507090302040c0c03030b0402120f0a090804030506011e150e 77
    0xf03126101e104032aa000b26180001c2c0158806200300480e8803440c107846070003c10030402c40c140d0b5420301c00e55a0280f0854000d10205a4150042408420040c03005150034000d9440030894109944180d000c2540804c49155508040814442c24148802c5207503400e424800d000400c414406a603d009600d000c0c0681b07810403002ea0442c0c09408603035a981c000ca0545130008110368860252940400d051140b010300340151011501d0041c440d64a6035841000405002495840010407240400072110000400b09444400030280c46024501070f0100c220200309243d644040c079801180254801c001c10041b40d540842c0703030780c2d0b4075800c0421104a6140d00400311901c86c82504044d40c02441c00d49464100c3c1c0e084100c0c001c030544284c80034441901180c04200482c0500800190109200c500040d9543d0311000030503070008480800240e28a2903480c2c14015400030380084800340e10210041c801780c100301404081d94005c03d20200007070f50514241c10801038811265809010001c08008180e = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 126090386 1250 126089136 126089189
    0x1703100503120a0f03050c090111030d020d0e0f0715030f0b0a0b030f0105030303070c080c07120b04030801050904032a060c09090b0a0807030b0a0906140403030b0d02010801 76
    0x1880001d08840c10800101c0e00c00c03916900214819000c203034996001c580c114000d0040a02c43c441c6501c03400c0c200443d01006451800c40c00f080c4103441c2c0030800014442e01a00e02c003805102c03018000003c2d013400c1704103400c1d02d01791202c04101f901d9402010200b1603048a0076440d111003102d807901207081d0b20070210000c0075003405044e2543c00842ca074000715044503a0f074091849503d02c5401c80920b07980c2e48091644034403054134034000041c80c81d40c0d2203000c41c518000506030780d2101c0b012201c3c601c0d510344042d00051900d000c121042140310050000345a07010b512903000d080c086070407501c68141030380d000c1c0c480c2e0000401d080520750301040596042e481418040c8410350014030611111300350f03e00092200341903006096000780341c90b21003040c43c240740004900b5140620004c011043c04c40e21003110903640101011b1095403650300c2400051b607280030f0310380c2d81c1e00e182c1012046402c1924004c2c058a005050303290080b0760100c0b201c00980c3e071058100341102d05114a0308076490324172000107103 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 126091636 1250 126090386 126090389
    0x1f0e0105040b0702010f0b090610050c0304030c0f150903150e10051803041211030a050a0602030a0c0804051e0c0603150a0b0310092304121b170310 65
    0x5952904040005000d1007142c050310458090b4020050180410b100008407503074020181d8000100070001101410601038005c0e2102060030524104030582140524640c0310745c200315840001007201304101c1c0081c4110304060605005088140150010000e118000380d21015100d1541a03041611080c0560710580e600c80300d44060710341950b202d0019002500007985c0b1003183c00d00c64100d99003420307c00320646040c0c842010420003071000356290350644141040e45140d041c020350f001840001c070308002c0038071114441d5401607101d01d8041540c408aa401c4200300061140306010480045d101049010040322141c01c0491a000a00810340c0750102612000750000000000d02640c0307a800742c03101500143c01c07201c4d0042183c591809040b03901080d0f44081c421100c956090068200d560099403501e950001000031915003a080c01d00d0001041c4c400b6550180d00b03c43e0000190742c480f000d0400d4034a00e2124001c0d02150b552544c40d0035102000d0381200050110100300310150140c0043c0 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 126092886 1250 126091636 126091661
    0x9030f090d15051e0901060b0306040f060b040603230c0901180b0f03250f0e0d02090124021b0f04060801090b0906060d020108010e0403030e0601060504080f0f1f 71
    0x10192510742003071003202c4e510400c0340003c5801880000c81e0318005000d01020741c0d07036108a2604649800f02880090710480c0c0c250510035131119408a000c034040006007004144c1a03801080d802d8142d500c580110000d03d04c0381092140e00b10400c0300c500c41c00c400f00d42c51404c0a01c0c0c00c0c0c501120104940c800a40079421120303818100050105080300c01e08055409480040020038a01c1600840c0c1c000294100f9a6207002ca9045003150300a507010b01c5501034045005401559142042c0d030003e000c00c1000d0704405c0780d5280c00071110650269414540401a40f103000a18031500141200c0d000c2c0e010900f05a0300c203003a03c0c0d0001e10640c403a9040600240301000c004e0040d4042403504000158080f03031140c6030b83c4140070016109240000b0702c41201c1d901a1550501a4240360b0419072400006205406050700c6820111802e00f0400010307009041039607455880d2800c0000c0942001c0c06104010102d90004240c0c810381840402d140040482c09c00c410f0250301442d83c0341134058124043d908 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 126094136 1250 126092886 126092891
    0x12140c130807090c020f151603020412030314340302040b0706050708100515070f020904120e0402040e0a18060c050a030501050301020309071a090904080d0509030f090d15 75
    0xb43c080981d800001407044190242c42c2d465400e440050340d16007512040c141080c812002041049440d90542034180c07502c1c0c1381c05450300b41c507a40400d12515080c607044001030780c0c410040b40d43e285600c0d0441d400c5821410075810340c03001ca030744012150359803070021000555802c003110302060103681150001d041505e003107500c1d1035142c1002c800901044a01001050134400000d002410800d401c509460340104802c1114840c4a100315058004100c11100c0a0800400c54050307614030122a10640c403c0c80d008900b1076400400a0090300c2003600c5a00541c0103200c280a02e5101e00d80311603110740c074040005048007441030050104a00410050045403130400c0c03001003030781e1040040040c000207031014007190b6070f1401454200d1004031007941d419000031405224081081c810f0040c4601c1401d10039041490617000151101d0080d60111418040012483c030702c99060b000ea640d12118030005540ac1002c0c1005802d441c5c442c84c0800c034802e01100d016041000385100b40c00030400c020003000c = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 126095386 1250 126094136 126094139
    0x2a030b01120c05030303041707082a01060b0903100c0e0a0e0a0c0903020907030c0504080d020a050f0a02010903170f0c030307030b040b0f0405151c0312140c130807 72
    0x1800c1e000780c0301c0242610121080c079808625810000103d900031035105440e00700c40c00307440310300e511190480d400c110b0b19a64200483c021441088075040d90343c10107010b1200c5008428081c04d4211507059200079500038003484401d04c43c0d45c1c00b080d25800900d40303501c00325809888140c203c0300280d44054041e80403000c8440070500007060b100442c820b500704031007003018018581098034194050310009508c0311600c0300180b030051180c0c01c01c14a00d00541085130a10380c840843d2802c001140c1112030069020212507000c1c0030042141c04118108000a4941c076202d42e00001e1924070710340400b078001e02c80d00c00440c030707100721a00440d51300070244000ca6488801c00700c03159459500030f4400d00c0000e4101801000140350500c1915040f060040c11444059030742402d010107818001e01c200c1039858000b202988588030b003c060140d41e4040f90f0f01250340b200030b20f4041d2400d6009a00c9001080c68000a903c10f0b0042d091120340200503401c1298450071803018a01d0f215183d608450b03a039010700d590 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 126096636 1250 126095386 126095399
    0x41a0d05060f06031903051c0608030d11090a0510140703090302030f0706020c01030902030705100c1e05060402090a0b0a0609170606060307052526072a030b01 70
    0x841d1400380700d03103071903000d026201ca2003055940c4640d01c84800b510b403024042c4000190180d0010110515907960800c031244074020018100ca80650080322142c000151418001302c4038481c110180c2502d500203810440d221000c05e5400840b40103040c0280301c03041d00511071501a500402034028135010056440f5203501e03004050541a1004a01a10405180c465070600201d00c05007900c62542c000c001600003040110041c142c0d03420280e03014002c1c3d1202107100e4845009241d00a0181d8803031801100c0207152030080c2c1a402d0814080741618089820000342d4042440c0340c00a07011142038030151141041640145040c102059100d000400009507250b004003c00048071341a0000589103010a1031f042e80302c0800710307022503000c2000c10000782094040c4014043c1d4000c1100c2c41c00f451000c0c450500001d4a408400f541e40501040d00780104120528035848a100001c4080e824090700d59207261220b0500c0c0000c684a0040480c0c0108401c102d860002c021600005002c0032941d41d01c2 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 126097886 1250 126096636 126096643
    0x70822120f060509010507230c07031a06011b030503060406050301021602130b01020a1401020c060901020301090c11150a0e072304050606070b070e1509010f03060b09041a0d05 77
    0x4404642c51800c003000580146818403d00c1e118004e591941c5900a01d6001c4500c0d0752981d0010362280000309010914049000700306250141d0310a039800c070550003074400080a104001081030b81007010901449228200f5071410400050381402d0140d203c0e155940040c8c064001508860380640c4040780c04000c2100030000c640c4010700aa41d0300d2084204407858205446410345024050b900c045001c0d40058035162081c00301c2e1407020001410501003000e002d0a090707003540d1424250390040014419419035100305081100c1c1420620212882e0000700ba40b80c0101803145000e10300b0040000702200211382103500d5070802d802c291400b450b2540e02c04911800000307100107048640f154200c180741458401d01d802641c00904031410f01b4031907a6400d90158004150302c040020001c0e0001d2541c650b4880c010301e000b1310042898079a85220001400c119840c00140101401c0035030030440b007501c1804664031102d09840200b4440d90406220342484051105541c02c840740c811000140140803 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 126099136 1250 126097886 126097913
    0x3081c05010902180d060213060f09080303010e0a020a0c020910090b0f0607080a35090d08011202010507050706080414010506030c09060f15040f0b07082212 69
    0x21a000c0000342d07215184002280521801c081c0c59102c0d046601401d1300c3c15402044d1138a00c50000545020148110442180300300e41c403640104030303110486c1606a40058560740138000640085085615181003205000d0f000340011860b641d00082a00f070300c504c40c070f010501103500688010030f02d06142600004003c428403e0b2080b80d480c05111106918001c0d92407424044014861400c0c05407580310002c5541c001d003004000c0c04400400c0d04446200b240351482051009481c4420b600e440f1980c0b03100c0304400a0844c07901c0d802180c1080b035102c0e003204800d81584d020000141040ca01407006903594892624007414501c40d01e04000341031030f846502c5a1041c0e00c0b5403680c81c08120560080c07401d842003034407821b5140c4c000500e0f02619042c1290540e0344454004c04a00c848403550021502d20344800340d01410a4100040074814101e0721025100104003a42c200c40c60300210340c545003180d0185c2010b03040f803030300d894080b0950007500c0200000944801030301c040c0e55501038a0840c40490340b0 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 126100386 1250 126099136 126099187
    0xc0a0c210206060f01020f030414010504030507080a110f0a0e09010204030b09030c160b070204150b0703020105060120061807080f01020d060f0b03060910080114010914070207140a0308 81
    0x10055800c131254400700f1a031841404010045040074148003150a40c03800d00310f030490400c04148070020200e00d0070895203004000d580d0242007030300c5090030012000d1015030496402024a000b05c0880c1d1303221141d661b0102c0e034100c1c20318592512411002e074007a11460388090101e0700042c06116a041006c001005032840d0002124441580c2d10034455240041d4410a03400303440c140300c0c000c0507082580140316094903695244c0981d40c0c8840100b941307600b1113041a8010b079590010001556000044c1414044100c0542d200300100303181202d503600c20003403041c0c40c460024032a02201900c1000310402401090f016501f0803c1c0e00f540c428000e42290404400c81d900b802000244d11400400b080c040c0c94070140103900c3e640d05c40040c01161007002c0c188007a0040501030009011900b8800c1040300c40b8141014600382d41742040c03c800b5203d00d1440008440b40c440148100c031a000102001200c002c5d0b000d0b1030000407000006404030b100e5074400707000403000160700500c0c80001820306405645 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 126101636 1250 126100386 126100399
    0x10e070509010504271704120b0a110a030e03092e05090105040b161203090501050a060b0a0c26120f0103150e1f02040609080102030c0a0c21020606 65
    0x26104100410750311a200e517107502a02e400b20a04170b0170380c0c400c0d4010716503001d008006030f010310584880700507901590080d0880805501000d00708001c3d000342e50b411014400041c00240300120058509100320501c0505050b83d40c0c00c8504c24920510039aa103055000300b00404140c10300c0500340990000d6100150598000600e030090b85000d101592403420b03040c2d40b083d08142c00c098400c0c0c065132011440c9500056140700c0c401c00a8001100d52141c0e01e01541e022846060a2a065003901c101820b0f030115103080c04802d211240d00c00b000c5e00d001100a2410007804c0c025414841b0f60f079401041c0240030f0f018501e80005c0500001c90041c000c000076507810013020f40c0c41c458444005103007030100821001000160064a16a40c6c000d07c03204400c5c0f600b582c5a00c000c03020f0500ca181d04070005900d5054000c036003008a190000012801080e0040c0250300d1490144204900d610884080005003c0c0c00420358040c0400d985c080c0090b0340c1c130741c00001285019603c0183d9100000c5541074850311 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 126102886 1250 126101636 126101639
    0x2040b04241718060108011a090402130b060c030c0307020109120309151205040507050103050709140405040609020418060b0d0b181609020304050105010f180b030c03010e07050901 79
    0x100311000c155044942591105440040444000040341024080030f219200140c0103410741c0d5401d0005600818030300700005255401c01c1c2c2c80d00180316030602ca652007070031362804010241e11040080001c003500300000142d990420780009189010301c0041808611000c034800070f000d0300c000b00406006000341c940780318855468420032a070001500c1c00400007a8048001c0100c07031408940059074400d2800c060b607404a075905108200d800498081e212980586001c020a503050702c18545c10140c949441c0000900b030020700200e080f10501414016559800080d092018130b40c003000c801d950042061000d80b4140002040c82400307008242c4801e8a0000c50750014642000c0e903c1950354400e5040f03540d941c0c1e414500d060741203800609280c0d4003441d0321640e1440300a0306d07041c0103041e00b0103006880c0d0801d07040060031110140c00027185448048001d0120348800008080505426000414000701c10310120b810805040503540d051740c01c0c01e03049140c0c11000b180c1a0280d0310143d8001142d0b030b = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 126104136 1250 126102886 126102929
    0x307020a02090f011503050702013b19120219060504060c0206090c0402090a21030e0d0c090b010201091b0303080604090b1602070b040902041503090525030602040b04 73
    0x40f20a2040400c1040ca4004070038902d802030700129440011400006220f021781d880350710b0720f008607445007031071840362000c020341c90b5000405000d44030138040014042c480360520450610b20300c201c0050304002040e0b000000c064403c1003411111201c3d00705103c0a9021031801001400d000e4604031800742c10490300e41c0440e0320008407035116030244e00007403000b2030f034030740038840254450f004640e0408841d1a01088918520f81c0c02d000006048a41d18240600349c10000c2c4031940d05501340e0b11410160013144003080460340800c00303541c1d85c0040003036440301c4440141c0c018440070300c00074000320507400c20300f89411600404204980c042d4440482d20380e01d11003080308566101500501000180d80441c1340c0400c000404c4c0407800c010700450b0040b0f6268026132010f60042d901030010303650009414007800611026007070801110342428400100a9554180c6840250319a01c104004010300585c03401c100d0b0403094004d58020300c045582c0c586a2904a40650090003140e258007501d207030b800f100 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 126105386 1250 126104136 126104161
    0x6060f0216091107060513020109080606030303040602030901021201090608010b01020102040e040b1e13140c011d0a0317030105010206010501111504081b0109110303070c290307020a0209 82
    0x96003001180e52807654200300c120402890201c03d01030f0075980034001d01c40082c116114081c000c004402070001a4440d07840010211001c41c0c00c18519900b090040c8503058800205607238110380d00c01c0000d80c4aa0b00c416103503009004a0442044421419000265800499101c0700560386140001c1c002813080400680c01d038881da1042d0000700d07050200240206450b0458150442c0c00c0207031048106000721081c26041e403050b203440d001c40d024503c0d0b9404000880c0d182c1c1101c856800c0c0507140503850300002a02c0720440e40c3c2d0758540680141100f40d21a604d04034080095640818440d90003803889681340610341003400b40901500c607003000856190f00900d0400e110504070001051071401c60600610b015401600441700400d042c0203000e602200c20706c1c1c51507006900c2c000059540c40d0b906019203c0c240d03200c02c2c83d010780c20400c00a400b00f8a16840903068590f10b8140c2c00460700c81d420350101c183d145a0540300c403102c000c000d01c000e00da400304001000f00d008940b441c1003502d03584c254207031 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 126106636 1250 126105386 126105403
    0x5040309050406170606040903050f0703030b031506010e090601030e070303020f0d02030304020d0f0303111209010b0f0f1504090603080a0f05040e1f3609020109060c0501020c030d06060f02 83
    0x7131039000e8000161240303880e42000309628071901c2c00900b0110351400740b842c0ea401c074142c1100403944411031b43c06182410820520180420302940059090140c00a0320181003450309a004201e1000060b00b2a4000d4201001510480c0115000d11b60b590500035190090000d1195590080c2e0b55804880c42c400000e4038080c1e50010401519400965207024068040b524202c00b411b841c2c9500102401320350303001d8601d048a0025041207450080c02c0e03503003182c210800061241040d05d0400c505502c900d02d840c02e003124155180c1070b0a1854503000b226602899000050f01030406001004104a100162600042d1502c40f110300d4007450000340c801d80528022808110648400140c143c08100c00c101c000b07018075400c0c003649030380f19003402091401c00c00c009000c003071459014402c030102000321114000500c0808102d070984a40c0000c4c001d04481c1308480c100010844540140706080d0f04489110500714101c03541c80c00a031903a180504114445e0a010503143e00881d5065070000c2820729 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 126107886 1250 126106636 126106679
    0xa0207111008130302150a09050f07180b0307090f06060813030c11060d06030c061b02030309220603061d030c0c130609020f070b1b04090203060d0605040309050406 72
    0x140030b9a100c242001408400b120305404501c40d84a4851300409540e106c54024180c0d503c0c08990800141002450048440ca1103d103507072240d00200311341d40c51810841c1500304500d41c0410102c00c0480044d2511186402c19004c2514002c000302640205500031011104a6140c080e0b0310359800e18020414458410042c02203a154105403000484001480401c250001c0c181410884450148011201160821601103170740f800c06000094004240d40031608a00391000202401680426103a010704841d0500034414813110b140d401d1001d10543c055000c2200007001407030764071304000700a440b080094400c54003121102000c3c104001c02240e4507001800001d100051038a4180710901000c50001c03544141d940c600450300442e103000900318012583d04040d01c4110508001703846100291160103000481c1405481c082c3c000d10907241160301030360b130042e1690303a4003010415140c071000d4020b02d0349280a040204040d00a19040f09032707039055500300601c0e42c544840d1300e040010340001c0c0 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 126109136 1250 126107886 126107897
    0x40308040f03140d0c0806030c1c080702060d0504020108060414150604090608010608240c030714030103060f0b0102030306151b1501090f020405010c06090c0e0a02071110 75
    0x40c04100d0005550380030038071a02d4280c00c154441550303c0d01e2900061900512aa12040241031950b072140065800c20401c078068185402c0d9400010b091810100701d046603800001d00c14030901c540030051360685030700034081690740c1c06280e8294005050440b8120b000c0350b446408120715003060f20402071181803c1c075000b040703502e403c0400c002000c286010340b40d00c04010000800d03c840c0d140190802408503a0001c1035941c00d052400d420001481018020319100800602c900c820300c06140e500461070b001065a00c1c0c56005003141c0072480200700e400540c01c0000004200b0401d580100002500003000300f2020028100480c1c491209407405903220b0b035500e04644070381460000600d01303c0922003080c3c424500c6c0410240c201040114a801500146401081022845e00401e010611440340861074107090100180c82801686c0c0050051a500d8070711808000b8204048400342550900e4805107191000c00100654031820007115a0b03040348070070481c0790504502c0440381ea076064076034 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 126110386 1250 126109136 126109141
    0x8010e10050906040e010c020307061103060303030c3604050a14010b0a021608060402090a0603030801090506040e010509071e150c0c030f0804030317070e0111030c100605040b0108040308 82
    0x200512088003600142d03100d0b545203414101c45c0d400f4400c00c400c5000640140d03844a100b803c100003100d03448900c00070550300800401025a4001c022250b00c0060292103e440c0c2c0360500703000c03603060030f5155a810b14000c000390303c0004183c2e146100900c25001c46e000c0c03040b035075544600b0003520003043c0f00100782003c440040c03008141041c0030741020503040c81102d4035048810740328a40c1d079007240d006d507a00350060380a110560600120066000c2035049043c0036144c51603600030301a55052142c8149a41d0f2400401c80503541c580040c106000039a00170301460a001000350f88900e15403041c0b2405440520b600b24007407008002c10011250030907490744e0705140002040d1141400030702c04a800307000801d4007100003401c0e5100720304054003c1001a44807400c51401600c4a16000d8004140d45c1307a4100f00140d05034801044400e6010030310f004968880d0750321044e4654060101c504840d8043c5141c07050942a41c4d6111008643c4111800c1c0000d007005401542c030351070161805000038182400 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 126111636 1250 126110386 126110389
    0xf0903061a040906020705071502151305010510050f0a0302010504051005040b19030f1a0f061c0b030c040603080403030804020d02040507020a111c060e011803020d08010e1005 77
    0x203124916030445090504181000003400311000c103c070843d030b03541d4041210b07414444204401c4024000300440b241402da215207000e9501c8490801080140c411000041c150010090b02c01031050f6000780240020708201c2214010310b4440d020301400794240d828040d60300d2030062a030380c1c11a50103860b12490181800e040c05411a19140a401030010400c400a100009000180007240c06110300103030094240c41e0050640f074841d1620706141d824240d40c0c0458507400440d0221a44048620000000191021034000c1c094118000c086140050500c90021201c2d0000c041000045003616604d22142c3d040200720742c4240805840c005042c401440002d01a80320b41d030300140002c000542003445039000406030307403080301c03a100140c010710394120401100034070b01c00c06100100c900c5044055410b103600f0000a031420054160ba489a80c1140c7c0d4610030740c864030003905072504024820183d820043c2da5040a400d600d00062141c5000041029000c00c1b064080c031120100008840e24100 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 126112886 1250 126111636 126111641
    0x30809030f0f0d09140304060e010e0906010e150c010618050103030801061107050303031311030609030a050d06052e030e06011802090a1e290309120423010f090306 72
    0x418140d5980c0c0c0c3c503075000412661740101d105520040029651907007801401845ca680c102c00e010b0610003901c03149231706641c0b0618031503400a802c1c0ba001d03064000003000121000c494110990088000107444252201d041d003110060350280c400350008651001c4d210004c0329000d11025001490b11401804518404c401d5001490000001c65080c10784a60010341164410740e005a2188143c4020104108140c0c00003041050224060801880c01c005025142d04c1100712000c10841c2c0010383c40c600304444e91198001d0b00024001080f2003a06c02c5401200040201ea44c5207224039119040700003500c2400345010640d42100507105592900d90400c0ad2562103201c411070164080c0402c40c070645070013524100070700300708604948010003500241d0800a241d00700413120400d001d180d5111451448543c003c2e0071452030344559035914035444900304a00940b0b02182090700103000180e480d0a48038a03c0201e440024031060b8405000041d05c03c0b200c2c80140c10702040d91800104081002e95 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 126114136 1250 126112886 126112897
    0xc010608150a0c14040915080a0b06061b060103051b09010609060f0504170c0109060504080a08071112010b0a05040506131109040f020706060b210c04050913030809030f0f 75
    0x1303003444c2d4490402c1c6000c0c040c49030025000b14402a5544881d402440149074050300101860806882d5138803141d00d403c403018200810300f500842000480d031001c062105c800080c4030f0520310594445503101d00c2c00740c3d125109941c10302000d0b40c200920340143d180c0108580c0c12152191513900c06180f501c101a5540c031041d80302c640174818203000028505402c10444040c00700078102400d0503400d50800904804255003000c410418180406d0000c440d00140078907020b0f82246015440e07032102e2904012000500503200e4002c0700340251601d4085c1c054100160291084950040361900c410a06c021135100300c40301c4e98000b0124041a60b00702160b8407850701d0501c1901d0301c524000280d4042415240500d40420900b680080da0f001400400d10903c0c1c0901081700d0954540f21103000307074103035100115104194858104000c42c1e00d42103200d00720ba00400c40640f41c04400c0ca0301d90b50f107504c0c42020010640c041000743c0b0004a0750300c400b10440e0816041c034100740c0e007007002000e5005060f4210 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 126115386 1250 126114136 126114161
    0x6240306040b0714070308041a07050f0c03040503010903021501050315130201020a020307060f021219050c07050d0602121b16050c030f010203070f03090201020a020105030402060706060b0c010608150a 88
    0x144290008620603480041880c5c501a84403080e4600b014903000880f131042d2034030206401958400e03c501e40e903100c0211441514100019516401489907072400c6205542c80a50b2643ca8099080100360b0041307214400d00381c1d03400f000c94960381e07914180741e120010508110018140e0400084001031620803d00e0381500610444122480550110b0701c2e200312500a031010507051441050000e50401c1081c1600c6088088181803030000303000c103c2e409510b88071070341c24000046010740940314200f29600080200a05021984041e0304241c8000d41c4810b0850640c01070110000301c414078481c003001c003000703407691400d840c00003000401c519600d82c01c00d04079414001d4040c03581e02d55908000d450003008804000581e2410f10103005000d1406040d11003040c54245041c1401513a0003050f03000041d90203003010b41d40c03640d036840098607a01c0350607402041c1303501c1c100c8017052100f100710240c100480640c00030441540c0340c0b810160303a0180859488030200918000a01451254000d0203c00d840d = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 126116636 1250 126115386 126115397
    0x14030c0909040506060f04020c060711030c01021215030a0c061103070b0a0f0509060f01030312060b0d0f05090304050a090c0c080a0509010914030d081005100206240306040b07 77
    0x10003200188080e201600e042e219036100a0902440d890310005d03400c00710000715800c51600006411851b03c61000400541c288a41034841c52503c0b1820300c00c41302d0090061008542d2002480c0d0500300032001903030030360b100311640325080c10340d4100080d031484882d800c00004c1c0040307482c058080703801e10310054010301940802e00c00d2000048041581c580609100d11001c03030003140540520381221001440000103900450510064151008060b810740790585080c500c03030700d29a83c000c0007410880c0c1c0400745003200010119103110313050380000d90003084032034140541d07216000e1156590107240a200c1d4042903800081001c18030590080c2c80b144041c2c00d10000d180c1d101e0711210400d4101101000c042100000c0c440b1076903a0000c45940030f0410200c00405407120f25000c2546c0e5070703c051129040c4051000417480804000400750001e110041000c00300900c050002505c0706415034024100e0780f1820a40280e400d007182c90301140c0b12010700100202c1d503e0f51103014035150044d00b041c09001 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 126117886 1250 126116636 126116647
    0xd12020a170406020d0905030d050c071205030c040f0b030f10050609010c0c0803032a040b0d0e010e030301090c1805030a0b0703110711121b0423010915060309020114030c 75
    0x440d000e400c481e14011f00c00396490b00c1d01c9056800a807107000385240505241008104001246012041e164018914003682c881d62240e100813018070403500f00d0b1405e02c01d03109000410b6082c00c030003113115074080c450704099901c68281440440c0014010254072200a100f807000d00d5100d05440d0886500620040b28550b54459500307055a0096a4501d0341c001300e15200e032655980381200281052424100300e03d0f01d49450482403403030261181c0b00901c0307512604035910010003504107440c100300600503280d076540d444086e10700070541600200c010031082c0300d4440f081c54800215400b04c40000c0c000d032100410a079508500c05070700401c07107824107079520441408400c100003d4424a0320072074080a42044071010805900c1c4902aa2403547d80600095401940c1c910726400d18558159808100c4e01c980340d04852081941c1c02c0c540610088050000801100d0381e0000710103443c040f182104010f4940c0b03c200c06039403581e0806400300320b08525024059444030011a4420244469030741400c = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 126119136 1250 126117886 126117907
    0x708150a1508010501020f0d080c0306180f0907050102011b0c05120a05041409151e0301180317040c060509040906020d38040507050702030f0d12020a17040602 70
    0x20000c1d85045400500c50380018005540c04120700741e07070160010018091007010040050134003c000303140360300560000c008210f99403030f501c81e2281c049610440360b20310346ca0002e041c1c5076403401c2162013042c18420540c0008281d401889913500103400550031440542c0c8045040d514051160002c0381c0324811801050300400d040005424075080e00e9940c16a04d519141d00910641d407000301d128864582c600a02030400c040c410740d01501e00042e1180802809200226a40c14100c403401c241c040d400e101c041004040d624452b44900d0740305e9201c0e136800b209100410800700c84100c40c0101072010741802130142c1405440a080d008000a00115805151355138020030f0303801141d0384038011a291080f49010300b00203c40c07402502c07100d4542c0c0364092030703c84551001045c0e00321018006d50343c90303000c00d13102c501c14000c86100700c0d006421600724800c4020650f42d1a0044900c4600140800d8440304001c0c040e8000c8900d40c0e0a2660390949a40311000d401702006000b030400c82c1c00b1503081004a031036 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 126120386 1250 126119136 126119159
    0x11060c07060e180114100e0a030f05010c090803070305071b090906060618170c0901080313091e0b03100c030c08060a030206070318030605010b04050102010c03050708150a 75
    0x1401265888442c1030359201c042c00420410355445950709401c0d207005200d882c203081800004000b040340c9606175104a100240d0b641c1054051058101d0303c8504040140303c0083c40301034402d4820070007040b02100801c0c0494205a0768010020070b90000c11250703020a12031006440fa150041211095425007031101c0022204154085554203454a501105211003807003070000404450420741d402900f40644e0040e11a924061321450f01c443c106da0a45417002080101c2c4851000f400344121941c68451044c3e83c0c3e00410751040000b10b21030f402141d0b840d800d0241d4032003414820000da40081646d008400600709082d0340d40c2e09803058000d924021046406407801110303154a0001e00340c4403e039030007005a440100101e025002401003080161504400c441d1120f4044c80e0071072464000c110030300c040704c10a52001d050b884c200030021600c10400c20090080b11400d0b0001c100c402c0c07040c0003d90035220201c403054041104000062450004001600c501c05002054540341c83d8644005020 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 126121636 1250 126120386 126120389
    0xb03060d0804150f02150103020a05060c0106051509090c120402040e03070b0403030507090e01030804030303110f0c0610060309110105030903070203102309030f070303110315090c070305030411060c07 88
    0x139245004a1408580500c1402080303810410310746515030450b000b00d0704842280c0300f054050a070000c0d42450f049000e51006010b400c0080c0010030300c0300042d1a0300ba0940005007070340e110300408804112400000b400710784018042c01007880c6565565003c202c0100700c035030016021070004100342030000301c420304028800c034030a84000506081001c40280010f005030000010018024014004194114242e4040ba54107240202d042c00060f06c0e4600c0c05e00034100904c429050104e030f19104140b010030414401d40c219010141a1540c07090110155a042003020300b614244905210055115800565010044104607480e01c41d49034081b910f02040000c0307055185a5410700b0024503040d08129401503080014014401d04203100410741b00c0c440c040d8481e26050700016000101030003038001084440c200b100305500e03441c160310880c2c811101a4049442110b8000000d050b8080004c02e03102496010781d034140c15540c4a40d5401180588000c005510020038400030140140412a000 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 126122886 1250 126121636 126121679
    0x10306080d030f05071407330c030f021c0f020f040b0301030209090a020604061805060a0203030a05091b0d1515450608010c020a02031203010b03060d0804 68
    0x110358804008860440c4e0018042808214580b075031000703c141c1c20710a541c1d41c0ca400c181010b0702d91040c04103c1c000f4030f82421300c4044000700904440074100342c9078801d41c1c052865031414032103402020740a2049101e01100c0c0e840c603101e140d075412880d04440d0f0081400d130154070f100615219034102010350301d4202d5400745040160010041c011410a5074400340c000c03d25030018010342d00070b58001070240c0950b0213507034100b2185114803404e64500550820003440081d140070340c1c0b0b41404800a40700da0040369050074403400e11000c50280040040c910101c4610b0b4015400340d0743c016010000201c507105026245090312500503800c0c2801d40c8140440c041180300780e222130700c0c60325101e0581420001c0d220f12284800c1c42c054182c2c903140d07103010342504281c580f480e00400621154017005062a40000c0565881c18520142150300010031044441c000c6003100c400d030741c0b40c0403004114030003405495640a000c2c00828501c0c180562801681c62085451a08180c0c452007810107400c0720b0105c62 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 126124136 1250 126122886 126122891
    0x1d0301021602011404030308040210050405061614070605190212120105030706090b030a0b13051005010909050103200303040b0309030403030816091403010b0409050f3009010306080d03 81
    0x1c540e0003107002002c5500c184c01580c02d040c0340d81c07400b03015501c0c0204003901481c595462079503520311800441d805824018a4541c403843c20741410003504001c0e4400302ca26007a010210402d04400107401c10440c1c0080e174a00e460242900c540303945030b0304240104415449007190a442e8074051030003070030a0009410300403405600d00b408162811b00d1a0b80650148000348074280042d0304034a00b200d610400307400c000b00754854510301051140c0d02407445440360a1406040c411f07078014400e8a1000c6070350903a10b03003100130789525910040310f45c00c1c0301c010310044c0c4d0300311404800d0400303490304200e9507801400c0d60304140e9038980b00103081c0d2080f502c1c0d0001d42c100040c280101600404e41039004108203410844d01f91a9450140c00c058580c080c00c0c014088801d410347e040d50302500210441c0c003003c0c20a0103040503610f007003941c0d00c024440803a0f1034052007035000041c0703404d030310a210501000d019880318100c03d84040c00b110b500541c000e07410591a02000705101404100c0b0400c5c400403560300 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 126125386 1250 126124136 126124177
    0x1b0f010c020d0918111209071a340218070305070302040503100b12100614030604050d0e060f120411010305011215090b04080c0106060c080a1d030102 66
    0xb420b04611041c0305003444500d000c184030354214015050195429150001004045d607054210580201001d001d0324144078000c0041c80203004c100c2c0720403540304c0842c5c030032600c1440051141ca805600c403100c104030380581c0740b0b08a0400c80103013070302d4401c003000183e45a41c82c0c81e00459080c0f28056886058207480d1410b00900d250300d40f040c6607001e01c082c80d003141402d04140c0026240c00c3c101400804040d112104500b10707594840e806140c541a64080359502d11002d0711040c003030003140c801c80394901c042840e82b44641c1404212507100e0303940280036190242c2e4140c000d48408104000e039a8000c181408090074181111000f4082100340da13030010b03503501d07141c90302956400e4410003090405043c0401084401c2140400324105980800c241540e54000a1080000e00b02c070744c2d001c0c050201241c1440184041c100c01082c3c0422010004c0c000c068a6040965102003d40002040072000304100d0311100d10603509207030b20b50180d0561202c1c0400910000342640c01c100980002c0c40fa40240 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 126126636 1250 126125386 126125411
    0x612180a030804142a0a05030f070602010b06031e0414060a050423060105150f0f04050a080f0d08041a090309010201150f03020f03150705041409040b0c1b0f01 70
    0x10a86201c2000c400070b10003980426204200c194214551701c03a0151040000c925550315100884d015200143c02c441ca80030ba0048815078a581c1071040d030002d075290a2801c200c03424800c04a9104100c100e140c00c00c0e106151209560f030703160041050b03685038258414003403490300500080c2d000302c007400400715142c102424108104040d506821009090b07551303080c04801c001042060440701b049415200c860340004418003d03104041c91040501e80018410342012020b030054000c3c2c0b14107640300d2503412348401d41d072982d0750030b80140800180d002400001b252071080c6200d50384140701e0245076090a46600950240320720688480b0201c2d003010030070010950f4240302c0c8032802d04801016184d01e0b4038282900c1603d420707601000c0e000342403200105440da00e04000b5084124030001c0e00c0001460001c0d03000f08281c0040c01000d0756050303600a40030043c50f00002060003190422003911154413070700e10520007a44002440e10503000000a080c0400d0002d2141c11741c0c1c6400c203400410044241031 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 126127886 1250 126126636 126126653
    0x8031e0403080f070c0b0f070311120402060a260405010b180606070f0c060216060c03120504050f0a0503030f070801030c06030905210a02060907050612180a030804 72
    0x10590581089050104004680d00c00a0140c10001c0195803d065448229044424580282c000f6020300b812a00344400e405102154920031990303507904200050440380000c44074852601c1c3c021812036220041030152410000400344074106080c404605c1000300d00c1103654460b504402c032a1003c602c0100300074800280074900242030210740c5111403480b0504001034480025001c1b81c00350300702081603002c1202c4801600c0105402ca00c1c08030100b651818001d50358000d0408844007a078000000090050050280a80081e89919450014002e10040038020100104241d4040c8502000c50084e88014020701e104a0300920113196680340a9003000c4500303001a054204118040f00100040b50402035a44207503101c81ca4045807048640c2031592800c10580c401d4003944500514115143d03944000600c4002415001c2d103000e569402c80d03442c3c90301d10911400b0b420400401c071030980c0d03801190045500481e54464100f0140081d003606181a2010008034042071900041c40180204903 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 126129136 1250 126127886 126127921
    0x3050c1503011203050c0f03040305070303091a03060105031e010b0901030b090402010f081e010605030601020d030e030f1b0a030c0209090105040206180102010b122103041109070c060501030803 85
    0x10603400d451075142c1a00052805075400d005010410701003044015240c003807080c0d0401782c1440303080341e4441da00c030306001c1d0f01d40d20b1510044000c6208124002403080110350a03051500550800d00c0c11503403108010f49480d4401090070100540100c44d1110600141f15124060860080c140780c40b040404000740841d110005000d2244030210300b0400180e90110390010007405a240c0540c803a01c40e10520400d0f60159100d01c8240b80c03d280021801d5544000550301c650001d0f400c548801c4e9020100b07070102e4001c0076100f202600f00b04520002c00c801e1900619081c0c41c1400400c0700c02c81448503035820120162412030001e010000e00100303525214203000d03084090603000300110304090740001c111340f007150010a00f213400c4e40c1c4d10a51700da000303601540d00560007802c0706008030301c500d02c0607460302d0807020b502d000382ca481d44140351100c3c590002c0d02e2007603030b1100701b07161140704081c20040741f070304010504800c01809115075400204035004040c025440f404490340c0b20305081e8050244440308 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 126130386 1250 126129136 126129169
    0x9070f0311160210050c0a05060601080a090203120310031e290f04060b030d020c01030c020a02010503010b0c071503091208040f0209190207050a0b0603060105010206040b09010b040603050c 83
    0x2845020300002d181140c02c60b01550403a1100240c0840c14000e960600506d40b40714194042d8503481c105001c40800c00c40c2c801c602c241d88054491781c52080420171910004c00103505036100a42600d01500703d0740045801c0a00c030b40c801c0081a59070754500c61a130700d40f840c0d1249841040d0304024208800560740b2400c40c000f2103040100000c0b0400d90400c0301d074008145410a13581c100200e400d0150325481600399550140642d080c1c404804000317503645404034019400a0700e4030b100b0780580d62010540384c1042d64140c0d1050305d9a440d00440341144c1d0022501c0300703102c0c05003402c0020704909807001c0054a04450b00c000c99401c040341440d04034200d18541031424084030808000018400303a4645002a0341210001e5194440e00c858000b48403031140f2144010380f0016218040c0b1030001100301d10103108040040c40e07a9030300e0b0241030b1501d500b0301c55140568401c401081c00101072941c05944200e5890001882c04680c1d0001401c0d41c095500c140c81c160000000307a8103a09104144001d000070 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 126131636 1250 126130386 126130421
    0x60d0b102c0121020a140f0403020d0606080a030c050601080d0504090222090b0f120c13111605010f0b100509010c0f05060f0a0e0601140f09070f03 65
    0x840805900e00803146034450381c0492290141007140b68050040045180100e1500d04500034148450100960007a14180081980e039607444030300c0e4615001300d0b410001d0f0b05441a040c94515400d00079800403018007211070b680c0f0340c0e201081c2d144041101d456150302985c1c4100c01c5802c241402c90403d941a002110181c210010000c845038000382100c2c1200c41101d00169540c00055580c1c007101308010f10030750700e41da103000c00148000309500f00d50740740f00088640f16400cd07401c1003040b07036400243e510040180c001e1740d01c201e801d01d0400c00c1c000403491040030120700b815215041c0b8045a11004404211950703030f4003480e0601c00309104601c2c0a10a4260030002c1d5082e410020b4040101d030711000c003c0080005501035680d104245018507540d00c01e041d22200f84041c0b4005885683c1141c2c0c0310030040e03c0000007110071000d4082d4010041c2d0400c0075100503420302d400828002e0103070b44042c3c1c00c0b5842c046801c0783c549803200c0d00f9100d803030300d81e546c51f01d0440e4520004080e41c086108010040c3c0 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 126132886 1250 126131636 126131657
    0x21150402090717070c02130f0f18020f01140f040603090c120b011521061719020f0406050d0b0f070c03051b070f15021509031611060d0b10 61
    0x1400c2c981c3c019082911810040004081d52000468060302d0418200840d070800102802c0e0741da0700d402c000004021003070103200492111000032a0341e800000003035400785800e04480c6403540520400140c0e01e54044061f450102941c1080500350311641c05100040d80e56030000060001c010190340240c440304a00700360810741910354440110060084103c1e480c200342c14416000e00840074180c070000200319480c0c030a29502c1da0600100081d20075040345802c605001c0c0440c00b40468410b014214000e02122042840e40900c000091a25040350b00075a41d82c00105541c2d5421402c4000c05100c1c085a0700640f0380b12004040d0440c01030224400d0020000c12440025005002e803008200d14569200d010103200c8078a528000c0030350b1050a0030f03000f030301000c984550620203101d82c10949808540e0102e0705070f02c00200b080011a02d040c3c10303030828062124414902403100d1a075a018a00c5e00361030740c2c4031900144041e0701100308040034607540c0090a4070f508044090b1a5803603617500b000ca0702013 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 126134136 1250 126132886 126132917
    0x10b040806041101020304090608100c0e01021b0303040911190905062d030112110609010c141501080a020102010506040e0604020d03020a0b1501180311211504020907 73
    0x140000b51009211210500c1e0041c0d003a442002660001d0a40c03a1007408010303074500c00f1b10744442080e00010f000783d08110802c400345004204603003004006074020401c00803e001104c012440c00d603a4030394140010440060304011a0103035065151820101a03912a01c0c8075248402010304140c25061024920040185984420a47d804d100e1060209441010100603500c1540b0107566054103940000c000411202800342c80d80c03901c180f0419a0310b10403c0b1400403c0102d000e10004180040c607503001c1103000130340300b2040002043c1d860084504c0b8490078002102c461000360000341d42d40e84040783d94015981c2c240115a0032400c180c0c2d0400c01950f07020000d80e201c0d54004e0000c0d00800fa03002a0000b01882000401401901f2884030f280d075042064043e100384506201d003900181540c90390300034402c24440d1081c11a68040c2c0918034800c0400103000c0012828906000707880141d400c04410110107000c10310643d11441031903120b03072405204200900c030001c1d0080d0100200700380c0a0349030 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 126135386 1250 126134136 126134143
    0xd0f0203090103110403080304030509090a06030c0b0703120e030903010609090b060f030a05060c0702040b0111060f0c0702030a050f120c060a021806120105030706020d050313081204050c0108010b0408 88
    0x42841c2840c010920440c0855a04840e20a0f540028098000003013044149540180917101400302114a00c4851b21100c0e0f01c0c006580150102800f180700c900300801605409100501841d403085c1002800c14111001510803151b80300ca800362940c100084e000e0143c070713087c421400941503104007002090900d0b1243c81030584002d1a95006040c405041107440e982000880b080591000440f01d09103001d56002c161a040500c0480c0624180040804c6640c05080c2c1061141400f0006041558501328403410f602009040c09110071020020400503813010b01038055017600030b000510700b04140c55001d41c03610020f880c0e1003466a0041c002002202c102084094100d1114a0b002d6118030441340703008810b0100094840d401440000c0ba0941d4120020f4494126081101920003550381c0d407a050b030f201c00b110460031000500c1040008c103922542c56052816500030b894107401d12641c0f26642c0440c0d84241c8003a00c1c0360b400b80350140a5036a1003070740c290140410307502080c105840c02021a98 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 126136636 1250 126135386 126135397
    0x13030206011a1c02120c040f0b07052a060a0201060f0e040201121e0204030605040302120c030a03150503010e03030a05060f060a031806110a030b0307052b061407020d0f0203 76
    0x81100c2c04006484011803070b0151441178000100c510f200703040c17608880701544d00600c02d052001001c0040041d000c4e98400c2034034032007900000a06045d60444000213102054104407015103180840c40c1ca00c2900d030507000d040001071070340000800e00c2c02c2c4492006001400c2d03106c8110a1044400c00c001070364002e0054808017114400451440802c09a0010381c03d8500e0740310111034800f0070000103000d4140c0125001d1802902503404400380300b076540f4902c1c40b6070b11000855070b20170011614000e10030760100305000c008110713070b00c1c6064440000900350744205402030a13590001c0148000c1446921410350080e0007180c980207885600d201013503803801503289110605030b84038000c0501c004106c1c01190b80581c8681f0402c030226410103991019089005042d001038900003911260341000915181076a01c000c4c1007015108001ca01c9011000d4005001da2506444940700340016943d8001c3c0d1101e040c10740c01c0761001340b526a80003072404d80310703001e500f0400020300100460035401100f19103 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 126137886 1250 126136636 126136657
    0x5010b3001020c0615090a1419020d0e0109030f08040c180e120408010f0504020303030a09150c0207060f030507082202060c01061703071101030504020f0913030206011a 74
    0x408000151541d00a003d0340107021040d010b1081080200c540d0140e8002408504894aa80c1c1740c440740e040408071041420805c800d140c03884081141608460600c0030b071180c1c0f05002510301140520b4081c02d80b610301000c2400ca070f4503401400100b43d0400080d0000e4489460480541d281a40748c3c0c3c144252184504480b40074501d45e96006a140354010008100701e0b44100c44a2940c0d407402d009080e8007900c580f40c01c0d54a080e0f035100b5418543e009039070255070010001d506644450356001c1c01000c0c0218200c400c080b512507200d401141c0760207041d003088416006070150900c0c025000d00150401264030081501d000b04000549030001e2050f6000190b030411100d40c080031320000722060081d900041e60100001c2000f51110005400c50000c0d604d07004004800d88000b881c0b510340d41d0240190003041d60340d4030300f151a22948642d2181d80d0240c0010b11007002c00300c604c804110303210010389a040001da140701c256014190100241801494182c811210540740f0040d261318074007034000200c = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 126139136 1250 126137886 126137959
    0x30a080f03070311071a07020c0a0e150901090b09070c030804320606040f02070b0c091503070e01020d0f09030213060b0301080601180614010503090703050105010b0705010b 76
    0xa00c2c061281d80f004086040140d001a130700c404034185800c0ca07440d181401d4010307200100004960602c0420720700709071800030703000000703040c2031402c2c1a990040003061411031412110041e460b5690b00c09242d4020059098002104151071041c0503003035400504800501c5260b45410300025032043c00d50303078400d0304080c1e4561a24514038003c41004900c10300c1c0c1402a100800e82e00c030715040030860700d00880044a04121044d10501804164000d542010304690560000200d500d00c4481c02800c070307403000404900c0c0d00c003401c0380301040d90342064500e04002826100c0c0e900f41560100280440034503582030600511074a00f03130040160100d400000e006055031240c108a41216800840180c42a90f003280c0e00d035a164880d007a42c40200b48030f4910000e41090b003904111200f881400159007100b00d00078944450440151000d90010704454040e05c61100000003082003031040602800c903201d2850369690807800c2c25030940c0c1e801030380c1c244a14800c64a08801040304000b500c400c10b04513110 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 126140386 1250 126139136 126139141
    0xe0f030111031906050d0c06081f120b101404020f0c0604030c330216020a0b04090b0301050112020108040c08060f0708070f02102f09030c030a080f03 66
    0x1080c09012880000264004003005008254002d0340d18400c0c22004604200300103640c4c1c0d020007504070b04d2081c0151003451650400c0c8400b0344208d42c2c8582c841d00d030303190041d00d14040100c5541c085005a01000c03100b21190103400030801003200741900001c8000440000e14102001c1d281607113500079a0501c655070020780b04448699041c10b0b15038003170441069810514160901812070b078004441100c0381e403002c04281e00a81c4040c00c0c0a0382003860b64556290340b0388603074403100085d4401d00c802d80080200306525001a41c1e04100440989510780351142c0341c1d8540307241c1c0c1058a8400c0d240c94884d9040a0040c08010030140c400100c40d502480c18180c2030700ca0f8204046202c8141e0401019402004100300c4a003ca03050101c0c050811030340d915405585848046071041800429440180c109900e403180030300c200d4001507020342c082858000042101100c40800c480c19620740d01780e149021500714480d01e018407d800c15050250040c05240e410f9a6501d41244039a08070241c0118000c0003 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 126141636 1250 126140386 126140389
    0x40c0513090b0103110a05270c07020402072d11150c03120403200a0f060608030d050402040b01020c09040b0c0d0e0319031b0c05030f1b0601090504030e0f 68
    0x3201c14900c0c0c1008040e40315585a050000320140c901000030701a00900c3ca0024660a000b10b072941d03c5040c0307603d0540c940c280c0c40c2400101c1c11b030280194a0000c800c0c080c450140c0d0b500c1c40100001403044810f44128503001e001200d40c240e131011005c0d184140c46e03008002060803103501c030120160880782255944400981900745000708817031641e06106c08030360403200205000b038140c0a24000d44801c0c1d403410406144a030040a10819414190000c0c0701c0c50000074001c0030006521807203080c01003403140c1c5518a0514540000d24074240040d01c03072040c0b1066003070a12450b880e055080c806001e841500202040040d94090402000740c400440040c0103401454107031031003044405401d0003040c2800b201c03941c0c2c90300903850701c400060148050415444c0244980700002c40b00b4804181c0c1c204080718161030054090000366500c2c0030800500d0b100700ba00070018484134600140351400c80100c29809440d01005810885007a450041400f01083e04660301181ea01d00c1240e564042a40100 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 126142886 1250 126141636 126141641
    0x1115090a080c07090912080109060b070b3c0906010b0406050c030c010207060b0418030210020d020c0d05030702060703020c06011206090b010b0c0c0a03110409210f110303040c0513 79
    0xa1011301051319102c1d107501045040c1c2890b450800a65a4200140e600c451268045800e144209c109644081040d200050700750400c02e584101c00d03c1c0388405d0041d880101a8484500c407403441304c00c44c1020620403042c001088182c9d001107190005204a60410030036007594851405401c080c03041c0459000041cac5010000c98542c14840d4009540b03d00d154038001000e0035101044d540f08a04200309030301c200394a00d0001000320f03015070041c80700300c0e41005172500a5100c4280071105a4013002524840c901c10055282c4a19866950950fa883c0c003010080c10300300040d041c0b07030405004000c208005d40300010900c2c15a0b00d200c9035a03010540781d143c91703802082c5004c801000302060000010b484243d000141902040c41400d460302107071030348200581d43e252400000c00c03a42540080c92003d05107948800641c52040f10f81101000d182c0401d011101500c0044000085c02c10766840f00300d41d8001d088007000404d580085065062590f40c01c05490018002c540c0542c2d00a03050b81032038040394 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 126144136 1250 126142886 126142889
    0x609021c05180d030b120309010804110111070f0e090304031a1806070809010e0705010903150e191e020117040303110403150c0207180c020703060c1115090a080c07 72
    0x1070b040b501d001e41d504070041d0140500703480342ca2041008200003030380a43c003c4203c40c2c01d9031050f0b4550850b95510390707074000b50000407894a4100320103c403d102070400204244000b0340b88580d500d0030914604a00500c80100082180e01a500300f44801c000048140c1000c1c07402e4030801003c030761030f6656180d01d402580014000f01080380700b1001401151500042c0150251141400030311012030789011041c0c0e20b82e035034400c13a1b0008200358800c0010803200542d0b200301388084400030a104001c03020040c5001080c61444220ba0341ea00780744c1042103c207054080507442c10140100b00300316260006003c3d00050311400c1e480c0c200001c0098101840ba6024400c0344981c0c00d00c06840d42e0f01c03414071400c044401407149440300c1c5044003160b240c900014006085600400d802e00c4149110f40c103a030050303d56007645000f036109640b03022000504502444a0080c025610700840d030200b8081c03103240c0014031081c0320303010312807105209050402092444225030800740b100d944182003a50286884180d = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 126145386 1250 126144136 126144181
    0x50711060c0318040b10030902120106060525050105091f05040b040312330e010e0103080c030415050304260a0e0102190c031403040b0a0f02011811040609021c05 71
    0x6c07194440e01540c141d44610352503130094070170900320007003800254221445801b03202c0100e907052086c881000281c07280503580a032540b209506102d196641c0e07a00750350040d11030348101e03003141d0034601ca900070045020b02c0241146e80148603900345500c480845840240000c0c042200080d1000d22803038064000c50415003442908031260000c031030b20700705034a01d0609419007410410000103005208521668182d07800401c40d05e155900c2c0da6680f82e050b1340008110005400f050000003440d03203400201c0c0300d81e02542d44800c5c0c2e9924080c40d00f1900350710700b0780b401d5050108070041e00d4143c00744078081d1080a1503909100c2003541525005170300d0505152030260324204107580910412051000301c0c41103030300c24540500070210020846883e4040e41c01404520b000c21300c03450440030305c103a080404583da00d00000445c080217107050503003403030708020991707002da601c607500c2400e4109485410700401b104402141080c4503090091042c2c1c44062403004410349440c045860035200c41000c0103005c10 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 126146636 1250 126145386 126145399
    0x50a0507020f0901091a090f06190906090c09050d0b010b030c04030503070f0c0f0b07020d0c0801020304140c06090609040b01170702010c080f01121202011506050711060c0318040b 79
    0x3e6860180018085440e081071b0741081030301c0034008600701841c00728081d00d08117207410000d5a45005100c62203081407210365010000f000000349050191103220b0140c8000440410003020110018002e41d01c0ea9000070700031000d480411011030703505480c850546981030055560380d01c800145003810b0080d5000a011808001000e204200c000000494418400d0380107004159540454040c40301d1b40d0311403804103003c208071460043c81c0c0850f0b40d403005440390b0712501e0400d0302d4118450890f002190211090094881c565250400420040740e160301700300d0f19646841d5004010a200c0d001c0c104030a0f0140d610344103407450a030f00402c5038034544805492040450720308528020301038503011084c000404c421801044413032881410050590700d5081c10003030701c0151640d41c0c5062004210380c01d421956280020b4101c0403150140343c3c014509a82c03055100c40b5903060801200c04500f00141c80349008001007841803602000b518000e1100359003c240740d40e80000418043c01c60003030300a50244 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 126147886 1250 126146636 126146639
    0x7020304050a0915150503130302150405060403170907030204020c010906111809041109040302011506020a031701080a0807050a08040905070305060f0a0909050c19060f02010c050a0507020f0901 85
    0x402c40d40c800301440d044c0703c07110030400c0d40c1c510b01115101442c4d4503645c0024002c1000982c144031291800307900310b102c0d104075124020b000da54582c3c401c80c1982c048400f0b80010040c0304c141580300c1140d003010780c1e0180400041e41441810f441d03840285120003802141c0103d54551000000e40c001612a904558103005884984130703584480c3d441407108202c46021000181c0d6141000d22241d441140e0101c0300c0308a110000040148e00c56005104030b08640d01d800000c1003040280a040c00100820380040c00a00b10341c0c45c002e04041d40c40c44c0d62161548401c0010403e064000421300711483c0c10940c03907595405c9500300541043d46c3c4100180188100080005010006620542c0714101302c0d0703020001134440c0401c2102e007045250380e031540002c0c00d441c01c0c0968801c0d40d000b1004140b0070421200e45903c940f000c141c522030480030000200d8a0743c0300c00c01c0219008880d0105a92007480200075024050801a001e809403403412400c02802007100b20454580d80b0b03100d00d000f84018200491903 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 126149136 1250 126147886 126147899
    0xf03030f06011103040503031c0b030706031b14030105010f02210405090901140612070e04081905030c03070516021216121a151c03020d1403060907020304050a 70
    0x248420703169107000401d09920001049808011350303094070402030103580340802c1008200f18405001c0710131101641e413a40d601c152550204041001050180c0303003c80c40c01105080c21074495a030f44030407000d10480c03120a1451100020490f415074000742444e200b200e4920308200d14010104241c5a080c1c0c10100d90501545416800303041203c00480f15240303e5905c0000e00c0b4280d403901c03401d40c11001454004101c0c0781ca801103004031040c55a00c1103540403a506d038000f1000c0ca00546083e19058800514949840421046d565a06e500b81c28200d145092804504000d0700c0020030080c1001004107980c944400e0300700500c10381d9900103100c2c50440c031510b504a0b0b260b103100192001e050a070400d00003a220303d2150218240c40d0448141c66100f0203440112007800340c01403501c40c5000c2400c00407000d40c1c0c1d8030461159062940300b000301d101011441c01a1610358000601400d000c401400c00041100040880344c0c081c0e01a100340d0016140c64400b031b0310350b001c0c60704030301d62042e64900c000c5000c = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 126150386 1250 126149136 126149161
    0x5070f0e0a050c1204030e060c0d0503011502030a02030a080402040b060304060e07090b03030405090c070606031a0a0506090115090e0a020c06100509040b130203030a050418060f12050f0303 83
    0x60754600000c1220341c40da12011007480c45540786140074420740c2000140400d00401c20b10b4148a40907000d9407030300604039103440c1040350034001c42000c00d0010005001c001d00782d1450140c41909400210718007114610003960300d0265998000c2040702200c001021521ba0b500099102400a0032407070301c07400d0601c0c22002401c0f907100780f07500c2803142510014503041c0a0180343c5031020081c000d145030604140910006a078018003403440d541041040380c00140081c8242c0c00154040c0d17480c2d20000b010076445038020f01001e84032000760307828103091000a40e64008040c0c11924040001d070000c40300c194003034070090b069600982c0030071207c0041240e07040c1150005c1492110000541c3c3c525542c14041901790901c07401907907000340c440400500083c851003162034026001c03107003201040c26140e001034910b5004041d030340000741d008541000300540386600140f0340d41c0081c100b8031200c0c1c1003500f46c02d040000c81c400c1859542c100d680c1c032010b00c4401d1103241140701003401a0781d070303074030701040c002e40c0 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 126151636 1250 126150386 126150391
    0x40305070212070506091011060702030403050601060f172d100e090319120207030e101b0303050601030f060909050c0105070b28020a020114090a03050702060705070f0e 74
    0x180725102d00396410402d01144040907914014405030030004044240590314295000e0300040c0014100607502034001005118030840d1240e004595660841c82c100303080903810380c0300500f8400845c0c0c0703150666801501070100140900f0315444540e45401207003166003070078044200c8002c61035a21542e142c0207908114440d0800c6803846128030380da02103400104c8812140c0000d1508240800e001081007440c4101d2000d202c0d1800451041ca01d591240c00c0b03074000c01e000c40c00318524040d190010700740301103000f01c0003009040000901780c50b81c2088180502c4540001d0406640d5000141642e01a40c410702c0c02d440702c064200402c2c1c0e10386900c5402000c0341c05083c2d0309403180c84614003140d0301c5041200c480c0c030742c40604490541c5480d03403c180765a41302c45c002044042d981c9221692041544054824901b5a60011540c02c00511f0b140710800b4001e04100070580041d081c107808a41c000d4201c80c0c80d20340c15590a0b41c2c0d03107440c0c140700e4102505030304007004d04000680300258501c20a51003e0 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 126152886 1250 126151636 126151639
    0xf080604181505010510090302090f1518090c0906030a060b06040f08100f0510120503040b0c031c0218060d11070f140303010f140102150925050d0f080903060403050702 74
    0x183c840340d240800361f07801d00c4680300007503216005000213100182d580f40450340002c040343c46c0c84180400b103c0040d072989004000e49403015412010040340f0201000105003c14094606020a060901c086521001e0040d40900141c0c0c545000c441551100000c0704c00070558040c045510507201c850140d100c0b09004e03202070281d801c0001c091540c030000c0c840c4a01a5003203245400a00d80347c05900b00d8080d04100090324ac60000740000501c1c24100c10050003400380b02c40185545002614200300b015000300b5902c41c0144c414058006410440c14806003000c00895250ba1185070007444c0e0006001d03c1c8616072081c14000c600c60b01041080503024480f684a00c4035184403903100d0348a01c0e500c3c00700744a44074003580020f00400c4610a0403020f400d82520600c152040c400c0c441d110131251070020340700c43c84503602201240a21500c0e00c2c103a08040c50310740c90300060440c5044000b40c4050700a00700500b4070740c00d2540c1c51082000311402c58200500c043c0680e071040c40c241c1406820382c1c01c81d1130242e = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 126154136 1250 126152886 126152899
    0xc15270806010f0b040e04080c0a080a2003041a040305010606020a05150c04030201080903090a15020d03020f0f1c0c0306030b0604090308040b0a0b0a030503040302100f0806041815050105 82
    0x1c605800385102c10000c1c0c1d4041c0360304c2c5091900d0440d0000050b00040c2068515180c03c20100140100900c91015070602510300306991b03620030380700240402c030100d081c0300462441032602451170401200301c80880b03d2261000c1f800c82015420b480d480d10865100400b07541c40c2400005203180c0214249429601030000e894070101c02e00761200038820122503043c91604100300c02e1005601810344150000f100c2e90440b810309481801180c188050358003e80700f0543e88951280025904004130700001c1e400e07140550809100c42d80c2d000c582d0142044000e8601c8c40429a4000c0030101104a113a143d490801404003814215020700109414041a2410049680003070b1081c01c0900840241d2503060396a18155175440c2c0ba0403000290181c0301500c42900e480c00c1001c036680d42030140c2c01460294005d507030b82e23501d5881040b000c1030041c105c10080c450900b0707040f1202034100c4d0030280c0c02002070300d0104082c84c00d03808040c00c404112000810541e0503600c95040b44005a010314180d49064614 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 126155386 1250 126154136 126154139
    0xb060c060a110406090909030c0b041115120103020405151f080711192103050603010b03010b031207031806050307020c030309060702010e03031201030308220c1527080601 75
    0x2000c2c0306103c1c0d805100003041d0007900c100b044410ba03522405d4018001e10380040c0d0360341d6940d2424603810040c0c1d01646d2460101103041104c1c501402136034030845604403401d14110a0703c0c00c00341ca0480521001c5d101365078402c0040c00440c444004035480354801032024810084218254a529260141c92000941e80c900004e086a0040080448030a8050001c18070b0004459509411501300d03182190340013a8200e800c0704070744e10442000c1912241e501c021510b8a880740074142115008628a84241e0510201c00c625480c0810340c43d280004100d400c0c3d0780ca00c218107042d1401c03d084100c40c1003001c00c140d0001601944080514000c0d00c481e82554000080107040655034061140701c1c07640104200520001503000d6400701000c56009400d4a003400300c5030303007903601e042c3c0300740c0c42500807603203241c100421404406103103002260b00000200c0c000009032550300106e445c84c0100c0c0d0111802e5103550360303100c2c0905000032506c10044580042900504029000240030780b150f580326201d803e00 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 126156636 1250 126155386 126155411
    0xc0507050d0812061504060203121b090d0611041202100207030533070f1404030b0604020319062903090606060a09030c030f11060c060411040b060c060a 67
    0x800c1c01e10550080a0030307080c00080f8000e01d2020001401c0554007000d0a070544010502490141009240c9038000d5900e030800c3c01a201c208110050030381d00c0480c2042030903546103103180b003556401740003950a1049e6000e10f1408800400050403a0340c4508804600003880720f444130f100c82c203500e1003550340e180e40072010b00d0182d039150b40600008180750002c60070200201c1200380315102e07007545028402941e003c88181c100b4042d00c1074038000005840240540c5041c1e40041049401070400048075103014919100c006848802030b001c0d074440c54000010a51040d005403410b403000e01d84c11810060282c0e1742c40c2200c130520323890f48109210030294030400c04d4041c0c1201a40c5c0301d001418040d0106903500001c100840d0710103071100c020700410f0080400800d841700441e802941c49160403070501ca40c0c90916071049a07442c0340381407089400f0880c480341d0700302c041251504964445000e02a540202e030014010f450300010542e04800d01042507010010005100342c0a010414410004c42403c1c0c2c0c03 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 126157886 1250 126156636 126156649
    0x70b01060f0f021e03070c090507090b07030c0201080c1909030b06040213030f05071e06031802010f0e030c060f070204180512030a111809090c0d0f06060e070c050705 73
    0x48542c005a081680c1c030140c07802d031091610348407504540540c0c0c50120155500b0320451926000106c40315034990400003842d0304030311494061704106540b01d040018030b03940184000c0c00c5401c028100708032503011032660746511069600c0410039400b002906a044500100440c00c43d103c00e4440132883c2d80440c0f8203050520841c0c0c4040301040c0b195040e00e0071502e076510442501e0130100c1e01e604c600d000028006030251850f00c038542c0c0c451010b0a07814507200004042e101001c2c007684c0007000c00c100b40340050f81c00030b801051148650070014041c0080d400001d0600010059540d004540010000b060801d02c10061404508c01c440401c0501080f03804e4030b4020540c144000c1070340d440200da501e1b08901210295901c041004400700392039a00f0398030704c44c0e5908440310504980c6260308103d49a8a000303003281d40e00611120081c065503113036100141400c00b03519009051041112585418801160070250141c080600c0c01c1d285410906070083c03080344801d07000c1c1d49600400c04041503618141c0d = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 126159136 1250 126157886 126157907
    0x70f03050c0d020702060c03040608100503160504090c080d0c030306120506010611100c0c15150b13080303010f031203050402090a180f03030204060201060f0f03030302130b070b01060f 81
    0x9450300b0180c414070b0700e600035408410280d901c40f40c28400f103405042d0420040c405454180d0f1035501c2400c1142d2000d82c0c011850300843c0c8240c1213030480c0d1224440342c100f614125001110b01107402902c03820290401103054010030018020f80416030411a08400c85800e854465641000754960b42e8141210a010402d4014001c3d04100c004011852048088151080b20482a00c5002015030039000c00c544140c8414404150803117a880b06001c051030781c0c81128175803c08240403110704111142207003244d80c0580524010701040d12801c40d008000c40c800602604c81c2160340d25615500c0c0a00441446d12040f101030748145491211140b00303008180c0500d0713015080c0340d01030316000c0030600030b0b019900c0341d60340d83c041011403940460324031002c0300c0d50503000740c40050f80c2e2030510030000e003540d5041e080110b4600d00c00702d0800c081700800d00110100c070b07013603e0010303241c606404070042c400c079444d0301c4640c0c01130002c0380030800d10a10100711030481d070203512a89404186400b05a0780720b03600 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 126160386 1250 126159136 126159151
    0x70c0b010311101803081b010507021b0108070e060a0207180f0e150408071406190501050307060912060b031c030c0306051c03020705060a05090a0e010e04060b0607080c06070f0305 79
    0xf100b00c00c0002600200140c1f8090740103011101e2188008140340c5c2c211007040b40c50b44010f80c03015008020130449003854140824007884c00030f01c10b10f030100018240c8805030b60f075540104000607a02d02e50510034055031028068030701494042611a5904402900071040d81900441c034100c010900c6880001e503000c5002503440c0e5080541d51603445050b40354124540c1640d0191198a8079007130a4418810144a00ba11441d23100004203000c8601c811070354142c01041c000c0e8440304080c042c85400c80250f01c112500c0c180b03c2c0949441d24605a000f60900344406900751088076044d580380d41003400811004805542c1c2007007001e108502c201d042c0c806911405800040c07404100308810f0825100404250290040744c504640e1500410000e07400604090300265010410301d00c82d140c4110010300511120390414503e504056400c00004d002510040910741c0d40ca40c2c4006a0703c0d49000e690a658000721040d46511480041c0d40c0c8415045400c51b00040190402154450007031044c640100d10 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 126161636 1250 126160386 126160427
    0xf04090c090213050406230303041a09030120040303030e0118020f0102010905071206050a020705031b150703020c0d0201110f13090509030415030b030c0108070c0b01031110 76
    0xe00001c0c640254003010707404107408252000400c240c1c44500981004004101504003821007890300c842c030f00c42010010b503100ea0010041005200000e95150070b05220707542c81c1c2907982d020040001e004100905052a00844200c04051480000b030054801c0300e00a07207060020801c01c0809074206d64180c1d40075841017104019007809801c003140102c1020006000014004605450301494901a58007890711034441c520140c080000c01c0c000d030740c1c002c590400150b086c4080c039525551680288500c0c260346144880c0c0410b2050001c018885425022752101402424080e50040280d40801c900408600c1401d5201070060b10502c201403003103d0758407086040080c5100310076138540c0544400700130850700c01d0703010607004650701c04e03a030242240c0e1005507070b61450800e8400385455210100e00034145020b04024107a2400b2920002d110f0003443e00642556a648064501c5034405071701400e40d0b02c040e00003208110b9110400031034100c048036010442c8403002030448d0340ea001481015000d51 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 126162886 1250 126161636 126161639
    0x80a17091203070324051503090a110a0312180e04051f02090306100f050105120105040209010309060207030f02060c090310020901030204030f060603150b031f0b0a060e0f04090c 78
    0x2090740910b0704000d0704e2401003581711020342c10103e82c3c0b42d6020070034003500207003000700702e14035220140103d440ca00b01c00321030031031401c0300080e9110000d01002604130b044100c000d01040d0f4070240c40b80055a840845001d8600c9000e01c01003450b4001c100721140c184039540049815805a03850310b00c141c0e030080051036070020016a19206a03c10111950740c95000c0c803040c0714540e018440d4600c00d14905d14204261483c107041e1100a040e19840541441000c11101140030b0301040142d0550300d081e100540c0e034101d5000100d00500030004013030100ca00c00705140b0101030344800c000030740c9101e66080394001d03120040610624400c03d46000d5041d80401c4101d9080009900603150031141410010300b4941d4a4480320403010000404844a59559805000300406407511007503801c008041040682d04d20004070382c2e105030b29002004003040c4001c1d1190124500e4100014280020380301382600e5a595a01424500280001e44e00c2510b08440c4010142068840c0f080c005030046050040e45 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 126164136 1250 126162886 126162913
    0x3061a07020d140f0106030311240403031a060301030602180609030a0f02031e06010f06030b01170406060b18041103040305070209041a250c0302030319090f080a1709 73
    0x6010f480c40b0080f6030041c4c21440d00650401e2107001c00a42c025140c2c80c1603e4007c0d4038a80c1880e070502410b0a0820140742c2d082841ca240080d83c9a000d03501d03040000d40b0001d0046465540001e82e807c0701e40c40782c0000004000c1061540181c41d94a07490002d2041c3d241e01c500800c20240245168180c16a01140703095001c203c00d19000080c140c0082c055485059154030b10800603200d80000103c141d2180004111458071884802c0040441d4030f41003104c004c190b0b0000b072408a204a2061145a405003c20705112450380483c00400c06050455690b0000100c60700c42c5080245c039440c4070714038000350403d081d1030540482344a86e81c0341d07036050710388000707603082156000003c1c000392003101e190000301c41c030030000710900760246c0718400c10000613284540f1100c445d00c0c04844c0708010043d90000b0b0b800020307000010b80b500241a60009654a8403c441110082900c2c1d080640341002004d9200d09001007040148007240c000d655030414070740036410070045524152a012080d034081e0010b070303840 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 126165386 1250 126164136 126164153
    0x911121b0406030209010b07020a0911040303120f052a04030b010509071403041505010b0702090c0c01020c1204090b090f13081b060f0604090503030c091c0303061a07020d 75
    0x492000780009901c98903500400c00000098100700558040001d1007819490038a18102c0107003030920041c8016400410400307614021844010f0500c17030000c84992990000d508040f12039019400300b0031030303031420107014580890201c01c0c40d050032008489100e4030140c903100b181e081c0c039000b104002160f40380030705000a603a0000d0140e010030503402e001c1c0380304181c0100110b004034003440d041a20f40c071540070044205c0304180e1043c1c10400c020003010f80181c941c00d0440f54800140a1800d40702e000d01078009001e80300e07055100031a4050605840960031500028000751a8460020091440311700c0901c40e0300e407015140901680b00342000103010580309850b0b0506144507021a50400620700d98104a144101c400c00d04c207500550104211614401125a40840219000d20030103903142c441c13540345e1002070881c11802a00060300c42513074492020140a010b10a21030703410242e25410002d00400142c0a40a0301405003101c4050406450094a440a40050251a49814a5451072031 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 126166636 1250 126165386 126165433
    0x515010306141c1e08090405010927050c030708070e0c03090a080a0c1703091c090311030712080301092004050d020103060302031e0c031c0c030203070510091112 71
    0x2040025480c145000d030351895113240c9000d100c0c078941d40c0c80c1c070b46900410056640507048003076601d05e451411480040c1011045400e1241d4042d0000c10045508026060451007414503425108038080005c55810000b900c1045407101c180025443e01d4060550556200581d1204210b52018001f035010a151000078503100080c0d0400c50700381c0307025940d42d095441c0086503450000b180801001a44007051040c01e07000c104080c180b0801480d41c6401610008d80d41c0030181020031690f0030752381c03107442c100041c20161240c0302078981900340c2031402d52510351007401005200c508155080c61400b4010300c1400114014603011800c080c203200501011070943c0500340d0400d500d9460000c00758400707121401d03140010112850b0a111546582031409000c00d4119000742c1c0600410002407002e0415030311440100d290544081400382002c0303107580191381010f0103034040c09038400c454010030703444520f0302d921403a41048007049c82d034104543d040d07110f0500c1c602d40d041110300300b4050f42113201469 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 126167886 1250 126166636 126166643
    0x1050622030303090303150302090c0d0906020d05090d020c0d060e01090f08130e040507060f050705030406180b030906060f01090f09050604060e040512030406090203010515010306141c 81
    0x15218800c11441821140d200740c0120b90384608070b40916505005144d01003105402c2000c0e450310b10746c08242c1c0440020300000c03070f0030400b088800307490501c0d82180c4407164000c8029926110401c0054006110a0300c40708240d01c03131600406c02d42400404c00d1400098020008032031010143c9910700940300704010300300c055607240a00f000054075200c0307041180d80101340303032a150b00b607541404161a0311500314210a0144504020000d000003c1100c207603456460301104014142000b40c401e0700a800c030023003403030001103404684254081da4001d140c035800d0b00b003485219a1844400300b02d12059400c1166a00001c00140060402c0954242c3e81c85043c948040e0441c1e0700c0c0b005840c0780030701d904680f003001d841d281400010f1600303008030000303050442400f00c0709007019a9003030b5560050070307140d480340a0040000750078070030380b035002e1844c0b581c01400074070003031800903002d5030551101701d242c41c0400d14110b00030803147c000d008224040078010304044280700303128a903801401107000089 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 126169136 1250 126167886 126167917
    0x906050a080a0e0319080a0e030403060c032a0e0f030c040903020c030102120109060501112a150d050a05010f0b09131e0606080417210915150108010506 67
    0x283e000c41c082008080c600400819040c6060b070007400204140e0b0060f00e20096182070074281030035480d002c412102201d81c0408001965020b4a0702030300944200d14401e0191280040380c1c01d03002c20240ea800750f00c000380b95201c06000c4001d80c10818030449d10750b41d181d0150701000c3c448440e800e1a034000008180680104d03010800c3d001c0c00603003a64084003001d90307100400c1004008444c40d9000d128060300b401d007071032101581e544444030356075440c0d100391040c042040fa03001001890000e41c039000c0540d0103408580000c60341759005816500c0490340d075080780c0c50600000e44182c058402c1e80c6c140c464282018860615090000201d074014456841d807040745004002481031961041c0700b0a00d15200986c0380744105100503104449641e4040750034014541c040100041030351241d503082c40681848161100c00011441c8919000500e0381c0301c86256000038030184030b500140016001068591007040d41d910403044080019018401c01e000c84e102d4030040c0302e1840d0041c0a0010307410f084118 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 126170386 1250 126169136 126169151
    0x613050303030703060602010e0604022202070602211b0f0d0f050f040b0c0a0503060d0f021002031b03040509010e0402011112070b0a020913020903031317010b010906050a080a 77
    0x2415980250f491001103640c3c0c0d03800300301c0c003502802680c0c8030b1408400540741030728060f00856600320f041c100b121103c0d01261400104814176505664109801c44030440d1100038a040c0d120040341420300b214511010a00081c40b07111010b10101203000510003003500b880042400304129810040480c45070580320205007040030168440c65125858820440d0f409003424100707210050000b4000401c01c6c1d10030004075030308540090842e601302d83d080c0c075100700907141810509402295414000e510180361100e9061b0b840e40000603207040d1144905403086148800c01095885c4124407506410a4549004220080c0c0c42d250087c1c3c841d0060500c10400307c04c84012a041150b800d01604034484003040c18001d02c07224100c115809016500c08510300070807040090f0780e01d03540c21629030805800040c070f90282d803000c0c8162014003030081110103c0b291203041070038200c042401c1a43d500e602e414410001d640c8980e4405040781e0781511690b16087c90315070112240c0400410107901251030b51038 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 126171636 1250 126170386 126170389
    0x503060a0509040c03030f021606180e0702151006080402060f070f0308010e060907020c0f0a081225031413030c090b0102060a0605031203040507080106060c051504080306061305 78
    0x15002d21407485128484e90603400d610300a400d0041a03080d600465103c10f07404400d151044001d4001c0c4c034118149100d41c1c01c0d140c01495040100ca8102180011988003800300082d0002450740e0015581d28441c002503580341c4030b91131460140e01c9100000f03001c850208000d4140b48006056441100d8001e0749080c030b49864016801c1280c2d002240050941001044440b444021282c0c0010044034010100c4c02c04440007541c0307005000c0110320401400303420100c20395a0014010040a010054400810321140100d036143c01c0b0741d045560840590122103440700031209140b00207589501c43e01e00217054600c0003011500003211600720010003100201c08039040b00d041710020840782201081801d07042c400281003c030301514259410f814444244090380d00411012890b5403982010344c0c4a6a0342c0c1400c03441c06020b80d00c4000503519010000c40ca107548070403d0001c040c0104204c07031082c40c40d0a0320710625101150040c1c10000c050000c00c0861400030010001c0701129442c0361903080d100d00 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 126172886 1250 126171636 126171649
    0x30408071205070e0c0a080702010e06011203020708010c14030c070602040e01090f050c040b07020f04050f010f0b1c0e100501060e030c06090f010507021f0203040306180f02010503060a05 82
    0x40181c0da003a07035018800d000300941040704001801d9060034418103803c0191000303481e13000702c00444090010b40000544154801d511040c500716120007100c5240d42d54610701d402c408041c4409900502507080040f40f2601705029011044501d0f0b030b107000c05074840c6c90580704c031500080d00001d407814040000e5000304850380080c201a11402d521816a54500000c0004940c070f0303085c03c0504641480200b22513448400241c40c04c582e54001c000e5a521300510000e034150784284d405039802841d00090120040500035964140c48842400d000b289032038503000c0f100b42c05000784644248540300e070701000d0f00045400038030000b60b003141121080e030380d03400c5214251007098103e1070000d2440101003005180c00c0100d090000c0c0150788040c50240340c0000324015100c400d806038148080000c1603421925462400b8488041d00f900c00310759034220081c000d440382e000748026600e19041c0b01001c0c01e05880c0d1a40704445591090035800c00d05450f50066400781c10044c00942c0c01038480ba00043c3e2603ea00 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 126174136 1250 126172886 126172889
    0x50d0f050d020c0406090b0d0b130501050901060306180b0112080d0507180501090b2a1902010e1002030306011101020c2b081e06150a0201020a0e19061103040807 71
    0x82e000382030000603881c2400f0031143c0715845540f140d402c0c0604003103241c903100917601482d03400100b0748240c1d6856804c032401c041d2000030020f203507600e05000c2041da400d06600c01000d81740b0070b01c002e201c402444045000c0c2c03138540d52400341c45a40010010060705225081c4a01d04c0e9104465203800d0140465106080794800c48200000c02c04042c503962039002004400d20203440242407480010b800c00c100d4480d507019103d81c40e64a416050540140c004445850350300000c041d42c1103842d20b4412071403a08900c512400101d000c1000050385020398503109203841e0450225600650940e40d0300c00046481c07013040b80c81003200d55800c00c60860208810f00405000e0040c11310a103054032040311403203068801c080125810068180140305e101c10000401408488000c560281241c0300c8000003086a20440000d0141d00c04c0062882003a03501034001c0c05400105c0d4480d59400301c3d004040c0420018001800d0710f008682c0c10b000c0c0819401102c035806289d00300b80840c2e090644a1400c5490038075207 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 126175386 1250 126174136 126174163
    0xb04020a02160501080c04060e031606230a1202070c0f06020d18050918070810050115090305030a0302070311030313051002040302060702040f1419060602010203060307050d0f05 78
    0xb92100c4040c0b20b80c4111410010f0000786400b070000e00c0d180300d4520203070046000f0301040001505024442da94208003500c9005101c521a01007944e0b9104050030801c80c5c01e407200d05042000100042e00070403442660346000b80ca46a09100c1c0802c410080000c0d44400340031900c001c450f54010800c1c1d10803d800308058a8150000e080d01e42011001400c3c9010fa810a0904080f0400d8240032a440d040810383d004411980c1c585d540f40991100c85040ca0b0158104034200e1242100303096545080340c000504a410708000d1070310324160100c049410300c030b441c000907001c1d910800440451900c203600800c086400b0f4a0101c400b141c802071070f41d080d40e02c00e807001c04400012442c00418070805000c0b011010164600c11813426245038003280c1c2c40e000d000c102030300c260782c0e9018003000d01d40507411084420110f48201c506919100340500010f1003085090108507181180100e0183e0051007203c0c05248004e009001c80762900c4104400f28240c54400c41e000d207030112100700060002c203c0b0500f4040c5 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 126176636 1250 126175386 126175393
    0x2030706030b133305100503040c181a01050c120d140f04050706110a0213061e06030b030115140f09070206010e060609010f030c140f13090209060d050a0b04020a02 72
    0x3060b00381580390002c00c143d04c01d40c6182c84e0410160b6074600b080082860141411600c80c4d03107906100448040079484450007104030090401d0201041e40000801c602d06030b80c514040c00b55800440d814007809003480d00c0c40d0b01221035000c441003094060b000c0b1601e0000045203407406041d907a11103400540b8081c01c03c2d0701020601042140911187d8098246480c0007003118180c18503107640c54044500190241c407034040d0a600c11411504114060203400d0751600140d134500f038021003943c28034483c10000900d4100020040d05c0c040c020350b000d0f110340340007203240366082c0020311a40c1c2d2404903c082c0d020f80c5501e0841c0250325030001c0c07076104079015000f90189602d0031070311544181e802090580f142c0d808000000060303800584024125940d80782c009540c030171240050b40c07141d0030303980b00621040c0301080b56501c4412290013008034400103004540c045680366030107010f1740116144142d0160f01440740c1d0300d400d6541d9008e04d40c8070781e43e50740101b074101250303010804980c41818803100580 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 126177886 1250 126176636 126176681
    0xd020f0d06021b0a050d0e04180b16020c0d020411040515041a070b130f0506090a030201060b0304030215090a020a09091a06090121020603160f03020702030706030b13 73
    0x4031010f2240324102c00d0240504219000350f03660300d071200e080c03055034004c0c44844102012140c0711075220014118060440910842550410101200c01168480a0350303103840c101900c581d00c08603d40d0602100030308203101d030b4205a801c210241039550042c0ba02a54103000000d00c2da6200075a94480a420481481c1d90320304014075400c0200b101c84151200d010204030302e4000403081004c660b40100300800c0ea40e005030940c80e00c540382c424040d1002c1d11038425401408140500818a20388083c13103031300200300c0e15581b59103040031404204c030040c0240c1c10007503100ca8410301c103120255000510100750f03907445155500261b00070b480f82d080400e03145c2d034a00c0c0140c10407030142000521418100d403c071581d45040c10008800440c140503070807001702d64070309030183c14102c002c0f8902c2641d8000d1070691079140c00d400303c1e44020701c20030640c00094100507415031400e001c0d10803245400d402501030001345013003480039406404259140b54000542c945100716502582c840c2c01c040c02c000300c0002d002403 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 126179136 1250 126177886 126177907
    0x10f030515061302031f0803090a0806040515100812090f18040818060c01090302071a0a03020a05040b0a0e01122a17090c031011090d020f0d0602 64
    0x980015401c005800e840414040181e80380402802107030401840581c0e260740c1d021610400409014280400c41d041880104e02c10b030010010300003000b0705450180c550b41e40e0b0440f03d80d42d0203040d903026007141c002036100d501060410180b04e50011607803440e506031a40d80c446407850f12441540004080c10f0100785034199143c45070b40099041d000319802d080c1c1d45c2610742080555140600000c151010000340310000d685654145802c01100074003064840e590710390001d021b0300c0174000840050040d0040442c20040041d0b02d10004110200300074203011451005030029803080349001c044c0300c41408001200c12405009000f440c41075503070000807003500300000d0540000076944006003400c000945103208802480300b021038040c400c081d11103011280068840903120310347c41f01c5040c15030003003000e480302c00202c190142400350211481903506031228405c5a005441c00b503010a4200542c408600e04040e504a046000034803401e40d1412440000b810181d0381e400440d451600414003c00c0b4 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 126180386 1250 126179136 126179143
    0xf02010609020a050a0f020c040f0203090d0201060b18010c02060d0e060c0301061409180f011401020a030909090507050306070e0a0b0a090e1504021c05160801060509010215010f0305 80
    0x1410340280c25410f04001c0031014200380140000d5004200310705640f90801e0340f00b001142c1d203090000c1e00800400003071072280c2d0b0103903000301ca203100e040c8250410b5120b83c5105200f103008807800c1c00403240c10451210f51411901031400300841c100060035124001580d240e100920034060441400924600d00500309401c0500003028014851400e10040201e25009000d0302051002500f1007555499000e00042c041400c45c3d20101d20781200c001044150020301a0300e078140c48001d40110300701d2913900012a40ca82031550014001001c4c10700401a03100275811021000348904151006035465102192030312108494540c0000c0b82c840960300391381045140c90001c1c0400714a8107241c085074170009891412544182c07240c100c8040c0c001080a843c0e00c01c45a1071060041c02990740742e603030302c0c035040704c003030080081c4e503201340c580400308901c03902c140768250784400c85403200c420982c41c100007601c0719040f013440c180c1540a90b14528202c0d102e0035540501074030640c0e403465407542c2141012440c = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 126181636 1250 126180386 126180389
    0x112081309050618040b0604020c011b020f0f060c040302120c150d14010b071e0c120201030b01180b0313230706020303010e0a050c09040e0a290606070f120f020106 72
    0x382c07680204c20301000c1580c0d251001c0e400340c0d041e44c015a40d240c1401909004005d10f44138110308440300f00e000181a81c1c085903100f880c2c80b82e042100c403500742000aaa882d88016103101c45000c00801c001c2005050109581040d4509507054840c48042c4070007041c0f10b4100010703040c410441c00681c1d1510b5007450b114034810101124407240183d8101304420f0f500313118004000c0c00d5030000340d00314407410001c22541903c00da808000001d601d69201c0e50055800d4901c5012408681064140d01055204641c40c000d86180c007150910700903e000c0034030344a41e001411244451940c40040710200e14440242c241d200e4a05240f0005031241c2c142080c188030305600a0f00840d082000104400c400032403030140c022514400c000344a0b10b840d00e03210280d1103611540c5420506010b45400307050303c0484c44503021400303103000c07071900c03040d0214104030f1988640e0a41e030109110320100b001400c1c410040c00301c1c103121f018175045031125510352086100d00b0307c03071100000d0710580300030f21841d84c203009150 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 126182886 1250 126181636 126181669
    0x20a09080d0c03082a04030b0108011803051206030705060f0c1c0903060b03031e030f07030c05121504050f3114070b03010807050a08120301120813090506 68
    0x2c2000990780c001c29042c40613001d80884414210140c5103480e0b250703240002c02e144071120315905c0d592840d001c50785010900c10141c195180c040303844170001c0c605822032002076240c0da401d490200c1c0400c00c0c80206901910707107a01482554000300b41ca482d900300415140703030005950b6840381e101d499001c1c0381c1980003110749421080d03050502c40310340c0c00c07a1010041d254456004903062451034042890344c080e40302c00090300d82845110400e1010240000d41c0981c4c0d43c0e88140d011a514600c0541c00e80d16038007420000180304010000c00075458000302a00a03140000044040000c03000240565a003a25410b01a60b0b40409014802d454200200342544003041c1040c140c440c0240c00e00d8081d03d07403000107400402107413520951040107100400160514181094407561150150740d940c103034a008442c050491054080707116000010f01e12071400c0355102e11860360f0f081101c0c8010524525a080301c405409000701030894008076080005065844000035452030518100316040341c41c10600b0 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 126184136 1250 126182886 126182897
    0x115030204060510140f0903030a03050106030c020d0207141c05031908010f030803070c0c08010b01180f060c0c0305030c10180b0106030b03030c07030c0306050f090c0d03030f020a09080d 82
    0x10f400542e0054407900c8a098800c5c140c40c0c4580a8003222440d5118149000b42c0c0b50000003100c030561500b687c0494141d0710385640030443e0900c2110242c5e0782d00200d0108a016903c502420019034040c011714483c000e001400c00d03003404100c0c4008246003000f01c0e001311015000403916000d500e0804420038260141032411001951601070100101d040078040508402c3d400400215900e002d0041c55120f04c2d40300307031007420040c2e40e203541034000c165a11002d0f0026000300d520059512a00524000344e4040101c0b4610640c540b00040e074810540007c1100d2043c512100080404d9050002d810100140c40c0500341141a03220128210360756900d003d8540d41c1952511000310301b80c050080e05403201802c00082d1182c10341c0000c0e02d14000d855041c00300d03200d2120040100510741c030304081240e00c55a4144115182c020381d40c450200101c54803070881c3c1c413030302040110386060490251058020b00f4001290541d80a410013640d00000300500445c08015080100c1201040a87e40101c0f841c90070 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 126185386 1250 126184136 126184159
    0x901060504031709060d0e01230f1308030a0b0a150503070c060b03030406030b150405150a03150806061905011b05070b1207080709241101150302040605 67
    0x1500e2805140806804200341c150b00d2403a042008044404100000f000c007034813400004c1c04500940713a00c02c00442103508120080200c0303120380c5100b0001c1c2d8100303010035806649002c0e0ba0039268070010541107444440c01c030640d003c82c02d050000c6001e80d0a0100218025014100f40700b40038259601000c1c14039603800180194075405000e49402140700e11704580039503c0744c00c00201034000480300c142e050000280002e280d907010784c003400841c2026500800000030f40c2c8009134143c0160f01c10160003494240c0020303c0031541100400b400b14a9060009040e00441c414114006460708610b2195108400784480b51030030b401ca8820414400c01401e650300c0c10000002c102141080700305007480047d211510400c2824402040602500c51314142c5a8116800c88c003901c2c48161000008a080d80021550705485112071100b038a601900075000c01e03a460013a1108a20506007180800080380a007101d1072200380107d120f05040701003020451401c5004020031508181d01803407047c1305d03103100c = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 126186636 1250 126185386 126185399
    0x501060903021509031f0b0f06030f0106140d05010e04050f1c0f03020c01020a020c01090e0108070311031509030406020f0718110d0c05130605090d0b09070b04230901 73
    0x14400f0061103200c2c001c0c0c0302c1c10044040703880c21041040d030952018441c8042985c012060f8454060280101c942e0700703e2409a40a101e85403105554000c1e2600c204401400b909000f6201d10228200c080305d00c034900540d070403008080307601c280c100504000d040001c2c8018442c040281610101c105009010341d0580701c2d56102c139460080c0805004c0c042600100c98a103030003541039410031a000c40c02503540d00035025000307449264003c4901d000c07403502000802d94100d5031050074140e1340500000c0030045e0442d01d40e1440407000c0440c0950520503000c10038a00b50040303060b18041d8400c0f10007136481d1814004044c0c2003040418001d00f150b48000f02c10005100c10a0400f5180c81c80c40c0e000140480381c0702d0f8180320780e00c12040c440e0000340c184078a00d015180d10200600c0c000d5103545c0307150042c036212081110745110300c11200c1d07480341c0344131508130200303174104c1c84190001070503821948001d644001c02d600d00d400c194404081c0d1180e9215055210440d001c0340c0540700022103800360558100394 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 126187886 1250 126186636 126186649
    0x3061008070e040e030409050112030503040807150213170d0801140409080a1d041406090a06090603030513051903060903140705010f29060d020702061606050106090302 74
    0x800620400910401080d03050380211003401100c0300107001030004440204c255039896000d0310070040c40d2490440002102048540c100758010350550f14285540c030ba50300e03000415000307144141c508404966600c07082e8140c51009002d41190060720f1001549050203240340c1c0c442c14960034055402a662043c80d40e41c1c4054040c0c19920070020b290051001000400c00500c2c0074a40103108110000b07030350109030f80280c0340c0080c14118030300e80130b40d0b0703e0040d052009071110341c003c06046490900204c1c4103868950080755104000e4417000601c43d65420000041d01c0150344140c1c00f0910028408400780c4002d20140003500055030410401d250745040c6943c00b5510b03220207000c550780c8190b03c0342050300ca41101c44003407041050b8180c44d680d950807d14020502a08440861407030300da01400000b619202080c0c03048150102e01e01880c1441050040e1640018160150b0690030402d420050355084060541c1c00000b540581c01480c003460902e080b01c0060300310f04280401220701700010794654 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 126189136 1250 126187886 126187909
    0x120801050f03031c090b100e0907060e01030504030c0219140d0b07110309040c090e100503030f09010306090207080714011a10030e0d080a152402030708040e04170306 73
    0x14005594025255044d183c0100300450008003964044c00500000b2401180d03120140c4040c80c800d9a859280c1031041695001c080c441d4a012032542c5640395a0303907000c0c4d48032551003802420080300903c50313580001c0203074038610540703103103800044018005418501c2652030b0380c40c0260f48000c0501c40c5925014144a0001d000508010200030803890041e0148282d58292101500500c0f40b50b124010180101c0d2840c0660100c401d02e14001540030803904540c0c00c1195400b401541c903005042c0c540c60401d900c4808218141501d41500088900080c030080c900c0030b0040c02d1454580741d1503e081c107107520710780010400a030304000c100340304420501c082e510100c8086880c440042c02845c8240c02a1048a1006015000e400182d600058100a10358400c119203001080700e09104040000c292090b0700440e1105140c030107c41403c045911200c038a000e019004903420030349965a203802c3c90384103400c04000801d02d6003c4c8010445000e010442100c00d075000b580c214500320010807280d030b442 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 126190386 1250 126189136 126189157
    0x50402120a110d18030e040b0d0b0705040b0c0d031803170618040f020a080a0812070504120609060b0105030103110f0a08010e0a050f0309030303070806041503120801050f0303 77
    0xb41c01180c042d644901d02210300c5085011001d12000c0c2c403620300c02500f00100d40081e4041a00d240b0020554030f002d100d1304065110007005210130307012940b607188011000900c110b0500204020200e401e04004000c0e06851024000406042e100008010241c540309008054222807a04504000940010303210f0202c4004040b100e8486d076941c80090038026905003c009a089440240001c1c05079a4044d03201d036600a403588900315581c2c03040c40e42d65812030340780541110301c140600c074036083c07031681a15007104040c0b0f8503a040a807140d41e510500c0d007028204030f8801d5541d1a40808028590103410300001c3e0908006065616544403c01c01030104104d00c7d204580c01c0701d0484441d501d07c140c12003d00b00300c000030413441f07000c44000da54030803030050152107a1140e003c0b00360303115800004442c07509034003801030350454596060035240110007800c1d0075441740d155061081c0c85202084101c2c000e500a46042e00010000a0054001d502c10307000315003c2c09015501420700e03100001101c03200030a = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 126191636 1250 126190386 126190391
    0x8070b0307020d1404030606030f020117010b070305370306140607020105070c030b010f030b06060906071203090206070317072d1205101703030f0703090302030c06010312020106050402120a 83
    0x6054070b0040d11701c20740d000100420b14200c0b000c402e21802c810020b030703100e200380c03120010f155000700071020200003440fa0002c4250104082000240b0900180c600d40c0500f080c881d000000d04006440886440d03850700500060310181d180e034295042c00340e84014001d2030000004a00c501000c0307000c900c90554041d040c800d002440600b00542114400000c43d00800500381c02d5840d2640c8200310134135803000f0f4900c880300c14046109403608600316605890000c2c0300c945086520b54444100341c1500303041b5010306075140c0d038100250300c5000c0180100d40c4260b85982d844400001c103060340540240c140010040940c440315905441c0382c01390b07030044184c40403100704004022402c0303448036040298140324608040a00c00304141040d013027000e1340d901a02c1001e003030a21030059613a0307000032031b04407a002048201042085000343d00003c0064083d1040d2071511109500b9689000000e03441100e99500b004c0c0841d0f900d135420f10a41020780350454007907160601e220b05542e42c4040203400c0103107155 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 126192886 1250 126191636 126191657
    0x70b0705031902061503010b06030601140705010f0902130b010c020114220801060e07050f0306010c050a03080a1503020d08031f170123150103020d09060608070b0307020d 75
    0x40d040068402209030188982c8041800c02002900c409082c1c0d1041c07000001303280b100c5603034541030082d80454400030f4181400c582d60803004542c425001e001c174451f030210030000003002c01da080c00b03101079100909402164106451041c40300d0450350140000e449407510340c02c0c1c40180c0e84142c81000403030702440d00040759003d00f51a946c0510400e40715980c000084881840d86900880329071003200d054070001c0184030381e50b6a56215a047c11038000c400248204401e50700c440b940c001031500941d041c03402c020070102c00d80d151450001e803c0002e4001c20181001c1080403290b6008281c0c02c60b0181d00b80140c0546954041568608000307802050044044001800089051940c41c01d108440b101d0004241c1c1d01d0301102e40f001e1142d07503400241e50030074040750900741d08003041859200808003d54804d60365481040c038009103030b0940a0406808106030718244445001d0110100d0150600051071032074010454074041aa5208011030082802000b110341e401003140740c1c2d5400a420164046c0 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 126194136 1250 126192886 126192893
    0x40f0804050d0b0f01060e1005070323070506010b0a1d0f10110606031c0c030e190f050d0b0f040c050d06020c0f120423040c05030402090c0705070b07 66
    0x180126000990458209400c480a11020b280f1150068090400303084007a42c850408581035502c840b155504405800c10743d00c0150300c40c100901c03809002c0d1811001c440d0112001c0701c0040018404090300c44400f142200c140130b400d0049a0040100e4040300340742081070013018000c4400040c001c848070141c80a860890b844009440d1092980180164240f50607081c028055244a401c98115032180c2800103a460500003440d548001d014206081c0c01000b500084500c20700b00b020032001c0042c5501c90591540f58552a8103c1c50800aa440d540c07c0c00c05c00d506490541543c88a48515142180c0502040a00c0c01554108144816843e0b0b26900c9040a10b40741d0001c0d40015002064041340e403050095650180c951109004c00b0360b074086181d07000d00d65440c0303c0c030214004c410b4002c0004111910744040c0e00500e100030804905030b0780400c0f07000102295003d0207000c0c04520004200011441d01032503466100000701421b600340041901e4441c1c1e1036a441c041d068040000254500c00d0 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 126195386 1250 126194136 126194153
    0x702012c0607140604050102030403090603090b06061c06030305041707180c0203270f060c120c100204090e010b062d09030a14100608031822140a020c0303040f 70
    0x70f0340001c41169228101441d0680c000c2d8001c03a0107800081038210041174003840f078001c1c03110040c1c1180000005442e0181001801c0d40a00420404190880e00d02031801c0110b0003000300550103502da40e40c540340b034044441c00440c2010000340c400d4014100030311070002680e8103c0c01042d01340342c0001d205150113401340d1445c801c1070340220b0580349034001c1103c1683d28101c0003440080988085540340032a1050103800c2c041c44030071000c103401c0481c01e0900105004082d202c0c146010040f610105240d0121108a0344517030448107100ba21960120b4a400090040510003c0b003900c6d19413500d8803000480720490140034808102d808048150340d250b0403c42e003540c20851000f23080d10320510017850035420350300315115216480d014003990000140b1007031007404100c854060185240c0300f050302201e0100200390034500c3c0d004034403c1d125102040e0100c0090586200c000d400240d031420203081008502d8000d00811065004000c408200700e80070050301c0e0441c3e4030100310f00f10103440e458000758 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 126196636 1250 126195386 126195413
    0x50c2802071a0702210a060902031603030302040f08030c030f0c01060b03130b0f0903090910090c02060a050a060b0d090f05062d0603060129030c0702012c0607 70
    0x1030360207800442d82d0340d100040e0000d050061007103403011900d026500321010044d6a031803403644203800c41da410101064441e00039940030f0703100030180d07510400000c01504035822184c20640010750301007402d0010340004c04690300a0011000150f003401504082d0315900e01c1900e4078103030b0b4100c000c50000710441094002c50080e00c0c0400341c454591820180c41c152103407550b40c05890000c3e102c001300c0d6072120b28000c401e000340b034603002541c6403140d41c0d81841810300c1c000d0b00009450150582c00144000e1750301c2045410b01160307010f44405d044c28000e0405495018020440203842d0200810800720144212140c8981809000c20100002c0c20940110800740001070300078050f8100704000c0d543c2c10003600040500488140a881c80f5001102007848401c4038410f42540c4018014001a401202205501000d15528003070760f602c40c25004886070415501400c0500020400b0ba04540e044003a559282100c210500c040c0d06415502c06600003a003150103015030b00006041041c020130440010 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 126197886 1250 126196636 126196649
    0x31b010b060f180f06030112230c010f0f21090f0602041a0f0d1d0d1d03160501030c11060c030703051006080105060d0216030801030501050c280207 65
    0x180c07140c216850041c40703507000c41690903030f04150f401c08114919006258803c42c5101a001a0941e03003010003982003280c3c002402c0d0f640c0411400c5a428103400424910740d81d1020102801c240030b1a0000944002c14404030103060040300c4200303402003030b0b1088201c0002c200e0500308902801e0043e20300c20050056a1000c0c00e0b0070030641801d014400513800074012200c1c034181000c000010481d0810355406034003420740e401e010810503116181d03034640200401d41301c0316040071100751090501602d803618141c0710030f020171140c4d580c03000300c0030342010a100d0110b800d034090013001c661080c030130b8902c0c2440e015483c1890340d50404080024131030700407811303810141c0b4101da2950826910784440c94004450140000782844001080c2c9000703100080129625500c485070350307900b0482003100d5900100b0780748410329801d214002e102103842c2c803410034050194951500070750540c1011400e54200030005c0d0040d680c2080700840100c00d41c80b0045900e44994684510000d24480407400c0402607130100 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 126199136 1250 126197886 126197899
    0x306080303041a130c030f0804051f030b060304031b03020f011d060108030703140307051e0306040b0a05010f050d150f08010b0301050601080f04060608010509010b0a090e031b010b 79
    0xb2003000360303d0004000f92110444022400c3ea02c4242400e00a41c1c6450010719800d64010104009100c481080c10418865080542480c1d01d6030041011030064901a12648000550b44102c164151242100102303060313503038601d54034260300c000e0b00d007449c2c90303c0096207140307141903402c1498800c0c020b200a440c000c01c0203100300701819000440e01c0201000401682c02510000151150300100710fa0200742c2c1501c0c0c1c04e11310785003102c408085800007070020041c4841004040c0300302078058148051001e0030307000152681031140500080741c2c00c401c581406103503409010320003a138004201c01c14143d828a0119550844481100d0141c2000f01084540700359009011503d45c01103603800382550b01001c000c016504001c001c05003a80c006403040c500bc20102c00101d460740e205110755a5102e030081002244043c0ea46002c0c03421144115040c03149d42e5543c8500e00c9051070605030f000024009034209200b0b541001c2c002d140c582c42030460720024202250340c005000e40003900100301c1300780020480c = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 126200386 1250 126199136 126199141
    0x9040b06031c0309020102060108034003080301140103060b0405150f0d060e0a060e07080604021b06011e050906060a02100c08041208070f030e070801090c21030507030f0306080303 79
    0x5001303410b114404038094022000042074007030340041035a0b4011201e01e0b0f00d410352140303241c04003801d41c4030404070b0106406070040d030040b00300d182503110001e5100310030b081d03529032404009406856414040304c0c10141008802c006881d0b085d030a590640380304039034002c5104070350f00c1d09940324426200c0340498068003007565a02281306a104004a51041c1203400c801d03038821040e101286c0c141d0140b1000c8164540c0410040c61107404907540c0510007610061030701801d00d08003d400420203040441d01c2e80312000500903581c450410031401e807028402d54500c28200720001d04507520041415005800118044500718400c20200f0011440c00004100490b41304900403c09101100d05544405400e001915110b00c00c512407071240009545400e84c2080d1030000714044d164540c03800519210b01c1e6000705540c230080c4a060641881210a0007510b0b1078410300e40e1410301c00042810000c06141c2c480d80100b40c01c4000c44c0c1245926140c5607110412041c1c050b00105196007105803a407002008 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 126201636 1250 126200386 126200443
    0xb090406020d06060c0804090506120307050c0109050301020a0c06020d06030f0303060311010f0c0b0405010f060612110f041802040f060302130f050307051e0303160303050603070509040b0603 84
    0x1016441d0002c8820b12a45885070825104203001c00001449007001b0041003029540c19441070350808002400650703100d07a20080c41d80b443d00691016038154204200d00c981c19038201800c45c004010943c000d508140f818100986641c0750400d002d00983c1c0c0001d20074803684d000368440d0b4059544046120090451400c000300100910f00049525040c007000445d1150702503043d4110340ac0c3d0681d2018101800f582d500c1d1100303400034104807160341d02c0e000194400000d5000e044083c101d1581e91449100c4215450380035207007604e00b1901010400c01907500035481040460b41074074421019140d810400c2d10040c8020312a6034030002c0d40e42c03420500800e00561540080c00b1002c500703402104000e0b1180840c0c0342407002d030321035180d05502c400010406820160312400601110803410483d081000b000321f420f5500c0740c44e00c01451045041e50004140e054491070360404130580c0186101820304022490040d030207400900000030300000280b0941e0104075484207c12030510703110301c0102488 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 126202886 1250 126201636 126201641
    0xa08070801052401050702032d0c060309060f0c0c01060b0912060601020d0c060e0f0f0d02030f1608090312030105100c0206070204091a0c07150902030d120b090406 72
    0xa0314119424000418544412500c03041108019580082c0d40792107010300554555020010480c0c150141541404800c04000b105094205600300380e6408104002032003802c00d4916040180b1503070050040c00800c400c0054100e41c000b03003110000406440302c01c83c145180c000c0301e1011990f50f08051010410540d410050448280240c0c1c2250701e01c0c200e5140140c4a040c1182c40c240181d0110349c02003c5188205000071105c3c0c05941c0000c2c1e09140c404038241821648811880c60364012151007012132020044800c0b803c00a101441c140707203010030140b43c24031440003034402c3d00c8032141a2206000300102102c150080c010101d40e21400c0c8004c0306c0c5407941007440382074402c0c1c40600c44d03c40403e000780c12800d8450341c02404240761020560801005002054080d0b920803041d013a510f800003000075400303010b0384410402949458143ca401c56002001000903002d260801d8284801030f18006503031007400310141020913214207078004810042c003000b11500d40c050720f60410700c020711401380d = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 126204136 1250 126202886 126202889
    0x1207030314010801090f06020a090306090b070e01020607082d090607020c010203040b090d1a090c10031b080a11070804031101090b0f090a0b0a05030a0510080a1407050a0807 76
    0x5410041540c1c1c1c0e00e8503d54222040030300e028103980c010f058184002507003540200550b1a07242005038110b0749a4840c0012201c80201c11030361043c400c814402c560350440e4194403814000d20044c400c901d0080001404024060b100d03840460168a40d58284c4030042c2507581e0f11b41500c144000c40d8541005140d07a85c0c5410794090380980900a0b0600995101200b00d500b03071440c02213010720348038007402482059120404182c440078104404484191201c542c62405040050001c1071007142d448104110005019032000074140b8102da541d10b10428482951701c41c02c0a82491509551416492406442c11820b40648240001520010811407402600540b40110b1101c3c114122039401074405482034020204c0b03c500a00514500000303a0004002003800586850307c11595101046580c0e00103d1041010840100400400aa40b0310071258016428590502000c2c0786c012410b854400c8a403002e0000b0f01d00d0b22181d9210b400c00c121343d01c0102409050843d1081c3e44541070f03034569840703 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 126205386 1250 126204136 126204161
    0x9020a0c2108010602030c070e040804030f05031201050402030f0601110f12070b091501030f06091b090f110306010c02040603021908150601120207021314010f08060f1812070303 78
    0x1030b0000b01395a8030010a8410090b8007100034440d81d41400400214884002e0045808120070000400091562000c02111070302c01d90045445003c0c00d840b42c00068416005a809903206200b000151088010020b811410038201402c1a80380c10301d0890811071a01d4032290640f084142010003424a00014a03483c0e024402050740303034840d41c0480741c42e4504141d4441002d0600d200510100f0700c0e0030500b004207441100009040d1601355517071081c040041c48006030025417008100044100b0b40100452001c20a200304000c4a20210030212400080c100904000c2c035902c0074800c5444a42c032601c083c40d001415107030b802d0300200b41403000b0364050023458454000c2250000c5941b1001c8095030148405855020202c05020301160082d0403000b0103036400500d1303a118000e040d4013889400d04c20f0924013011140b541c10300d00700340d01601d002c1c0d1241400703034005400c001001c144404141c1c0c00c03615032100200c001d17003642c40d041d140c05807401903105101c0001401c80101038040e07100e10006282e = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 126206636 1250 126205386 126205397
    0xd05040c080c0619050c0a06060603020a090e06031f060503060a02070c08060c070602131e050114090a0504050a0e0f0c0a060f02100c02010221040c091509020a0c21 72
    0x880b09000560040075050540034518503101d80000703009002074a00116200100c2c0d01030a100c0d02c641061b10300540c00740d80445c1c1d0001d400c840b8580c1c4078100a011f0600d1002264140c24180c01007a611601c0307101c03c2154046030200d9041000302d82d00020003c000003421982d032400cbc4031708000000c0d405400d08480d01c07111130340c00003035400000c00d1492040b00c100c120f180c2040c03ea5120350000c0d5101000d848c1000c0d0f02410042804004c1030401009c0d00064400e04c04103c2c1440000340c81100b200400818890782401440345d1039541c0300c400001d441060720041113548844084401070001b4640640300c1d40103000402e00184800252648901000c44402c2103250791900c0c15111121041c10342ca00582010820808591158208480d100030500c0018580848020801c40030f210055103078440402d80b00c10f05c418400700449007005040540d8007003014606181560b44516104d2080210b05900490941903241c01400355150042d048040543c250400e4820380e8140d1880c00d41d01400b199 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 126207886 1250 126206636 126206653
    0xf0307060206011e03020a1809060e1608060105130908070c0b0c0d052a0705090a06060201050c1801080c041a0403120311030a1805071d13030206070f050d05040c08 72
    0x1340307010000101e81e006006a01d010342000340c86036040c400c001600c98960780314203c40c000510144070f81c410700991800601450150841e0030010300e03515601c200100d51000005004a984201d02ca02015061702c80004094110707140c03170141c50240000103000c11038110000201091a480108802c10041e01075070144c0546050030b41d40d50041c0a07280d4403d400c03a10118030303816003915624150b84400e004a5241940d61000900e880700b049505038503694844004200c02902402256001128641c526040012018511503018001900e1038104102c44001c40e481c15a1802190301600780d540d0144003801181030044400c1c4d00c0b902c41161000c0ca030190b1904034510a00ca030b061034544481c203151464403448148005400c0c42007881420740341401980000400401064009103905030f1224800c01828103050b141d59001010042c5440c00f00709980c000a43c0450001c0e8000100d082c45440903400369070444450280a42071550349192000344400d02c0924007202c03003112101001c032940034 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 126209136 1250 126207886 126207929
    0x9030a060e0c0a0b0a0206011206020c07080313080f0606150f03040809010f0203031e091f06030308060a06050708030703020913090506070c11060901020c0a030f1208150f0f030706020601 82
    0x5d100f034514203401a000280184a204c401c6110b910445000d10009401c00c074050f2601170800b0510751080c03841d82d00c0000c7c1d0800c400c2010a40c00002d210a42c0030348110916240f000391600002041c051080200180c080324440d501c0c403e40f0082d041c03101ca102e072a441c0034500300e040b0307901c086815808039452900b41c9002601c0041101e1080410301800c0301c0c10341c400700d03036120001c0000d4100c182d5401844e0041c00030780c40b01003804149210b1100007284140c82c6040183c0003074030103852680a402e45003420711501d03400c00200c40c4166844450340e0341e00d0760f03001401c078000d011b07800c1041c1d40302130b030601c642d4a81d4100750004403845000d00107a40d055224510b09544a154460009040852143e03400440c0e05c1c05038040c255001c0d044c0143e4000790b6820703001840100c82c0380c0084403880c40e040341c0305080c011030b010030300008030380e80c01c0c10041414030000b548902000840150320688070ba040240e580c1e1a07400c0c246415030400b600700c840064071403601945440703007401280e003042c0c3c1d08200425070 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 126210386 1250 126209136 126209159
    0x40209010f150c060618050604061202010f0503060114030403031506020105091509070509090607090504110301050d0c0504050108010b0102010b03010207020609090a02160f0510050402031209030a060e0c0a 90
    0x480d0340c201180b401601080c003098030402143c2c0c0094a54940d2403030001a00581c80c89120742d000c1d100c40d0b00081c0d43c41d1020401088583c40d0300401908180d10601c80c0060341c00003e0001492450f0030072a849079280c0b4012100084490071a583c504004001c0c0420990540c01082c07000b0070703020b4148403090312070310101d003200c03001c43c0c1c80003050f030202c0480200340403050030b003941101c80d050940d500c4688030004180f94090076100640280d02400422540c135a001401340302a010403035041c130481c0c0a0308110580c50006010305803007070046040100c10080c24058020040c5409407091102d5a540e0344841e0080c010050400c2c055401c0c0500d03190185010300c00c5520311030b4001c1c02d9605081c0f024050180c0704400500080c2c0031b540c208032007003074105410340719007805d8810100c40580c60850324016003801011a031860145e420a4240030060383c011400304100c072002c064181d22420000001380c82c1c0b21403600050501d5207401c591649005004ca188490700c001607480050096983c1d41b151507 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 126211636 1250 126210386 126210389
    0x3080a020f0a081902070902030c0408071409011701090215030619030f080a05070c081b04180b130609110909030403030207060c02041e0603170c0303040b220308040209010f 76
    0x1035003c04000043e036400d143c0006a1055503039104540c4c1d410b882d618403c049a0003034800a0404002003410400000200482d10162044458980c80010440c01140300c0d40418010600411702c800b40d41120020258085987c8580040003054959420030340400c2c29441a0307000c5001d0192107512030000b1205035a43d204981d40702c200b4a041980548441d140c1c0d0300a508028100901008861b010031580c0d441e42000d0304458001d07052424241001c03060441c6118041c6002d80d050000c01403030056a00401c20420341c018944e40c040e0f540e05030240c0c81552020400400d010b191030b903203c05100c10844074207440001a41d660221741c6894109507501d004910000f00140d1183e4014802c040c8105031803001d003440940701203103810f0410758550b04580610944288250380c0d18042080c41304849100804140020800b03240a00090301c0070f0f100d1200030406054600700101050103035104928452400b0020b5132025607400d43c80c0340c02841ca0b40c0c181e9003613220381a080008140075501a48020 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 126212886 1250 126211636 126211643
    0x801090c020708060a020307020f03040806011503050603190204150e010e0609060607030e0604181425080411060403080c060f25180602010603020102100b0904080c01021303080a020f0a 81
    0x18580d4842048401031352004203408e0031409403403a038017503131403040010300040e145883c0a04030640c11300b261031810340d4500403840105800d240c02d100c0b40742c50109003000c55984030740444403403400900204016010409001c2125000d5100001d81040050421030513a6034000c0708080c9031b100c60007000205601680c40c598416420010300300001e01480748094401400b40c409420300790344800640755500d0281c1c2060420f91281e40081118011410f903d0703010078154004126058501800d440c01840d13407440000340543da0300414140107116001027006500181196a100e0700d07480c090b00b003600001c109070614072419021803a080f0075140030910400901d100da04031005060501e030281018040c680043c0111100030080d4180300c45250340c0a001c03641c00104d4140d107584002403034041d03403010742000e0624003401440d607a03903030900068000d604600c0194441900501050080c46600c130300068407598280004100510740d00a0304001005400f80c403d111010070095460340c40d6407000a = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 126214136 1250 126212886 126212893
    0x13090e0a0c0e100b130302090702060403050a05090f040603060e070603110306091504060e1812040506070201020f03070f0c0503010e0606150405150904060f0602032a0a030801090c020708 82
    0x70700050b55840000b03035120b000c0212510085503100052552980071444850324992121018015801d0038070540d500090684024520751420b600e008119018100d111001c12400040980050351441d00045500070014410448103a9a180020040c004600d401c1d91030301500400150352400b0788604000881082005071440d46d4510800120309001451200da00c49036550080c1c031621303240f044001414640c0d00344031590422080300d80084150504030b4100780d01a0440150307a12151064804070391056400e41d4941103070740f0042c1d060400d02280410301d4803002c81e2280510200b40c001580060044202416098a500034103080c2d503c0405042d06a03480280400c00da401d01800b204050b180c01d4922900f040d4030ba44c0020740c101c8207071507800451440807a03c03408900d000c2c80b82d00010040c16500c0f801091804201039240d0140d11501050351007145000e9070041180040354000b404104c040d1502050a07140240047c1d4082c05a1a025444d0903004034203140005190002e443c010300c010b = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 126215386 1250 126214136 126214139
    0x60305070e01030c1a0711271005041e0b0102120f1207050403030c0f02060913020d0e07050d1103011e0e0d030c0507170705010905030a12050103020d020607050c0613090e0a0c 77
    0x155015800d5030030300d094114a90182280d624504100c0c400f803070707031023030300004503142480c43c020400b441d02038001c1481a898010070304030401120f92002d0311000005000304503041000c0042c2d041544802110301142c900080c28081c00441c1d10007010000c0b010f000c504070030b03280e04130100c03200c5c0500e01005011940c400d42c0c11000c604240c070405801440100003a107005494004519002044e0003086034503500072403e11030501c10b5000340d800c0010010020304802c1c0c82c1c40e001a8071080e4200005d413000000c80c10320790f241d803802e402084079100e602445041404007409800020884504030001038041c04c02e688855910901840c8074000c07551781e0340c0c3e003880b506e030b2a401424050100900c4c8410320400008000550a0042a42e028080c90281d500e500800e00050f1554414041121010340b4050050006035a5480f03480ca0140c0c042e10f40503190401850424a425640220264040310100d41503207403242c4c035504103040e5114007000340040c94540070b01c0356444018440040064101110 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 126216636 1250 126215386 126215393
    0x509090c130911070209060d080f0715060e1f0303020303011707051305010f120206120a02090405040c170c03070311061201032001051c020a03060305070e01030c1a07 73
    0x500700e02061a18286402a5584540e6088452207902d10a68807800b02d80c0e1029440c040c84070945c006030a440162040095035607250552040e01c0c140454560f000c207500c4280503922500710848940210108003e43d1504002490b0f202d00b2106882d40d03e05182e594024140f962a00c2c9088903419001141503900304020400502d803034448206c0c1900c9440e0b40040c007036855640400381c1c2c04d140100055035504029030b400e8200d1282e08502d0041e059101c1c40c0c0010307102c6030308841c80700003c00d41c5244c05403101c152440107413040300324241c0e11034241b01c20301042c07000034074480e01118a0b00e042120781040d071240c3d450700c50401034004d07035040e00140c1041011406d0807070350009048000304842c1c9410341d18054648409000e0300b00781c9480013102c0900c603401c1c2c00c0300d1454244003024200f1600704100c001d503610858400c00c46900b170703a0341c000c10024107042c040e42001e0040c40e4404141c07403419403500d00100d0311800911054550080003080003c064414440c040c1c807a21001b401d2a14050341c980b03 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 126217886 1250 126216636 126216661
    0x9010618140a050c160b010501181d070c210e010f08010302060d140a05010305070f080303060d06020d0608012403020907111c03020d060501050a1209080403050a0b0115050909 77
    0x10601c08800e002003020140c581c1c50301400b0b20301c040c8503551b20400c550401000400c01411800b00340c0f4110407100c1e0a00c96040b944040314828500451070850940d0381c1c107411076040220600080015514402d400000c9031100860722050005513210f444000500c401101c28144072421200070644460043c405070610f00010140a034100c3c0c00401c442c084c14448200c064811071f03407001615076420062007005014003015004000d80b00d42d008069003007862007916844054000c03031207030781d02419641c2003207901d0f0151014810004002c01c02940d603858080d0190089407040c080c9040c0895a41034076808402550b015250043c01d0103c06543d00c907400d4458044400c2135005912406c80e02c0c00c1100c6400000804140d403947d009602d40540051640c20740340c441d08042c1c14060b052103401c0000da803110103a696144201e40100e419906800c00389135500c00c82e003018005000d0300da80c0c003013800030f041c00c0c46040342c540b080b8020030202036400031262402000151713640a6005000700d0310121001 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 126219136 1250 126217886 126217891
    0x207140c06250812130c150509060a03060306060603020d060506040303020a0b09011b0c021009060219020d020301020307080108070806072f070807080d0503150d031709010618140a05 80
    0xf80d600d14078000402c1c00044509070200d4040e2903a240d00d00100c41045280306070b5000070101990003200c3c000c2001c0010301a40034072075a03c0c1c012140420602e218900c82c0e000040215080201042407584840d40100658444400a21141d0a00c40c00080d80e0030580c08880450790558050450007100395680c2c0d03164500682009260364807642d00c103400e05400c540b10304ac0c07400c494480034000c000510503c242b028540a029041c40b4900804210f40c0e9004580400c29044144102d00741c04640e02c0094400708038448083d405610120030401c10680080c0c495060311042e80886803220fa9510384d96950310011246903000400381881c0c0f00a480780700071499003030000f80495011541000056514012240d84002e00743da200d82401c1085001c1408040c0402d4603501c3d21b1451440d000016050701b00c0040700c60b81c0030385c641150200505d481000720b25000700d0041c0e1080441d00700300c088640603060301e000c6d007008868125902a00c8500d00d2058501c0c8031206840c641141d5110081d500041400 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 126220386 1250 126219136 126219143
    0xb030d0207180c0c0c180c0201050405061b2101140a12060f0207020303030f15010c030905060a02011413110105090d150f0216050d02060f0115020703060207140c0625 73
    0x1441c0c1e034113000540528461015000d966020700c41c000e4111009025144803c000106592428084c000030810110744164040c950780c06040c1294458981040c262269018801980d6103000b186e1400c0313060b00109030f041b40c100301d0083c802d6030f0b2031204101e0481303140d10a50340d040528040700da00240c82504990081c802c801c000501781030700c2d50003082c11a8011103020f2000b074021010060032041101d09022240c500b86014140341c1136556015001603d58069103120340e0000c5501400380e4403d4112101c0700c0460080304551342054942020740401000702110f041c0c145401d084842d520541c2510141100140740700d0080f4003581300e040f0b4050400d00f045081c59141d030f00611442c4400c0c0002d1890303c944038840d400c0110142003c41c00e10303040f1140d0b60110b411000c2030114003c0f00801380e1741540d000d0740c910030107284480010b034940100c41d48000e180900214002060200c52a0346003440c080c9141138468500b503000822241c2d229850f01d415200b0b0300c1d0f0b0010740c0d41c10920a42103000d98030 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 126221636 1250 126220386 126220397
    0x806011a040302090103050c19050a050111031306050a08150603010b130801060b09090f0402010e1c15090b0f0907210804030501050105130b030c010f021608010b030d0207180c 77
    0xb01d80c2c001c140707450001d0300140d405501c40c0c061240142440c44421045401a4004880c501d04140006440113110f11071241003081c1d0f41b110b0080310606104a1303271048503a23a05800f1003665600084c0a6170000c00e0840c0201d0a8600020814603076100c0c00300501d10000c10061a581c2820700f407400030b030845e8410704040512942c0100320003031300344078800c0645458108292200071050400a0b40040100001c0020810409110050340c2001503608160b9040700d80608403401d220300e0401240b49000090000c4040c80c2c003410150b036069000c0c80f5074070300610400080765180e091b582808036068649202d80d9100031000c11000ba82c201310801521003140c44615060007c1e00c4191450300305800988142e5951401009a4549a00c0140080d5001c0100740000400a00001d8071441c16036031660500000300c504861240c824080c8020810382c00010314071031501d1f480a240240948000c1314068402e4090040f811400001c10000701c0380303070341030105600c510111941c014001c0000c4d518217011 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 126222886 1250 126221636 126221639
    0x30215070c08010f0609060509010e0402150406080403120c020a0813080318121216020111030304030806010905030a150c111b0301050109050412081f08070f06090806011a04 76
    0x480003554000100b04080020a004091105181c21540315600031079015246c070500304042e840c0c107031903039044803880941c2090940d00c41c00426038141081481150f0316400107804119582c100f480070303000301d000e80c0e03c0092800b0883e2100044900c50b07040d040141c0e200040c180000381249000b80210358084041c1000540d40d00c075154510307088940d400068400d6071040c25181c2c1400550928172141c3c500061000c4100c9070040714091250905203408400b06035420b0301564011240328001c01c4440049a6480c902414002d1140d035003500d407030340014814100007442e0300d0f000419280c1c1d0380d00003002c582c8040c680c404c0035000b043c09003404410300010404009405a0a104c503403222107400074207420300e01301502014210740c4141c211080c038918000601000c00d0580302807050100c19402c0100c080d440b4803000b100450f0a10740d449219032003c0001046c0b0800c00301c2c121003150455040c01e40d1480c0c0301c0c841070382d0680040c00303041e95a03031100c80108099400ba8001400c6250307408a03817481c09 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 126224136 1250 126222886 126222893
    0xc1103010f060e090f070b07110f10030504050f03031e040507030c03050d02060f070c0b0402040b0616020f042a09030611190f0509040c0302120403020a031206030c03021507 76
    0x242d9581e0712407410032050004122000341c0034001070600326251070141214a0501c0d85e802c00501404101030407054130107103082c0c51502d402541d0714010100404000881014810050182170b044070100c8079401883c4000740d00d910004243d0303015943c0d40311000c0c40a102800b441c081c03130900920940e10b51081b90030000115150924120203107015502030402c1c01505000a45050300141158030110140000c10040c0f50344180e8031807540c2d9100c0490f1480381c8450000801414600b203c035035200c54005148005064110780005181d4803c1d6018407900b9070020030401100c081c144d085400004002c5411548201c1d020103c030f140c0d03060f00b8600d8045444c1c0c7c580c80101c1b0342c1030791404038030f50b0300007003039a004d6a00b0b1000901d5084941f07000c2e010b5800e40e003401400780c064001042c0c0642c0e25070016610081c0650140d614410b050383c4101183d24103414025500c241e6103030140c000c07030055100c0c00c03101006030050105030ba8020244119080c039546c280410001e881d034540c0350b040801e12a15002 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 126225386 1250 126224136 126224141
    0x100f030f06031e0c06081003080705030d06171603151e05090303060f060a020d0302030907031a0609070c0f0209040305070605070816032a0e0910090f050103030c1103010f 75
    0x900041ea100c4500350074185440500344030035800c081c00b4401200100044652287c0b0110140c07070b4800c1c6000d0311208245820f610314011342c0700400c0034508101c40800c80403a0f94540360460014501140d106514407101380311240210b020140200b10740c9600026240f40541210607100403012102012850720074100e0100d6100380c0e0003035040c0d00008148000c0e40b40000390030000c000101c407694900742c04284007039511025904039100780340c4c01200042c804103080c13140344002d50b006100709c2216041c1d1b20940740121400c0301d5240c40b83c208070010a2609214144c50748007541c1c0b00110f0f0030344070115001c010714890010802c50400c130003009101c00240e000c3c000d10b4000d901c1610750103450308184964510b450304988240d01014913000320390200704650100c03540c0d00c40341060541d10a00034840300b125224000004160498900400e1011069603c0024421184880b40810102e01c0010540080c1d0f5828400600014110b4259501040c881c03903903901e42080c010300004894491060b50810f = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 126226636 1250 126225386 126225413
    0xc09060c021908030f04030204050a021603030504021c05070e15030a1b120501050a0c050a02030a03091a0403051e0a0e01120e010e0307030806060705071a0720010e100f030f0603 78
    0x5c2c5807000f040410450816000b0f00307400000240c01581020a0380e6a0740340e0300d079481c0e50040d040503124004203040d0740b10071148110b103071400014058000d0381401e01c00d40d141e01d20310840344c01070038000008800141079010000c52035802006820302c0c03682a01c8644100fa00c071000800c00004517003001071611004a209151503200e40008100c6180001d076100448a40b0282002444020440591f5055001c8111240c612613402c0c0055032140a040800b07900c20f61413150b41d40290040d09010625400601801c1303074003000c00218190400c01014118140140d100d50408101c410300c02140350360080f28043c800300800500090303d915210282825a000c00c40100c605800004040b01416805410107603c81e80a4031080e103882d8107640e5a6641b12210301c03600440c0c0c00c03601e0305d059401e680001260101d40d08140c840903e0803041c03049039100c80034540041d000c10541c1c003000841c1e007007070324000340c20700002e03114440100400c1109801030b200c46914451403995401002c40007a488030440305e03 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 126227886 1250 126226636 126226657
    0x11100203010906061b0b01230d060203090d050708030c0307121a100e1c051504030f1e080f0c0f070c0306050907080709020f04150f02010c09060c02190803 68
    0x1800b0351a082002e0f050b00c201aa200c14604100700000000c58a402406411a00f03101c043d00b03003034002110351948c0c9510508460754800c01200c1000188480d640185009005400585020b0b006451080c0c9885c0700394003000300001404d03c0000c0241210390f01540d0300210b1404d203149080c0c2e0303860b410022a0307813182d02c0309410f11218071101c07007508105c00d606140e4003080c10480c2c1740d00c040d00006006d02ca0b803003000361200f041c446500d0080002c1800000344500c44071540b0700042c103041c64041c2100712a0400d01c4009881041d0000b407190005080701440000c50300c40b0284e5454100c00042032500041150030851002c21038960346d01c0801c0000c2001c54020311702200c00e82e04528048040d910050408811607000741001e00072510007113140411650001001640c0e441c00e55580100d40c05a40d0001c000205640d80c004105a0001c0380517400010b5580200041200d904040d501d00105000d088001403803c070058005003040302411a450115580004074540c1d95007840c0e00e07540c040e44a21 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 126229136 1250 126227886 126227891
    0x9050607020a03090b0711040506030102090d08090405061507020409110a0801020315030708070621020406050c0d1b0201080604021b0307120813030c0614070e03070e01050a0303111002030109 84
    0x31042c99840104e59000e40008000342e45449065150300c0702c03141080c0c0310350388a10382d00c20101e26655400d50407614000030140040200c032210b03082c6a901a000404954001d43c00d00000031003503d00813001e552200c50b550503071414010150240402000121700485d4030340406000741d03409980b03111900c1d0003402030000150b130701d10342466102d000f0444050501d00039440300c2801d001c06400030034041c080c5e85452500c07510100c0702400041480400c00c0c10722243c644001008220250300c1401071003044100021507082d449640b8040303420200c0712000e203000210072802c0200546c80740e4900c9401502c02000541408c0031108032045e5560003030030070000ca5000050000c10000c1d10840000c01c640103041042c80e41c60840808401c144240704010100720600840b182081050f03807040c015010500c0040c50350703290003507001e000024010200d9210b40300b945400522180ea40d04124140e8078080c029800302455681c1c10f80340c010340301c400b262840c007491a202200740c0161020318020465800003 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 126230386 1250 126229136 126229153
    0x5150c01060e010b04031b0504020f030103111905040902010e0307080f071d010603020c010914010c1b082b0903050318160311030c0612010e070516030c060905060702 73
    0x100e0031101a607012001d4840c0b5000100b02da510300a080c0c40860f508005440c1c900260b4005610300704c00c168100551162002c1030240d0301d0540351000d141a80c0c41400300c45410140031040003900450000c40740d02c007c80505050089041030b40050307501c40d00c1810124102c00340c40b000607040c1885a000b2800690250f40c0305c0715448410410f903402000c020b541005032120340c074424070740524140201d1050680020f142d054502c000d5010612154105281c454201e499611407406040441c4074000090440850814441404980440709503842180d05260082003042c0c0c0c9411425100340507003240418065140f9940316006031380026200790b4403d45d59103020071b08000b000c0c941d00003000003940801e17040c9041060401075030056035000700303a4162181100f40041d28244005042640040c008070b5801c0b480313094000501c3c1610030740030840600303950312541104c15028040e907011500c2d03210414000030902410710039000c40c5c056600403032596842d440c1d0303d103803002c1600c0030b80c0181e000940 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 126231636 1250 126230386 126230407
    0x150708070f05120a020705010c11061201050126130c0509070c0515010e0f06060f0f07060612020310090c051002030318010b030c0918070b0406180b0d02130515 70
    0x44409203245907105083c84d084e810025613607201030140354148011740700380106004c8401c20a4005e01d60003441c855644e1040240d035814420700b8403845001c940024a4a0041c14240c2549110182c42c2852079502d039541040c0300004180829003510401010000428940c50f0030b20454402d04094a074414041c070300345451441c2036064072240b0394201d880c40051004650496010340c22440f001c0700b418041e01d424000542920070141006060080010020140300410024003000c60251340c0c1041103556403c07c00108400d083c0000394141c001d0b8000c003c40c9180f0b070f07214804407401418030380f5080ba00c0f41e001c1040314240d0910940541e00210030440e5000510017481c0305070310418024270804c1d14590200b07603074440c0180d0130742c030401c01640054480032101c3d00e400c10030751660040700c2c0e80c2030f41d84617465260b80c440c0c042d40300029198011801e5041c0c41d4603102017100c003600303281c1e403030465030601d030a0094000000310703501c0034407600340015681c0d644074003a145002c022003000e541e4041303440f = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 126232886 1250 126231636 126231643
    0x60a120f180503130e280e030409060302092a070c09020d141602030f090d0209010b0307080f0c0301030f0204020d1505030c030a02130b2205240f150708070f05 70
    0xd100240c85c1c1c5407101001491941c0801c82e000c9000c01c440111800d0005035203030400f81c20201c1e0800180c1c800850000f4100040d40c00c03420846c1d000751180c060a490b91485041c400f550382c0d42c0390301c4140a5600304a0400c0744440202041401100310701d141d1a11401c40006a074042519100500c0d00e03514003441310305003e6002600500705a50407140d000c185180603440780a4040709560381d0320301180c0801181c075034078450360302c060380107141c03074110747e1580315060345078006030381020000304a80002007142c51924010340c01281841904c6055a1850f50f5104190b402004201c0c1c200340c09010310300004001c1e0180114082c030480c41c40303544600f00000c1c14602401c00e02024482e520220420300541c44000300508504443c2c100440ca01c070f141800308001c0607140351100250000c1028801422a10354030a90151304001542a031601c00701c0c0c0380c07605d00707404030305403e502c50324403407020030356203000a40a0b501c18040340700541000001d403661621508028000c0c0d0342d0b030304442500e008000c82030 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 126234136 1250 126232886 126232889
    0x2b0306060215040813170616050c07031b08060a05010501030e03040e06060f130611010f060518090118110306060103050c041a0405061b0c060a120f18050313 69
    0x91000b41415405201180074005000e4400303001103100103680d1250340003140c0f004c2c0c003a11150000340c0b0040c85142c2143d9840d281280d40200c840c2c030800c1340000c00d500c07070004c4501c44003009000306242c5095031210058803007548030070500c0c0e18202d040002c20300c0040c80300c54440c0800c0980001d547d0f1411b0005003e0320020001a4500c0d00204030500c024414100c0b0140c00030303400d940c1d0b1070b100c0b65503001501891042d003183c0c1148a103120000100c259120400e82c460705c40c024020320841c0c3d4910221421b8072071038000d4035409048029111541981caa005a0b804103d0341300101e10141903904266203141d60f540c090712030002041713000d0201e080411119401c08401c0ca0200410328018410780300c039024501415003500b11070803124240d031035040140c0d00030f004010542c540e1101c0c1d41282121400600713040101c075000d68400c6503010b29081c01587c8050b84561200d249183d18103149800900d05d0340c1d040071360349036076890544000e480b07090f40610040c8503500865403581442000c8503201581d = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 126235386 1250 126234136 126234149
    0x212070e0109081c0302030a0e0303041b120b0105090405150702030d060e01140d0303060305030a11010b04090b0a091b0905010f080109020303040e0c161506050405040f020f032b0306 80
    0x204c203152108180c1441c000e03240661600d00140c803134a0302502d00e0060403a407405034a49100110900091094a10085104a480410005005907030300319440c1c143c1d00d04100940f05405020040206003000c0d14400e0b4028440c000351007500c0091300c101106c44074103a030800011380c0082110284011588103d0300078285000311903142e585402090304c6280394041640e80980300c0e0700c6170041014000d401140c0a551b000007560340319407a5890041144909129015041d800d24545001d541054132401c1000c5070001881c0207140c1d0b480620300c0142c01002c40072102d403000b18040922002c0c2005041d4080c0c03001d494081102e524004854100c08465004040542d01d40901d45005036800800c0f18211196100781819540d07500784074150174052120301c42c1e0728a0307491440b6000c0108030034120440d185010410082f980e201e80500080310403c940080036015000c040202524101070710058030f00004003140c1c2d140c0c08a103420b6000c4110305416045901c0d146400411b03103505400343d00040c018 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 126236636 1250 126235386 126235393
    0x20d120e01051e091318061a0d06021e0d020304020a150806090a020412110a06090f0b090307030f0b04120507020303071103010f020c07031209032001030212070e010908 74
    0x104010b50502100342c084600c2c0d10705400003051202c170b84414900001041c88800d04004414580d580d030b421403134410340c003101c04628000c01d80b0b0310317040e034440c040c940350310003400c001070541041d0740300e000a521000c5004141d42868919150501080c40200700f00000c8a1000d030f102d0601c0d03c140300329650390790070080100c03807404000c25000e6808525558012030444202d1420344031002c13484020306c2103800c0160311002403c09041440050b030a208822002580e0b8441d10f1583c400040305d58250328000e9a5185144a40400c0300c08028000707458400c10040684903a2aa00e03510035408040358402150800056410407052010b4524400c980c403400341861031402045a0000c1c0d10f0348610003005011903c1401c40412540342580030038040c152800c000c41d03488020500545d92501c203484200c41d0103103406900800c180c80f40c0e10443c11a0b9008004000c204034800b00d84060f0f081c0c007d0202c2c100360b8207000a28042034100080c601607145901c0350305c000c801b40400108040400c2d00580044d62 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 126237886 1250 126236636 126236647
    0x11070b0906060108041e021206070816120e0c09010618050d1505270106140f180a110d0e01051605031317040602010c09140a09050a0207020d120e0105 66
    0x7604818443d40c07140d07000300c202c54a035041b5644c4000c56030f0703640c8020750048020b000389620000001134182c014640c80d12000344941c3c1d115854508000c1d03140c0b0380c20028901c120040700e4141c0f03640241d80c294103000300340c0d900f08607060041071040308260b00031000500b20a07844045500c0c400c0440303020b800c0603204d01e4215034030780e00c40940c10b0306030700250382c0740940e10790010b1000040f4500e0300105554441c00768009818281c2240d0183c0814000c0302e40d40c803420421000146071043c10b05013080001750018441c031150b03a201d8514040001c10324454181c540422070031850310306005158075000d05000054404560076001c0c02c4a000030942e801d0203600d4110341007096084400d0700e40c800102500007200940501d02a4000810018444c1101001003808901c0907010342040054086903030342c0da980e15950300c3c0301d0780160380d540203c0d41c1c225001e680144060610354010320352002c1d120001616081d1664013203000c69030188026501c800d4045000d12580d03602040c6c060203084c091800743c1c14507 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 126239136 1250 126237886 126237889
    0x60c092c010b0306040905010c0806131e0207050f0a050114060402091f03060308030c040602010c09030b010b0310050d060c08100e0c091801060f23030a0c110111070b090606 76
    0x1818001c000c0b403288080005a01681d0340d400060340554014001c2c85400507054000c0c103681d4064903054461940c010265141400078410b81440d1041c0300e41c03203200b180d090780a4000942c0200380c192401e0058019640c480c042c20802000418419800091644401c07039008102140161100744254010003420300c81d070381c4800c02078000e0502001c00c0c000010400d8004d5005008030b40c401041e451002c010030a0f04441070011f1700480f42d4a13002403046120a100883d14441680401410002014014040d50011801442d0300c0b02114070812f0080741c8a40c0080c0c80305a03116001c544190322182d03107082517035001400c035800c00010359203c1c0c0f40c0d600700854800c41d49001006c030090000c0100c0c00030110b550b042014141c8040302c5408102c5542c40d090014418403a000b40c00010500140c1c40480b14039000103182c11180009a00c00d0840e190389902c0380c0030b04a0304104008006016a800c0c418030820b11980001a20101c00317980d5407003062520086050b4020a410000d400c80420400903 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 126240386 1250 126239136 126239219
    0x30c0e0d061a04060f08060604050106020a120207050d080304050c1207030605090a0204021b2e0e070b19030b030706170c0418020a021b0307060c050a060c09 69
    0x1070780c80032001c681d140b4101d1841e0900c060110586034800e04048001400c0107007080d2900603510544c050b1400b0759580303414171060300c20a10a07000168490801100411a1046603071040d040d90300c1503c81c5035907154002800c0e00c61540050b140c010000003400204074003081680c508010a0314504410305110606540382d651903c009411680c80c3c0c000600440c43c14800612003e900400454991041e00303450b1403903081044c810105440342c10000d245450212100360042c20301d0492030301260100f40c0301100a001201000c0039244510a404101031600c030000e40700180300c090705542d550a0b2a079004050b143e91041580c001d41011406000303103030b4003203024074007100d4501e621583c0d501e0700082c80040384503d40c01100902020349400d010158150003c28a00c1c005a007140c0c01d04108003074095845004032030359a8542c1c000c000c1004140d01503211001043c0c021400d032040b030301e41030319400240c0d031080d01e002000031040f075424003c0f403000d00e00300e15161070f00922081e9a40030402c0140300 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 126241636 1250 126240386 126240409
    0x1104060c05030c0105010602160f2103111c0e0909031b070f06020106060801050609100f0c081305010927110405120c040509010b03100203040804030b070206010303030c0e 75
    0x4000e51800460280181003044507070b030a42d40d074020001da41c0c1da00002515901340d825a05801c5c00182000909004210b40f010103070b848504040100c0c080c40c4082031030800546008070140116060290140c500500c248030400c1c801c0082c4658420743d4620023030031303c0090041c0703510618281702400400c6d2000001e03a900c100aa02c2c44102100368a40c1070340c90003460f68131801503d922007c000c50b01590640001d000c1301c6158031481c015903261000c0000307502525a440350065000d01400030103d10603100c0140600c41814440b0888209440c2e2081e01d620a542c4000d00a501c0c203810005544d100707034218020105245003e500c0a43c0f919081140300c00410315565003071321001c0e0001c0c01d850350002c440082c07800074a0348a0f8030314450141d60326810015070303c900c5149440c000594115040c060780520b2030008014000c010804c20f9084025040038100341e03003100c824000800060780301410240106080e80041a0541c9503240042c1512901841d14042000229a500d11350b25420203000 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 126242886 1250 126241636 126241649
    0x10506040603051e07030212011505040204061211040b0d02030103050706020f03030a0509100603060e070f0f05060706020405030109030801080d05130302010e011e0c14120906030a020702090a0f0b0102011104 91
    0x1400c540c4c0c0300c0c1c0c00c5180c42c241d600042c0d40544004072010300c40070158408152407621582c108511540c540820007280980e10810000c11a07142c042e0071f0f03031195a8058104022402d222505080e10f03034231600c1c481e4101d030130007400b8594004018800d00c0810441400140341520060008801405403a40c0f2408042d1092010681703c0001c98810780d0140240d407080d0031211800c000c030a81d2410081c01900b90169448200c2c001c000c0c0125008140010400c01d81d5400c03030056450524000070300c07419500c0003400351015075081c08007264580d070030301980380700c50b01a80d5035107282e50520001504069820101d90284202003001c00ea402d040518510b04594090811414405114006944100d00f0100294071640f51300c000d1345440e500b210460881d14091241418501070945100b40c0d220300840407000c0c002d1080c403080195280c44001550b115400345009801e09507a5400714001e18000d503032091000c0e44031100f00c1c1148000c0c1c45801610103092000340944541e5a90b809002d21543c082e00 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 126244136 1250 126242886 126242923
    0x405060405011d0915040308150906010504060f090b121b030402101409031c0207050a0e06090717010602010903111501060503131707170c030306040b01110a1401050604060305 77
    0xa68500e41400704000c070070148071007031061b86014a0300506d0201c2c01c560312914040020028011070800000c254890041a1540342c034141c10004155501e01c500c80e060000c110410f640426489602c0002d03000c54440c42046103e2030804280140d50803107080000340303071054140204005655005d0441080d8036003401c104d0b0b4051407520b040090383c49005046c0e9054031400d009406071304448031804448001030f03402d80700d00589642c2005942e1040c1e1107400c0d4406072620204e943d0345000c610b680d81000c110300b001c0710404500311610031107400903804000980d40d5620440c06140c0c10941002c64898480c0c0074019004101c20380c1e1080700c006000d910100400400061102c41007500b403078a1013500402c2454401200404251030307507200304021030f4003a105801c420031506202058510400c2808c01543c11076a680d024403000340002d009140c1008040e0003600440401400ba98103124004c02c1d45140d0107108103003e07401e55101401c843d0140d441d0200c2000480c02c041a040c01d840c803241c0a4 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 126245386 1250 126244136 126244141
    0x7110d0201140724021c27030f0e01090b1204020609040e103e04030c0e09010b01020601140904050708030a1805010306030210080a0f18020405060405011d 68
    0x407941100c912800d40106000060480140141c8561000754100c1c104054000500825084d03000e0b40105680701d42c0204031030b040e070026150342d03810010007000c915903200300f4000c28501c09400261002800c1e40441c5200300f80f6507090750f1144c0031840b100000e0a207009081c0c5480781c074105d2841440c0c116002c4007c00d81c041021036880070100c0310b0980d40140203010f000c1d240f401594940341614800010036203411141c0094520000c141d40903141d0050800e8401e000814403850744402d4042030381100d403c1000301000284021020340081c10303035043d5007801441c0c0000c000e42140c031310310704090640d441100108214090920a094000c0303096911103060f403510300d800e0f031a040b20350700081954000400c100302c2490703201084400c010ba04a0ba02c000c500d030b0f50030040d030865085001c041c0d008a11031b40035200c0d2074011820140c0011111800299081001e04d2400445d02c000d00041c0014090103410f80640c549805425001403003100d0410295261282603120260800c0e9081501003801c0700 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 126246636 1250 126245386 126245389
    0x1d0604032307052d040b030a0305030903070606030308090c03010911060a0504090f0b0a0e09030409050c070209040b0115030e0601090b031009150c0e1809072408010501020307110d02 80
    0x41d4005100113820300e200070542c0c081d05481056000782c2c0c4200510355a034a40320300d04e8280a00b261243d0b02502074001038809441c11240c40d8030082010f0f06c240b104100c03c00020348940b007040c0c001c5000c5c1d0368000d8181450b00d0001d05202008940c0e9120341c1c1010340031b82c04210351300105212200115050b960310380400c00d042d02d20780540e074041c0500d2413030080c1780e00100c03091360803407405541d040340d00d004866102c5030903c040b0360080d54003203402c1d03206100a0201401c19030000b0703000041c0c440b0440c00d042081d400a05000e0080ba000c68851008600400201802c0701c81d5240c035a469050903c80b0b1841c0701031241d90b0b0305051107180344a0791203611440698400380940c00100d4a0700d082030180564605018810744c2c69076070021002881c10f0400307c801e92151841e0304940c5802401d15a4000c1c605142c2c900000001d814003c450060660010364000042c00c4e40b2195480000b2003c0c40f5808501d010300541416030005055400070041c010029080010f1601b24a108a0340409035130990f00 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 126247886 1250 126246636 126246643
    0x24180803040311150a05120709260105060102030c121605070b0717030c0703200a0605240901090504060f061e0503010209010c0f05010b040207031d06040323 69
    0x2484520540030000300030080c08583c0e01400034114042d54483e01311400c0c0c4500061510400f01080c0002d002800320341d1341c019400c040c480e0481c1780d6190140885407961500d6144c21462201201000908451001e8001082c0039003030b80300707000740007850610114001c0c02d0703107951041500200544001511184600541800a00b6507070050700721010240c6485503503006500815090307800c848492406500c5a015004a0b0b1054141d00c0c611810303d0510f270b030181c0304010040460b1107804240410f030024041c0c1004004400d43c0203040200d280e0500207101d03c81c15440d04041d01c50480c8901801d6610344890060604580d1050800601c0c0c0c0c0c0c0d24102100207005158082946c0b60400f0740000b5803901d6070350102000400751802da1382c450b5803074080508134403907a540a40401d06089003040847c030310140880c0039501640000c00c40542d04400101240d1240400b20045008800700b50b01442c1500b010040c1203400780c48851401e402d61300c5400c84c0208c021021400c0880b00700b51240c1515051 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 126249136 1250 126247886 126247889
    0xb100507150e0a0516180b0d021509010e040501030b01060f030e0a08040501080a0506091609050324010602010e1903031b0302041802071112071703040f2418 69
    0x84000700072141040e0b2040303845038411202a034451145580241c20b480345090142c2c111140000c19034400b09143c1140c001500b0400701286d40410744400e09009a118070300e00e00c40101610594070b0f500c08801e40003401e4100145070481c001c40c5480014030000c1c07030514200b4150b80742414815800921000114040c0c1000c1c01520f0b0b0900401c4481c1003045910343c0500151202600c07280415940c1a440d030040383c40440f80540c0c0011110003151100c01341a400185414441c5450702c29103446601291900f881522814110080c191545119404a802040c0900740c82d1000784544c03515042082c0e5113044400d40008540c80308085042014040e03888180e0145003075003000c0c1a0503c421024000b03400c02c0c82000f90045a5509a103058842032086070540340d446130710811050121000d01c005081900d8210407a84650400440c2480c0c0414031403c910803054000c40d5214248504000741300302da5800a861804000310f028282d5100007210b41103810a071600000405510001c07041340d0629 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 126250386 1250 126249136 126249173
    0xf0c03051603030e041a060a051b0a050c1002120904060e0a0b0102190b01151704080405010e0d021c05010b0d0302010e061b0d021602040c02010c080106030b100507 72
    0x700710071152410900e8109004590094035001d405020400c1030105036403111481c2c840500130388100502c1403a109016001074110b5140960405100300340b0240100403102000c0d10300c0d8010918482003041c100000c2500f401c00b5074450503034a41c0b40d400650b031440c590606c004188130129144020b5150303507200000038500c00f4900c019500b48040c4810045c00350035203850040c0900484400001605c0201c40c450b00e521825000090b880d1105a200d501c54480040d4100840c41d10840e107110a040600382c0124001c90005954929000003d00402d03004180d4034050003200c070050340543d4a031204a01e101255444c81c05070003045250841c0100003174424540d2061102d0140014144e05504c5405c99200c4201102d030985c48001e4901ca0003162001d04040d0301000308405058149190040c2440c040c1c1601042400d511035400103080d1185210510b005039542e041100325141c0c06905a801401107090402c012007020001c00c15010b00003a4040610000240640070031480c40c00d5005100d00 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 126251636 1250 126250386 126250393
    0x402031903030906050c0309100e0f060c0a0f030b060f0901020f0d030902030c06030f0601050a110303011706070c05070b0f0904090809100e0a030f03020a020d12120b09040f0c0305 79
    0x20300386405401010860700070ba40052822001039140c601c002c08682c0680c1804004000071014044410081c1050f03101c1101c65000e02c04009143c00020085c0301d0017002405d455640f0707002c810800030301e44801c000c00003082500303018110001d41c80da8000c44d2120400080c1155450f170400c00141d14010041084036124818100f0b01d4100c644c2c158040155142300300c0030348221070085020804103000940d101c00c81c6104203800f2540c20b42c011001891083c1541c14088020a07030143c0305410360b00300f6484800140c501c122500000301003841019413200c910304010221144036290b00b5514642e0303001d40701d036082d00000d03c10400c1c5c060703005440a014000b881070010080e285001c02c003942040c80502d0051020904cc01d04060080c00000000c0350068484609a031464440920180080e0010740a5002c0e07103d42c240503071101c0300b8821070345008003007100c2e40900011700107184179246042e80c00d05519041c1134220a0343d42252041d0841d8002d9a1034a0724a1141002c20140c0318580c4010070a10 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 126252886 1250 126251636 126251683
    0xe0f071e03020705150a1a10202d0a0507031709130b0a15170a06050402070f0b01170604260d050417030103052d01020d0e0c0a031a040203 61
    0xc4905d42441b41026420500c00b40c000785055a032030a59541a00740c4c80500a1542c1082611801c140300f01118104880c8003608c04441001c1c4c2840100301c1c04d01140c9405414902070070f200390034402c0700041d218006210024080d100c0301d4460996000040000310600c0c0c041074410354800a40c2c40c51400104108182d9250000b40300090800e1040d00d4003500c0c904000050355480100f1138140c98040b5190705143e00503107420b041b02448010a94107032039688078004986030700c0d94809003403201d201d0b10100140452904100d9247c08050b400890701400400c46c1c030509000200380c1d545c000d580144407520040f45400c40c0d404503410481c1450407036402140000c146503190b0006402140101a5008520407000000315a440240005400c40c0d00080180c184088910003a40008c90111004134608005000a41c01e903070004ca591103e030384e1109450401802c0600080c2810b0000312807d40c02c03a407441c0d41c3e1180c4900c280961030700851a420026065440501906202082c0d0059414801 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 126254136 1250 126252886 126252913
    0x209070e031c050c07080613060b0402070c120c0b0a0f260c0a080907030c0b22080309040509030702090601111005010608090d0309080d18020a0f0e0f071e03020705 72
    0x1c0d0000c42c504ca0203407140b28000514800003081f660b0046080740320301d10101006854003801740100280320703508640c0c01c0008401103a030b000c070740c05e028201104001c01c00d81e4080c100100d0b10642600414400700041100000c0140c02c450741c03000105e17450428940c1800964140fa1030f20301c0700701d4444090912a0204400040260010709036000c1685441e41503444076210700340d881016000c01012040004010302c01d807031280f4040c0c0884a14081c4505490f50310028058640200c1c0d40310044c554000f203031050244c41c00b8003440e58000c024000850a0118075000646480805461207042c00302020416481c00018451b51003c013030a084140104e594400000b0118001200d4001c2c040c010043c00b65001c500c28014544e80036040031ba500d00b041ca01402c1d07c802007001040074901d09001801490040e16072002d450000c22841c89182c0c0024034104410818407001840c11054403105003c2040c407907000441c4100f412513404504500e941c850700c0c181c000f44a02038010340b0602c1a018a406035 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 126255386 1250 126254136 126254147
    0x20a030504050d031a0904140a03180506090f0907020a0f0f020a050105090a090e07080703050f120313030302031b121801060305100203060a0b04030503040f0b04030209070e031c 78
    0x10781d10460440b0b08551681008030116040c64203640c6815011400016191401c2c8100c550058001c01d0343c50640c0c101c0324a154035100c8610000c5022070089078032040b040d008a01d04000500301900c50f03601d007030582d400103072414001d14501407041005e14082200039100708020300061758070082030b2041c81c14600708544125404081203201d485180d20100b030552050b81603071000d0002509180045003030610440241c42c0003100240135100300342c80002d40d4001045100000c1d8060005860b920030703921442801d20294100800c0c13049400c03c240a4055540c84203010a142c252600684a4445600c00b06800e40202c000340038030f42003c164141d0843c0103150050146007040e440d000b50440c01035141d8281c070454030020340103810a40084603010380750b8000f03542c400c40050948003070b9511401d5024098109402c20b07a10390b480803805000d80c0400011400c041c00c020b01c0704a0401c3d00d10b500142030508010050402c2100000319000c89490070008581d0360222003180c40c0e03a003009404000c00 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 126256636 1250 126255386 126255391
    0x9030607051c0e03030a1a03030f04080616050f07030306050a03050c0a05010206101e1703030907090902220e1f1a030618070902040f060e010801150e040f020a0305 72
    0x750303602c07035a810025422140704409440000300301a6056a40384901c03040200340003a410b1010703000c83c0620b006c0544d000d100500040000b105800d4403a41002c00c040c3c50018000c0c402060005c0441d07440c01843e0b040f20945000d21540517800e0b50b5000d0529044000d40b205500145c7c1100740c05d078002c020824003140b000c082490a030f03045070007a640c8100480e52028180c50055210811280a00c59a0f10b0103200017100004400d140061980d0b4402e01502408022100c001c01e410200500000f0314060003000001c20781c90304140001c800315000102b9040c0300e007034082e201941e02401c0380710a0700c1c1608100350503051003059888107800c1c014036450300b5100c80f500c02e10b958640140d81c2c0313101d0080b50381c10960f00c030081c000f01880d03076a04e01807030101000c415000000e423160007000107a038801d03030000300007412882d04103030465460450054085c5040000306d83c180b00340c4000500404000980c0c42c80c01c0c00c803528110a00210041c0844d0046c0f440742000e0040e1400007840c0d51005406400050 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 126257886 1250 126256636 126256657
    0xd02070e280b03162102030c0310020307080c040e0705090118150207050a120803090a050f1e0136140a1407121101050c1c0f021f020c01020903060705 66
    0x183d03101207880007000004c1c1035004242c00240c0a403001c0c0c041e071140c44402e0300c5061000e03045404140d081000a4070b4003105202c04510243c0000c10008000d07400110140c1000300d42d1a01c908042c20103000d42841c100c000d0666041042c00f18124446a01c07841d166400443d01c04444802262100b000f22084050880d4000161098110015040c01c10005007070481c0d4004450303509400b625038403000681d1020300200540c0c0b0a041419000c102d0a00004420b406c07500d00424840d484005003100c143e540d07200c500007907403406000c0000c040c200402900f50034045070100d403035214203203482c00126985101c007526484c400100138014440009070305ca4094014240803840609501e02c442d13488406015401c412010030300100c00041d030940d6009181e106c1414000d08050010410300e281800d01e02010140040350601c40400b25045141d03280e414165102824842000222083c030149002044161076907000509213008602903054641507a0003d003914264141003c00414270b0f0086020003 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 126258992 1106 126257886 126257893
    0x1091404091406070305060603090c2e05040906270c050d050a0b13020301150503100b03010602070303090909020a0324050a020703020f0d02070e280b03 67
    0x3090480014008240304d10b0000001400c0d5030001d049036008243c10404d0201919000c66605400700e002e88100f182c4907465a20080d80c00000f1000c10b03180e02c04000b0940f44564824002c000f2a041c011003804141d0b00c0725450303034004100009940c940c141d103844640c0031908035003114240d0350b440e041050521495682000c10380d130b03084982ea008140d544581d0140c62800f0b070544204042910021401c660606020a0b428100030704a10140b0101000150f096a0f1480c2e000c005065007040b850303141e50751004c008e5500e80b4039002c100c012648400010442c3c043d40d21860745041c1e0010b000702e01452442e142c1c1503180c0e400307008502c9258031207080707481014240d01802c1e000d00005100140e650340c0d40e0a000341045448414403416412001c0c003c00c4a0303a0005054013980d14103856050316494948074403000348419001402100000c228520800440b60b10240022100b0f800f035 = true := by decide +kernel

theorem cover : BRFrame.Cov 126079136 126258992 := by
  have h0 := BRFrame.cov_init 126079136
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 126079136 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 126079136 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 126079136 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 126079136 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 126079136 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 126079136 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 126079136 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 126079136 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 126079136 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 126079136 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 126079136 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 126079136 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 126079136 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 126079136 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 126079136 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 126079136 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 126079136 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 126079136 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 126079136 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 126079136 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 126079136 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 126079136 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 126079136 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 126079136 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 126079136 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 126079136 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 126079136 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 126079136 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 126079136 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 126079136 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 126079136 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 126079136 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 126079136 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 126079136 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 126079136 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 126079136 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 126079136 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 126079136 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 126079136 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 126079136 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 126079136 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 126079136 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 126079136 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 126079136 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 126079136 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 126079136 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 126079136 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 126079136 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 126079136 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 126079136 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 126079136 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 126079136 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 126079136 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 126079136 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 126079136 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 126079136 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 126079136 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 126079136 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 126079136 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 126079136 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 126079136 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 126079136 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 126079136 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 126079136 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 126079136 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 126079136 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 126079136 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 126079136 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 126079136 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 126079136 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 126079136 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 126079136 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 126079136 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 126079136 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 126079136 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 126079136 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 126079136 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 126079136 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 126079136 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 126079136 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 126079136 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 126079136 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 126079136 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 126079136 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 126079136 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 126079136 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 126079136 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 126079136 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 126079136 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 126079136 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 126079136 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 126079136 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 126079136 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 126079136 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 126079136 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 126079136 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 126079136 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 126079136 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 126079136 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 126079136 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 126079136 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 126079136 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 126079136 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 126079136 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 126079136 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 126079136 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 126079136 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 126079136 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 126079136 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 126079136 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 126079136 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 126079136 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 126079136 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 126079136 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 126079136 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 126079136 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 126079136 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 126079136 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 126079136 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 126079136 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 126079136 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 126079136 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 126079136 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 126079136 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 126079136 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 126079136 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 126079136 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 126079136 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 126079136 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 126079136 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 126079136 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 126079136 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 126079136 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 126079136 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 126079136 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 126079136 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 126079136 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 126079136 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 126079136 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 126079136 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 126079136 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 126079136 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 126079136 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 126079136 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 126079136 ≤ n) (h2 : n < 126258992) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
