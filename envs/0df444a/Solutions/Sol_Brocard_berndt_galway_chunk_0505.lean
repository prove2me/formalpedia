-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_0505
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-13T20:09:31.497668+00:00
-- url     : https://prove2.me/submissions/5ea5f1f3-19a8-423d-84f5-8889a80dea47

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 90647482 ≤ n < 90827338 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 90648732 1250 90647482 90647539
    0xd0605040602190810060f0c0803160906020c0f090a241d0403080106050f07060c020703050d02030903030306091012030305070201051332100905010b010503010e130507170a050705 79
    0x10884a07003002580c7c00e0b50306006690b40a072070520000100075507502491440b0001000320b80d540c06490795686012138452144c0e030ba00030360202c0c0b107442c5400f44e03103840c1c8032154000b03146480000343c895103c8107100c2c2d000045400701c0c0f260800c1090810010356500b90548610218400d8103d5924181e50020b00c9458140110300034010040b0b88010070320f00d240c040c3d41c22658802d200b000819954100a0350380c1ca01407008407080d115448403405014400300036221001005001103086450300d00400030460001005441c90a424140000d400344031030072115916406038500285c4c900300404020700b07642c070003452040585520406038000030b10500340001107038600d404031054807010b44030741c4c10440810f1101c004244121408820005072a5010169107486034000300500d6404400640d00c03800244202490f846a9070b00040003410724800c800c2c401e62203a82520005074840784804040c1000b0142c8014542c46549e82004006003004014007603e82101e80500114507500350300d600042ea502c = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 90649982 1250 90648732 90648737
    0x209070c0f08040303020a15060b0406032406180f03030507060207061418070f06091a0c1e060a0605030c060a020106080708010504170a020a020405060d060504060219081006 76
    0x34140d81400760340490310052652000c1210f58032a0340c0d090003560344586203000d44d00110206003101d02d82e013452041e103044030070a0312003605081c9840001e4000307046079105101c0b14501101040041007240210001030211600c4103a0305540341420519040d240350054105181440400e0002c00d81000603240c40076402080544c1e280703403506e409000f40042154402c050003050081c044008920b9011024201400081702c010507542ca124205041d1a407040c88080303508900d090040900ca5424842c02c5003d0307882c1a40f80100b60040d5610301940039603405660300c02035a406101807010f01010b50001c40811060201904003000281c4510819200078400d03500000c0080400d8000e401010050080c1403e42d01509c1e5140412406003a04a03421140324000300c501c1c28a100e2000107642c00d00c1560703030041c14070340303416800d20004200190401d07501c07001c0322b000040010514010640b080f4402d28000d03864076003203500c925410b10b40d000c0000c05c0c403c10318108a0541d54101d408011076020b072 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 90651232 1250 90649982 90649997
    0x120f020c100e070e1f140102120316080606070b010b04060e030a0c140315010b0901030b010c15110d050907080f010605010503040b0a02040b0c0714090103030c0308060616030c110d020907 82
    0x1840c003052040c0c448440e04d4202e401c0e00d135000681206c4034070300048100c001c1c0c0039203140304445c12900401e88001c4425034020034500c220512420b208a0009603c510b019041c01e107400e00d56112a1481c1c00242c0c401d64101c24001024480c40d0f610011042004034190004c1c802024181c3d10726103800501e014030700c6150800024400350350360811012400c034480451188103943c59075000d0003143d1107180c06601180c02d100710310203d07512800c0b05482603178100345602c54000b0003445401c00380030343c5103c030390707110a050101952144141c81824050f00710391004040142c6002c0742c285c101820640398803220f07450101e0800090360010100c0e9403050b8024114240c0b55201d10300c1c2c80003401580c00030b24504101007400400c0343d40028840060781c03007070185851005100030422000107001d003c001c0000303c40c80d5481002034007444a00d074200b90b0007030502e400c00820903840162120104020780000701f80504100a201380d4101d14160080305884080000c003507500403581820008d00a0420040d00 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 90652482 1250 90651232 90651241
    0xa0e0106020316151401031e05101104090c080a0c03020c0c0d050f120d060506070228051507060f020304030912030c29060f0a06030c120f020c100e070e 67
    0x41144d1406101c522003010403280c2000206580c502c2800d0008480221090458001d103220604200e040d4507481030080c00c010900c1d81102001d131106001c80c81042100f4030001c1901c1405025010304904c469482c800c00b460700c1d1011000343c0786501064018184104540fa43d07030000415000c9100f02c00341d03054a091055441d10303520b0f10030b5030f010500050103000040c20310000d0314401402140349009060020710b40b50000c0041c188a1190000c2d88030281c503654a0b1444841e407249911030400d100810400c5030340d0000301d000d030b038070294005046500c0015104100456803148221521940c401141186010340c1d0280c541042c0740985201c1c820b86072082000c1510404241c0030450f8404d00c0c0c9655050300940d415409050440c00d2988040ca840c0007900c2d80c28040003400001038024241c054251800e01305600410b4442240420810508074510340321070140520603000c0905a00180e95068403040d041c2090205012695411705004002d0001480003580e203003558856034901c0013907201c = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 90653732 1250 90652482 90652493
    0x60a08060c070c080f0606010f0305010b0d0e1c02010509070f0b070209100f0305010614030105040f021e0d0b01031e0503030f06010e130623060301120303110c0c0a0e0106020316 78
    0x4503488014144156200b0140081022038814003485082c0c90348810b0309e280100540684409002e00c420b407000c10700207040c0c40c500036009480c0c0c071045131007aa81d00118000310313002c42e0680d0b0f100b60405030791550180408030388200080da0041040c10002d62249040640488862250040180c0300f450003202040000601801c81e81c0141040e0041c24181079883c0703051400707001e45205840d107100900c0c492064034201800740512503984140d07800401c0390542d08120040081001070301020031099040710254449401d201e66079409040380940b50762451411b90784000402040c40301102015081d040011000400d507900302c0c46251400c0726507600e60004940b00c001611250780d00400d044003c40403034500e680501c095618041d500714042c0f0075070f00c4100d0344482c0490b6840d001002000100552150b01c5100351025200c1d00c0c0c003041c800c0b01b64a890301700741c011110a10701a04800c80200301e91500303003040e200904002d0800600c540c50400c01944a0042182c550100c24024001c04100301 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 90654982 1250 90653732 90653753
    0x60506030c0a0f090534090510080901050105010c080304030c050c060307050a120b0d0602090609040e0706091202100e0d06060f0501030b0301021801050a051306030c0305060a08060c07 81
    0x208081c01482803190f50340e19404a1000a105a6100c5460500414214041d00d40c0e5142c0000d00e0381c544180018012544410b000701e403424180800034209004952681d0f05540c500f000790482d550340501d410702001c5030782144c0703040e4840760502014180c03040c00194020706403503206d500742c141092900858240281844c510580390341d4060000800c00c840d5940280c007411559040e955a501d0006007020450116103011071890f5100b141c40c00001c0014059400030011194081c007035a08040e40c0750b021401b40e480020074a0141d820030802408050780c4503080500500414511a2001c800d035004140c05080300c5403514100000e405200602d521a4001d1960716075001a040001a0340e440e06a04d42c0c48990280c140028107000180c8030758139050081e104244600b0300b103024070030540c40c0190b5980d400100399005000082c07240c541c814603901c81a100a245a843c041000100380307800400300c50f4001c0909108807468401881030030300025071a030b44031200800040d60f071000c500f4288401e1 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 90656232 1250 90654982 90655003
    0x609020f03070e01020a020906041139010c090905070c02030a030809010c09032001090306020c01060504050105040e060601031a03010609060e090327060408010504051f150306050603 80
    0x1580001005504904403030000c41c840c070b18070b03520204100241c100490f25107581001c0030394411b00c44004141645000d07400003e1010320042c10508c0c100d15a0310110706440d0b010b17032401c11803544232070500160555589400c1d1780c89485c0b00800c070403082080d005d008140c0c98000c560b021613071100054105409160418150303900141240c0c030044080c50020702e20402260003220035400d1101c82c0c5030307003401a08690b0036213070f1000f000410f00c4071030150751102c5e420308040c0c10304010003c1d1000010503c140b004004900b9840008581a41003400340700503240181d00071405549495a0000082400b04640c1d821000903c0d0104035018a41075030840c10345100009036146d4030b071a60000d501805940441c00700e402034070b540080d03070341d0b40f45c0201d8403801262501240742c0000d2424a84030325146400024202e001021682025104c1a007203084580c02c0b00d0490f4a6403128110f4442400c2101400120f540340150600c5008142106505a0041e9100c010501500c0c0d1000c60005c9da0309012080c0c10 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 90657482 1250 90656232 90656249
    0x61b080d090c050406080304030807080a0c1506090c050304080702010810050a080a0605090c01050d0c261512030702090a020409090c090b090f1602010608010c090501120209210106 79
    0x1108180c18199004466031281c030344121700e800d01c001160f490200a880807650800c503183e0400200b83c840140f03640c040041602001140104180002c21103241441824100e0800140250803e400311007140e29400c1c0701c100303110003441000001000c29044600c56982860300780f00e19110800c0f0350001d100e5130b8003e2540490074802c042800c80c1c00184e20480350b80207035401d21450301e4040c00c3d81d4071580c0e890719480c0050000c0204c2120145907401450500300c3c0c500d030804000004601c0307040d1441c52803002544001d140b0090000402c00785004160075402209c0d03001000e40b404e50440d0b92485400c0340240103021410000d101d4031b1296054500900f492001401000390700d01c0c000801c034680340694070300035150a03881600ca06203840c0552141e00c4450a03e03803207440f0b0751801218020300c10f07449000c5640b10034020600300401c4c000c02002440a03100d2030301e40c03420800003408205901c00c200c10b400d48140601d2031183e03241c120309640d001c04402407400d0507850780101030150240d0741000b0301 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 90658732 1250 90657482 90657491
    0x11070f0909111309021305130206031009020d0c020f0f030d0b0301020403050a060e0d0c0f060509010b100305010512031306050307020f0d080103020a1d0c0904142e061b080d 76
    0x4a828070ba130000c814440c82126089080e8080d046030302c044a10594021617102c0788501d981c001414800c0095800810038064003210f0380e540c1c2c810324140d0b804050090741c20354840861410054040001110908060026240f07140c030440c01d8503983d000d42291140c0702612028625920386003036040302c000c0c5030083c099944402070760904c0360203882e00ca4070064280c440c00d03400307410851141e0008042c603544012289407140d0643c0f40c44018200180040c2c01d903550b1440058407590b18405900360915090710301041c0366241c9000c1000803400c20312140c440780c00800c1501815102ca586d20000d481190500a84980310240100e00e000e420583ca1038441c4030320031140c041d26030041102812240f0840750000425211910100024062140030400003248004205140e0f49800544640c0502500001e0f01040103046203460040c280c0e00300c0e4220b06034a4504c2800c2c400300c25811042c032400007103121f40c80d181c00002031044a1210410070f4121b9a0000760381004010811215019003e840620 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 90659982 1250 90658732 90658759
    0xf06050604151404082e180201021002070804230a030c210201020d0f0e060414040e0109020306041106040306020f0307030e0714041505030105090d11070f090911 71
    0x50060710002646400b160300611005030030100c200848050b5040403014000140120904410b03902a000c2e01b80444010011100900e1001c0c0c4600b10386c000e849a85c031030055819000290818981d07051a868850040194070b0103d85088200c500315400c1c3d611055845800b0a01c00703014206441182d548001051800003d000c80c075000c100580d00701c108218208100300400e26810361000318000c2c0540c00c400c45910019015002d5981d120415040c0041001c0034400011629486500540200c2e40480da80201e5401c05100b450b031071860303c82c020020111144c0000f03170740301e000800c01001c00400c0c600d20103180c0c540400703a500071a44184195142c202c0740c2c503030f000e890300100d51140000e8078048407240113580024031030040b2003150080400004284050001500b0164082c00c4244c40850b400601600d0034802e0500c116034240141c00c40c8201040c2c010084906210038070b1882e401283d041c0401c04465800c10b00701c8072701010010f811b510610305a00c64000c440b0840c0c0d4000ca8452002 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 90661232 1250 90659982 90659999
    0x3130b0721050c0708031303060e10020c10050a05010b0403020904050307060c08070e2b02030316030903330e151815010f09020a051312020f10120f06050604 69
    0x1061902e030080f00340e030700e119200e03405195203001305c07a83d40d0000d03082c8080400c0854000e50000ca01100500e0903142198072288000003660b02c10311400f43d003503000c0c0040b814500c2892040b190044000e031400d010765454120380744142d0049020182c070943d8040041001c0250800c211026240d0008051000c21308544000d004088101e481c200494644080701105240406401d01195408030f80e0340200502200c0214802401020803a01031000300402d12020301c40d40200c840e90b5200795901400c543c02c5151601d02141070403503400c5164000216032a100c103000e5050302e80304a6003400005c01140c00300070507142c040b0308140320403061641c0c420302c20a1900716010002e0000d03280101c0307081241c030000d18048018244a01d000c100c1490702b05004108954000345058149803901a04001648007008000c0c160307544200d40e0404085000c50071410b01045040010100702c0e018854440c00c0040581840503521201c4c06195403100212503a94269001c6005440050001d0740c907a929003010 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 90662482 1250 90661232 90661237
    0x50f12161d010503010c080708061c150e031204031202070f050106060f0e012034270f020f0409140604060819030e06210903130b072105 60
    0x4460400201c00000c078182c2814018403803c000b2960301e0b1405a6a500c1d0208c41d12400680f115600411a0380782c011090745426100128074001d400f10102c0c040c1980611086a650070b50001c0f080c2c1081c080c114888228000040c0d01580609100700401b0104d48044003c1c40350104c0200740b41401102003040c054154002d200780c521030f403a43d8040c1101104241e90000944030002c0c001042e01c0d0403910071000c40381010a4000416049552040e20107015003041e0755140000f0f1990861143c484210301058840b0b40010720110b0310710714407060890503e0055845a1055885140e25441c51512014213941240e161036402d1031150344030754441801703c016083c600364440d1040110700202c0c1e461f1419110721000c41d0711901c020314800c440741d0720124070103200c1801502404488901c0c40035035269000200000300702c441001d120b03d001402c0c0c46816540203481040240c0c01440070302c0500e02c0c1e0031405019541303100e81c003607218807051070f044801010400b00309065114490a85d012550018007 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 90663732 1250 90662482 90662519
    0xf0903010f0509030a051b030a020f07151b0c0f080c01080612030403020d031806080601120608030a11012003012405160311060c0d1104050f1216 64
    0xe10070289006901d109440080d0780090540d08104000d116860003030b07000304040c100d541403071100c0e00d8549640030b045401c04000d000240c0c0107445500000c100a1120701302401c420a0448240c1b40300d00001070416104094450303007145009803803424048154451001002000707140030605481c1c01009880f41812542203010074140c601180d410324207047c1d0480407058110013075081625640030020441c01c850710540500c84051b4840341021640207240020707019a440f10001420040001481d81410700c0403400703103074545081030000e03c5010044820b8110381e4646400080034412109005080303821411082d98070005412003104862005503040b030380300b2072001d01000214000e11a034054541c0c01c960014004110102c00403005e171620381c01090081c9080c0c440728a082890500d0030f001550010081035020650710580310300340c0140307000c0c000f22851850425140a021880c002d4240e15014070031400205451403083c010020301c0004946c1110704141d403642c822612049203004c84 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 90664982 1250 90663732 90663739
    0x151b0705191203030902011101061514070c15020106080f0a02030d0813030810030f061b0c02330a0903050d09050f19080a031805010f0f230f09 63
    0x7185010305144031100c09003214100d10075949030001d581d400304c00400170214101d0600a80f44840c02242d1424442c803009420083c002e0040d080c5507100203401041c0c01448101660802c001240002c0c110207400c400311420030b8400c0400d452075007016405041070b0703080351080b48038814210040101c00107072091424026010703192447d000c80011203207a03404944520040c5008225807000901c50010240e00000012400c0d0aa0b40c0300e03642c14150504810b41a19003070703201c0b241d0303a80314501240004884000c3c0d040c09001c010095002c0f81c4803440c0c0c1d25440064071790701031800355400d142000145821026260f2280e0343c4030045c0c1c4c00ba0144621b400142d445200c0c1d013010000071809585407905036030005001202505074401080400e0354403c002c69180016101d001460361400c07c00011158441c0d1211458110380c80c04200c406245548031a04002c0b82c142c02c5c22031190802090361503034405192040400c01a12080f440540c4e51101008482100003044041c10726090080c100e045000c9 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 90666232 1250 90664982 90664999
    0x106030b010902070302031b01020904020d15050a05100309060b1203040602070e1003021014030711062505031509070c0506070c030509060c10020301120b01060804050705151b0705 79
    0x1030b0480e42c00c138012250000c0169008002110052a1040004015003c0d407400985810400310220f000c0e604454503400d4915240e8408243c140e05203110390024000540e22450424581030000703040301039060207141899540d03501d030414400300f6044600700020261901b48506540120150b403a4014841c0c04018010301c400031880540721905240203078006042c05e4815821030f001c001340b0b81401c00aa2040c450300140364151540c28001451054019803500110076501c0c5400e9402c00200900340c541745110b0440c064080c11174501d841446202034507025840b582c698008440205400350601e6003d041001084000f40d03002e1040e5404a1240080d20599120b620013a600b02c460004000d0220307005116030040e50504c1f034042d1a04109400846003c40d4080c9400c0080303078400c0c0c01043d000081d01e100766060140c2566240c1c0180410302d4076040d00c3c5001d49805880d40040d008052141b407502038098140d485810590b600d0001c020001044143d0801c400d0f83d540712a0304c030b0705010b840e00 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 90667482 1250 90666232 90666239
    0x3110d050c030621070b0d0f0f0b040f02090307030605040f06050f06010f0c020f01050a140f090a0602070e150109030506070c1b0b030a0509030705070803070309050a050f01030b0f060c0106030b01 86
    0x7041101002c013041a402428401d05003480c0ca2580d81000312082c00c1141c0d503031013400d40b5008500800030a00c0d119840041c84e90468003d0005442c0c288000d10b40c02401003244a10a440c00504d0404917508550f000070113848034a44940c803400c01c184060402410b080620140c1030f050300b0800d01500090b02d4072a10b0700804402580c80c00f01607171001e5400501d252460141d540100008c0047d412586480d85210034115401c50840d0440701c813400700100040b801d034a076400d1041c28400584824002001100d140c036003884820310000300015498030b001d03010014640d018290034000b80d03a200c000d50701c0600c2c00001c01040650701120036540c1840d080550512032200c60f41e00400d81c0c121603402891a911803032801e029110217459401984000c00410300814401e001d41000703490f0400240d607982100381002030840c90341d03401c180c2c464101c105082045d6034413100940380400e8203082c00300c0c044c410040012130107401c10a003103030403c00005910720b9001c410350010068903c501d2012100f40d88 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 90668732 1250 90667482 90667519
    0xf03080a1404030c02210a0b0402040e030c0d0f030b0405040b0604050604020910050304050f16030c0f0b04050d110a090209041a030a0209220606050108060d02010f03110d050c0306 79
    0x2002e0750042d0118000710354220140c2025111583c002010b0081c0e0f2540565032500d0601e402070160082c1e030055400b109000c00c40c03502e806502c0c0c21600c100029420800d058031001d0b1100d25810004044c00100000a01c105000c0d8100200c0d00030000c01c00c000300d01e0a030404045500080f6801803096180078001034452420f4800d4800195018041200800065030213540035400035006580c14803801201040400c410000380080303038460429480711619510306009079082c660800c120405020303105001e204001c0064030100d0b6000c442c1580568410300303048800c0f03c001c4a000380c1141e003003003012401415a4001303100c0c4000036501042402014100b5102d0010960250381d810380090385a40c01524103103601a4104003040c14640c0a59050075880340185040e910484a01d521450100034541e04213080582c002d034140c0b0f03032144c0e100c102d0340000c043e041e40c0c1c51000185682c91070301c900704c3d05000c8140c600c058405a42040035042600441d0503d41003141d03514400c040541c01e80d47d03c0f14 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 90669982 1250 90668732 90668771
    0x80412080c0906210c090a0f080c061b07090c0908061e0403020715080a050c070c06080a0617010213170a0b18060f150102030a1409030a0f03080a 64
    0xc0c1d1849503600744481c101c1040400e030b21400d0645000e641c40ca09820030b0b1804444410f011740d1001140c240d441c1840780070702c100710a083d400503c40b0001080e0400c1044404118864480c02c221041c40e551105d4641d01840903105896425032803180c010040703103c035025030050680d049552150612165100310241d07481804691207001c49a0313a4100f00c00c1341c41c1503d88140c01902c640156429291645481d034003641d107502e000c200194001041c0040354940e84aa641c209130074841483c40c010341622208110109881446c04000702e100020b101d00c40d0990004002d00014640c00d410501c005a12034003035000740b0080d140d0052440000200c1c400b0000d0100813a000100143c101c008607510b500c81903410080102d2040c2011a5698040c15003e0004511501d00c85401420030705142c0006000512402da800341554010081031442c030b6003180510000c03211801395640c1c1e683c42000880d051403e620802000d202511400d402015003220b0141e2081c0388a00d02048480c2104110ba04030703c = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 90671232 1250 90669982 90669991
    0xc05061501021c090b0f0301030c14010806090405120c030408010609060612050604020405120d0207060f0e0904141c0e030102070312050a0b0303130501110304050f0108131208041208 80
    0x680c003070b0352105800c42c1c090001e041e04002030300300307040c0e90750b45c900d0002c0c2c1c1c41c0c3c4010742213800c000c0000300600401921050303103806000b0303061401d04070301c44010028010b40300c06000ca900c9400700c040060304004041048501251407008021f03100c05982403801d6172608a400344a4055083c100040781041e0148610811204550368000340405c000703c2c1c20f00148400f91085401caa001c000100710340c0c80d05550b4144040320800244410815250300038102a0550400b0013080400070159141c107500904550702040101c1d040582512107240600c1c281d0300030b06c03240c0940d0188445030300d8000900300c1550381d0141030b901c500390396107041000c05080b40f06128005000c2040405400601d8150754032895002d40400000104114040e000038a19000348442c1d6058203a010f8080c040e95a000c0070a103020b07820030340250300702802d010008242c460045107650401001600180c0c41c001c00845200c81c10380c00000a0000020305240101f40e40411a01564802d203000700894001e4880d0300700c107104 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 90672482 1250 90671232 90671237
    0x4030305132f03060f180106080109140606100519020f060c030603120a140f090307140a0f030b0a090f0f06090c0506070b070806010512090307061103090606040b1309030c05061501 79
    0x1c581c0c1b0f600c5000040c1d442040c84200c590f51325800800c175640c09204d5041c0c0f5030701446401904041e502440703441c00c40024003541c05422041d4400c092140c0101c01d840d0301035450319034840d400d545107000303d01d0a07070320a00001280c4200c00505c2001240303207009500404003a070a40300004c03911003040155119000c28480044ca856003e1010555032a010307200c0504100859882c010750100024130381a459040712900a00d015100081440c0c2000c0450051004000d415016861910f40c0c03259403200600740074010b6141d0000c58100301803980005201540409294214030080c02c3c0707040100503040702200e0442150502141904e4008191240c2d29400300d04400e443c1c0c1d484604451200d405056141400014040c0c15141d4801d0301c4400d206944800c021a1103120a041607000d4070140c041c841d082540400078090b81c04000f040b000d600030400d1718045110042400414880411291500c41c1145080c5001c41015400341561501c1e9000d034044503050f464854144980f5068010b00c02c0c003 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 90673732 1250 90672482 90672511
    0x5030409061d0c032a03190f091709150301080303010303030501060809060718080f010203090c010903030221040b0705010506030115050a0501080402180118060803030f04030305132f0306 82
    0x801d04a040e50b200069002c158642000ba08040e910452a0300261240c40d004d0102946a11f191500b80c07003000240d000f103002c10702007403115860f00c0c0e40525502e03420161010000a007000d0a44400c03208460511003103901664035a95034043c1c43c1c07a60822700080b000070382803c000040f044d11401209004014900141280b92140b5405991590714940141c40e00c03074040a00042c2200c2c140021805001510b002507640d1034803a20322801e116141440c103042c0710090b40c0500120350b00050141c0003003000d40c4180c0c820319143c082000070780229413101c0c0d0025000210305080000641180340190300917402030003108501c440030400c02d84940581900102c081200b088258819010290041d0028005407000c0492040f19840c0a00907009100e00b51135801c1030140d56020340c4a4070006002801c042c50031414a4800030ba000500904082c0c105034880000c51a120070400c0d180462540c800d00030b900c4101040d0b1034a40b10285100380152210200358001020704010034014030582001e60500d8 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 90674982 1250 90673732 90673741
    0x30e0114010e0a0603170705010b0a0303020616020a0f14060703090b0c09010509090f0103170414040915051609090501080d080717090604060e010216080d020705030409061d0c03 78
    0x500800002c20320011281c41e00e0000010585201c6d1042001207407866042e134402183c28403609640d03601410500540c0c54110801c0403a40c0400c0030f9401440c02014000003108410040345000e01d144c40c00b61000c4084a0704004108a46241080320002103040e24101c1d43c0e62501074040365a060380241ca916a20000100d8102020004041d240c0c81410010304000303c620121303048080498080d80003244000060040c407030140c4d08150400d6030030280310714040c2024043c1000350f000f00052400341d40c0340ca03075040810201c2e0140751020f0291110130007483c03525407100d0350b190505070b5484000c00d55510022613604280d020b00307030503100c480c401000e80c04400b034011591200024184000c1004146600112094a040450140d00c500300208000d0904d400c04204485c40d44020403a541c4c0b04000c48501410141003100800f9005110607440d45584072004000e4803070824001d007107000026001c107480c0355070b0b403024040c5d494000d1390005c01c0c1a114a0090048020740380100c41c21007c0c000075 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 90676232 1250 90674982 90674999
    0x9071202030901111308060105060307090312121a011404050312220b1e040302100804150e100605090403140708040b0a030504020102010e0105070c200d12030e011401 73
    0xd6810111202c000190103201038050840d940102549072084140b0f8001040300c01ca00300159405090110f414906d94104007101030a0140c5512004040708d00c1d01903103a2a403401582d40f0000c42c1c41c041c0c0240542e80c6642c906c91202000ba02a89012806030305a503049070030341c181924290b420150050069010580d640c1c0020b400c1256076409504881a9465404000078a21001000101b462a441d65200314004d11526034402808040e6a01880301700007507500d070004c600e28144c2134101401c0740d0315617040c0b014540ae071081000ca1703003034140500c2680000c400103404010380700310704040104a880700308120603004283d034042c2c00030702d560315515403800004004080304c52003038401c10326055481d095142e0540006174460017003543c4104100035942c0a00420000b81c040f08001c00880c40c21540140000103d44030160907504440740d0f0410b082181c03041d0500c0c4640045c003424040c007082c50407510003020b054400d40008e0800c0c0c800000c5141c1401008900c00001d91203429603800d11664 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 90677482 1250 90676232 90676237
    0x403023f041a040f1d060d030c0b07020c12010203160807030b0a030c09050f040201140a0e03060c0406180501080117011b03061505040b031501140a020307060b09071202 74
    0x11803801010800c00040d4040a11242804090795161000d0301da62500618070660b4034540c2c00484400824075541c4012854a0b02641e4801c03421aa0303000e1009640c01c00712160078a44100910425070030382030000441d0005a81203001c0400c54411803d041c40481c824242d00044e601510010751030420741c0240360042c42010b51001c0f0b9071070001a14000c0e400001c1c1c010460f44d1082d04e680d0700c9004180031440d03150086961090182c0800380c2e47e4141580002c1c0510b00300448040c640d800071841140d014441d0b8107124000000604444050074601510f5000b54030904c944c03c08150b0364240c850200c1641c1e200d00c0115a416112402c190307107400c400d05a240301e501217510055680d889123a09840728039614241c0c0404031350380010100e00b032030034070701e03610380c1603400300d4284401440104062040c2008a03603200081916115031244034400594000000c3c00810780c80045c00300300c08003c0c5600102070107019014003010710000c0814014070000c244141c40c140001071a00d00c1012180807103800 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 90678732 1250 90677482 90677593
    0x302070b1302120604150b031f021809040c06020606010f09051507080a02010902030c011d0f06090a0602030711010306060210051510020708060c120411010309060c0305040302 77
    0xb1107070f00d483d0910041401c0c201c040740c0c215820400b0350a10340c0350f00d07a1480740c2c800c110400e4004044800d0401c1d014008a45a00c483e4580306400080584401100154501780e000001d8040e0842d07040510300504a000140030716030040c03007140009481584213a5102801d49855107030014418105000c0c411000011080c080440d81d0400031500098102d00052089001647c000103840c3c2c1d09104050070b0901c01100181004101c440316100c03075102898184840d482101c070040800c850710081100e80c05038218559000c01400c00000e4626004001054060b02c10000c1c9051020440019412641c443c041c120040e40012440102111a0783c411038004c240840400c2c00c0300c0036140041c0700504d007203ca040050300300b6a010000d0850401504d40c214801e05225400e22180c1510920103c40050001e0051001d405448541d40d001e41d20020032190841803c0c0300c104034800c4c2c0500940020380e4110010b20960100c080601594410b016075100c20020780c09400e807150b580c002d12442c6602 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 90679982 1250 90678732 90678739
    0xa02070f0804060e09180d03020c07030507061d03120313050703061503030206010803030702030906070602040506040f05091510030c030b1003060e01081b100201090f080301090c0302070b1302 84
    0x20400c0300810305003800340c40100354603070340d0310308090000c000d10081d04c1000c0e0940307841c0035498030310040c4040041070b400480740c001d2800503100d21808030101d1503d491a0b00c05000c60056140c046079aa62100700b41e0f142001c040f4060f41c5c8110402e007403580d02e0403100d45e010300203403040c00803400d0344006030f0903411a80c2c01613040b2925140c917030f299403040320158100404545a2464104101501805180e005203d4a0050340c150324041801039168460113410f548a0800012020100038003a415240580070151510381c44545038a0350061441860140c0f0384207004007400140b401074505100d20105c440904521180f000c3c541080d000f40c8401e04420b020306888500b0b428a41e2140d070040030281606550104696182c00e2030b181c2d11081c180c01070070381030f001580c618100b0111042c070100144420b0314843c005002c8401c00700c0c0100140d403030003031010f0308040b0118144020301c4045c60503600414000c000100f40140190124031403500020000803000f000100001d480e0b0f00301707094090019 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 90681232 1250 90679982 90680003
    0x30717030a051614100c09080c091b161a06030c0126091507020d0f0807120e0c0126010909030309020310060303080f07020a110103020409090b0603010507170a0207 72
    0x81d03840d480710340c004d01c0c041c4560b41e00c0140c0b50702019205c0d004c1c04480700c40906022800e80d04186089032580100a0a2802032540034040f030906c01200038890b8440d000420b9054a034010340c602c41c1c00d094152242a101c404414480c3c14441040d89006802110002c3c01041030403281001554061099a034040e2a0142c16010388646506080b034240310b0541503000d4088415074002c40003158002800c4007045601440c0403012280c1c00000040764201c8600300140c1d107640d11401200c4640310009903401541c02c101c0c0312440c00000150804440400340c8604000d0704e401d202d41100e0450811f880255207469000411107114246d00941c41d00d40245004609403039950082880e116000c0c4038040c42c1a542c8204000385603000c040360307801100c102a4000541071400000b50f580c0c0d2a918041c100f10030403501600710307038003a904a4004002510041c080842d0302d0400b01c1c40400115a0603000354244000614018442e2000703020007109a010480540c603a140d80c8002508403000448694505 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 90682482 1250 90681232 90681277
    0x19030b03010c0e1c05030d0b1306080f0f0105101701091704030605060a05010f0302030a0e0d0c0c05030a0c15030b150301090b10020c040c0c020402040b0306030717030a05 75
    0x3801640c06402d00750302c88201d07512408080c0008002c0e8185400361441c442507500002500c00300442c2c0c46407a01c00c1d80070614206c2d01c400117a00d003107a00c3c00320180c0c501e0703c103000440788800310300d01e0210090700d81275961142c2c0c50345000307080e282d003124000b4010ba10044c051010702c0c3c1c1c12000141348907484000040b84440303542e880c030f40003010384100b1544903804981041000b0b40c501840703500202c2510304210080c40c10f800606454440002442072503004070000d4998841075100068403d8a03a04450404201e100081c041500480068460310700c010700104482c1000076800c5081d60703100502000c030900c0c00e0825011a180302041108058172a900107549540c5c039514503642c1910f2a051a0fa254505120300040f1880b6085581c010961000e20516464005c14014122001500d001c42d801190b04401c07035642d041850005e500c144013180c0811441c0e4844c0103548159001c1d4111041551101a401d010341c0c80390f4843c02c543c4c1d108004000070f2521400291948a01d120545080141e4 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 90683732 1250 90682482 90682489
    0x3051e0103120f0c060518070605040b0307031d070605090406090b0a09110c060403090527060915090a0c1407080f0a05040b07060504030f0504030c09181a04030207090c0519030b 78
    0x503580300d82e0f800700d1f002d211081d01c0c01c140014002049903003042840e2915220b4440983d000041540c0103040d40c41c50790b80403030503117003900c4484641e010f400d44003070940710304019115410800c1c00034001c5140000100ea132050b140306006881200408040700c0c24038008054004d410000c1649400f0b07201444031a04a03030042009a000300e00c44d459040c0d02c0c50130300701031003140d07030041c04440c0c21038150012207200b0750490103045401041c241d0307840c0700d25503030200700d00b00072001000040d4100e001c0c501044a018010f500201304840c1c260780360b40c01303145020011540c1c0e004468001e840e034103007001407595000541000f018405041e00b0840d080c60760301c0a00c1c654130303080040151461611074003008101035000e00c0e8245840200d0500c0390501d0f0441c0c580c6600d0311501d000c0c410100ba0381e030a0070200700c00c12a603880c20155010b22907040b10950000d040d4800c5406807401c6000d4401d0b0807001c03d4000040c001c0851641d00c0341d4030f15040c1012102680000f0411550300c2080c1991a10300701e41945 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 90684982 1250 90683732 90683741
    0x102120702100c08010e04200303040e090705090106021203040614040506070215160c0f060207050f010c050319051902040b09090105040902010903020d03050d0c03051e0103120f0c06 80
    0x1a55030042c02d290155450352800703440300c0005900070040084014000400103a00381900140c020000601d010f264030b403500046041c68850641c5480701040c001601ca00066600744076040450540d01d2941d40c40050180c1841c0c28016800940c2145841207140d030001c0015640c054061380b0045020120500c508102da0740c00d84081e125500000104407116404102d0340042005650521a0500d00a1340d41e0101c2c15413941640100103502c07446201f031000703154808121301c0e00082c04540d1181ca49c0381c03c5a42d2460010f001c1559400d1034064540c003405501968460b0301d01c0314400a2070204461003400404c00100010009580c00c00c1100441a00d0320191029105220038103940d13030b10080030420107100503442148618101440c100c0183d0380041c00d902202d5050b218610b1a603840c0c41c00390350b83d01034a00520442c80c6800742c8404625890380019000b00d0030000b8140481485611a0003c01d009000280a00e080d10800c81ba550748a4118544c5d504036070b1a012181035400d660300c20650303 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 90686232 1250 90684982 90684991
    0x30804050118030c0203010b0a03110409050c0402041410030c140c03120a05010518190e0325151407050a030906050a09050c0109061413092d060b040302040e010212 72
    0x5a25100c411045086c244a8080f04c92012250802007500e0341d5240503d0041000003980103e841d40d8007801000410050748151142c0100199150f640318175080134100c20550341e80707200703a11010410420500038840d400101080780c2c0c0f00b82c1d03400001684402164400707001001180f004110a40701d041680042c58022a40d01c10082036035490a020000580394074840c24410003004c030203110503030091a1924141e0704040c1b0b404119004144001c2c0d0030347c0601c52a01c81b02c1a1184c1040038214500c11400c82d406101c3c0b400c0c1580010300e414450304881d1a00320f0702c507040c14140081070ba940c0c00748000c2c1c1036a22071403070046001442d03562460240d0b602611203504554452515008000051100c502c0100d420310300f03c0360040c40c004000b0402c600c3c914102003507600001c0d075005a90304411000020b0203082c0024000d0300c40001184003503441c904e00fa15420f000940715103c1520981c002c5004980b8007042583c2018150b030200001010100c1040c0c4181d9802c100441c4914102100540308 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 90687482 1250 90686232 90686237
    0x40f0c0b0318010e030c100e010605120106060f0323060f0d05100f0203060306010e0601050702090f090615060a05031f030f060c08060d12021011070201021608060403080405011803 79
    0x100210b4010326007500c02030400d82046030130611841c04240400a4100b11584402002081c5044038040480c01400940c109642003540310418145454054010008685861743c0700607031030142c000120101c56000340c40c200008516403203a00c09000455140790003040051229075000e8005000848e101c4240404030380d039400c0702c000d92003041030701d215074141c003e10320f1015469450300c0c10000b1346500050042869003980e0401003110b41c0d10400948801b280e001e00130728101e090601c007c44401c00c04403860030480c880c41001420845440c0c0c0301c80403587d40034114a091600c2264140c5043d040107115408150945030200c1e44d40e091034190703900940c05010802c04c02140387c2481004d880280178520180a044003d10800740c03104982044402d07000a1007400c440580d060403420919440341c0c0300411420b21000c0c01f04010807100408480b4800d80841c1c440d03005001010023200c00e1481004119002540041e0200c0d02600d9001d60251091000090712005041804209024030350103500 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 90688732 1250 90687482 90687511
    0x3050304031e031a06030402090103200303030408030117070605040b0901020f0307030305040506010603060806040204111306080601020c190b07080f0c0d030509060610050f040503060f2a03040f0c0b03 88
    0x604407808181813000c2078280c0e410351642c80c0980114011041c18070005003228103160541c00c1c9a40401424580c1800040689990741882d0418080c0381c0c0003801100c04c05103520f0121280480005100800c5030380c25107801c0d040a00c0c150403450250030240c0e2a0b41540a40401003030401820b02c001c214051098400145500b0282011403402405811075010b162500600380100480003034543d9026604032000308c0c40c02038241940e00c0700c1c090100c3c40480c0161001d000302d0a10740095010b0300c82c04007a03003150505d5112804000080e031462201a01c00c104008060020007140c0005164071402090030f14600300001d4142200c1d90f20103042c0780d4258015040c0ca56000b40e06019194014038940004d140b20300305540003e074442a2003a2000c00c1c45400940c220000460350300707642c0203001c01815280d0700d103001c101104c0c0c2200c080b03484a032200074904810010b2001c403c501010300d030510359510b05513030700e0790380c0c2c15880124000b00350f80c21020140005030710a03d98009621804005c0c070f8005 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 90689982 1250 90688732 90688751
    0x906190905040b0105010203030129090909070302040f09020609090709030c1413291306140f0105031e04020301021201120203101803030209060f04030f1103060609010303050304031e03 81
    0xb0751414045e00038a0464000304010021500300055040000300b001d0f01c10440c4028115000c0b0483c4a81081907800c00e0b241d904000008401040010403230b0300965050280b00c170481c1041c0d0844045401c000e52280083c40a001070b820b040e00321691003255810804010b44c1c4071f4841101c03031449940200170285443c0034031602400c003c00d0390f410861030070100780b05900d02c038644501c0200d0a04072150035a9080c102c010440d5a49103188842007060326810030001d621002080d440007803a01d0940d008607002400c900055108801700c0e4402c1e400ca414200150801c2e1000400c154009082a68199000e02004104400c0040350074005d048501c4058208591481854100000003d80210452424029540a95500000c12036041e45480c00607510000480060701e00c0c06415400c134540e03c0f0104000c400c00101c541c4030100315010b5041302c00030041c28020560380720400c80302c40743c100550000420009006070007460b00203220b4240116440f0741a0003c401e501490402a40017030f0711146800d = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 90691232 1250 90689982 90689993
    0x9030c09040507030c240f03110a0201060303090b040311010c1103031611010c05120a02150112031106060607030309030302270a080c030604170706050709030b0106050304030e090619090504 83
    0x220300030442400c00b2041303d03c4542c81150086a408240424441c1100d1f0700540184070394801881100c007441c030141c403100440002270007040307280000c03070100d041c840000c1582304420b810f07102181d91108030a41d0035482c98004441c2241c884408540d114030101301c0800316541030010700a06d0100700c40460ba01001800d01c3c6010041e42e00180d070500020903074050100380042000d41880c64007024240d51125803240c12842c1003603078002d2038085101e6400202d4016030119400406a010f81d990300307448140d110007592140c8041e10708652040b020040003000078040d803c100011030084c200141012840c00351709030002c0401c018408440203081d907400043c40d00c0b15448003d00100030042240e202c401011030b685140140c00503180c0c074400d001d521743c81629102200d81890f401141800141017000c0040d18403841800101e074030101400000ca170f15807194056905c0b030f503019540d14452110310fa09114010202404407500842c5408a9110b1007400d800d0500080044140000b000e00d81170420 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 90692482 1250 90691232 90691253
    0x306050c0306130b030606010e01020c0d050105100b04080309040f020706021803250308070c0308040b0c150402010c02040b04020c0a15060e0105010807271502280809030c0904050703 80
    0x42459944c80d14080902c141c8000401552109007800c0040c490807802c030043c0d1414007146030070b5920840c3c240350030040080640100d400303030715a424103104454646061701d1890013103000d00011907206101e01100ba00d040d400002840c410004010318041c0e407a191001642c2c4904020007100e0044d040d4851941400c000c00d40b0a0721407801042c2c4849103031310303e19a10646921018080100103c0c0c0801404002600c201c0210f60001140d0307901d80e0703161041b407484d40041c01d40300b10502482043c1507501620102c1540714a078140d59020158a1641c2080003c1050300422500300364240404100d5800401540701e1180c010700e10a6609188503401e5815138034680c025602424030003004001d41c0e40c0114045400001d0713410001400030f0681c00305d1411181071100725255900c03506000401c5000701e00b2810b6041c125900745d5007076071182104c21059031003c00b4405c4010f03081d90340a4000c40c100c4c038081d00001034001c05030b926040d050000030700218803d807001d84061b00404800c10403c000b0560 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 90693732 1250 90692482 90692509
    0x30807120305090a0605180607080f0105092715070201060509090106060c030507030203160b0921091c02041a10020607020a03080405240106020f0703021f090306050c0306 75
    0x1c0034852882d000c1a42c07030302e890145400610054503200030880403180404a1010000e000c012140d482c03503d00b40040000c0419501810302e8504600041020b0814901680c403c0004129039180700d440307041a00c005064401c4116128004c50001e081c80026500c0a170b4020781c819800410011b007014100070020002501e4080940c1c54240200300ca55080110174a00540504000761034000c0c1e81400c0c0c0c03e6110381c01819940720746038400e54042041c90140706006a40704011110761841d516100181c0c0c2c0c01034000c1da481440107020741d1f1954940800c8039950f03078401441380c0600710f080c2c0c3d0100c1d0a4508140220141500050100c00c09040800da410324600c443e20042000d03080c4100081c0d25660740c480003404002d00d40d400142070100030440911700040790715101c1d07500c02404d182c1136602e420a01032440140140e04c5948544400040c6440542c4d40040a100500000c6802e05540d4201007020406200710440d0000c0801c466218a0384100311152030309903689480e400304040340520703c2 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 90694982 1250 90693732 90693737
    0x70602011a030c040c050403050f060a05070302180f0d1403030411030a030813020f0303070f020306180c0d0512030703020a08061804260d060302091605030a050709030c03080712 78
    0x7050301e0030690b40020b03a40c08450302a100080d500d000300d181106c492191b80c001404c18450ba8240d000c0002002402c580b10300c40a9008020760344a100c0220260300c20031b42c403c0241503140400340c0c5545000038004403a00e00042a0310407441c2141e071000050704030080b030072000b5080403040005000c1441e400c0c11401208034040c1c4100b42322a03074041c00c800340c041c141e484501c0000040d6021034035a82c4070003d500c03100401322034540d11130345445d04141d4030169040340640110750104030111002c1d0584518045101d018140c42c078452401d011a290384100151020b1088803000303d80c05007440c7c02140100000d641c0540d86496003040604a0301d406032002c0c1c05a403000d900c1c003420703111841d8026003096102e1103100c580e1100c84c409144100896200010310040002c2c4098000e00a0b031028080341e100340d401070f030035070f07501528141c0b81310100c101280071403403c20009a0082036a400250320406605241203865102d49941171036484a403c01c03610260b00144d55014450713400a0003108101c1417 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 90696232 1250 90694982 90695021
    0x2c0a0b0105060a05030a0b01020a0602030405030a110609030403060e0106030c08060f0c030609040212010b0603011d011401081303020708030f0309100903050d0c09170d0f02030f031303180807060201 87
    0x42000304036220080502d2035041c1c1d101504400c0343c3c400d01c4ac44500c103402c11015034980c1020700b01151a684203440d80b50100d40c1117246c045008001107001c0b8030502d00040034600b094030315142c8401400030b0700f1307241c8055582e400c4040001440222007001406802004040914082d40ca050000300d000e007030088030703520910801444c3d6850503030441d40244c0c15240e40c10308201003241c15000d4a51803101c0341d4410001300010a6100300e4802c031a10410a842d09080c1690b61080030018400341074000f80d00150a550000300715860700c48071507032164424411541c0e0b1560f104180350940c0c00807101c202400000009022481000f0886000a11718105040201450a230b4015001c1c1c0314070048014155251600b51003000c2c0211078940040942c03c5139810794020090541d911144c05807501e02c041a007142008085074400400e0b5104248452585499a2512a2000c00c035558181c8100c0801100b0780300c4504002209400b0001000b8610003410f04604003880a800e41c1d0907000101091003e1 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 90697482 1250 90696232 90696247
    0x6070206041e0f0c14100c0507030305280c0605070f0e090910020c010e01050906010e0a0504020f03030a08040303231b1303050d032703032c0a0b010506 67
    0x182c01c0ca001421000da0000c00940d41880e100c0e00c031051108000e4030700c042d0f07001c000031030000300031103051240e07400c854164448902d10f030240d45492080700007400c99403000809200283c0160002c0400329460705d115420b103043c8080e1211104c00610420b800643c070894002e042108a000300d40d00403050f420070074400303000c4510050180104030080c2d8420b000d807001084001005115031201134900e00019940c0d5034201e036099001c0c0c04030030001c0080390b10303140014940c0c2d030303010402d03c0c1641c0413003070170b040c182d10390300300309400b81c031002c1e006991010086040000c6503804000a043c0c0d045291901c407213070301d080c1c28040c1c111000c03c10340004504801002c0c501801d041441603500c82040c54001d003104008800d1600c40e4050010a00c0c5c24043d0444013000f4001c0005110070a018655824071070000040d0384805040045081e1400700d09051284800081c043e4010443c04485200c0302c4910703000c80b25100309c44810364003c1400c030307800c840300c00303c24000c512080d24090901903510702d10740b221 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 90698732 1250 90697482 90697493
    0x180c0501030b0a1410051306021e070b0f0703031415090a0c0e04021809180601050301060308070605070e040f0204090501080f0304030b0c07080f0405031624030e03130302030607020604 81
    0x2450885407041d04c070340c0705045d020b60282e02501d468044440c4628010f94460744040e640b0b001e02c0c00302d0b451100c0c0b00d440004000c20700043c03180558481d000780d54100790811803140500c0d00004812024144c40714060f541d44031500170814440c10340302d5000303003078902d449003070101090340a04071244032802c22811540098211021b0007a9034401da50050341c0d51054240150303501e111000d0b20794840102408d10840d507090035580018904044182c5a07980da94070b0800d0700b02d03001d82c40024280c0780e05001501c0440c800d40c0c045c07503001c0154100710088208080000f02100c01c0c01c401d0340358140d4045802d0020100900c181c0f03015106071001019030076410300c0d40540d640160310004110101e10310010308030304400d40a80d40b225600139100c41c0c41301c0d04845032240769000742c0100c40c042d2040425071a041d145601c441803c13100c481d9148054071207103412443d9a10b00940000717084c035483c0c02c11003050740300400080540d4843c1c07405202e1a00d040d40b04240c14404042e0116045500507170500000c02c0 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 90699982 1250 90698732 90698759
    0x10203030c070c03060606051210060f0503180106030c061205040c090203060303160c41041e06150518010c021201020307020109050607030c050f0a03180c0501030b0a 73
    0xc15120307816191001440c0200514906410041003107084c0b62000446a4008000d81703090003046111003503556452240d0a20401d4921809000500400004c48543c2c003681c001c40c3c009840d100d50300303003190103052613a081d03450302e81c0100c0300c0706400c000c100035542c0c1c8007040d08600344c044c0e030382408a414180c03030303041020a030780c014045d5655001003c550156030401c112072041584200024004072141020580c0300094801c00c00c002064004642c0c5400a80c44d40b4000c0401d1f40c2d0850200b03103c861401c3d45400e821034100ea410a650340442c0b580108401b82c00044019440c0020a0305070510401c80095a40e40e1010000c1c80414000320003419405450303144000402e02c4c2500c00141d5034000901201c1c0c1c004003681e4035502c0003081c4058144d043d00800901e41c01341c41101c8060320390640031803c5500980c4110002002802074900c0221014000c2003890000d14021035088548805010301d00e49d1300d4011a06240e209400700b1240d6014062240821030458058841a24014141c0c8269 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 90701232 1250 90699982 90699991
    0x8010b0c010e07090b090106050702030d030b010e1c0501180302100b1314040c050f032a06120a110f03010501082701020a1b0c05120f0d0f0f02010b01020303 69
    0x4800118009008100941c4407610070b011080c100c07211180e803091160001c0c6016038045028040550011070005c1c007460440d80600c0d030241c004c4c4009407600c182200185005643d0030b0400409480c80300301d40d42c070512280c1d00c03501d03054024250302029140040c05c503140c440003074803e08002d0b000716000c00d40208040e480e2801000001c070703d520700c180025540b02c0d1070301000d1300b01a1410115260f00d80391041e00f244502e206040c3c2a146a0702d8204101101d1008042c4d158154400c1601d1480c6111119980d90384003247e101d698910300d54038002558a4010300d80365881e84d00920b0030005415054015012141008480c103490305506c941002d4091005004a506200100d00426510812400803809591080e040c04c0d0980c0c0340504c4c0e0700c0c082d60103071610000190703150401c0866060410700504200c0d40c0003804001d15840c240901c90050404280711007d0b003d480ba140400c00b2050040800c4124150740e150740c407050b8041d025004660603044401103a242100404560f6000411a03030007 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 90702482 1250 90701232 90701249
    0xe011a060f040509010b0702130501030c18090f12180602030a030c020c0307030804090b0616260d0507080108150106080a1d0a02010801050d1205030402011b0507051504060801 77
    0x150120340301220582c2c85994001e6402c8503a01d03000150301740c408009004824802c84081400c807810405643c00d40d4003e0001514204000104200001d0303ea680002070074503080c800f040001c01c64580e540340c45002182501c1d14604421a40c5e002c540c403001d05a8407401c658428802c590034894000c0d41d9020340c0c0d000806055a0b5141e00741c1581c000c0043c05d400182c01000c45404944078581500c040d0440d02c00c03042c106043c42c254805524044c800c2d60601002d02101e01000d0940b078a0b03a4078a00031900000840360fa441f61413418030660300300100700c150200400401d81d0305100c40c00400b24441640985401d8101e14081d80106540c0500c1d00e044903050324001c11152100401240140448100c10446c2104804e1400920001241c500301482c000d0300c079001d4580e80d407000d00c048142e1150780200520411400a0241c2c0d00a02c055900580185802c010160b008135540344214a0004180d401d41d004410030056890042c42c1d02d0000e18034491a907051528101c405044030006002e100344 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 90703732 1250 90702482 90702487
    0xf120708070e1e030d0903030e0d050a080310030b040b040c1706060f0a120308060f03010b0306070c0f02060403030201020702030d050c070506090409050303250201020702011d030115080c01030e011a06 88
    0x40841c100303180600240008054030300105c4000400b9140701060f02c4202c02182c1c241a80b4650340c40c2c130002e80a596500b05000c0d00700c07224a070b40d403500942d00080822510900750700c0c002c001315850001080c070640c4a000b4076a003a00301403c181030403064640c840f101e10342c44442c1078014000c000c50000c0d000f200690f56000c0806202c400035940341d00d6134122214007109408002c0501d40d11440743c034000c41003a118944110304e00424542600d415140c4985c0640c03000d404140b686211741d152456803801007035840c01c3c0d441c0690010702a07901952003a00140e4010511909524042c030111494140b00c1c18900e00e0122800c005a49904040c481c4500c10b074408900c0d46c2a6840d41e400c0302c4403155100702a03964138600940f492600000c1201d640c0300b88030042c5602220b0f40d005108681500340c050b100d1691500080c041000d1942d54440c5042c0c00d03540399a54011000b00148018010307180820180c5010049240018100c2c1d811300b44554841e0306241024a0225484907c0d0b481d00b107090750340f00d5 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 90704982 1250 90703732 90703759
    0x402061c0902100f0e06030f04120c081308010506010e090105040b01050f0301060c031202041d190e011a180408070206070c030809042306040b03120f120708070e 71
    0x5004010030080a5041040026400081c944c040c0b09600103943c541c036003c141020030800d0145501084454081e01d085050104010990f08032900e03001c241213184c029400711160361003c210350818144609800d1001206104000082c0105e550240083c604a109902c4020010301141418410341e40120380d6140d40c1c58650348994101d80900c2c9040030103d0396969124002490b21040702340580014801c0a2007400340b40c1c4074001c5070304a4500324162205588142d05544903450050801040c1c1224001508520040381c000c1d100c0d40d0414100001c0c49140040001d241c141d08844d200b84101c0d000700400c004600065403032500b090700880f0803900e581c84c1c2d10105841d403007640030144c4a801081030003c02c120000004003255001a182403203000c9004100101542c0200311a404100e15000000e44c02e083c503600c0540b020000800b103a0340c000c08901c0302500b039800204801c44c414000248000408400f00203a038000140c0d00e04100c13a4500014000d208003403010b24940310300c03000c50031340 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 90706232 1250 90704982 90705037
    0x3020705150910060b1b0d051207050705010c02070f06181509080f070306110405090711030f040902030a140601080403030b030307080c1b0306072133090203040206 72
    0x207503e00003842c0740c02c2105503201d4070300c991213030001010300800072009000100307102400314591030b02043c15102e0500303040744243c80d190964030041c401010003000340405c3c0003280c024000e51003260300c950081c4c0301e0b041c1018124030208203e50410700070701030010b00d001c1140103c8803d4108450810501102001c202c07a0129151070203a84010698402c0780c003002100030f4041150801c4074440d080810100342c943d43c540d000341c0114490158044000000904068001c2c10ba04418030007040540745440981420705134241c21642207605403da000c010428045150710039210103821000403a4000d15065000802c40030b0000c2004081685880c3d0140d1a902c007001a0b60000f580064100d0700c482c0c0811a0f1660340700b908000b140f03440d06030481544181004100e50307000d18034030380c1c83d4000003040703030a07841c0c900003015408281d40703a8901158000d2540350340c003a002c090125214500c6d154000c180040c620140f504200c3c2e91500c100113000040c0c0d6039504481e03100461a1003001c882107032081c81c = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 90707482 1250 90706232 90706243
    0x5011202031504110a171506070212010f0e0c040504050309012109030e040516020601170f1e071a0301050d0206071205031f03110103020c0703080f0415030207051509 73
    0x540d00a41042c0c4d11140d00306207100600302d80401d079603845540c0661b052040c14000e0040d1030009403c1214411085e1a08084008044050018082452280c0420000c0d0700316a0445021403200341d40b40c0400c1d03205c01d4180b2460459a130101c506000600300340d00c4051b00c1e40700e1002001c2c14050040f007601e0704145045040300501d0000e070030400034a2060704000c2d104410260b10310340706503d0074002518100f410000b84a00001e1a0300801d02a030808075041078802c00700c660a0007911582c018010300b20020081d48101841100c42000d01c0340816404511f0000180c00c246180300380002c520f4411140307582941d044450172200024003000742e001003a0280710708040a040004401108200603811000860040445801841b2605546400800ba02a0340d00004100806461900b03031341d588030f40c001e40003c00c0c0440c2034501d01c41d81c1e60b68200a40d40000c2600006810200b030411211218a8025000480a080c15454400540d80742c9440740801500d202944001001040000108000 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 90708732 1250 90707482 90707521
    0xc04050d0c03050307151d0d03020a0905041503020114031e071106090706020d050a08040204020d060b18040605040b01021905010b0d051e07030201090306050406090204020a03090302160501120203 86
    0x4c4c0c0f5035a103c24101001e001d058080042c090a00f002100104002d502c4c40300140030110102510307140c09840030403006980103c0448040000c0303d100891581d41d139200e2040c14040d001306100d01c0c10b1640c40003408038109034140740e040600900800c401607900801d44060480482080344059940981c02c0e55100c205c60f1024005110300b608010b0702400028130501a20050b07004c8899019000c038080398540301d900300c1d2a00142010300030800600780f030f40142860341d01c60303080802c201d034854020240c6a040090b07120922015040c95052a0500f0301c1680040d100554091043c0010000040d540b404507180c114244160b180c10782007400400c0d0700450b04d03c3c000611a4004041c1401d00d15a51a1010070b120019140c44290043c14080000c0200413603506844410304545991110402094014000c0c2da0198130f98200c003005030340e54030081082e05099140002c0d58049410028980000007102c0c1e10740c41c0031030030300707024a81e000704408074441c0404c000540c1d241c0d154490381c032a0070f54248 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 90709982 1250 90708732 90708743
    0x141203010306050f101505070609020d031d0307030c051c020a080307020102070f060e102303040b0702011a0f0307080a08041e03080d0f02070b0a0f0b0102060c04050d0c03 75
    0x2100b000710a4000500034031619101d14032585a00c2c9034a21502d000c0d00c683c01c0441885060700c035465008501800485019801c001194022500850101c0842040880c00a4036246500360319415049828400c403000b503000300103070760550342c52000c1c603452805403d1103207411401340c0724240010002000001e501514004076695500600c030b41e2904202d1089005d030003043d4000c07a080c001e40ca01e00c8200c80c2c00d0341c1d90104041042e801d2224100b1046512000c00c0462306104150180044a803020340400c040002c0d9240391a003004c02e203a580c09031282e401c690605074014050222031014510030300c0c5c08c83d01065102162800640742400d581d0001d511401a280034138140000840940100c03007008103030101c402e4007000302c002507003040d0200a110b014103000340c01080034a9405031105031842c5e40e00520340310a94136503014101c01101d50821164440c07030217828806c214050180101c000317000902d0070f814a40c8150302240140e0190a001d00c10041c410010702070040e008900641d00320 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 90711232 1250 90709982 90709987
    0x90f0f1430010b0303031003030e0123030a0606020303040b04020103020f040806040501240e0c0711040f1a01020102070c030206030603010216050a020306011a0d050c0903030d02071704030b01031412 87
    0x10075080c000340d114060590410b52a101ca00495410040704a030f1040030740480040241d81541c0e4240c1340701b40c003107000904200c201500004c0050f880ca0701394030080c1003400000d490b4a05500a481602c0080d0440411900b0078000e01000070380d500f11300c5400603424280561107900303140b420038140c0141d90050030b55118545c01d01c01440700640c4046044403060301c120070041d01c014011450600305104040c100c4d07506000051014081602600300e60384035640220254111600180540713004031a5451096520381c0d022900d882000f40110381180700380002c0d07041c01c00c59100d40c91a0221781c80083e005040010000d00e80d95001e5048403021402100c211000440c0f50400655650301c10f0f508a00900c6443c00108601c100c8092114000b80c8054000d4508400003400c40302070403000c6d2441001010620000c01d04c1e0742c1c188054100c000c01003000580300c070fa0707a084c2500440040111540445410401403010804012400e4156078014042d030700c2c682585800c20b403030890a150340d00e1107400e02 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 90712482 1250 90711232 90711289
    0xd020321041701050c041202040f05090319090b0f0d02040306060308070507060207050d080717040816050616141f0203011d16030b030f0a0b07090f0f14 67
    0x11080504180c41001c800c16010352640c00b5040d0807194160303450703401d01c4c1041c00208007901031440f00000540c4050f10200f00c511320f4400076000d480c2c058030416116040440c0c1703a075200d01440d6101c000610309140c5044854038088440d2098070070124032980c6940c5c00100c80e0f01c00b0050350115002140e02c03400401541e0354030f041c1a1416003200108440e04d005070100014003a2001540000340c079402024104002040c1d600d121065000403012500c40d050f40780e20051020110010384014900500940140b00c400c1c5001c0c90400f80329004103105d110244481012064040780625000307078806101c8140890411103507190003a09a10800300800d10300c404003c4c400150041d60480e910341e1070400c58010701d4140c3d4030403c0c0f4200c13514442102c00c58a44195184240c00c04004e030b8402400740c90100c002c0b4200541028040d12003034850240d1001446202544072030031000504002c001c224960b820240d160b00b98107450300c05c0e204000d1050b0f610800c01d85d24041c052140303104003a0103001e00e008 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 90713732 1250 90712482 90712543
    0x10c0f0503041e120b01050906030a0501060e061914010c05101a010e100c1e060e1e030310090510080d02060103031b0203031e09060403050105150d0b060d0203 70
    0x4070411104a003100080e0025003240e082c20504d640035448031204189a09010502050f4440102a140c4c103100c0d219a14001c60401c0c800d07900540f103042845131803840c7c0311040c89500390105031f02c04101001800304001d009040417158601d001d00346060050710300e543c10000d1901845c141d20b0030b042480d00000814140070200f4802c940d403420f8858000ca07004090410078940d520a9000003c910038a024100052080c039030501c24a0009090400c40d038181e440318401c5880245041d0b509603c681219010600d201d0400050180014000c502c1d5140c00c080d03440704140e062203000c4081e9141d0000c20841e90300c000151028002843c1115800100c80800958441d028402a8041190090000104014501c043c11150340260040d8078001d0303549001d10036040030f88410080e904091220401c0d0b940c41200134001940201c0010034641000018a0350150200d04030500c00d0051382c44290009802c6161300d0350204040380d10200c14034250000c6818654003110303450a40c112803510f0203e180303 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 90714982 1250 90713732 90713759
    0x5030f030a030c050a0c02010c02011b060605040506040b10051305180a0b0621090c0d0804170105061813080406020709060b090609150c0d090e0a0614010c0f050304 72
    0x400781e5020310203034070010416038151080344002c1c000200d410038028099401090ba1040f128070601d015070900c40f20f610baa00400384000d1003100c0260303d42c0b07c01c1042c0d00d4035009407600101c00321020440c039071b070542c002040086020611014000c001c01c0258001040030403420040001400b88465843e4603210840030050071190402554940301040009003010000c0c0c5003000494158005081500c0405a00d00c40b00206544032600c10200100b2035a260f030103080400c00d100cac202c02c6450350b042c840900b003c40c034203080042c00380e8503160401049640d2800550002d45040c0080c620545401c0700c0940420b05402c0050b000d000001400500300343d00290325022201c03040750400a554070780c082407140f80306100405500187c24000034100703103000a10316400d044400300705032a0401640c0d043d070400509103140404543c15040c02c0000b0961116a107500c00c004030740c200b00a600300101c44441c0c0d003030090400e04128040d0005130030070082e0144010302c50b40100c1141e4a036a602c0d0107415004 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 90716232 1250 90714982 90714997
    0x120010908120a0605130905120f040e09120403110d0212070914090a03050310030c030309030b150a030b0c090a03120e0d080301050103091104140103060b190e0406020405030f03 78
    0x42180200081e2200b41e070b13204110542e10005c040b01c0e280f5644181c46000792445102c140c4150140f42c0c981140070483c0d0000701511015169200d072264a846591040588020454042500540e12840c0411a401c3c2164181c0b544241c2481c024030012000c2807200807440c0c4002c1d0840032042a03a10030280020f1058200c44001c04240610507a911030300560721001d890621440c0e00002801000a0181c406154011082084a9102c55481d224000001000da0041e0042901c0345024014840a070300750300d0f4000b02c0165440c10010029000c01c000a40601c400307482c05803104c0c0030401c625000021112000c0e8000e290503815a16800e0036455948900c8801c4081181e07600c8071190f50902007400300ca8280c01080c0141542c0ca0b04e801980904141d0608680c21a80380740700c11515a50ba1042c16440c071107107007001c1c1c9250305514042045546002e2014400c0c45250303101e00302148034011103415135200111480d42600d076490100c1c080d01940d044140d25000303070b00451103100070003c0a84601d = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 90717482 1250 90716232 90716257
    0xb03150a0609030b040b0405010b0a0e0103051c050702100203090a03060f0c0809070303110c0904060b0907020309060708090a0e07020f19020108010e0709090519060e01050102030304020120010908 86
    0x2203940e80c800903501d880082c44001c0000444800113801305056046480d40315020f03400204041155100107080c6000680103803400506050050042c40700410002031900380a04045040541c6030b4800b414034080e04c94024410442a050318801d64801e04c00d4400c0c5280140c04488095182d260a4010f0084c21400b1410706103000c070010040c9102c0c5000c2806850300b8405080041d01f1518100c07600851050035880380c0c401d01c810041280c4640e211684102e0107420009003c0c1c00f00c0040104a0601a0400c17086500c14001c01a95603210b000b01c456203030b8041d60041d6202c3c480b0001c151442c1465100d800001d001b40c040284850f000b140c01403d1054038400d945d82941035094412048005400280c002a42880184801202000c0040e000503c609104081da0351300e620003400e03264201c800a0041d03000907005519420709010f058013803c030605c5511a13039030400300000d60f02d00005001034100702c0111048003100e01100e41420114984c00000d000024050900c914240e0050001081 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 90718732 1250 90717482 90717499
    0xf010e09013803031e0703051e09032e021605010603060204061407080a050903160602010b100201050114040506220218060703080106120b18060a06050f091302040b0315 74
    0x2c2614000c41181c0c0021281c152040b0381a4444402e4030340c40d00964000c90030300104100301555210f054001c4488030b07c406171016a6803089800b8541807140b1540188419408422603901506204c411482c0c01d014002d070051f01e90140c444108504841e40d03001600b1035182a0011080c8078450300280309179000c549a8a0740001d010298040511030800c001e00718520602041103414800c000518035000f0041c01c5414500707400f0f500c00020480ba900c1600940c0d035540c40c9d0526802d050b040c5070240781041c0000c2085601d00b120402c0313608103d6032f04511461761007000901c2552400b100860713600e01c05400340301c400c40d030082d460000e500c10508001d00b9030304125489010718141d000c0b1a0001e40c596120f91244e440d100040c1c4008030b05507820042c00751502105101900c80340901c0704c0100000c0c411841504103030381030049544590b080a020003c040003641d0703d00100130120350002401780d9820034003000700c286e200000d002c1c50f00b18042c0d1550000502c240e11941b81c0784a42c401e40116005c89 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 90719982 1250 90718732 90718841
    0xa150f0312020304230409141506010201140a0c090e0a020d0f0c020d08100b0a0c0b06041811010203130b0903010e010203061005090a05030706020a0311060f010e0901 73
    0xa070b481c0541d2150041202c0c179000c141c000700c04080c03207800c0300a002410102d2031488907621030321643e200980e0303a003955000c403502480094111040c550000001c1c0000c200b00401050100900c480003002d002a594442c000610b0040c40b8807604002000351100c044914140100b03a074022703510013207050010a01707281000000c0c081e6880744214503400d1790020041491103200c10f940c4984018100041c00a14440001d181c0203a84d00030400c0031a16501e840c2c1d03810741440c1c061000c04020b07216500a514083ca40b4101c1440303c1010343c2c8841e0083e420001800394580100d2852050f00c40c0d8002c2d242c208070000410101c804050141110304500030300000c8000401c1c2804c030300003110141c1d4040f00d50202260502d000d94000d01c44e00801400740741c10700752100c003c42d00d0040203900c00b10059110a03600c4c014141e00c950000c039540c002002801e03036401c000901c1e03510751106004000c02040c00c2d1010943d180001d500c10714468423070501c50f00b00724620410300811150301070004950003090700440c0 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 90721232 1250 90719982 90719987
    0xd020d051e07060503012601110c070e0c0a050c0c181510020c0103020903010204050306012d05091504090203010903050a0201060b03010b0d151d0a0c05070b060105030a150f0312 78
    0x107000d0b9010f69803a141140c0c42d001c01c80c0d12184116034240d04031210140098010f0000b8061845026106102c2a6030340440c0b41c01149090030b1070703004491196450b8207000c40c9840304011200d082c503a030328085445020680400d41007485410344182e000000000d02820410550703151440b4011440d131041c0c00381010010302110511043d52800140c002d0414800250300a90141c140c40c0c4014000500741511140401d1416000b0781100610341004d4454038400e00e50390142400e481e07a80d86080ca061444c0c1000302c1c6040f04040c09000395060260384500780b680701c55105140454006009000c0342d2103504001d845588111010750045d401d04c0e0000c034240d00010701701e9048600c501081e518104413076401d6402059030301881003116000034000501071000e6810b8110700044440440c0c46414420401022142040308080c1401014458000130440e6140420b6000d0400c1c2026640c0e03070fa80e068660001c000340b40001c1420044d1400c041000c0590441d032005883c0305140c8046030101c070500a = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 90722482 1250 90721232 90721243
    0x60109050f100305130b01090b2110022809030209090d0e090903070503040b03010603140403051204080f07051c0201050108030a050a09051302070b0a0501051305060d020d051e 77
    0x642e048002c582c1a5a6aa403190307011591140c001c00440d1748030b4030b055840d10000c19081e40000003460300e070300d010502842c2482c118540c1c0d916210010040000c82d50311070303460740c0e07480c43d0982c546a80443d614644043c04880e180303451801580303c03801040046409000010303603010590060940303400007411400c000a41105030442030311110340b8012000308000716840020251139103404144003c00002c0d03c1003000c0d10260001d0007442e602d0f981408001000c0b240825003610988981805020200744c00104581c2424106c0c014040b9558490074003100502c201c0c2c0e03130301c040c0690001d52003080c8032003c21a46090810410030104a0780c00c0c0d54200d081c1c580c02e00400700c0c03a40042290444450080c4d0040031142042d090603034a00d41d803407000500354140c1c406e14146164001070450b04114024101e240e010a107000f0811055041c030002c98941c14a4200701481d441d9102e001c90201d984420b1482c2965a000341079400d0f204030f51030800c0c0c59501300c488a040103540c80d96540700d1428003061 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 90723732 1250 90722482 90722509
    0x10c03061a0c0c0628080705030c2208010606080105030307020f0d0312050c2d03010918060207060e071205060a02070f020a03120906030e0706030b1801080606010905 73
    0x103100740802004060550150140060610035020b5503c2d0b151181d101410906403840c1001000c01c508000760000040e03000454010000303090300b08040719412078107a940288801d81e840f522800700c010340310341e05801c414005842d80e010001c00584840150428805e407406c07a07480c011241d0b40d407010700d0342c0c0e80901ca400070750100300d140207500d060502d003040059150181c6402c1030a1445203803210100c3e5400e5450304944040090030f060914607088100d4440007174078603c3d0618881141d007403082c6003c10300462000d03070b0305c03824070110035080c406880d2910394000504543c2c07181585403200042c55002c000200d40e005a600000d05515041c03030034060300d0707004805004560f40e480b0668000303600200b011201420741c0f02903200541c80d0281400d014510400b410841280000005080d441461340314808050401e851030360001000309540040f1101c0d800c0210b4070400507000103030308000c0000c603020742001810002421a40024585020300400c0e00c410300550b8599081c0405c000d090b8a = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 90724982 1250 90723732 90723749
    0xe0d05040b0f13030b01090603110607030804080904060f0909031b0309090203060d0b04060f0b0f030a120905100210060609060e0f040f02070503180d0308040615050d0b0702010c0306 80
    0x800a400b4605a0092014560002200744030a4480d40d6030005520203800c603080b10355072400140100b0219001c0c6001d825800c82d8002c2c14039407180d0b4000d11004c3c009000a10300b11010919000c1a152500008050500b4082c80c0703410035120151080141101f0809a00041481c40c40d060b139106030311030080340391782c140c0d9817010f400b401c00350310b1030195101030040c5800c01003140500002c18071340e0010310b0049115840c0812404070468502b0152416080540e1045140c40b0940a0316030f000610710b001d0031b83c04032540506041c0320a051303401c00f40c01e44c8160b400690b25842440d100d6408501c2e600c05410940c41005415100c44d4115904075441c052000800d103900080b16a600c0c010304103d4140b0801440480e82010542c40c281c01d0f41c00414003110a0760010920202d1018069464031082c00240d0b0040324071100c540340200b1103000603101400080d500d143d0b005d03100d03444582c00000342401522048800c0780700d28225081e52001c4034400015440d1030104c2c243c0d0751003401441c08890007003 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 90726232 1250 90724982 90724987
    0x90203070905012102180a0906110f0403030c0614010b030403111204092004090605040621020603091203010f060305280b030106050411040f080d0c1e050a060e0d05040b 74
    0x4a00f0659006060314166402148101800d4003002d00300c400a07c50889001c0c0424040c01c40e2505209803a454190000c1410061001c000021040000c0d542240c1c2c041c6891202086941000001040420304c1813110200072000030521810f044001e600441c480e984048010540d0200d031f13511080c110b040d48010080400c4100a042d0b01500b10302c1601d440f500c0400305c02d00d042c05003c0e05a5016500140829486d68010013043c0740c24490300c801010041c603e10018105404400040c10000030000c0c8681d5011012a009220402503008a98041c5051a5407035851705410410702c00d0a11400c00003031308100000355001041c000312070403160704414240086080304a01c0c80501400c828a030b8056690f000c00044964841c01400c070300c0c4034581c04440e610340c10302d2507041d48860079410010190b40403400ca50303040d540c00210b049541c1d4105081800c264402c42ca01d000a41108001400a00c524400d00341442040e41c0445a0900040c0c01c80307959210380d15041d92240554840d20010074400e = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 90727482 1250 90726232 90726269
    0x180a0b0103230601060905031005100911040906060e0a06020109050d1202090a030c030209070503041e03050906130602010b0114041a210406180f11120a03020109020307090501 77
    0x4882494082c42c42d900207001500007901020740b80002c2607000d54001900c1440c1000305003820f02c4040c0300600c01e84014411481c094481c100d60703c00078403540300082e076100580c507c2c20b400c200646019080902c41400442d0ba6500001c00034180c2802844c4108141c8000082c000d00502c20490125400070240000c00d00002c004d40c0c0745140e0000e2201c0c140d4081000d001c603503449030003440c09140308410b42c0f8052825401440581400240f442d02442020010710011074030345c240c07030400d0084000a1000c0e440491608554038010300c61010b82000b030202d00702d406a1071243c0d01c101645d0103035008000c0307880301100454030403002080e2480c0444080000740109031190301107900003491107440030700e070100300c0c0002c2d505604802030702c2041c00459014032081092a0283c201e4840b0210824541101d098448030382c1c9020000005120195003c035559494a80069102c80089014140c3d6014412818064042d210f517501c128480d000e01140420b501d111441410f040c1c031215030940001040d03 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 90728732 1250 90727482 90727493
    0x19080f060a031a19090b0906090f1911090a1d010605010c0605180307050d0e0108010506041503091b0e0610020a120203070501060303090e24060a09030503030f180a0b0103 75
    0x90251850302440482200d50031a4404d43c019403020500c0f910b4041320310310300580d195042050150100001b500288014004040d0000f444624042d201408203206401860111502c418254620350000910820880414210f6000c2072440100140411000c0c0c2e2040a240c02c0300c44a0040c1d82c04075124581100c04612203511407940004649c5001c4140072005c043c261a5400c44c080c1208c40e640002030862855901c0000c24802c4036007820109004d506101c0054018003d900403183c2c1e20b502442c0380d00d08140300360008070a454005090201492030000d05e440e5845060050900e14084d840100301c040c1040b2a00011504444c0c0c003506040d107807640d500104030000d640c2c0c0c401710704c424041503000c80d2080c403914004502c2034440c0d4540514004103100d48a01c000c10280700f2494100611840d98810700c22643c03030400442e001550780c144c055082e90f6800868101800750710000c001c001e045040c40c00018001c0842e092409014112000804e644040c0c14100030081074240004000280 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 90729982 1250 90728732 90728783
    0xe01060b0d0b0d0602040305030912011103040303050403020c2805030c0f0f030703050d030b04050112120806060f0c03030a061e060807030b030a0302011a030d090b0f19080f060a03 79
    0x4400900c3c0c50844401921814241e82064006550a4200164451042c034000c3c44151100003084001d00c0b1003104c941141d40360703010045c00982816141c02c0040d04261003400206034038180100030f00d04464540782000f1410011101c13100c0000d1409002103000d10b00000c1001c0c50641c02007159000356a00d03014029100110341a00b07416101d18440400000d1080c0710300c042e0301c82c3c4c6640000e0b0000e00d010800043d40c0060b4421464004140000004100d5401d10300c2e020136050309020aa5030ad44c040403403031030b1181d10025a8415030100d07500c0b4007a03202100450140a800509100407900c1d58a880070804244040982e200e4407100c040000d54002c1d03800a501c2075180c140001c400000030701080c2070551510b02140141d5450214007041844039001c50180301c4190001c0044019114024000b00840d00825400803c0410104444410001228181e9407ca02c2c501e583d0603044801401b419400d90300419041140c00004000d4105141c0840499400074070010314440102540000398 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 90731232 1250 90729982 90730001
    0x60702041404060911010e03031206210616080106021905010204091814010b0f12030c0109150f020f0315041b020f061e01061404090f0608010e01060b0d 67
    0x158a901400740310780400000544100e0154001080209581c0f4024408019815225040c060010b000314850344001040d56000d1440843c0030302961180800261726038052069031040111001d80d4910402000c1509800743d0211801c1c00e180e59203031101600d95031401d01a0000680c021420005910900c003103410760345000b01d00040c40c007601c82c10500d01341c40c4102c808005081d03001c0e220a0400c0f1a500c0d80490b40401c010080103036540000028107000d00b007400051041121295441e000c20b024000c6888511040008221030f008500c0c00907100c524505420707240e0340c42c180307030115107090600031106018071008080740b441d0303142442000d6810400038582d03085581c5030325481803003051005641c00f540d0250018100744007418046890301c5801049180000703881da54262002d004600c480f410756210703007001045001c151200d0312050144d03a0002c0c40a50800d001c01d44032426035400701003034803c008000e001340c05103940180e0986520b071050066505080040c2141c101c00c1c0c0d400480c00 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 90732482 1250 90731232 90731239
    0x206010e07081f0801021602010e0901180902120d0e31052203050301050321040b0a02160e18010911010f1101091b270902120a030e01020f07080c060702 67
    0x34682c0b5032a1311422a040819480341c421100c80510042d0340c2c022103840041300c4200c454500039810a409109405d10940c2d60071061603c4a502c3e404555030101401480102c44049904600030040002c0020308020300541c02500752003c03816000d08000b041d2100700f0351078010f61080d0514040340600400006010080c1c1d0400e6107520618002224114501c0d2130007640c0e15901e03541440c08040c07c0504164030a036081700c41e81d103142030110f0043c00382c40498400702407146d00c0d1002924180d0030a840c4201108004a400e040070408491002d0300b07034050710a0140366142882003898007802c030391030a00045c0034143c9130b41d03054501703601c2900100100d03440c80c030b408210001c0c2c03004050f00b074441c2e22a081362030070034040000740148504020070000700111091600ca00f040070168100d00001503103c1082140c940656109546030764014900c503140c0401210100c011500b0003c2c02000010015030050060405910b104400002c2c000142c401800107404c20403c10010008954800d141c200c1c2c1 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 90733732 1250 90732482 90732541
    0x30c0203030310030303060f050a0509060a0302060d1a010e0603161e02071401031b0c020105090d0b06030607020304350f070305010c051305042a030c0206010e0708 72
    0x180c40c240060b43c000c04a90001444041c01e40c40c000e4190b6010b90400e06040d0f01804042080c3d54505000300b0864105850075403807078544030080740c44522640c00207900f001001490f411640c00941c0100d42030b0341030300c03c40e030080c0b1000310044400311409940f0540c0302c5410710100364503030743d0000d071018000f0490500c0c00120100240c0c04084210081c0001c02680002200f04001070000407da2014007007460100120385042841c1082401c0654a0f034040004601407481164042c004840c00d902000302000150800340ca80501c9081e8216107142c00780c042d40380801c4010340008142d4090794000c002c00091301d084070794040001d4a00049a5101e0307403444400b09002d80f070902c9161102c0e502c1001910a00e411410b1603420b42e4a58414041008010404c5c0292048065040320540344119008684003280b1184280300c1480c2d040d59005030107005a00d202829015800308005141075000d072580360380d0303641030711050500469020011898810000300c804c0ca40d803010b40b200c107503101080c00 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 90734982 1250 90733732 90733757
    0x30c1e030e0615121c05030702010603020a030b0a1505030c060703210b030d02030711060a020115060810080f03070201050705030c0601030f0311031606110f031f17061303 75
    0x2450b240050350075a038a030f4074015020800b820b0110715450160749500042c11880520300c500b08410350100140c401304040440410321581c400e402c510011500213140d00b1006031203041000700d8a2094801d61901c0c1d1403c0c5c0d100113098052040d00d001c07a00d0040180417000c40000500840c1e501040c011010040c0b11900d079a1200c49058200030401d41c4641c000a440466800307051901c000c0d02c10003070a40d0301c203009402c0026001c1c1c41044269000383c5066480701d801501c140c1c05000806003101c2a4654800b01188203607202450a1141700c00d44400300080b55207018503601d850341081e105c20f05400401415015501640c001c1c880e540c45401242d160415041d2086e00b007640a0b00304680400a4202c4601496401208641c0710051003024629106200350160807904581760001d00346903d410018600c0032604040d41d03d0740d901c20b001c5079964075164010b40400307600d09180d501002504240030550541082840c107140d44444001d000d03c1e02e0324607425010303050349503040381080000b200301c4 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 90736232 1250 90734982 90735011
    0x616121103040602040602060f04150903090329161209020604031a090111030f07081f060c0501150f0b0913110901020c03061b0d06050a0f03050d030c1e03 68
    0xd601c224040c3c840185c071a4141407009080c000050320000c0c10300f50b0395040c48082000d8200701c5100e030b0760380440000d580340d0a2500751580400b0740d101078451150722050882c80d411141420b1442410400c103c6010380d1051800d070149a08140305400049001044001c00c60003580500c4506000404031420983d80b80d40d0007060200020104c1181d0000b1010701240e03074130034056500c0c0412807c15480c15484d002404280c19040100040108a00000071451340002d21800002c542805c01712101e101e5110171018107112000601120349601e00f940d0742080e0682008501c00365a801328564160a103010b540c041c00340c00c15924180c1c08030b850102a030304a0020310440c81603408400006031981e440400190401c108402824044d0300032034108124902000341c0104000c00c0c440040d600d80d8140c0306100f008280700e40001d03410003920a00882d0800e101944c0204a92081c02210441e114140c0c1c00c90a50b14640c8141c0003250085010100303a0480c500680c07000c1c6050310f0001030881040510 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 90737482 1250 90736232 90736237
    0xd1107030606081b1813030e12070302011115070f0e0306071d0301060f1a040509071e03110702010c03050d090c0819020d0305030601020f07030804060e0306161211 72
    0x80b42c1e240c0c0c00f140f060404204010140a40b4842c00c841e0103e00290800c10940c1c40c400080880c901c170303111b0105500030140121040502d0f1000980445007071420401410b95882d4240070681c0800c0358881e00c3c10900b4030000d1813200104042c0d0380900a40ca40103019280220740045441c14006040310f03001700d0313403410406c0c640702d00340303c1d561006000c140f074188081644000301194001e0741412001e000002c910300700182242c40015009443c081a1b95182e0001c1c011a00001e40c00660306040c8400c0590141d01c50035030024412800710503c065900c02e4044400e000240710460702c09001031000b660013018112441c034000c0c14480d10b0700c021074548801311040920210340184a40310240800841003003040c0e010006c802100066503c075400145020441c0c0310010100480040010300c03d074400e2182e0102400741000311170496459151100c4c0b581c10a0040310001600d0a1407030314240b600150081c02000040a104603d1080000807034842000328040701550352a80714a00950002c82c00 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 90738732 1250 90737482 90737489
    0x706051009110a0905060a05070c0308120906010e040f23010c1803050604021e030604060902011d011e0311041d09030306090a020705070e13020a05060c0d1107030606 73
    0x40c096a041c10042510100e86061001004150b0184010a14181c00c08204002c2d2076080701c030036480352040d100484032482414402001614a40000010050703000040d10a02960a9290419658402d510303030303840710244181902810088007080101704a20740a200c40b41c0501d540514081c001002d88442c02c1d820000c0c201240e640d6190081a6039000540b01c205c0010401e80c85511855034440c150303200c5020b0000f078480c4001e054001440e1030380000504146c507018058174111b160600f440e20042103006010b0703010400220001c0340ea001c2d0390055408126050f1150042d544c00143c0b081c11981d030140a0b00145662544031070602100d84014100030040c410a16034680f0b0009141208080003a00400b070661017407042c448030b80e941004155200506580040c0c50300039500700b4925000a56121546011a00c3c1c02d102c00c0c082e850310300c2c101240c025207010b50500d0f910300070310001e48590f400c01c02141d006401130701110341c413842009883c030310388204854903980c60b600c840b01162442e50 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 90739982 1250 90738732 90738751
    0x40b0d1811010215010f17010209030a030513120b0406090609051921050f07030903020a0e041a06011407320d0f0f0e0105121005010207240f05070605 66
    0x140704401580c0c1040103000260010224240c0f0b5450100f800d0030f001c12501840b00c0030b402140103801038100960580d0210394004045820310002820040e040e640320020b00821149000000f0900c003464094580f40540c3c40440f01000759900e48442000302034103041107540350303140d04d000000b0030410082c2c050f00c852881c4420441d0300c21031422480040c00003a10070042c1d00883c2400d170311030f0381080940c0c010303d65640b801a40c0c1c10051804070341d40c00c03554000942c4148000808901e201c1c0c8210294411486403281d6034802009203840243c442e01280c002e40001e0781000c0d161002440c1c078000d401140d2003128100d10311044000104808a415415000e2030007610405150380ca104103c0c21b00e020341d4500f0071001710081804001c2c150100900b0440c140040381c0d1400701903904c0742045400c11450160591642c0c1000e088500c0d110107940300307050040c4514040031442404000301c028982e850210000410055800140c0f031a030744014542c818440f0074040000840d030036000e520310810b00e15 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 90741232 1250 90739982 90740003
    0xb090106060f02010603050a020f061c050a2414060708070b06010f1d04090804050418060b01050a0504030f0201020304030b0403080604110a0c0b0907080109030e090601030b0303040b0d18 82
    0x45008040c4a41180346000f16070400504101149010544022194059032802c10103040304001c80c009101c0c41c0b507444421030812240501c6615607038020b9002d524511401c1c403420191ba00010040d120110b040a002c140458040110584a4030b1803115642c0c0075007803506064407a150264580c001c020142d501010040c04c01c5842d60f408941c0301c002c070b0740c1414901c520345260030a0041983c041e8000c1e5020310740e2120010306108001098070001c080c0104184440e600250b409070000e00d81490890301f8030700f024101c01103507001d803054a0012800c0d944040c101131031a1a240c030b5880d01c40074140e0550208000100c082440301389100d11413030090700d0f82c0b80b05041c008144021100d00d0b401e0041d02e13190071b201c00c1c4a00c82d03105000c030303000356001001e0501503250307000807030b041050b1035002100c5907203040072050806412001e0b0848094080310101355550302c6a006400f0744119104059040c0c00800c0203110a0382240d0181180c0c0344500030000c0c20051444010114402402c01500c00308040c = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 90742482 1250 90741232 90741239
    0x50907080d1d150403080906041a120c0408030d09060f0606111005060d110136050406030203070308030c043f02030c1002100c080105010807030b090a0f02070b090106 73
    0x300b84110000d01079500300b490180310003184569001d0f0380401402c031a8006002241d6507101000d450142102e1410000c04201e02c91017003640e54040423a5087c00c55140d0005410200b08034255011100c414010b50300c1c0c0080809948020070120b502240d50540e2407602e0b003108003441c481c85c0042c1105032191410758485000310b81c540000145803081d280c1c00d03c0b003000001d40320710301e520100c00c1d88141041412a11b0f4001030314280c07007030800c0300800f5100c88010382003021980605035080d90380d4000108040d80300c0c010320060328850300000c6d42540c405041000024002d00045922850500c00c103400d0035200c1003103011442c0042c529054124080880c51303410000c0790400a0700c8440e00d42020b900650540c082621440310740900780c4680710034980c41c0409402031110300200c1181040030000d4030380500d405070840030207018030380c001241c050021310702174040d02c070f2071140c2d030750041c18071066969460b10140a00701c0800c07001c0c0460340911844c0001180c14240c44e01603c3c0040012400340e09 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 90743732 1250 90742482 90742517
    0x140f0307090816030312021c020d0c02211c050103080406031803080c0a09051804060b06070507090513141c0512010302090604020f0403110307051002060a050907080d 73
    0x360071042181e088441240d000300400e03003c05049a41c9420590031004c40444403400900882c84070b502440b210740f4101d101d41c6281d6000308a008405c079000c111280c0140412680c41c2d14801b20011151800c40c12081316a0726080600080c0691044041c41809500d01c12030540d1820380c000c85040f07401250501100350180510700d0842107040b20740c0e0030101d440d14010308000014000201e070410008250102070301c901e07034800c0030b04000790828078070850000c0c14020f162001c413400e44d031103445d085901d0407a190640403125490b40100050219508141c0017000405000d44400c03480c90b038031401c4100080f0080017140c882260000504185c4003800040055006890004030801c001004010304030f010304503985040d00d8059904180715501c28011800921030b500c4070006481c40807600000704104110b4138a401902502030344e02d2517584105100c000b1250b01d00540241c0c20060000c1d40c018000d902107688a80060115484207594442c10350414500d45e026000040d07072104912210718 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 90744982 1250 90743732 90743747
    0x608010e0a0c0e040e0705030a0b0a1a060a050d06050901080105090106060801060219020303041a07060f0213060e010212030c0c1c0507030f0c05061009050f1b0703140f0307 76
    0x9200d07250a00004040c20001803560020f0489180700ba40d841050f00310004080100c84003410000c3c04940304103503682003003803026000301c03111980d2070704201320754607074858640001d44d980b8006000d05041203900e10007910290424581c0d460381c1c87d910040068113568841c42d0a00809485000159a007005c5400c5406e40e0f060390803110500c5103e00042011550015038411000c56444405081855900c00241540b060b5030101001d400c000c10207054017a4150020a500b078403a603820012074001303a20304c80c01e0703024425414600d0b0355640e100700012405207801ca602e146052042c1d42002e1030080d2001e106070070541d050a00144003041440a031001000b003030355520545402c02c141c422560000074046c1c032400800a040007118414080894000c4000d4a509a800400d850242c500403100f0203000000f8404c0315641802d01c004510224442401240905c0d1700c0c656203a140758440c8040d1400d980100c03c200c0421074411015020064032101807c001c2072081c4d202d690300c0c18490001441038 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 90746232 1250 90744982 90744991
    0x7150c020606030106050310110c0106030305040806070e0904062307030f0606050f03011712040803030a0c110705010e010c0b01120b07211a090405060132060708070c0608010e 77
    0x82e803405d141171103a0307640001c0890004030181c00215041c44d085030002018000d04900400540c00c1c00f034003004054101c0040d20550b07400a08550040e40c0c0e695007100d84c0000008100d401096041c081808589103400c40c000c0c0120152101c140141d801c20100d02d02001210002d0000341e440c80c0c0c40034801c00600400c0024900b40c6046e81c10300f01002800000d500c03040c4a000e10003000c42002c0f110074034051121801001040f51340130b464582d038041031a141d81c8120b628a100c41e00d407008c071060850281103040541d04001e4020600303141450300540b00b900404205a05108900c116030002070130154850740600044488080309005514040c0711000016040c84284404541c0340c3c804030010100d108081a6525000700c1c2c1540341404188550030986c420b40d40003841041001f090080000d50b0314100c44181d10001c41c09600b840398104102d4820742c00c02c081c0314645806182d60b10f0500301514000b40910a45031402100707944400030070b01700d58800030100d40c00300e0040243e100a8084140d00 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 90747482 1250 90746232 90746239
    0x306070201110d0e16090e10091110020106050d0807140309010206240a06030203091605012c190303020c0409110d0507090e0a20010806010c05010207150c020606 71
    0x2144281c030054031050044000746140380b584d03102c6503415088100302e20982080301402c004e40c0b1686403820321307011705400005180903100f08600d08401e10010320070760f0071154120300c0e4030440a5040b01000f80300385404505004540d294000400c40d55140e44508001c9171041c464669102200e282100c0405964030400358950420b010701c004903600400da40c2e80c881b01e50744e4550300d80345901010a0a030075010300d40d560041924040842d035540c1560003103010710518000c4903440103a414414142c03202500442c0d00286a14240f20498000710020100700c41c1600040f22a4904801c0450706510801c10540f039020740303401041091503010301035140301840541d8144111030441d00d03400e84920b42ea8054901410035079803131405000052040750080e04440c00d083c00301e00032641907240d81e03842000301a100d00a0004548101465015680c2501101030312147c0441e91020300554521009078400c2c0c0b03495400f0000100011003180d880001c2c4502c0400c0043c400321610f100a20b860401841c2501 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 90748732 1250 90747482 90747491
    0x121b1801030f020306010503060d0804080a0b01170d0f1d03010e03030402011206080604080d090203060708070f090e01050d05070b03090d0e0301090f060f02070c03050d020f06010609031101141303020306070201 92
    0x1700da60300a0490741e000005541c641301074440d0340351542040c420750b031200e513071402109114410060585140390480d0f028454130324100140188444e04c401c2900000da005c20403010401031003a0050f2513240308135101e200303150840300340100420309550f10100303800101d803c0081007000715a08925145080b00901401300401c074200301400d03640e0040584050240a0045000d01055000d5003000c1d0f055030340942035071101c0c20100805070401c0c030b0948903200850250380d8042c1079984954001030846d01001e00c18000741e46030805105202e1040042a0b81ca030094100103d20306080d18025402008803200401d0300206103200144842c1c82140142c0c0301e031741001402d8010030070303a481103542e07150000800a100034100c40440c00922030980010045000240c00206204010803007220201c3c09409440c1103125880d805521500240110070101d03098490900104100040800c262103041c18148000075840141d2521a00301030714240c50005c0e245000d00843c00e0600403e50080394500080c0b2 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 90749982 1250 90748732 90748741
    0x1f06060219030504030b1504020d090303050c0703050712090b04060509190503060a0519060602030c01051305060f0a02040905010b0c070602070b090d02040906020a020a06050f0408121b1801030f0203 87
    0x20000e104510002d0501886e00300440c071020000418404203682c0103004543d503c410f1040c810242420503000d801280c90701c40083c200140c01411500301a9060352a0b928102543e80d44c5502e0003448141e500c2000040d84c0040b03a00e00c3c1e00e100401c0500142c0c0c94141e113400b860b074100b01114804258038201411541c1042103903480020f90345811451045010810750740c2e00e009480154408502c51080604003071000030415004001401d07081d5130000280040d58405501ca803082c0c01c200c20040c11540104000f41e05403501c0b04110307401040c0c0c0480503140c5030740d0740a8002541d00a8101d40e15101002402008800701080014002e00450000d00380e0b42c0d2615140340710501a03420560301589500505500710b50750b40e032010005683c0410111b40310303001c00400075920f2080350801c0380ca80b8a0440420300140400c03a200740b0981d8000320301c91070113000041c1c0c4a071380384d4040c0c60341403400c804103134244442c03030600301404100c071615041588000b074541c001000d9074003411420a4a034410420310 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 90751232 1250 90749982 90749987
    0x40509070812090108070e010e03031b071e050105030c070f060507020609060103030905101205040507050915030d0e120106030308190209090103030c0213090b0f06040c0c11031f0606021903 83
    0x151b030152641c05e101504d55013003001a103101b40741ca0341c0d40da8503000003d01d2910300f03101d1380d9007880700868600803200b08a403500446807003812280070b2220702d502010303401c004c1c541c410710055a0180c6080c400a0500d03540d2b540b50001c40b03041601c1195541d844004000600c1d0381000403981c828802d0b00109200c0d45949c80103001101203000f007c0c0901c05072141546a60302900300004c1c41c1c1ca80d01c0040001d4500b60903c80d844400340c2c00307200e00c179040e0140801d4260200b07120034501503c00801070404600c480c0f41c140c8110641d02e019a4101140c20031108842c0d07003c0c0b141d00c00550103506e80c030203680b4001a00900d8030301340409007140d691042c00764a200f0b488803803180741960ba03d03081190050001c3d00015420595003038080f4201802c200f828400c0002d028203842c0100c01480c0c410b40c15488200400c0141c814034500341000503440104040410319030307080c0968010b8041c0036500040391885501d03140100e501c07054129507444220401150f42c0c1040a640c9405038003041500c3d2a00e5903900 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 90752482 1250 90751232 90751247
    0x402010c0804091406100e09100314010c02011b02030405060717070f060510031e020105071b060905010c0203030d090c09020a020115060207030210080403050412060f0b04050c25020405090708120901 87
    0x46002c8c108990019600c004440c20000c099604200740c260314109410001e400780a404144070015400d1003400040e648004d6a88803913044580c000c2c50501d4103000a0041d41e411000b015074441141d81a101c11110f250340050614034090034030142c1d03051490500600340c60001d40780d803c4405e101601040892800180d0328100b860300e0070009102c1a0a0004980b10b007c0c0c0070014142050030000140c040c40c640901c2070854940351a2000541e5551006440d400d2340c19202a405800800c400b1140a83c9540400402480f8105064001e0b4031071101504a8100031041310250b0b40d101c2e003442d9003a9413090074500603c5644020072543d03007035602260340b40c104800b041c01442664400700d070416004030166000b80c0580c070041c2d00d40c2080c03801e204016211182107020300c2481c103014400310b8146405400d00c2039514250061814014179106085580010b51000c500c0328a529650b005035a00d0003558010380700c00e00182100b82c2004066814244a11401c0a0b03511303003042201c1c01a60000b64 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 90753732 1250 90752482 90752507
    0x519030b0903070b010e070f0206220f08030a0b190812030a020d11070209090106060203031302040905030301030807020307060306081002031f030b1f0803040e0402010c080409140610 80
    0x4031411103880d80548149103000e840e10090001152100100d280803040c80714034030034000c030355503142181c8010a050362106001e0320b41c940900c0400703000200703003004484c5000849201d000c010707501da601c076160211150000c2e0b0303a50032500d8651802d001140b80132494000301505003603407201d2141c82d0203040c0790380d0348031004100440140400022070003241d40d415250303217180460041c030080c2ca1183c5020080c0c0c0c4030520803407040c120b0b0340204805007414401d0900703507802074000b10b14680f50f0002d0140306400703038001264010b442e220b01e00006603051002c0e43c0254854800f003038640110f8030426041c012150814004c0514000341000101000920440b5000500740d0069480e01c4144800c20f82c124410011540b88070400000810004d1100708188a018040311118102c10742100751150600684500251980700780801c3c4035800d0710341d41712500030744141800321a0310000d50714414680c0242c0d0042c4c030300c9541c52402c0a4980c22601429034850300854108010004545001c0c08500c020722 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 90754982 1250 90753732 90753743
    0x30a0b0303182b0c0302010f02060f010308090d1a06100c1104050a090b04030810080c06040b210403020c090705030403120506040b040e1b060301030b01030308130822051903 76
    0x500710b4481c104400c41608004143c0580c8001c14001400c202c0314000551000301c1c0001c0b442518030034281e20200d01340d40500c0d61b40390b91214903482c2d0b46a12201d90440501a540501c0071100400050021701e482d2441030a45d004410980c5045020485d4554201c0c0e0403500b8000200511400135103083e40e03000000900b128002004d8640700001001000651f100600b1185c1c1902804241034202c400c00e4455440068003802040d1682d031502c2d103d030200d04081d600258184414042c4840c2100a00142c0c84c642418103c50042d0142075a0f001c0300988082e00980c01c2003d45e03074094140414066408030305824240c2c48c5060990b40206403400c40b000e03617101d155640c0c001c28a103a13140c0e0050040844002c0040c0400d060400340c0070303212a04100d92682c2175041401703c0c0b0032814504140c9040b260000742600d42d1768a90f40303080e10607080040c824540150803080c108000340c0014040c24040c0880c541440c210703200301560f86503014507604601e1045401004048180411810030b5040e00c0e03114 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 90756232 1250 90754982 90754999
    0xf07030201051914010e1306050406050a051602100f0219200c0109090906060504060b0408010501150c140a0b010f0e0603070f060302090607060e0325081626030a0b030318 75
    0x10881e261f100030720b180024255800c05052106200154000501404212404100e203444030141002542a239080301c0300943c0188880000010bc80d9001c0a40e011058101510748110202d0070b821980041d01e5003008220321101011111081e90300e01b0182451a00081440b08030790030010300380c841d03503214200c6101d032101031010070401c042d0032200c020300c0c0141041c46070b07e491715181904c94020340541040c80d03291000000300400703a41141c0108a12a45840c0c048050716111107001c00d0042c0003006072485084013070300c00100d8051400e402000030710020540d290902e449000c502c000900389600c1ba5110304030030b0111030071001c0e190081f6261810011f96815080c1c0219101e4010b080002d0016407400d03d9044600a0200040081402031601d00c840e15001446543c240c01c20143c1c0a4a01c0c40180444451403840200005409008803900d00120004404c41d01440c5044003079461072420100500c40514030902640401d4501100650308024242024440400080300340610803ca007 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 90757482 1250 90756232 90756241
    0x3090b0906060f130f0606030c020f070e070302031f03030f120e07170c060301030c080d09181d030304060b091506070b0601200105040c06090b070201080406020f07030201051914010e 80
    0x403a8003044a40d2090300f400d06c181a918500a40142040943c20000d0300407a03006407003c001c0880d508040d24816110000292500101100250001046010307003004094500140c0d5481c1c8015000951103079840480360500c420300204035070481d43d281c1c0403190500d0b005040d040b00c0425400280c546c0c00ca1a81120fa0741c1c8103075245041c2c0014029a00703d02e0000010092203144803e400c191400841180c00240c00c00b0b034200d49400103031160a5103101c80c0721101e00d41c3c0b0601d400000c03c0d20258501104100c4143c00044d04550003920b0403908540d40d80115003c904001c1d0f8800d500444c3e454560048403203d10108001e4400c162000b03004281420028070140e00030b5100307801d40306402050040c2c511055038501d00078801641d064459890107400000d00341c0c800d0501d0030035a0030150030503080195650054880c0d20001c0c000315942502403044602c0000c513039000d000031500030381c0003007254140145d40b4124088260806822075050000814441c80030a0126044607039500c04015655107 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 90758732 1250 90757482 90757519
    0x2091e01120908070b010f08030d020a020109060f0b10030b010f030b0a03050a0c080c030a0309030b06032104050405010e041a090309060a0905040b010c030f0f0c020303070303090b0906060f 83
    0x1195401c464916140101c2d01040c020400c01070040648640380101c2680d881e038034134810035101482070a505920800081415030741c9134014040d42a0980000714000f00540c4e181416200d007982c0000350580d41d10344103842803a1141012402c0c0c1d402d03040c10031002902000091404405605074000d144d2512001350036615100080c0f8010340e0000c00752206c0c0134980c41d240405020a00c542e01c4184a900000b00052502051a0017026815200d0103c124510b035503080c901a00185003507818010507070011196141488600007011000c052155214200801c00040700d8040c0c02008031600e2000c100710001d6003481c82c41c0981c01851200b0901381d961404443d2841c85100d605640100d004100400501d404c005600245c9000301c0d0180321300080c00c40112008819102c0280010705c14440032030115000c2c082c0da00e65800686000410b80c5c2c51600828503580c000f00c421000a035844c03012205014000380c1c0c084e00007450030050400d41c142000003071401ea0a1310f440503c9040711000b42035101c0c2 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 90759982 1250 90758732 90758747
    0x3020f0402130b0406080709081920041a01030c0509130908040305120306011e12150305030c060f10080a1205090315060a05010203070503040902070305130b041802091e01 75
    0x31403030f0a641c1d03032a0b4035000d009051210079200c20002c207001e40004124881c010414508200d00300640300d040c00400d450340000e810109a10b0303590040101b51604681e111070160000c4078410441986900e44d80000040465a05c44c80c10401c120040c0624505c0c2d030f682d0407005090808412020550780d40c0c03818440c071184071300c0e07000810754070400440c034000b0354164001c4c40c40350000741c030b07014082e010f039542407200c0550a03c3c1c1000042c4e0421000c0702d402c182c0b61f10400182000e802c5024041c0c1d12681c85514543c021902e0103400c0d03010900704001040c5c10080300740d02200030480b00d503050741380041c11903440b5010781d402004214100c1928071443d10a009031071388214010102ca200180702d5141020800040d6031842c0101d003202c10214141d4000800c5030101c544c808000c514180c034094000001b50009102203003048020829000480084006040074108101d2001e03a5a0b2030f120303144a03444908811041e40c940140040d81e0b5a0391801c00c40c40365a41280742929600c0d4880e8012903401 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 90761232 1250 90759982 90759989
    0x209060f0d14010905010e040b04060b0a06050d05070906020d030b130513051e0a06090206090a06050a02210d020a0c05030301090e0c0414010b30041b03020f040213 72
    0x21035000c210116400625000010039000c20707102c40c034440e6200d404c42810380e1824060030b0900b07080500440c00249a081800c2d9000f07004440c00144a079500c4001122080300754000d000041c0c1c00304041c40d8040e035501c01c0d15080b018a0900808540c9000c6019403100e0543c4007410900d5625408240c0c25102c0030025445425200170401091401c0c0c9420000303000048029101c0b8401c1c610b00d49540190340c4490a065070745040108917803c015590003020f0039181904a0704600309000b80031a0780c948201729005440c4944901f038031111440ca000b4a42981403d0722200c015056080d8520040010215080410180c00c096500c00264609546034510144010003078440040002000b8400354003101c4c400e03443d4015100d511070b4403410082034510007442c810101b40d116004204003054000201051556088a01c151102100000c445202668911000c40020004210411044100000e4210381c110b040402075425074010465000708980528050b40c0c0c00100c0f0f8101070401c18145004 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 90762482 1250 90761232 90761257
    0xa0828060e10020a0f0c080414031009050601060f020c10030e01150305011a040203010509150d12090302090108160510031e0603061d0a030f030209090708060a2304020906 75
    0x1503580b030001e200950041154500040ca1031003010f80461040300300c20741d800d411500e040d0500307041079456900a96a10501580351103071040aa400300d1071800780325070075402480a04542e6141c010050724608610401c0c8086401000d9041034907541e8041d0907a030f10440b8600024412090751005004240c00c610309909a0070b1761400104001054100d0311401d030a454028803000752145c01e01082e03000038011983c0c042a80c1c1e00040740094004240c01ea910802000800340c40d0403903d900b540707405109450170000715403d1085c4158100000c40500400540d4018580700103000400c50940301c3d00d00400344120100400034030342512940000c80002c01c1010241c1e40d203c002c10310480204414030044030b9a030304142c104202c00c00600f0340e500c229540c810141108280c0c170341e0f003211050418400b5400385942404007440d0364490030a0248078204a448850080c1003507000c00c014003040c0d80c07246400f00300403045a0300d44801d014400000000980340507807140060030014445001d1051103200 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 90763732 1250 90762482 90762493
    0x30604091a19090302070b0a021501030b09070b0304020d0f0201020f030a051201050a1a090402040902030403050d0e01021e1b06100f0b0f0f0304060905010f09020a0828060e 76
    0x7100c44101c1490003005002c01510b4003034820202d030015980800c0d000360150b00103600820558044c440103000a0302244199007c40d200301822058610003030300181d0b0301e6903440e82000307144501040484080d20014500e41d0561420fa80050018160860000c190b0b1020625440469000300004403445501006698a600c3e07454001002900190117002c20084020000207182c1009a0f0900584111016840a00b01040d02c01006588030385d001a400c180c0c208400248130560b4400ba5010f5071080e55850b41d998a10201942507a04901d032441c044e034810404d40f500c811808002100030240510003c4c1c0740c2c07a1440f00710204680121405030140a407808000715501440304982c02e848603001d042e103606865000032225030283d4000850306400402c2101d4020b46201c0296034890710600300403507010040d603a441c5c2941c02d204041660a5191120321003103160540d1010041c0030100c008102c1510050f0518441400009025200070401c1032044180304150300400031000c0054101e40 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 90764982 1250 90763732 90763763
    0x6090a08030a110c0d0309290406030902011d06090f0f03030403050a050607080c040b07050c040e01060501120b030d0503061f09030308150907050d0e371703060409 72
    0x409081c40000da000482c041c502a560082c0741c210401715800d43c2540e99060072a082c0340b582c2c400045d418105500102241d1407130b407802d4a951b0003c0c40a05020303134001c0b901d1240c510014102482c0d00c40442d00b4469018040f01d016122001a00c5c90000c0c112030b00000e41e05070401203140100a404042d4040c00b00040220070320000258800000e44a1000c840540d85ea0100c200d650f0f10095400340b4401d1401c22040090035200300290130202d0180c0151080d80c0d01d08000102150400f403036510349c903510340d082041290381083d02d095003035013920024401900040000f81d11140441102814852701202050868546218512049000000100c1c60342c464180180280c170031407000300c0000720b1610005040041e0b00c29a00c18001009d00001400d441b122001e60302c81d0001042c1ea64010b9641760341d42c941d01000c100b04403210480114408022240003c0341c21859454510000d40c6030751740142c10700081501e0112030100b1103c030b034031a840351540310003e00500082a405084d00f03c0494151 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 90766232 1250 90764982 90764987
    0x31808031504020c1e190f0212101505040204030302210702130204150e21030c07060c060b0303040803030c03060303070210030b030601081209090405010b0a060f0201060506040f0506090a08030a 85
    0xc80c3d0824900170704e4001250501251030f5114150140c00910300c1001d42203100203010443c807807029600c0103108002903c040d0b81418076181288820200058039006031001c039001c070b807602c0e9004d420207030303410b51600e411904c01940d100d01c00000a00e10860b0b4880307000038001d101d070540f0b440e542d004160341000e0106c6000c10003e5041401840100e00403040000202801425040b40a0b00040c08017407103280000c40e510341138070f00c0c400c0c80c070003034041006010301e014000e03c00d0b0800b030300c81502e428001c58132505016040702c004e01c6800d4000e074406c0200f8854400000306981e80a1a603452141d40c80c1c0d28070001c24114003840302d000b90002459810039408030380541103042c0040b01a012a11540c0e69100e0355652981c250b27862114480d010492054503003812015150300a0080002241004084000c600008410781c40715000030392460309034007004e03420b0207000300501085644030300340750a1029007600a0000d21400348201000501040b150b203444038103100030805001502e03290440004003 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 90767482 1250 90766232 90766243
    0xe0c0c01110304120813060506031f0e070509040503030c0c0c03070303030209040516050306010c060605031b010807030501050913031101090b0105030705041b0f09030c03030f080601031808031504020c 88
    0x121032420011003500d00c4036114a85d001e01c5000c400c411442c002d4a01e8036035500415000c2c0c4100d806004880c10007040076085281b580c4100c500740030004401d241041300ccc0342081d903030342c01461142e40808140070105000105403038003c0c01c910040c0c0c1da00c2c414000b0b80c500d803a80c034190740c50300340c0a500c5002003131640550140800010648042c01a035130b840300e010502030169070340d4401081d020300c0801c1d4254412065480d10610521001544e141c55a00007403a0148011000c47c0c0500c0f01c8021400d81d50b0f0111095030802c5450400388459411300e80010380c400d900410b06603c09421242c4001858842d4000c541c4060b14400208000d84c65400c00ba03201810900070345001c0e1144110008480c00c0ca841814550071500d007171400707006594202224a000c95245440c10003d010070080f010030b0703a030011000110302c651508200c009402c580a0300c403200c0140218140b500c0d00343c5000c50341d500d12103038502e0b4030380c010480c5580e41d0741c0c982045240501c14003229042031010501c2c030758500d0700041 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 90768732 1250 90767482 90767491
    0x1030605070f0e030a11011206030c03120503040c141305100906140108010504050603120c0609160605070605070219050a02030c0406060504170a06141f0f0e0c0c011103 74
    0x200c410304140c11050540f01d242c0e001c04165010780c0611083c0c070110318800007a5010740d00501d400d1240255803484582540c001da0001c0d580c00c400240f0400400242003020a4015118100709055140a480d60410740703185204d032140f465a035851511071541d40110400e42410100410041070905003c00380c20480756000e0420000d1038030f00040f602c01004405280d039010141d40380c132456803c20045c00041c240c080c0c0703819098070441c180d06442c0d241e074030082d0803000480c034001c01407440c1001202e4a440212503c0700d101d0b4151020500285a100e01120421902301c000400d84d615810380484c41c04a02c40880e0743d02c07959031112401007084c01300300410b01600031011580c03070a40b0354007044200c40c481d208420200384100700c100a1a0320000c101d005085008080d514070901546443c1e0544072003100c0407a180200104100c94943e0300041031200384c07040002002110304048140701c100c2651700801341e040402d20300180f440028403040b41d40d9810160000c1c005e18036202c507521103a800c20b54 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 90769982 1250 90768732 90768737
    0x1060f020d030204080309041e110706050f06060301050409050c101709030c0619060306051003021905030303060f0a03020607031e02030a14030916140301060614091210050103060507 80
    0xa0945449102e8000d4406440c845e070007943c580b60100c1c0030031005098060030550300d036501c0245e80b0798041d110311403221113011000035141d403840203280c04000c480c00140b190102c06103400610206031071b8141034038107503181030310f00142d4070409003842e5241c00c100c00c407032542c0201c41e08410011260b0218600354400001c003001002920703203006042c0c60307000c0c807043c45d1107681c41100084c415092411000850343c00d81c079400100c1c503840740ca03480c0071346004079504075502d60030060400460504a409802c45800b0303c003080e58043c00d280029490b8400984040d07c02c44211041180a82e11081f0720402568014611a550446458040c0240314032401c000d03240d01d00f00c2c10100b5168000b200701c6001070743d51b03039640c1070b2010f400c5d48403c0507407c0a041920a8842c95000740c440b2400d21108201400b0304a1003c40440100e108250039690990005010055041c00b0402001ca00c00701352104041300705d03410b0101031424018646003d0b05c03400c400404600709030000050040d2039018502034032003513 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 90771232 1250 90769982 90769993
    0x90106090b030102041202240f0405271f0e0a0b04060f0b0d02130e090c1306050105091c051009050105060f0916090f0306021305090402060d020304050a0b01060f02 72
    0x2981018200d00480c81446c03c00c0018490030001890b284a0b0602441400040324006c5604d00070301e44815003101810f00c00d00c004c00242030005242c200320207407910030101d042c0b0142d6282580010481613001c0d1280080d4100122424030300e03003000e01c507a8003500786414591428680030304003001070004a01c505001c2e42c5020f90108a00800c03034010070035546600d40281c6000e0011001100039486849074000a40d0080000710b401c43d880e0301d0103409103688800400400d00540c1c10054240d003050703041e14102e440e2400c20407490760800300303030b62002e50b04862032422541ca2501c2c8400001c00000d000b0150b002d0322140d99181d242c20fa0160402d54000c000801050343c52070148010b0300032041446900c83d20400018001030850900300144a0003842d059240c1662842d0b07603196240b1580040b14035940125048081c1030014104400401c0d0440740942141803607008158584600e90070100340c1a0000001014805c00300000b800155200304c60503407941e1350341c000401050700720a0810050113070 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 90772482 1250 90771232 90771251
    0xb070506010f0506091e0103140c03040302010c030608070b0702151617042318070c1104020906040b0304050a0c030b0a0b0301090b06270a020901020f0706020607030902130509010609 80
    0x144e000e0394000712001d041c00c210382030038680d072550b045006200c2904250703c2d203010001000f0100d0040e030080f03052080c8103481e400d180c50041d007540d181182e0b9400700341c0303045410081c01c04006408400c03281180a01a900c074040c3c00403510540e8450807900c8030175000030380880d1010b12a90441c3c00b0600554640f8007040c0b04904101c0b6900c20b078402c4214032055a02d5198102100800545080d140180603042c6220394180c5003909001c112524404210103240a0041c00300d040d401340c0585004130f401b1807410600000145440c000c1d40658000d031079020000a04000c020007280c44059040404d95291030f80c1c130b24003608000c5040f220150910700b0410034811034181400348104150744404200c01a50740ea20901109a2480c05150320034410108220310311134440e03c915004412003a005690f03225514006490440ca840801c2ca041d40302e01d000b04200d5602148180c3c001e52140303400700d4025000d000066040c0007080b02c5014a03442c02c2c0902c00300b0300c1c055000300100c41c07440d0420b010340e40340d = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 90773732 1250 90772482 90772489
    0x30c060711030403020609091302030703050c03010c0c0f03081902030a0b010906080601080a0f0b04150815070203030f0a0b100309060b0d02181305030a03090302100e21040b070506010f05 82
    0xc3c510000b504070384184000340207480c18a10450780042c041c3c441540000103500003d2900b2980e80c0b05443d290000300e00c20703c03141000c1c000c18510075a18100022030103416030700c3c07842c5074000f002e0241c20400d0800205003d582c0300c03c140c2000760140c40c0107644030b05100d584d0384014000001114081a040c52001403e41d014011080c07003554143c42e0b0000c5696540c80d010050482007008a04c29a510045540c081d902c0744101d1086940441d09203108a04005000d1301c0d00b0500d115220042021030700304001a6400411658000e12440007400f50fa10760382c1224018101c00c02c0d5551f442451149085091a81035010200090240740148502c40606050000700e10102c0801394002c0401d80400000c5904c2003000e43e04000d61808101440c005900c8a1341150041c014030000603850f8558a024940d041094080d241c0d03171500700300940b402d1722044503554011a074000d01d9010b80403000c50110010f81c42544c000b8901080440c2d41c030755561800c030741c80744401d025550f1003c50860f40400c0505 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 90774982 1250 90773732 90773737
    0x10203120103150c0e101211041e08011b0e0409080c010509060109060b0f0906130e1009150323100c02061006020c06030a0e0a06020706050906101511030c06071103 72
    0x2030286ca0000c22064901c811289030031544104403035103803a803c400c441c104100d40180f006181e00303185c0345a00780da04620401003d089a01829013681450004441149050064142d564560a0880799031540e240807a003c0d060080e4090b00d80301001c1540b5030403500640107184120b0000301031f02c0c501e03038880c42e000ec129065806000c0100c0400c0c41402e1140d04420000c11455000805080c14605400030039100300070140c0200852445440901140c0d040000d4020040c0010304001d201e41340403100a42c2002c0800c0c4000b90407640d4075054804d031645406801e444410b00070b401c0d50000c0c8940301200c006000e50b40c0514005108010008038111581d1041e0b00a880b420b5000c0e100c0078000c80c0400269400c040e003080500e943c0c0f400f4940d4030300000c02c9002417480c4505400358aa81241c1015002c8890041c8500c1c010b0b0041402c00c013040b010010444152490900c2821440d003061030200d510800003a0182d0303052000041e801c1c0c01041c00128980320380029503c0c2d081d05c070b8080803d00d80702e0 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 90776232 1250 90774982 90775007
    0x112060612090c05030307060c0207090903051602061e040f0e1003110a12050106060f050306030a02060c0c030105041b050d080a08040807050d080f011a070809010203120103150c 78
    0x103500c1e080d10292030851a04200c0b00c090080b104890340075202c40000c0d0039507100d100100c2c0e106995400c4061240d806024910080c480380c20200050b9100741c030094000d00c0351406038a4020a8039810ba4119540d100a0b1a00fa9800310301e401100304503802114000c0d8824000c1000000680c50009010314510b4038803031080f03881d107074804000ba15554035922459500841c09038030040030040865101600e03000170000c0c5019100200c0c034245060350180503400060410030410104004200c55610005600f004550f0705440e480e030380d00482c9208a081101a46086905500708014001806000582444801c0300a801e440038103540d207082002e210b54030080100352510130f01016090500840d42a9401405115250f1800e105075031032504224240312144040741f00002030002300d03101c42c02124003400c101f0706c2c508610854005e0001e002d0040420042212400149481085e4401d001b0f03200031484203060041a5612490026031081400100521940c6010307110701c01d6a20809a51091 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 90777482 1250 90776232 90776237
    0x1b0b060f120c09071e02010c120504020609190909110301060602030a170603030f07060f150f05040b0d1407060806010206060109060c031e020109030924052107030b01120606 76
    0x44450800501c800f4240060000382480080b50903048860f000c00c4a518000380281e0000070007001d580f5001d48001c203808551503909240800300b10041e200d10048130129041101c04012140a549618101e2112074111091240c2080c0c042010001c0b41e90a80c1e1542104500905c07503c0e8550400320382e240035010360280000c1d07074514200d18080c2c00125041d00010013a0560340303044444260a40c0582c040c1d0000c0f1415a40c0f5441604112114840c10700340380304c1a081d940d6407524121200032522414014140314075690103401c04140c0d900e20141c10142c1d400300f40f003c010700358403030b0143c0c40d007906100d01808104140b0001d0002d601c00700745140b0604c4140c450030141e500b040c10898981030007010860502c5550040800c50000c1031030b5003040607c2560000c10001c4040c0360090907801c26a0245031500c4180d00c4020390b001c40003841c000818400d160454566100c0f2a0305000280d10041c040c4100c50594180315245038940c0001c16003a6083c0c8803090840018078980003151418801d2400 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 90778732 1250 90777482 90777493
    0xc03031808070f080702090f060102012315031905010c02070b070b0403050c030c071707120b0c03090a0c0603020409050c0c07060f020c090108030306011722031b0b060f12 75
    0x10300c40d603400e40c1a03c0d0080d412a07040030322550101d4001c80080d00d900c0040c00c07200e01000303004e60342401103c01c8400e1843d400601250781d42820030705808049d0982c07106081c0806002d0843c3c03010082d035402c4440300d800300c80320741c842030500c3c5000302007480f04140140580000402d295000e00200c49407540e2103004201943d5a60b2001c99440e040303042201c03500d000801c8154a400020005807000c0c101c803800c186020a402e00d1210324150b4282d00c000c14603404415034401180385484000d5101290780c40049d0b40f9914421914200300304000000c00000c850b04002c070b00c95601d40d01400035182000030070030103512403440c07009442c003c92200d00d80d43e0f4405c80041c04001e10802e031680203455180115440901d105d800610700038026003009510381e0010080002c6980d228003940c0c540910742c8400c03141800c200c440122070030362101d1800b8200710101c03180c0c001c2501c640d071407a808a0790245103003135080c2c003880c0114111a040c2c07002442814110100140fa2030518542007005111000402c3c = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 90779982 1250 90778732 90778747
    0xc0c050703020d020a030f05070501031d060121141c0c0b060d0602041802030603060709060f0e0102030d05070309020f03030406020712050f060106050703120506060f1b030a0c03031808 81
    0x8080c0c0c2c0004080fa0007480c2c2031400000518003d401f400543d01c601c01418000d03017000001001c40722443d150742001c00300c2b00f080404001e004203000381521440c0100c0d111907c913590740300f0110141c00a000306801c40e019081d070403d0b180440c2030300090401d122002c610b201740284c1251030b054419406004041c030000030410310301c0c0191303c03403d0481c819180075044c00d0341d861902c2e4004241074030000d80d882d000020030821707150a0110550040c114208040083d0a10100a100303074184107000040c801100d0069505a00800c250b03079000b104660248900e00c0d00503002030240810020407400b452085080031040d140101c2583c01b69540d650082000c203160481082c0c0d0980c1c0c005054955010300b080140102c0c0b0103100d01c9011306119216540d4401c040c0c60001d00750803080308008440b40c0740034180645030366030404032a401c101007004640c0f0740380c40f40c040c41e094108040079100d00340700001c0c041001d1a0820010007106001e518200070400c908208549070040e11503004250f1a000c00464 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 90781232 1250 90779982 90779989
    0xf010302010f18030206040902130b0c1203040f05010207031e2d03020f03070e01110c06030c07050322060306081606050c150a09060b030c0915031f020c010c0c05070302 74
    0x203c2e0035035500d89610807981d240c000c502103501c240c000c422080e800040e49843c0f0340c01100c0140040c13180701c0c07901c1d241c000e00d00c130000e80b1240903016141c24600001301103007e01c4556180c001e8030a4004001b1565151079280142c070600c030306007081e010083d60050340003030030f4040c500d517807180e000e0400034010304000300c0790058041c8160900c1e00107065003446006050b40021015501ca206542c40d80c03100080c03050000341c070b50b004421101416500104501c07006454541c20b494200c0103010710300741c44081600d000e509501580e56082c2c80074041c0302800f0060502c201d100d00c02c03521507440c10000c0d03d03141d0180c00d80340e1000c80029018440710304000c2201f02c1c86400103143c00c9426005a83c1303252071400441c115805c0a03684a83e0098403451140240030041c890401280740480c0201201d4407000045164480020b000b4106181e211041034070a40301804007080c56001c0e286481d103885030b10604003009401c00143e6072525807a040070013180c140164030602d081070704440141409840e540c04c0 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 90782482 1250 90781232 90781247
    0x90c1216061407150f0b0a0609030206032e030b060d0b01050d0c03080309011a01050a0e01030e010f0c0305040b09010b090a020a050f031914060d0609080403021f03050f010302010f 79
    0x41d64010100012001300358048081841c1d5490320b1000302d0b0602d984110802580c4a0010300c51051020510070480d060700b26a46004595043e241c441d200c0c3d03038a801080000941c0032118030040d604003186402221640356910649105100500883d02c410080c841904413800c4d000b4071460350500144190f14007003140a090500c107400300c40d41642c503039032180c00301e410941e08449260344404400030003040391032581c41d9803282071038100d0400503143c400511400003a00040d0600d582d40e1040082a079080d082160461032028080c80140300c4414014008e280031181680d228020b800030031807011040c0035039558258010140c142580700c45440c2c070000e51042d010b00c03041c05010005025a41c0112001c0c0d44140031034003070f0080303616541654605403845171043e0a04109840300700b10040c0c0c0d41c48010f03201c02d6000803001900002c58680480365119580004c0d6200c0d2a0540003d0300d07107518281c4120008290303806000c9a01c07180d030b4198240000f800000e01141d20600503081d8548110035 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 90783732 1250 90782482 90782507
    0xa0807090f0b0702091b070b09060106021506040f0605031f050c0309060408130e010f030212150c0a030e01060905041202030306130b041e05010611030702030a03032003090c121606 79
    0x1841c5d8040301a1700c2c1c0484a9002d51f000b1640082d90804001403940180305140c010605800588507480809001c10455070b030003862a8403550ba1101c05600c42d40f115030000020341000f50464054901880c030034081522050000c0c11014102030000d4144844503054900035000396006045a8440d075854052035004400c80c4541c0158000c000907001581d021418003c14141c0d12219050303095006000304505081c1e5142e210740e001c542c3c084660b9004802c000e50003040d550300103407901d00a1108a0141c00d1186040e0b03160341c02d00c940400c0200303181c0c0c08240183d2096031004c403c400407a50aa07241d010450300345502614070614610142010741019141e41401000040c240618032002e100070f09018010858040c0e8401c010b015180d000b2600c1004910104010741c14960180d00081d0348100d000001020143c40300d0700c1c0300e0040c01308802c40012800704800e1070340328035160b04002c1c0d9801904a04906c501094142801020408510080f1809594103403074441424100251000c080508 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 90784982 1250 90783732 90783751
    0x30e060c0615091f06081801020d0c020f12070206030a0e0d0309050706230a0509062209020301060503160909090605100e0c071b03080a0807090f0b070209 68
    0x40400c050010a110301e91080008414058407110040148403103030000500e011041d0300c400d8489240f000c80782c0c080c030b03040b0750386407a0010250b074404005c0c10035000c0742041741c03c2960010036006101c801542101e0110310711942241d10011300d61445a9544656070402c0a890808004c0d22015050000045a000708030043c00b08944103c15140c600e445d01d05446540040e40d5480c0100c204542400503900602841c03500388150500c170b0100c071400810a140407151020002265140103008000ba1080b0030350040c141d584400323142045230720002c0c03400c003400584c0c0c9000c03901080c010128401d907416581141e80700c605603600c40f242906102c280c88140018401c5c0b52000080803d2903001d650b16091003400040350701d003010b081824040055400200c000e20312002002444400f200c2600c030200c0c0c10811104d03101032265032202e4201e005410207411000700260301d0302c81c0c540102d1141e0151003a41c1d07400412681c3c0e203c4c0089040c2550040d0101410200068005480c0c00358040360440b0100 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 90786232 1250 90784982 90784987
    0xb1f1e030902060705060f010801061d0a09022709030307090501030902120d12050a09050a020d0c1a0403030e0f0604140112020325020a020d02090403020a120522080307030e06 77
    0x250009503c035005220100c5080d440070081100c52860801d609004002c50002484220b00303225060a6090b121000714064031040c400040e9181d0341c1d038002403000c41c0c02506c0e6030141e01078101d500e4109400e00c0d06a90b4600c6d042030200761021000022030340702d14999070310f1215040c00c02004502410043c0030036680202c4c45580e118400000f84112140d41c40142c0f500559191498090350076100c00a0202008603d0412074002180020032001403483c3d048459001c210860701c0c18000d0b04103284c000d1403440f51035032021416003140c8001481580d01a03120569040080d82c00c014001071628192030700084140020400c175920316086c1410f4071b005042810b00a140388044104036081114159075910242030301406d00c100f0040340240743c4400d880500280c610380d030013107801030f500c00100a002d4004640050705051007449900481517200706003050b0b0089800300109650818a0000c5000d1520070800352844084e580d00e0084840a901031814074100f0f40301610905201c81d48950002c2c0c04 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 90787482 1250 90786232 90786251
    0xf030307051f1a0d0605100305060c0901080f19020a0e030303040c0509010506160b0403031103091e03130902090303070203070e090d0302090f0405070203090d060b1f1e03 75
    0x144201080d2403445440c640d011440c82510009581c14511410442601c94000c4031030f68850b03140ba8042590400b00126164445443d10b41e0074040542c00a011801080c1c18052103e45010080c03510301002d80e1005110344030b03070460000400c02660360302508420b08007480f4808690740c001d80342c0007803c1e0418040c50364030301012904680c821942141c00c80352400341403020307181c603421281c0905801c1d902c182c00c0448410000c800030100d0f508c00740801c602040040c04140c4603030428049200381c441d059840c0d0608221240d038940c13a642c01c80148040111046040704000002d44840c00c07512000944054500400e0b04029400f42542a0305800100202030242e2401c0201000404200500701a03d20301a40c40f5424500081c1d000000c1600400141a4903510307014004078a6008031070000700d13a1100842a443c0d80704407080036420400a2000d00c051011940c883c50369100d064a981d400d81c4003a003080c203da41424100c10b00031403600707070f01c200400c030650303422100c1d50b201400d001a081e0b10 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 90788732 1250 90787482 90787493
    0xe0f010509030a030801030b0a050708180a020604032f030d0e030c060705030d0c03060501140a0c14100b0d0201050a0f120504080315120c0f01180b120f040c050f030307 74
    0x3d490010703004283c2207801041040080880e5076400900d103031080242d401c145600400c08800074001044950341c49603011143d2505100b46052541e0051000359902c0c5c0d246844807949030301040f09000c40741c1840b806042600011510203c0c4d042c001c001e040c1c081c912840582d80c05c564002100d800d071198001a107801d4480800800c000d47c01a4001c40c0c40300d1f44014040c013030f140140c1c41d1104040c14900104107598005042103040c02000707412546070783e2280d00444800d11610700242881d00c05a00c0700120f0503021428001070843c00d01d003408890610701c20b1080c0719880101c02800100104800440b0510803c00c00c2e102820314601041510701024140d001d80d407003500e09035101403000061081491244650f802424070a640f0314400411301b01c0b101c0c1d20f40c0d0078400444e004052a49088640b07a1003144d0382822140c0d0b001c0c541d1321031920740916080981240410141000403840031075829040c20704030500c02e0364050380e854425420101070026002292030041e0f01072109100c0b1900241 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 90789982 1250 90788732 90788743
    0xe070801020a020a0b1302030a060504080d0603111c0f0209101205030d06050d0c06030b0a08100e010c09030b040206091309030c0c0515031b07120507021e010e0f01050903 75
    0x242160300130050040b40d07003031001c2c18035009002c0203100c4c0001151440140c9000c41c86c5420583c10580004442e030741d07400d09140c00e10071800001030300f516196020082090f1b80118082d003d005070b07111180c03902c41020301c01031224030840142948003907506850041c6854440e031540030019802c584c80d00c90b03854001078402c4e1040182200d55410100702900c840080303210700f1000300002c442441c0303400e00310b0711611101070351070195004060310384519041b50340780c42014900610500089541d500150301e00c440040001c07410842c1c880d424000402d0140f0304c1040303000c003540c1d00040305c1c1c10603071919420010aa44505110758006600c1b0b02c9081412100b4403030305113150702a407180c2d28510081d1600080f144000d41240d807282103407600030514600c6020540c2d600062800115403020782d030a2000308240100c4000400400e485090120140d610801074450f0b41e20035240811900d1806000500089410380b0007030010f00c50300c24158952414032240c0405c0d02060600a00c0d1440c5080401d0500c3c = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 90791232 1250 90789982 90789997
    0xa17070215090411040b0304030324170c090c0d0911040e030309120f04060e060c0604080a030605030705011403070309020307060e0f040903080402090403050f030703050103050d020606060d0e07080102 88
    0x400c0042007140c03090034280604806081010812485c1905110f049840e40c007024002604050b0b485001601d5042201408a2410180c2c075000c51201e80da21220700c55540240c07445941030165103202c401c5800c06821180c0180309511301a4244206540698000c06040c0000d0ba03989900d480d0705c0070240ca07503116403c44002c0c003201855582c5448880280760049800c441903030300d101005214a401026000da40036540c0b82e10748101c56280e544005910b900808a1038004c50140e00180300402a04000415062916840500c45180e03a1010181c960070144503070380c0403804a0100580c0010f6450007541e114100307060029801c030481c3c010070300c2c12610f504464080780c03100c81a1005450055200c2920800031207007844000100d94000341b0008010300003d002d07500e11404107003014014000d031f07010b041012082580300e2a040c24001c0242c0030070300c006d803041d00680c8400c00d01c140c0b012560520030071024081500c0c01c94080d4441008001000400803180103295010600240a000600c0074 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 90792482 1250 90791232 90791269
    0x40201050a02030f3001140d02040b041503051b0105041401020a0f030504061407020303120910020a021606020109050606150403051002090406080a0c0522090c031b05030a170702 78
    0x1039a50f4890891124140e062170f400409016500410840441180054043c0c1007554410400c440e6440490301030000418190352007410181021510350301d032840072084a000b802140c6031401c10404a0841405d02c100e00da0004104020034003e001d82c1c0c00305540b80d500c042c0b045810000c856141c54401005c952030880024500040400400e42c1c001210510f82d500100b2441c03800c0059030000381d4900c2500e049040e1071480300d002412500b0300380068040703203010080a541c0d9994001009445507035aa2058080f040041801b1510714070501c10003617407682c40300c000c04150316100b041200401d07032558480c1a01004020110016400b130003651003403401c2450160b200c0280108000a442d01a008444140d0080780c1c82408251189440400c6900c19507142c1c3c028125030803071241484207454081141170800201c4001c0106484052080b20b0081280c03005603010007910002c002c01340d12529078036521040c4404086441c803882c1d50300001c0c2d0160036074a4140990b0101e505088541d2030242e2 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 90793732 1250 90792482 90792517
    0x71b120c021f0810081c03060b07050d09060c050c0927070807050f0d08030a0204050d08070201030f0e0706081009060b0417011509050a090606260a020108040201050a02030f 76
    0x801d8003c5142500640081007480000303052000040d0b5034030001d110b500310a05401c1d00700490702c2c007946c0241c014100c00361900350344040c64100a640c543c01c0711514000201003480000b0100d00c036184101405a220018055060881040102a500c0a060700d500d1115134010f41a1051000034540844218000a400101d10b00f5004d18242041944100e000f40382060745202d85603102004008607aa01c1000c141d03c0343c8403080c0140081c001c6400c030942120134010080b052204030005000018400d0b0303000e00c02e04400030610790990b080c41c05148166880850b05110182c020074103554000c88064511900c0759407002c482085d10620707806540b400c03000040a000708106280e004051200c40301c000e1211072221406800220224400d03041406ea80d8008103a800e03080703070480b204075600400240305080d15070340d06a10304580300d142140728240490001c0801ca2002c2122405241c058640c0742d5a680c90b0780040d200c6d944513446101c11408100300c03100341c201440c4081d00341c07015044250075 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 90794982 1250 90793732 90793789
    0x303030506060a050703080a020d140a290402070515131b0b0a0e040212070e010306080111120402010207091104030c060509210a0506150405071b120c02 67
    0x20111038014000034080c110400405011541007011a2400ba0740343c07804626a60303a04055200030300844070b040c43c1080c01d10094040b620041101a80a98680042040a9000d0540e2044052802406554001203080040c07c0303618065010744001c0c0d014400b80c0f11700c20684201340201c4082121145004d01904082d039007440320040707031501d081d490301c04148062403c1050314207007805000320140801c0380d0b106015009440c0c3e901525461402050802d510782068032003c3c01c10711605e01c507140040d282c032400050101c0140241c3d041b25221010103881e101240d004282c00260090060307040d88105040095203210600c02d061170110f80584068469085161407128005685d000b0000c1184c01c0c800400c441da01c241c0811081d0740c0e80f0b440c0c01c0204c848403d1040c101440b60101920f82d0084200300810116040c200302c1040b1000c54003000300e90f0394002c080d51100c8030050a40340308042884240c00207104080000d88003011401c0c90a1359017007980c00156110103040c0484c60982802140070f = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 90796232 1250 90794982 90794987
    0xa0308070c0512070312110307030f08100b03010308070303020c0a03080f060a0e19150602030409110304050a1e0210030b01080601030605330301080a050708030f160515100303 77
    0x15010301802c0320070300c00000b400c3c0c0105941d0350003800b0281c58904000318032400355006400241a4aa1150a8945900783c80c20f0241c2912490132500012400d030390700090880c401c101c10401912040c1c4c1e0260300310707400c0d07484400300b07600005000c8081c59401c1000846400381000183c1c02da41c840c2c4d5554040c1d2500c0140e80c02e528401818031800f42c00000c1c003e105150840b0000c642c42102c1c900007441c011762540c2044042c100b500508505945005400b00354290b0200c002c00c1546c4400c51f052042440c11048000188002c940151035030700315042200016900780b0860f00400c03803c89007a412030726103800107191260038614040100740d4961030088507581060110b40d2007002424208000e901d000080340c19080204004104c0782c41c02028190080003400d101100200c241d02140e8a942e16604a1903990b90202c005458502c100400020010400403c0f5000f160340c02c100c4a080c628000303c82513408182e8030301159070340215804000f8030b901a0211070b02c0380b0440010f184145240d0b0801 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 90797482 1250 90796232 90796253
    0x3130305030c133209070c0f061802031501150c080f0d0c1707080c070302030c060403200c0d02040c050702030a200a1a0304020109030b0a0501030b060d020f09090304050a030807 78
    0x10b140e100107050383d81950b13a81d104d6100d1907002c07129041c806030f05442454000305400b10204005e00c0d142c6803c1c2d00720351241c4512801c0b00c02c64425022261480300c1c03415052400340c024031a000c01051114624070303405100710441e8174524401d00030340d800c24280103814101c9400020058803180e60b50405241e26a901010241c10107100b0315102a1500341201d0081071030f0001022061100000142002054070800403602d4603000b00003614600c0c2400d2800511407903c1800750304113002c0c40d00c08c1452420740410b081d0001e0400803c0c0006802095081c40f000d099640d01c60001d1141c10301c280c80c0581c030140450000940301c2e440004440850321008054101030080c041e009003040700090011b24140130001c00e20440320103001c4d03200e80c1d8502c0103c80709281a08014012200c000c1130182440b0582c0110741601d02c02c2500c0750300c0369221400c0c8100340c59800c0002e94016802040100a4100454a9034005484000b40c9144c00d44a60104c3c20840850341304a81341e81c0001020428084074011 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 90798732 1250 90797482 90797549
    0x10506011214070f050c01060b1207090825081005040303060f0506160501061a0309061303080402010309060626070b03010f090c030b1f0801050603130305030c13 71
    0x804000030240c0080b01c03801e004009000c101404141022951454061000d86001038030460003804982d48400c1c164640d50030210101c03001d0b01c14000810307407041c0560440d4083c0c0710000300038901403000000b5582204082e003003543e11603407040c0c40407884017800d00058140010390b040100f69070410385401812580c0307642c00006403400000040c04613960744000c40b612000c0f40d110503101c044007800c0440c01841240d1140070100811081901880002c101561141d40c0d0707070056400303c2d5101c84d40210f46810031503004000494002c00200150b000394000f890490140e1b00001d038884c0c40f800b00c000700480009100101015885680307501030000c000b91000390451600050440d450f00d65841100d08a030b020762090240c131080441030440c0309038403480014034000c00c909020191100000030b41a01f46098900051000002088500f0018103c170b0203030703d05400c405420320309070b1012039464001903c00103140e6030401100f00141040c840581c082e1001d0a0304012400c40c100305155a8244800c = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 90799982 1250 90798732 90798767
    0x6030106021002030c040f030506100b0a05030f070210062d051f0201020c1005010e07080103020105030a0914060a0608100b010509120c0a0e070e01020105040f02040b0a031401050601 80
    0x144020340d4041800d03002d660b10800050b89a40f04c1d01c003d81000d00481d00480e04520f49541d00005105c0005842401303441c0e42c080040d02c2070f840d04c2414002c1c0c0f107a01000408504108049880030030754400007903100c001807054401d48045030b100c9209070b60a56210321048510170f820119030b054200728000b803140c00300e10342d031058919200101d06820034400045a442d210418501c0b11039000b901102c00e45102607040c2c1e081c201d11410303c0c50040c8000e0040c100c045a084000950b010b010f600e1041c10303030740c050712168150386d500c6c046580034141e40700301200d13281164030189004140c10042c00340900c4e104000400d0050500070443d180225400b50405254201002c400c85a60058102d4422480556841c490340500c512518588840708001b15000500d25000080a00241c0e1a203409004695203128101c0105001207003a60400c0d14060301c25101e240b909001460035a03c07003815002c0141c1111b000c0c82d40c80d11504114202400da2100a075140c50800c0015a0f020107810225030210 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 90801232 1250 90799982 90799987
    0x180906031207020a0b0c06011404090c0e0604060302180604180c05100905060a02100e0a0c0b0714030c0601030b01050a060f08060111160302040f020c032b1b080606 72
    0x41000035581c441c25810360000060008280c0d041d0f48030501c205001e0241070b650300d543c4151003400580c0d40c001c03d00c10705001401a0113141550300c1d150090348500e9801030f100c4515641001443d0a0403080900803d40c42540d8110000058030341c5001c240c24024155203107000da14080e4140010b4601c051803d40f07181d42d950540b04005000c1c188004142c0320180d880c4980f95092400640390200300c0c1c0c00141e409a00803500010481c2c0c0004c007614035000e840800e02200084480865603442c28060050840e091701d80306004282090300a440c40034015110494070074602c903001815036021b450302051507004a00184180041e00c00c3d0340780101004d5034002d441c940361800041108901c108070038100042d107408181d0580c41000d03e44009403480b400c0e030307004100f030901c3c0e690a4440c07403000700c4c002c0d81811400c001c0480c0074401c0d42c6210314140090751400465015100f41e800c568041003200780c0034440080b1803031017181329000310301c1c0100d200c6403c50b8501901c060020303103001b0040c92145508 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 90802482 1250 90801232 90801241
    0x519020705190204020904050f1902090a09090501110a090f0605030c030f04020a0b0f07060501090204061b15061211040504030905190302030d031401060302090315040f0501111809 79
    0x41105503070001c814030b800c25150728400140a8450646526071040c1001c0c1031000c104204003045009100780a18200410102d00c4840141d0045075191540031004541c100145e100e65048130540d2840b40303000089001005540d031400f07070170861104000481048060101c2c0c000480341e030380506010b0500c1e40c1035203810101c18440c0c9c4401040c04440c40300e0107003c101151100c00105021b0140940410f0721940482d9a07c2100d81001405454060401c0000280c3c0403182c130803901a900141d5903070b40035401003c036460f170320102500110340b0f441200403c040284024402e81c0080c00135802c901d0a060358a00348021200d00c00120701c0e200d01d2900c028080001d80002e40c0030b00b212801d4070110514a00c02c40060021009507001a4150003442d0404280aa00d0f0f80650700034900c58036959421307600da0300e04404a000c3d01e0400b94040c0d00881e286c0081c42c41074007125a1191180300340072800303080c60303403100c0c25100252440400741c040400c402d04c04050a05c1c0201c07160205446502040c0f50 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 90803732 1250 90802482 90802493
    0x150501030f020609030f0f010c0e18310c030311010c2a060203090609071706010603200703020f1002090303030402040203060f06190909020f0901080a0b031005190207 73
    0x1c00007009200b1070000030030610f0303501c003489544043d100b21700a80e54041c00c43c80d5054040c1c0100502e07200041d03030071440d00f1854034150403c10f00740310040c010109079a03118000880060381040b44070075011408040c1c3c007454a4950a02c0003942c0c42001c07481aa149580303400b800303811107807102c00096410008864025507200e54000300005e440301c00000c10b0094601122349800e02c0c2100942454000010003805030b81c0000c00d1070040c42d000c4200e90a20303955911902c5511a10a58402d03590030002c01017107054071a801480e54000742c0e6400603284007500712000e0385503000341012001f40e00300c940041c5440c00288aa03a22001c2150b40c20741c6010754030300c0001d8892100034030003885294040040b4000c2e86610301611456100a01110b54418110103150740c08400c060300139002568070a0045011302160017035946003200d0000d100d00780b00c2ca250054488040c0140565000c5a8810045100f950204048401c10a00800c00241801c0410a0301c25207825850560842c6004001c42c2c0001603 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 90804982 1250 90803732 90803753
    0x907090e1b0a12023703060b0d050718090e0f030c030a030216020a0e010906080309060405210d03150503030c07030b13061104080c0415060c0c080708060415050103 72
    0xd03262400d280c1c100f0b00c4031182c078000e0048104414000c84129106860014208204081c0404007a8443c0c5059039004c01103054440724010401c1e9080244201c07010300c00c4507000140c000d680f5042007800c0c040c003d00529101c05e1594000514207071111282443c4800a0110101810588c0301651406203074a0340c5907a00c3c03107400078800406500082c1d20600388800141c10203460b0b402070080042c2503480001004084083c003585074264a41400061400000821680b8074174020f850b01c2d007044d1400c8208202001081d10241c840c034071414100c0c00106050100791016201510000368220260220080300b001e2504564040d0340100404201190001001e10480358403501146c42c41d9111300c0e00844198203001e005243c141852aa0b0030fa00c04500054016a00000101c4883c030360040d0401007a14400f040554080c003c0000c01e2003a24030a0b422142040e0040031081410750f61910a20b1074982c0790740c072008031034000205200802c00f1800740c4588000c10b400302031142c1c2d4103507195004041e = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 90806232 1250 90804982 90804997
    0x20610060507060605060f0a12060e040b06040905060403110c090f0a0c050d1415090402090402060a030209090f01050117010317160b16090504090f110102010b0907090e1b 75
    0x404045082c00070089240c115a01505020b0600794590591058a40260f002071a0640204403000c070100c012250328800d50080b201d103070301040750b203172155140e005400341d0280845030019201d84906d40400c40800c007040c01540f00360303a114102d00c51401c1c041c2c00e00b030b089032201e40710382051024000c00038001c416140d04001d0000001849040d0b0032000e6030144103c402c000070b9a407d0407640c14924070605041c030f00c18010481540c40e0386500c2030800c140307030604580081d805032043c2c000c1005400c10001426a082040c04c005190950301000a00c440c08103c403506240a0003800500055078010aa03035041d4814800401055040d6660441100c0503a0310285840c140031074890162105107e403861401e8100d10b5110180c02c0242c01e2402051703031080000e000c112003800008040c1024421540c040d0f800502c81c0c0c40100050f40c52000e2131048054550456403100601d60681e40c4000c0943e00139441a00d80e60300651130182140400340c0020502c594804211016411402c101021601030 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 90807482 1250 90806232 90806237
    0x60301060e0621120a030b040501060c120207090e030c10051012020f04060603020a23071502040305060c031609050d0f05120c01060f05041104061119060c080702061006 74
    0x24003442c141c83d0900007030b5142800e03081c0d105a900700e20080c1401c4008110006040d942070000c06011018802070f600c003841000000f58400342943d0118150005000c81e00c00c01c1c0c0b0560759186d41c0c031040350301035418402c05c50410340c100164542028104101c0700541250030b00b42840030f46016005088040b40d5403041001d40b103030180d03180c0c0440d590082d031407580c600010800c000c01a1144402070094202d50a040c021481038100120140e40d1650a54110039950203224a0701015503200406500e0380c0e0344e04064107800f41700100c0010070a00125100f03007448503402e030b160310b00160b0150250889802c56014880c0d0b03810184a5a111440a840041d8200602c90030301c100c64940340d441d0556021007031590602c089a072200c01e01d0103401100464149078034064480c0c0d1070f00c080200b21001080345203040f80702084100080d500038401c943d29031015009640d200322042142d00c521000b41201201c0995950040344a0940c101e40d40c140c010090344001e1023545000d0303590924405460240360203 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 90808732 1250 90807482 90807499
    0x103020d0209100e040c090b010804081e09060406020a03090b03010e01062006010e1504110901080403020a0501020d0f1a030703031103220e0106020d02120a110a0b010e060301060e06 80
    0xf104000900030005242088240c4a2807405013003a001c165080d0041c605054140740c00c00d1103640c403d04031640070707582209100385410110509011602a40d002d080600c03102440428080d540d2500035100400c01c58010b09546840d0745030080184409422820781007500b4401406801c11100c00203044d07811908144481801740c4050b507144c2c40f04210912201d101d40c1c03001240c1c1c030f040c00c00414050b0108011424442ca140c00030403041e201d00000d107900e0400140304070842c070b601c29048180c1140c0039006541a0740c2050b03c1d66820781c2c0c09200860011600c440341040c200f0301c240308260100703510754145070102401400103500d500c1140b0004e0100100048030040741101030007101e1121130900410b002130304800021601e1200d440c41043c220500000000600038001309450310410744d40d03030103844021003040d810b584d1070300301c0b0b40000d0801c442400340750361161007048400d48590158900054540c074194525503100c00c02010b0310b009904180b0104410149110000d82081e400c860300036 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 90809982 1250 90808732 90808741
    0x90105030a021218010c0c02030604021020031903020a0206060d030306050d060902180f0c0a0306030c080307020f030c030a03080901141617040809121f150e0103020d0209 75
    0x60300560282212481e00c0e4810302c00128616031044c000018028000e0046134000b03003082c1c0d41510120806505a00724200140c0149001c0342c141031004805d0070b040c03000501c083e040354072112101101000320b50002031400070800e03030b1034002d401c0d2511030714080d0302e400c0d03106400030349601028003482e00401c1074200c0303403040602942050300605406085581c40d21058107025001c0d105040d81a401480940c40426914107030b808a50310911141c8245096920b901c00b40c100c55521201500c0109551600040300107007010700c000000302034680c001c517106c59040c010449498100040c45110b9400030140c8601502c003c51a100f6154041c20806043e0390780300754042c09030020451001c03120048204101d503220107030300c02e520048143c3c0c1d540c01d000c40031459403095140050300c010704000801d00c84501d035807824641c440d50100b5500705a60300700503003604940e5849102c1440105180d21051030040d80c0070075824400c0188004140400309516507004120011210b0358081c0c003510002c6d0006 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 90811232 1250 90809982 90810001
    0x306100807021f0603110d0b010308220e0105130c0807030b0a05040603050a14010603110904020607020a0b030a0c021203070521040303020304020a270e192009070509010503 76
    0x10031100300c034607040d00007500340c02c411000100140d005c01ca550f610041d01d1000642000040500e40035400303052440181d003507441d10fa0160300714410508180120304940c00400031140c0c0310300d00426a4106c0b00a095042004005111240c501c01c0862245071466003902554800c9625400048500b80000c02510f00b401003109400e4581016401c14109217000040040c001004100303d8050300d6910008080d401d03403182615003c2c131024011501d81c2521080d140b1300f4902c81078100d84010400c1346004055804241c80340110743c40601c50f03007401f01c204010b2400314000c40c5ca24030310501c0a0203c1c000302900804143c04050044000c0100100e01101002c0110301805c80c920308126040d21280b80078038008000e580211800c0340610085100040c0c10108403034a003004127040b00030390034072140021500b0018007c42245e45502d04c41c0711030700d001c080030340345014008501600a50b4001c2040304400c036801105c5001085c0114205006c200d0710320760020135074080d6a424a082c55887d101d142c00e0 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 90812482 1250 90811232 90811243
    0x9090b030312011e0503031303030315080f0d031a031e01060b030c040302010f0e130902031c020a0b06030f0723101806080118050903040905070804030201060b030610080702 76
    0x32030840d400c07030310b0000c503100401c0300340c2050b00e042a0a0011145455070241903da0003214003204d01c400715030200380000b03402a04111000004510381012081e502c09034145452161032800001e500b184203400388c00d031b0385130083c000840d401018035511900e050020076070702d07110140407d000818100782d25011307003000e412020041000e412101d44904000070950002e500074801240030600c0d2409545085000315a0307401222801880800ea90750420000302c01f80903544400ca9150080f5058440c00da50303004c60340c0b4440e4005500407d089201c13031604400200003e01554840d6110401444200030000740800c1a00e14180240f001800c030b08408000b07a00d4001c0d045907000100c044001026640074040071182140703c103031401c0c4240d60340b0041d100d804007805000302d61640d03803645a206002542017542c024941204880ca420390740c0e6a0802240c40584008000078802e005100034568240103c2c005480b159240900d541401000103441109c0040d440d4284510140000c2225009120 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 90813732 1250 90812482 90812497
    0xf1008061203070b0f01050a0308040e0a1b0905041104080303010b0c150c030a0c0e03030d0209010c06050103030513090e1f0b10121808071b090e0105160c0309090b0303 74
    0x110390f25600d01e450103001d82c803000c54055041c8020b42000040d10301d07105072003008994000840350701d418103000d002e040c0d1401c02403c18211948503401070030740b038004410740a4200442e42d41d0600b50303402d0008106c150b0b0a000e00501d0307103090a01003030000c10070110840c2d0440300078080440d5944d40e10348e103c0381800103000041000d840e1541c10458511005001540701d010b040008024800c0040e038296905100c410040381c01d58000d001107a9104c1203503008050303418050401a0918502d690358100741e0317409800803400244049080035030343e4128011500984a081e1042c000c5802d580e0039280d46208a64161348004641132154041340300c168000401e80e0380c0900f64182c490b040040c040c10019100030024282d501e4440d40f511248480958211040d5020484901e41181170b100c842d560303c5204c8014921401c10400058400140c1c0310b4601009200e03400070a691902c1128201840300920b03002c4140404040304500103035004012000703841142d000080d03003020f520080f925600030b041 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 90814982 1250 90813732 90813769
    0x6070c1e0909050a030f05070f02060306060c03180301060f030b31060902030601050117060d1a01080d2604020d21020a050601060c030c0b1f0308090f0f100806 70
    0xa00c002c00d000c1d001c10340b04c0c8001d001e03880d501458201a0802c40d980d1180c43c1e40070f03040103c20041440146030060045401280c002d00a50078000702e1000d071810f5620500014405080c5240343e0081800c003070003114001c080d5590b030070090030300d541c03605001c80100030120840007001d51002c24002680b0801038044100a43d08021000424a41600101990001a4880c1c4180c000026140d0311580260b9850304080641440da80c65120520180c0d40c16907404940d100c42814001844d02c590500541c002c2917450000e00044500180143c044e410020400f2075406001440d500402c6041c240309800540c141e030241d10340c1d800342c14414010f03100d0041c0080d8101745192090b8003242d0008810000a009105a40c40d40e40d03114801c1e14800340150300203000c61100485203011400c28610b483e4080c0700d8001c088015201c0c2c0f0502c04d4500301c01c0d0412202c00307001045c8070219040042c000402d0000598480b942c40081a0009401c40c800c84059010880b40f10b0014400d5121948000b49003080b1382d = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 90816232 1250 90814982 90814991
    0xd05190f09180504020f0a060504170703060e0601030308011a0301030311120a110c0303040503060c0309010b130c02010b01030506010212070807020904060506130504021c022805010e06070c1e09 85
    0x601594040d03c01910b00360f1058404000c3c0703000302e14100801504540342e6441361480d1502e0b10380c01c0c0d41412906c0030303c079055020720b80001012039407900540e1540411343c00505000d40c11840c02514051041c2c2040018014001004150070410700440341907075054188915685c17050324010f40343c00d5040c440d2506039400403410301c1c12150010350300e9000030703914000d84444049803014140d0300e0143d48545640365001c44085a03c15252400854128072404008502080200040750342804c0500c540c888942e070390348107107290075420701c103140310780000346400d1145080200000350f4a03164000e0181c5c013080006901410003c50500302e400071a800f4140c418035103802d051010040c1811030f1040e01501c40d00c115642101018480c45108070781c0104643c88901e840d0001e8220380d116040102d0f0001c2d54903c94070008036103401290b40c4a01400401c2c88060b05000c00105480204800720b400741c9428800c15000500b0050346a00b5a5002c0c01d441c0c04015640b24220080c848541c0036424003480e0 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 90817482 1250 90816232 90816269
    0x1101020712051c05060307061407080c031305010305040b0601032315040c0503070815040e0a051b010f090b0906040315060510140d2013080d05190f09 66
    0x40030300710f07070709225107003920042c1c0003070b4408103540c8104c509a916070804d02080c010280200c80b0740c62108000d0107014140342151340d414010360310084a41d84942e2011400c801410b51042010740076040a2a0500160605540c0c1035198400500150f061648417455040b108034019100c0d90030f45c4102c00e400310142481075100303051610707004019000714280041540e80300c4c00b0702c04481c0903c400e95141805035880070821002407140c0000c059002c0d44a0700144110310f02004890a5280228040d107c050101060ba2042d45100810b09041c8045184080400c0c2c5c0c10a002c038003195a01164035a0b140b504800045192040ea08018006013613280c5070017544200786e0046058541c2902d9003408100c0c0c800d001d40d0043c8080c441d21510303d01c1000f1800750340300e081c0c100c0140103407094400302d4100d550007941d182a4110405100095080d01d03410028000104080b100d00b010508055150810511007070030701030031071141c000520102142050385640320350340e8903000348810b4205950700301c1e1 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 90818732 1250 90817482 90817487
    0xc031c0b0d080403120503070504090c0201060e010b09090721020702040905070803070318030c090903020a0204020417061e01050108040c0906090e01050901110301060e0f0a090506100507050d1101020712 89
    0x3c10301050300c9054603200d122002c0c5005504507401040c035515682d040500e0040340c00302601c1c8206401046540f01c2200180e41c100c0e605000340a08901c01e010ba40718160801844a008030041540d010000c40c29120216182c014000c000c2140280801580e1418140045400f4006900009207280f00b11000007501c410080042c000c8a4803d0750b9080c2000e80c0b0000d100740080145c007000e880100400d60030040c0b00556440401c1030340c42801990a61384503a00090101d82040d440a82d50340c40d107038408480c0000501106a11a14510711004003005028420300c81d50343c140a45d50500c00307800c01282c140040d100c44840100b9000c00244112511501d001f0060030b04040030000c0c66080c80d0102d02ea50388107005e00d10001c1e034400c0100307045038a07007881102c101036407024607130300120b8081c51440c080e00d4811002d4058030350004080348909042e810300c06a4183c040454040080912241c4001440410440701e680030625100501c2400819268028451041d000b80241c54040382040f030b054 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 90819982 1250 90818732 90818737
    0x20d1808031e010312050307020f0a0809100302120a09050a060c02160b09311515140d0b060d02070f0302061006050d1104081005011a0c031c0b0d08 65
    0x20200c0c25205440b400d12090129440c0c20701004102182e5102c403032141c103106d132001d1a0b003d1140c0c4111940114071840340e034104820717a1029a000e400003da0401c13a821703c5a545d1100b0705c1c080c6806c61801c0c903100c0001801e010040d0525202c6134031880c810003803003c104000404948c00c0303001048500c074ac603840a903403044000c101e107004528610002403908841c0007a5024124050400804551440415440c24103c03010101c1c0c070681c0444081e8541c0300e64803075143e0322075101112001c0a41080101c019010075017914a08004050b507a0300e0510b00078000307035a40307410907400206d0b2601840001882c02d019004048200390b2001c9035810034006107046204079540603400350b400c0e5850700c2a059a4035031f15806a41c01042d01003180c4110b0394010b500040190054802c17250400d51501c000390308007400c1c142c03e03003100f98942c0010310500d03071040e034808131504284110a01d080302001c810794580c016100c4000c035080042c1340c2000301c1c1e0540e13003001d228a074004028441e500e500385031032041d54 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 90821232 1250 90819982 90819991
    0xf090a0b0901090605102d050403051e030a050306040b06030906040605010501050307020a020118092d090b040f03030603080301180506060306010206010e100806010e07030b03011a04020d180803 85
    0x50500c400001a5506548102011744001525946ca12800306405a0f10440100880c840407003440c04490031421503000b528022000781d039596583d462840c10141e00d020700d080120800554003040e401d124150000845400091030308100e0348968903a00014014a049480950810000030030020f0f01e00700030a00c07138451445000e0801143e45c0f5400119002d0104981074405a403082855602540c083c102090740c60307114054125005880d107030303130700103850309031241402d60404a020310075600090050701c1070350381c070f80f020400c4a003072039407034908605102a1014040141c84200384081c180301ea0010405150030400b0a5940e50b900d02c3d95001902c00c04000c401d40d10f1030600402c0c010318058003141e000f904142d00810181e401d00708405403500c4060849200004101000902c4075400d0281d14001c104030382104d8241d140c0180041c090752800d491080c442e92601402c03841060b8403240e030031031000c426200140c58281c403251400c000d00e17039414644d50b41da503100035000411101100641c0306 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 90822482 1250 90821232 90821239
    0x10b060d060509090d05090f040207120503100806070504060518121b011d01030e03070b04050d09050316090506060d1505180705040905130b070c020301050c04050a12020f090a0b 78
    0x2140c0e90024285d4950640408000005070200f000c0300b040d01d4885401c405e1580014001458880f0b2907a03198561040820460080341c800320410000752080c2405500401440e0094403d920b0a1200102030748140d000b0041170050105007001112403040380048502406081c0b10081c0042440a0343d50b001d4100742540840c110004ea042c3c41c1d480380107117021000c024110000103001600055015014000700c4001e144000d2128001090924099a028030b008201602000002d03640041800c202900424080da2081041a5212018034080c2c4125688134000003001d0700c0b0040007da440c45400c0800410034102900c140070342c0307244a900740440d50221200051a1000340d02d90052500c00c80c0e00402140090008000082d01c540003075600c07850b00100926400f22541e282c021104048e542c04000681003d540011401d09104490b00800c9040c0004d090901c2c04c1c1c0090460121360007920407100142c2c0c1d82c0c2c81117445c0c448c1003010460005005501900c0c00e4a140d0f0004c160b160540ca20 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 90823732 1250 90822482 90822499
    0x1b02060604020d1112160507151122050108010501030e0d08060102070506040308030609070306030c06140417010903031d0a020d150c1e08040b06060304020a05030d05090108090d05070311010b060d0605 88
    0x181b05000e141180c04032a80914051000c800d100314481c02454817583c218201c4100b0011421003142001400c0311100c2c3c00d803c1865124180000103140c900143c1005040c18604007403400d00e09030001d070041070030742e840c0b0b0003240c69940c03200100d080c0034507544166041407021802000b002080800b542c0f15040c01c5c0c46c1708215944041c01101600da481c40050030100001c030050100a01c68800d505d40d10440c0088146496544c1109040000d000e0404500390307503541403510f04042e07041c001d0308011005c00e03420240d0b1044501c04542c480341e0f41c2000a104045410500003080028001c01ca00c1404244041101c0c05440388003509165444000100041090011b030320201c0c055030750940a181c0002e0005496500c2005104065001400a903481a80f0b610001910381e000c1114101d607030300d0313540d4907503c890760100050b00c28140604051070329000704202038045540b120903034000307641501e0b042e00b280e48244401401088400069500301c180003443c608440e1381c03034011900b01d0300c06413040b14 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 90824982 1250 90823732 90823771
    0x12010207030e03070e0708100308070606050415031104020a11010608070509130b010501030c050c010e070f0e01030b0718030c06090510050a020a0311010e100e011b02060604020d1112 80
    0x44c1c45800a0089461040001c0b01017250b981c441d16510794042c650310a1040859125101c010b450b4020b94012150300e501c6544c01c0c002c9003400e0280100800c08624102626401d42d92110700c15841512501e000d96030102d0100c40c154030a80304c441c203540510000304801902e032051943c58a2960180b40d024500240c0031582404421240410054004c40c00082c02d900746030046011b00b080004002c10000300b070269611800083c0314051241c3e000c6002000030500d82290f10101d03084580c030107190b80c5203041c010008196a9000c85900c090545003802650710550410349104070207402c054801d40d850750003c03580e2500202c014041e190102d4646068031030100c402c07140e5220360340c40d000058100240c40800207014015002d20200920000300c0c1224143c140741e454000042c18210807551200d0404550700c42c04e114405080c01c210030640d0720f902e00c031180a980c80744043d20060045a00141c001000492030b0300c025850410849140d81c2c4422100900050f00740030707030301004912218280e19 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 90826232 1250 90824982 90824989
    0xa21020702040e0d090e04020f100206070801150203070b040c0b030709030204110408190203030f0c06040204140f01121a0405010b012a06020f0903120403030816080619030212010207030e 82
    0x114202c001c0ea5100c12032800c00340440c1b80a08082c0080340c100003140301a102036038400320001c4490400d0f074010b0640380b070881c4005154a00607032081d031782a44000c004040c1c1c2d560200442c2c0009810031100d0103140c0b502c1ca0a21642001ca901c40c42e00f14401100b0701039000d42c0083c1800444c1d008540c06e0081c0007075103083c4502c0b840340b0300c00c20303040758070815a040e0003420203954010018002402e0342d083c142d000d808600194809200d0700d0b41da80082703040004518091054000e45c1050303461841d01880d007455214071b0700c1018018052205200e400580c100207400c194111078a114442040c03060805180c4a03005c2d0641c0062240490b200e0211000100c0c02480c4452240c0c00c900d1407054820115114100250310072516035041400402050010746c5041001c3d28051341d03403000c0195902d1039820000d1032504040c209610302ca1030a003c000740c445d400803905412010460303030b5815102d08240d045000c00ca5503840250002c50310040c15040c0201076002c2d203c064040e4680a40700003454040 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 90827338 1106 90826232 90826243
    0x31406060612270601170f010504050607050c07031b14090405060604090204060f030507030b0f070504180b130518030403021c2904061107110103020a21020702040e 72
    0x400038044010841f288803200d058000300b040b414180d0f241611a80c01400c02c2080140104000c0d0a541d4180a03c90046910110b200301052150242006006891050080341840c0c03502003070742030400d016961b00c502e5100340980120f80d2140100001803e1808080c2d0304150340341e1011400303a9a041e018405180200c00030101c20b8694508001a0100145465002840030041c8040c40303400c501910b0503a500345030b4001020306081d95050080500000e0181e0200301d80541c060031035003a0744014041e000860f07034500003001c5940010f0fa02c1c4200e05c4000e4203d40d8006400e100003980c448100e15041c404d1006001e40760200380508030b46170300e0b004035807140c1c0c580030180010000d4030700c0380c410b0100b0002d518905040064443c5882204103c0c00181416000907201c507070240324001100300350304841e112054000603e807a0b03000a4000075003c9004500e850380d0144442000070f030 = true := by decide +kernel

theorem cover : BRFrame.Cov 90647482 90827338 := by
  have h0 := BRFrame.cov_init 90647482
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 90647482 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 90647482 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 90647482 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 90647482 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 90647482 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 90647482 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 90647482 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 90647482 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 90647482 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 90647482 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 90647482 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 90647482 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 90647482 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 90647482 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 90647482 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 90647482 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 90647482 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 90647482 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 90647482 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 90647482 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 90647482 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 90647482 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 90647482 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 90647482 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 90647482 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 90647482 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 90647482 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 90647482 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 90647482 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 90647482 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 90647482 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 90647482 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 90647482 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 90647482 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 90647482 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 90647482 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 90647482 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 90647482 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 90647482 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 90647482 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 90647482 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 90647482 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 90647482 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 90647482 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 90647482 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 90647482 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 90647482 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 90647482 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 90647482 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 90647482 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 90647482 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 90647482 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 90647482 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 90647482 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 90647482 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 90647482 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 90647482 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 90647482 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 90647482 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 90647482 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 90647482 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 90647482 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 90647482 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 90647482 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 90647482 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 90647482 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 90647482 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 90647482 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 90647482 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 90647482 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 90647482 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 90647482 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 90647482 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 90647482 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 90647482 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 90647482 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 90647482 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 90647482 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 90647482 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 90647482 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 90647482 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 90647482 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 90647482 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 90647482 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 90647482 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 90647482 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 90647482 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 90647482 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 90647482 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 90647482 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 90647482 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 90647482 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 90647482 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 90647482 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 90647482 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 90647482 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 90647482 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 90647482 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 90647482 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 90647482 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 90647482 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 90647482 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 90647482 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 90647482 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 90647482 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 90647482 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 90647482 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 90647482 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 90647482 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 90647482 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 90647482 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 90647482 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 90647482 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 90647482 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 90647482 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 90647482 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 90647482 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 90647482 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 90647482 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 90647482 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 90647482 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 90647482 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 90647482 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 90647482 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 90647482 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 90647482 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 90647482 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 90647482 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 90647482 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 90647482 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 90647482 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 90647482 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 90647482 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 90647482 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 90647482 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 90647482 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 90647482 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 90647482 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 90647482 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 90647482 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 90647482 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 90647482 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 90647482 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 90647482 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 90647482 ≤ n) (h2 : n < 90827338) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
