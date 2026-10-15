-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_3922
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T11:03:53.948202+00:00
-- url     : https://prove2.me/submissions/c459d7cd-aea1-4aa4-b2ab-f581fed0afd6

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 705215827 ≤ n < 705395683 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 705217077 1250 705215827 705215831
    0x10303020109020a150828050c0c0c010503190b15070f031d0303030a020708092701150f0f0909020d021e09101805040c0f09090605030d0c02190314061e0a 68
    0xa95801c00741c2070401003a0300d80c11f5031403c00043c003440740301c8400100171414950040b1114001c2010055600d40011071b455886140304201a150030384187d0031a2170041001072400d10f125440300500820b64109500603100340040d0301c0c41030308040d0054104c0309040362403102400c1e016285000280c0d60710008051040d07058010407502e04225030101038900c079200c014401511011030a030303200d000d80b86030042c080d2070034510380000a901201c06136080b090b500c20369800c40c2915201805035042440b42041c0b20400c82550f01c00039503403420f4400350005006450000d6500c02c88243e0340001c0009a940c00000b00500300300c0210300d980c0781142042c4810250410750185034260702040c0c440e4403039500140d0018106003540540c660301c0080c003803204000d51501200c0b035403a056403e049a1403070090b103405600c0800604409030080041001c1a0310091000703044101c5000040c0001886074422a504807200e030708011182710a01100340e114101400050f00e14601001c1001e010402601c608004c035 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 705218327 1250 705217077 705217111
    0x4150e04060e01030506101203080604200f130f0605070f080903060c0306180103120c24020c100b09220b0711010c030506060d0221010303020109020a1508 68
    0x185903904140700820200358240102d40e50303030410580b118412510310f40204190240880c014841c40766580056070150b9402020f540e0b1001400014034460360301880301001040340f5006510b4070401001c582940710703a0740b5282c2c0440000800308506541203010701443d6140280101d81e03000003518010750f007000400036400c0d800c1c20710944511070003060030b405000304000c00c0880f00c80c400017140a15400c0e628a10740780c80200c0e5400100d402804000d002c541c4c1c0044850100f13100396880503c250240401c00d444010131924007062101542810030701e685c002c100321291044c24080b0b0002c1410603501403142001d10f82c000f4006000040841000c0741242e8100310a20200c2c91110300c14640c0082900310904044a0103041d07140a010fa0040707940c280380284010390f20900440340110b1010344491704080d41400c5010181d00300d64420f15880c580380e42c2940c18080304801c00d5008501075000003c1032026801030180c50074842d004a0b2064900030844007445902044c8550310480030705051440d6 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 705219577 1250 705218327 705218329
    0x20d1e03050c0f040e040308220305210129071110050903061003020a08160509060103021215041407120902010320191103030a05060a270b010504150e 66
    0x70b40182d44000700f0b44600440c01184404543d01c0c0240514041c0d280e0b03140c070350340c1c4032540d954524080c0706074a005801e61010703c000a0103400581001c95803030350441c41400700c80003c0b0b02080c0d001da019002c400c040000c000c2c40088803503014040001d02044062502c42962603191088089440341ca02980c130704040d65800c644074a00342d0300102802402c4e2003860030103510b00c800d14002404141e218030010b0b6400907202000145001840000b4050075a07043c0c6008104083e500c00144880e0505400b0407080482d00182ca5401d440f03112051040c05d000004030040c04110f601544001100342500000d00c06850307005804030443b070007840e9003c07071a408a480100c0280070710180e160584641e40180c0e04803070302014050f1441400c83d05c001d00e0180c3c15064100c0b03000c48201001e850360341041001c0b8001c8145900482c0d0702850107016400310558640943c031642d1100c0ca100c0400301b405c40d1400207100f441e0700650030011000d182903030401d410100c000c4078031001c440d107400901140650500003 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 705220827 1250 705219577 705219601
    0x10c0c1709120618030901021f0f0606050a02150609130204110f0703031b0e19050303030a0903030b1813051c020a02010f1407080307230a020d1e0305 66
    0x21030809058070b02a01902e00b08240d0307401c01501d0408920072120aa409003078000000e03541103800590050140805003002601103500340381c481500507490341514421201c082c05454014956690751640d02c0088660007030408801801308000c01e0411000d006155550043c0c01d908070000c0e80c000502900d862002030024110228448480200400d00110b01c0d006140a419028082c1d00d00303000c4213554211000e046118071210740042100013805452030308151300020108a850358010712259160b10001e40f868004403000d021845e250003c480426038940242d0180300015144c203e0142d400c142d00e528440402000700350894058030300c1c0313811f011080000702508008a541d101116050f82c0009484541c003082c2680443c50640000c852030f4850480704469003a68440c8038102404c1d5038804903281d20161411307003004014120600080302410264034401480c400d0103a07a1016000042e0400c01d04030040418042105e0742c019160451410070b003130011480c07600203000e0340c449148500d = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 705222077 1250 705220827 705220837
    0x6080a031b020904061a0a030b011719060605120307030c030f050717070c081506040b01050d020d09060c030b0603040206031003080406170a0c20011d0105060a0602010c0c17 76
    0x984400c150f03040c00140802640007100300c2d03005100c400d00149180c42442402405444000c0c00803203104010441f480c00c1c012017903500d000c100140c8402824840c148a044040544140c0e4130540c3c07298100103910b03241030410603800300341e0059800c0031b00740e440c050842d9903110700140901440c185181c903030358170840403030702039940c090401108026050051911a003040314221541c1d14880e20114441500080f0700740c110100d05500e040566460040c0400740044603141410320400340000e03000a41580041d20100050203c005000d5003141024803d84089903100c1d41418644042c00e40941c40d001c0403070750b0181e01661440d0307680d200c5400003407420815034000303058034a000c2008102c00d903010300c00507004401c0c400d0340307150358854000fa5005c0704c002c00e00ca0004542e114004a076a400004001082c50040c1d034000240c56400b0304201741c019403c0c50404055075035031400c000c1030380b42c1102d03050003404881c07008028155078054060000304809201900380c0c0c2e0200007c0e0b4220b803600d401c444e = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 705223327 1250 705222077 705222079
    0x6092102060d020d0b19080a03110114090c0112020a0f0e1c0b07120b061909051c06050108150f04110d0f0b0f0f0711030f040b030106080a06080a031b02 67
    0x15922150340709004014045d04024622800c40c1c24980c800b5420640ba102c4191206040544a60365059605486203c1d400804030400d540360a224441e103041001c1c0035201d1464100a441d02c0e80101000400c00c0c0e10b9114800c01340c500c18040007551f250700101003000303241c0a0030458483c541400005e800d40a200340c580001000f0440003200300b00701c1d058880d01600c240e860701d0103040d000c1f80c0b070102500d4000c403400d078002c001409848180d2900b02c0c520002803001c1d05060408580380c1c0c0129441d440c039404844800b6507101e0400702084124802d02c0d00510a0708007400030409188940c2142080c041c03c850000280340d400f060a00c400024100b40c003000040110050008074a8000c9003441411010303a1700c00f521400191071300c0c490750045031040ca262100d413005641d4040d001d84140c0d140207244192848188001044412508000e0000d022111030460301d07503152450080402400030310000c030306414080100320b0080700242d100c42c1160f060400f5540080410074594540f01020006 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 705224577 1250 705223327 705223331
    0x260102040603020a110705030604081b060916170601150207080607170f04030806190b0c06010e01051e0f04092a050d0203330709050a06092102060d 65
    0xa003564060f03005003011055521024410012801010f0700e54030184a41a05a0030000000d40040c40300d0005241c0401080e00400c0d440310000c0045140110407182d5000f00d078448102100080c40101210008021041c2030221403560441515224113044c03184840e241011040c16404038020710401010b000e807002103402030324041c05c00906542845ca96090340314607102c0401e2100302060704c61031059801da10b580c483e03916071f141401406503003041000c0c0d84800e0040d0100d87d0151010081c5440f80c000d0005042950410700c00310700e00383d81a4415032140c2144000c6209104100700082c0420608461903446941c0b003101160151004da20007d00481c0c0b01e00c62240d0b803880804004904080300c00c04221459107070024450160b604c1b000107589540003025402400704500d40400100303d03015007448131425205070030141c1030001d13101d0701c001c91040081813026090003040e600c020410ba00d0030042803440d01211010840c0c8007000388003121810350a03042591548411240c880f09070481c2 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 705225827 1250 705224577 705224579
    0x4080f0a02032104030c021e0a0902030405010506011e05030c0d0e030703030509010b2803140f0c0901240905031e0118052a030a060c1209030926010204 67
    0xd480758400c0c00320701c20728101c3c500003418030f030650049148901d5040d02c4002c0954495000c1000d082041000c09004040c00315130740c105902c6404c0c0301e1000704071492016860b0f046c9441c0250a50b030740284080d04210070080600f5681e44900c0c94000508501c0c28a0382e9262075000d400410741c41119040010030b0300b130841090a9410000c001d001c0c2e14020703139081110b501ca6800b841c0c20f0b560b0700c00380d0540c084403101c00c0024030b03034201d8251702c2c054826403413107040c00365243d4806011018404804000350002c0e07640400c168418454001404070407614501e8541c10f04420000120b18100e4090348140800200b0004034000c0003e84090300d0f0081c112860250a5458181c600d10540c9804405500340039070072403007101003040c0085082c3d200c1d014108180b12040105041c0400641e01c03084014008100b223015141480290501c2c4c2c0601c0700484c0b0503c20b01c030041c014914006078080d01d40d00e00f040c4c000209511480300010344032000000401c500d0301c940152074500d440d05001d070140d4400a8 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 705227077 1250 705225827 705225847
    0x601230c0109031125051c02130204030b01090204061209050c03070806010602120f0a050903100f02190c030c03140f0c01060509130c0e0c0f07050d0815010c0b04080f 73
    0x4444d00103080700307411215080008401c002415030004203a4407100d101d00400e1010380b40507020b5075040f0341c0da500c29181507040c036000140071003a01c145d40d00f000c5074006010f00c1071103404e01c151400341820b040c00350301c0c140c0b5200c802081e00c1040c1519482465880005408116040c003220303160400050846082c40d4445a007103850390001c1c800c203000351180c05103807140c401440c403d4a40701046070440703505141d0110400d8500780d02081c000780d80743c040c892030b005140c05140319005502049080050b11111319592481c1400d2460900409000d000030714071000035841450200c2081e03151610051003c044440c0041c9402446100e9003a010089050906a48150b220300b00b1550701310740c06040ea07158814804c04049800d4402303024011517040521000e491100d00d103400c810800b00301031410006054484080d080b07000200c4558210000c102c06030303540b0900d010303084203d0302019040700da00400040d10195141c4c0e40140310450140000302444182030550b42011841c0c01b03036580d1440d55103 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 705228327 1250 705227077 705227087
    0x702090405100f11120403090503190c06030902130c030e0a151401061205070e040c2102161514040b10080d200c10030603060b090601230c010903 64
    0x7030b001002850019802002a41030280001802698207103614240d80c0b001c1c011540c2c0c200900580c02d00060307650008181e20100408a00303104456849040800649000803400c0400e6006400301401c1c814a00c015a860210038015038410301000940003c854205901030901158031100c1400348509140034081030910b020321074407500b103013005000c2180140340a680d40a000d100000b500e106404903404107140d00240d00034006007020103007200400001019520b112030090b0004103440205800c03851800b400500800c0e801c4815420141000080b0740d002c103003450054100e4069508204640308281d21030201c001c505c076429410341c5481d080c000408a000e41d01002e218510401c0094540c5003c00c4069004c0026a16070580c0c10340018030f0300d2440f1403400c100031103000750882214159104070300d41f007001030140c03000b00710f0740d18500304601114046840c0700e0003030300107074100011680c0c0801e5410707540d80400402c01c4141c81c405c50032403050103400d82054641d1310346030719881815000 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 705229577 1250 705228327 705228343
    0x9010b040503070806010b1603110304230901150c0f0605040c05010f0c03090608040836030f030703051b06042d110621190b0603090a0b0c0702090405 66
    0x103400b00c60f42d107030f40c6140050780c6110034800c2119402c414420340d40b114016085504801d8000d281807903218514070750f0340e82103500c554032040a04041e07014070000012190152001c2650803951a240b640c5052195000c891030103c0070410440003450341d400300048103910010140d001801003099151500e09910701950600403540480e0952014030181131080b0400210342d641503460986180c540310043d52100c001400c11660380e001404440d0f607080f0b98809801528104491301042c1d061604100b81d8813002e640c0d900c5019800c40b241d801c072103000c00400c5400031a4140b416507030380d12001015400200304190010500d01900c420700c8103000a4481d80f0702c3c5003c03001c05c0c1c02800022890408001c07030411500812080080410510501c0d01d14050007411400766110700d02c0071124140614000c10498540a032006096000b03000300e86030740f0a008600300142c410300d02e1401c1048080341d40d52072507000203100d03249110001d04816141410350380368a601030010f043d24246464074a8490342e038 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 705230827 1250 705229577 705229579
    0xd110c0708070b04060914040b04090b040c14060f13120807020a060921051f06140301052206060302090c0a1706060a032a022a01120c020c09010b0405 66
    0x514a80443c210030b00404440c12107606880d990300043c9400306002005513001c03203441e8010707914201c02a05440b80d011300c41000307200d220b05404c00c0c07915251804110401703030062880c6030078000a04541d512001c00300c9610050251241c0d4640200c0c080070700c01d05e90709410a002507840c0404120030801282c0182185901c22592400703115240d080c200c1e40d4403500c2c42a40e001001086103075503d01e100c01115002c250040c800c0e01d1003403002020030040025110300410700295a1002000ba40540144c4416601000c40c000d20007410260049054100c1a901a0300d06035481000798003003041a13401b44e8011030b4080e120010900d0200600507440e00031100400124010b1004685c124244002c854842c000c000c101d14104031030303031a0460003070403c2001d1412007500032039051840074044850802e17039502136009090340700140c25100c2c01ca8880d2143d240d1258170b00d908141b0540c0c1c2105007486071050100c030024800c0300c5c00004900e040400c0210503004203040f03001251034440503004100707940c4 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 705232077 1250 705230827 705230833
    0x313090605060a05070210090e0c0406200c091302040603030f020118021c060f0207060c021905060f090307200a051f050c0f01021204030f0f020c060d110c0708 70
    0x76403542481400e11815110000090040140314014540906100c07a4200c1a1030103840c1c040c2c13207000180a0301e4003a04e40c6003024401040c2000b103564440c268892001100803401e080f03217082e1300700c00e5036403200c041a41d102d14004000035a0310445224240d00f4242c00a00a00095a5074240a000020349180100c0103508003200340034254002d4a444001a40c06411081d024607c6480071580c8400c040e0129a06a210710401200a100e4006007010034000e0000103901554004040c2c138080450810f003c040c011013691502040011560503400848032848480556545206d01d04510642c04000c11401d03841c3c2c004a07406c0c14980072200f01d000c040c0d034106800b60301d42040190000c611882d1440f4160b0b88101c18100a00c218060421b82032280c040f101c1d003038107001200c2d0a98000e0140043c680359480c04100c2816400441680d03402403e00b0078800000910784004d4881c0031181c80140600d000003502c0d011091143d2000021031030392940b40382c0729090f500815403580002d125821080c4 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 705233327 1250 705232077 705232079
    0x2030705120a1d0a030f1b0f05010c031503170a0309140106050f0a140f0604030209011805150141030a050114010c031202190c12020601051003091403130906 69
    0x40000b401c1c14138940c0549890032101c4502400312003918540c1c0c01c400c0c420444110380d40000b001e007108103155070b20030030010032000908030000702114180084020500c41421042000c610020f85660100200528480d51010610340035006800181c1e8020305032000c01d0f80d00c081424040d3711840c20b41e0000c480410000655504209260505000b558961100a0014070365880d15480c0002c14840c040c0c0228101035894000440da403009901c00354840e070840c1b0b4403c400760b00ca03200341a84141810860300200140d0b20008210342020100c1450a0307111090003110340d504040741c0034041041f0f507040e4084000c1e0f88c6c0134088d1a00207403050420b542c1000004107159801c19460041c842c4182d4811042074160345007180d00c4008044201a510303805c1001e41d5600421051408010410303840f05180d01425141500c145d00c000d40f15001190031500060020780c0d10200d0200d00004645000f2030940c0440c105014400c001c00052145488001042c64000c440c8a4100b0120ba03608082000300c1d0b = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 705234577 1250 705233327 705233381
    0x1200c0d06020a200322380f030a0c0c020916080c0403051914060109061e290c0303070c03081b120705130b09040c0216030602030705120a 61
    0xb0050b5428101c4c0c55041444280c00715a80c42c40c1d104460209892180f05603640c583c2414034000c41c51039001c1000c40c1e00101a1540030b8144c0c46000c40303554445040d0714003400f9054590071800050054090281c0703610340d0310101d511540301e90b807500b500141500030720300300b0308400484142d0101402c03005c60040d8001070210b00000066800702c94109000d003141c4d49805d01015006070422000f1106528000e420f841040001c0001e00e0181c0f003c03290000d01030b41485407a84012600345000c2c13462592542007444517000560701100b00a8001c0c400401012041c011525107000e0020300c41d40d1071001204200074a0303840782c01d4801c1c09009031601d002d00c0e252690b660454040c488034210000c2d00400c018107040e01c01220040d03020a19141450404000303e0408003400031715072202070880700c00700c0c00722024034103442855803a08603400100507000400c080000303442501d00c4003400e21036001c400115001d0144044450003c40c24038408030030f2414031003a000601012208100c180d000788280091 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 705235827 1250 705234577 705234617
    0x5011505210c0d050f010e01050618101a0d02130905010e01060207121e030e0307091a1005040b0a0c11010c0b061011030a020a120e01200c0d06020a 65
    0x4002207040544040162001840380040b20300808460920400846100400082c0301d0400703040181740000c11039052090400100240030f1000c10b0b0303403024260500541600c48c4004100301c0c1d5000f00c40f5138400d28140d1a203ca2405803149040000b4000140450310441801444055036103660081085036251506070000d648240590700259000c0c5506009400c1549039510756140b0801c0440790070f002c071410340854164120f9048012a100c2c080b648007510f400d1040d8030103410301c61410485110740b080040c00d0f0861040c0c89901070411900080c0c0382c00d00c51001c480203441e40080c074a03070300c03021840c00030000b549400042d517035290102c013a0700c40c541c400c0345840c070490b0f004981000b071138a0b04010003030794080404c0200f051000311038210807803500a0000d03010000032500038000201403818210f01112012100b4070401800b07101d05091683c020b1403040c7c0241526035a2402c4411034503105207010301c60524141d0102c51080c14008010198006121080d00c90b0750303102801c0141e00c04001 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 705237077 1250 705235827 705235879
    0xc170a0305070305090a0b070305090f010806030d0806030f0304080604030e0901031a061306120c1a1909050a090f0f11042102040c0305040302060c07080403030e0d05011505 76
    0x20009000b00403140100340700d000a00142c8800400001c41c40760340d04105c29199006403030403400320b000803450042615080380102d115440030709100174a4500720001a0721220a024680140316168001c103819440400c4071640055494080300da4480c0c840501590766001210f0450000d02c5002d040c0d0030606000204504a96102c000b928507aa44500341081e1410000c0410f40c0003c00344142058402c140d005e40b60081c4a907121910840200341401400d401141c1c000003a01e8402c01d9001d0460455101207400131012001e140c04210300d000f008031020101e0ba81b00c16480380d010346010840b81c1503035001694440c80d6034802c0108900c014120001d6560790084605511414001001564054140500034007040484898a01200e80c00507040300c820203864800240d64070104810580c04000c2c958200850b40c5c902c505286a0340c0d030314509807180b0b000040422400016a0035591102981d003411154000d000b844180385a00025074500010310840307200740300c82000828038505c544400c0b6 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 705238327 1250 705237077 705237083
    0x201020c07061e020102040e0c07020f090f15060c0606150403170d0c020d0c03030f02070b1e07020a08070303020a3015050a1401090f0e06030c01030b0d0605041b030c170a 75
    0x703688c9968210700c480302c94006800580c3c1040c1d12a041411310385d111a501482070100504891032424102c01401d0302d56042540180030f1001003244c00084c20b40000c00990002003103443c2c03603800552401100c1d16004e0340d80b00605649403c1e400c401d00708400300161102d02d034005810001402c403040708a070388221004070300300429406602240841c1c401c1e08040e01003945080090300d8280071359641038449100b2034800311025401d44d80500401201481d0b0368002c422840200010241503e5582c242e00c5006801824194001103040c0382c80c1c00303101c1c0c0b48224a80da920b03010590060000d071450407001114820f4025140c103100700c240c1c0f0354524640c801d8607000f40c000000700d4100810324021030b155504c0203041c01201180000c40c25004000b41014109140d00c0c0b140307a041401c2450702d424101d52a560605007032644005a0752201d4000c2486180c10003000714080d140c608108035440e04070080803a0300141d011010051003491784442040710044203c4614071280d0001c0c80da100c0701011030013 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 705239577 1250 705238327 705238349
    0x206070f15110901080f2a04032003031206030a020406080f0105010e010f03060906060b0c070e01060219021c1202010e060903040f0e0709261b030601060f0201020c07061e02010204 79
    0x11800d440c0380d0511290388a80440d0002c03400c07c1e000519542c4800302548012825000001d0600402c040034107400b8044446442c00101e81002c54002601d90180034090300900040e000028800c2d42d0400038002a140c01800400070345803582d07640d0f0740312445000340088942c00c3c400001810740300a88418120398035401c14241040c01c55907404050001b000d004d5038800e403201c9000c01c1c00702514008000d4020f826000f44031441c0b5180c02003145100503030001c0c09640107090346000406c2d203078808035a0340743c0c125400c903803c990001d80798410f244e8202c0080e0443c5c0050b0f0521180c03d80551184210700703660b2044850030b5580001c995a0b80c4114011070000c84a508010480c1201c2400c1d410b8200d030846c10b001d841c403600c5078003000c54a070001c1c044201182802c0c940c2c070a041410721240c01d07610100d040b032008400800021a0f9030305010f119280c200028540c0614445100b035068800306c46611f0300741c900c020741c1d42100616078001248c410b41c44c81c461114a804003401442290100d034003a050f8 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 705240827 1250 705239577 705239581
    0x1180c031109040210050f07061526031e0c06040c080114090c0105070f0b0f071101020a0e010e0d3005120103110109151d010207030201080604090206070f1511090108 73
    0xb041b1155000340e11050609201840b0250016946000347e9907012140c65821014500d0102c001000e61407001c89180c00140050441200c0e0801004440c03600c44288140d4280003042c00703c0c0c5d0000d10984c111440b01f40140c1e410b000c100080390b0810000c9844120081c80070601c02041802c4101054400504d144d10080d50300a041d40190082c0c0b160b20301400c1c41b601842c1c0d06898501c4200fa0840d00005e07040c0308441000741d181e0f00000c1d0307102c4001181c4004c5080140300a40500a900d01c0c040480c10b02c0808a00d102c810781e41c82ca078503283c00d0341c001d9401000110008403400e0084030b055035080200b03120aa240840c4e1710030760a44501d460544c4404a9076465900d1b1882612044003203681080b1040c0340115201518000b680c048a42c1507039000744164007141641003030005441c1041c11504200d1003080540e80c803800898010303504450003e045801413000501e02d109038500181404900d2030403a050201e120240e4481c0520101c0a00090004c40040c11080c410500301d207011034440c0300 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 705242077 1250 705240827 705240859
    0x5100210050901110c0307030318031b050f010e010207260304080d0b06162a3503190c0218040501090602220503010203010b040e04030201180c0311090402 68
    0x4070350840e4020000052180000354100600d0384100e001c0d03001d5138000a0b2403c10943d15100d0550300200e0320004103128280360340c00400060000f07070100e136a803051165400034058148040c0c0f14060011001300319031203600a855000c1c0d0000d4030282c0d034030940c400d0000118bd099400b01000c0320b036060809451540d860380c500460f500160387c0c00c10fa603aa160024405034803400c0080c02410ba80c0461880c90700031a1600b4043c0030015070090404030310340302c3e1100c1d0884050341040103560200b4105483d1003880e0050915102400101000801800c040201c2284c004070062024070303050003a142d0003c403501c401741e5400d550340c0d50094000c0503081d5003501c074140c08602c0705c0e00948508000326a2113013640729a0240d0b040340c04040140d901c50301540c440c42da080c00c4150000c150550003581550716101d01405540124401c40c00000c50390701c0001d082520030341c03080c42c0742a2412808161101c55003801c0862803414041120b5031003040c068541a860701c0d1306254030869000f08000b16400b9052 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 705243327 1250 705242077 705242081
    0xc0405101d0606041e0b040308030108012f0d1b030e0d0e0a0902030c09360603250f090501060845060103050307020f010507170f0c01020a020f0705100210 68
    0xc44080902c460206e408036011005100031405035a816480754101070a2500b10360b454040448802c40790900303140c9a03070484113110f0b02240034000580d1030ba82030300216800390002c40030024244401c64680d100082d016404440c40e9110300701103880c41c1108000039a1190050008141d000d04812000c03c2080110b13001107901040d003580181c202034400700820316121003c481895044000c041ca480c545940904101d610364800c1007860035800d0003808243c03220041b401c2c1042c00000d0b118004400c8000300149002032841d08880313030704290b40e01d454100610027801680d000682c8bd0011072070b441d10000e801030b2110000701c110002d440d0200207110340910019041c0003011018003140c0354800d401d001c1c040c0214042d4000d5035030b0300c505104201c3e007001240045818042d080c490800845e800c0100d280c2100d00c40c619460340c910b81080e5056072805020855610b56000042c24a04294041010081101440200e41c2001d440701c00704010440580340010050303200c01083c8400040c16 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 705244577 1250 705243327 705243359
    0xe09100509161203272c010b030c091801030615050102100f11160c0b040e15010302250201021c1205060a050a030b070905042c0c0405101d060604 64
    0x607003403543c01c0e08400100500151484008404034054140c0708120460750360342681c4844042900041c080c0740c04004180076191b040c05041001880440003400c1000050226a413041c401495086071000507214007010724800d0004560761400d20f00d1190241810301a4902592016006040c010088031100c000401e15460b0040b1000d84650248100003800f01c005c20f54032490807822250a81d07035040000001140c0c3d4894540400d04000401902c0094550144c0120072144450015858480100c029001d4025112032100382044c3c414641041c105080c1d241c28401e07002d0b2030358500140d100d04410381e003100c030010124010b10180c00d00c410443c1d001984c040303401010304e01e07136035151360120b080d81d00b460300100e0301e403001c80c0c00b4440481c1c1c100044000501e400c0f03400b032089070030845400c2c50724000740710719003428a2401a003201c020f02c2071146d002d40d9100500200014503002442d400c0b24007107881001e5003800143c40c0449085030b14a070f032500c11035018100d51f2809240c45041000c0440d2 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 705245827 1250 705244577 705244583
    0xf12110a060507020f0d2a08030415180f0b0909090a1203090f08030c031014010c030507020f15030a0f02040f03020d080408030d050402120303100608090102040e091005091612 77
    0x25500086d00002ca4403c3c4c80c009112100340301e00003021000344c10016248103030300080840c1e801488100582c04140c035141040b00203510741843c00c14101141c0103800240350300021031801c03030b560010501c049903a000d0859494100c510031550344032241c00584071081a080582400c07041202030307048078003d410040c0028410040502c0804c2c3ca51520100bd40081d101003000c1c40000007030040703d060020b041c1d805404498100c1031084074110010b0141030484200509208000c80c400056503203010008002030006416404543c07614025081d40f0fa0048071003064807441c194000d52041030b144280e409803804c0c400620521030a41d020004529980d0000315070358503080001096500040c006840030500245010489040a10411200c0e05240700004c425500510800c4a090041c81003441280c40301d08004500d52100180e4901910a40d001161403007000300c28044a0100041c49900c60f2880100c1003140c2d803184000c0e16201d00e104100f495800c0300e040402e110b0307100c450191b0030040e84 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 705247077 1250 705245827 705245839
    0x161203122f3613050601020c06130311130906050109150b071e0c0807080613080915041706040b010504090b1501090f031a070203040f060e0a0f12110a060507020f 71
    0x40c0e007000040b244100d0b8406443c01640711814000d080d41c0401c4400c10140040b50802d0070940d0000f4101c40c0c420a0703200242040700030000400c541c3e01d554603a809a08103600d42840920b00314117003280900303028490103003214a81a03c00d180940081003040640c3c5240c180f651810300340381c4481080d03002c07206150169140303407240000068100070200d8001c154034000b0b0412180780812050030700c01d00170300640b00c610b1030280c47d000140240e01142d2150300304031180c1500c000328210700801c5000360341140c03a012450b1141c040c2100c2c0c000414911440c41030075480a50382c1c90394141b00586080c14002400c10b001540480c0455008400c41448000185010707210155940c0c440f00d10004164003d03a01c04601040044143c0904211242d03c14002d0000390300d000c0c5401245107003000c80c0d205102c10000c0c41d031165201c980e20446410011b018040d40480c44540352201106020120001140e40305444404082d850408441c41300071038105031245410580c0c1078082c072030120702401950b0380c001 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 705248327 1250 705247077 705247177
    0xa0e03030d060f1505030c1204031e03060f1401020307080307051608071103160b0a03020c07080129030a290f0a060503161203122f 58
    0xc146100d003500034400c2c50107441c0e0079803404441e191407044e1210190200304042040107040c031081e9040380c4904514410f041400c0d03455060031140180841e05001c08102c9010300081071a91640001c0155008004d0a2103e03503681c105040410f04140010350150b041885044003282c8104061580310401d03040681c07601400c4c081e0009200085041190009030110b40c8005000d5550707404a40790700260300410a0100006050501d01f4a51080d0302d6030000020303441c08080d00c41e0b0151040d0004400c122280d407925050707201d010f04180320403100310b42d40c1c5c1d06000c1c1e4185c03c1c0001c0390f000c500025001d007075070140036100c041020604100201e00070301841056505118441009480385842c100201c91500707045d003541e41aa101d59105070f02c40c0d840420281c048002c94051002111341c20f01d003e000c01e41c0c0c185800d5560002c00c00d02c1c0e00700d02c0c1c5441c1007240038090140541c10605012101d03078110038589248a451070055040115111a01d000841903050101c00b054000143c01c1c517011582c4 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 705249577 1250 705248327 705248347
    0x6060907112103041101081b0d09020a0e07110604080a0309060212090a02010909020406081303020f070e04210c02010e032d0c01080609070c020f090a020705070b0f0a0e0303 76
    0x2030b4803080501403900c0c0c004108000d21101402d00c01401000346004600d60030482903910130340345603034810344a401700059064401c1d41554044a1400e501911088000f89d0302d0090318259442110703503801050b00d00030903800307260010410902c9160301107002c40c181524100b0840050665140c00c03a81150f08100f00c4681401d8040f455109010703510007003900d41404e100042294409500401c0414010302040c00b40c2c0b900000066401a58050350203405600e50804030f1502c00c01050046960044100200d0b0107514280c2c03580c4610700544040c12540f03400c44140000040340c04020700040c0801d1a03000043d0f02c9540c4400c149030004044420130441c0c0e402444007403204840c90407924a8898088824034014443c2480450007428034581c6403810300c000c2140c41c00000d0145c0304000980401c0005c540e5006004d1400c000064515011490295141c3d8000d5000c180140c0f454854054005a5048000111504400071b10304080c186181c8140550b0195003030141c0c0fa50500050103130b815a = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 705250827 1250 705249577 705249613
    0x305060105091239061c050115020d050703090b0c1e0f070902041d1305061e1f1a0f0307030b090a0b06071103010209030109051c020606090711 63
    0x144071036400240101c24900d480807a03151408003482c20001340c0640303800c941d43c810701d00b511003807880582c0c58030741e5072103e03105060b0001c11030081500f005240c5000800d1400501c420300100380d40799001c8a800c10301020003a00c2c1e9010b00b4600400044001c4824426030848402030070310306810108491008188014541001510491782450350b400445501c1005808021138002040c0c1800218031700b80c1407071090300340103210203a01045200420042074689200650140705aa080400e40e90b0314100780c4e402a0207190481a100c80b14900303000420a80b401c40c0c0911041010540e6a110b265803038480d640059402070580c0f0f0500501c107201c403a41c1080c4590055108403400c0d5400510307400c20b542044003022020f00103200c0c1920303044440c189910b88008a44129030000d00c90001040e4480c0000c1c06845040d020581550801d6002c0003000b030001006070500301340b006009801210b44408990746c034001c803a6194041c04000c041042c6074041c403200c1108600f41c5050f10342d4000713002e02c1c04072 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 705252077 1250 705250827 705250849
    0x1103070f020a4404090b0d050f0a0303060504020a120e0106051207170f100b1c230d0516030e0d03180b070f150f14010305060c0703050a030506010509 66
    0x101d03104600341d00080028004400f107409105003260500401d50f8050701d88141c06079004420300c466035401c41d900789035150760050035034941c088229500e0315040e402d055191010f2510490200b420980045450f01c3c00e8000e44280114a07603070200302e224484241805020f600002038000e560b0f80c0400724080d00c41c0c2c8100c0c01c09030903640090048503e0304410b040781e245143c01c4400d890b000445580104400468500c00400402201054400c024000640c644048040440c00c1079031180c01ca008100e007819000764035090210204400a20445110380c85111200d40307400003d408105040010300300705010005907001e07241a8090a01c00c1010030061000e0300001d0700440c41000941d002e81881e0361015000c3c11845125909010302a038a014520503010402820031404580d00170002c0e6481d03119100c81e09000e0300600501d800c4203510000701c00203000a44460180e5400074642d02c02c0e0104a070b54607503042e52114907103132914070120021309025140754100b0104021800315030391114101c0c4 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 705253327 1250 705252077 705252113
    0xe01050915031e07020616021507080402010906020d050f03100b0408100f110405011d1f020c060301030206070b0921030708100e01140105040b190207091103070f020a 73
    0x20354038109818900c42452525012503c2d80d0040000c20071599800b00f460703a00308158041907a0030030811441a410a544619401000001c400800003600d0b801007050703008038000c0c2c0701c0c038501d00c2c1c640d10100d85480c03600b82c100d4003040007002031061500c1120002c6030b1050891242c018225203a0071409001e500a51040809901c945030f04001036009106220151940c00300410903e000031100300c2d040e029501c207080c107102400150340b01c10f030720710448118601e07001480451071182e01d2851510b00710039118820014810460b0381c40075400e0020459058a4004016a042000e01d9480e1024100014904421806600740c07440c07510200500c1c411401840d1049151645480d103401051218000c042450480202804002c0120f03c40e41041c1502d00e0b15969000a40340702c001a10940300795800b80710584000200100c0c80c183c8112920200b0840d035003500c03091555030382c01d041038030a607407080d500c10141040460301043c0610815028141c007401558034950317442d1140070004042081c6030b = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 705254577 1250 705253327 705253369
    0x90613030501150909030e01030506122b170103240908070212210904060e01090e010e0a050c0907170f180114040611040e0901140a02040b0a0e010509 66
    0x203240343c600b4444000036240a41e020001d620132900c1c001c1418481548050501d950703500030519075115207602890b42c8500c44100e03907404804208003072141113006131001304261000b4614440c14440c00d410380c01965045c02c09001d503400c5450b00110078154010200d803058101c0d56800300340076280150070300309010340c51540d03d40d8018018003500d005100590b009682101060425680d0706404824480e04036448154132a0b40711030200d0002c11480c2c02828035254024000242141c203074200424451010000f0b11070009050080356a41c07070314180091803500490340342d48550401c507034202d900a000d4604803900c0010200c400165010540301c01255540705001c205050900040035070302d000101008014102e10203c41e0a500e84010384010040e6031100c180092800251042c1d5001c0d12140000790014140345141d82d0081080c0341d00c2ca80303054841400034050182901c00e40d41103401070010149401c40c0f00302c088030400c41000e002410700c803041c040fa02e00c68882c08805048403142c1d40403 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 705255827 1250 705254577 705254591
    0x3120a0302040e1602070905040b2404020d0b0f0301061a0717030a090314040b0f1e120406051e0106030b0103110412030e040207050a200402160b0711060705090613030501 75
    0x8000d01b4901560000c801c124205814400000c40010300158021603840d83c0404030709400070200819841c54251a50050002c203990384400d865910030035818400702d87d01700080102c1e10505090b24030501c2032011503800c0f24060242428440010011a0700c110000540315141c210101682c1d00207660343c4034040d036100351030810503401040c085141241020481e0515103000c07200101c034803a180c6220203c62010412046140c0094840218410f01140b199161009405260306100b421242503603090b040c213020a13000050110014606640c0c1c0b042195240e08202040d000b61401d820110304040d51383d28030740311000c0f000000c0c002400a10010300c400a9503820001c20360300408000c280f01d0fa10402ca00380000354001000b00126920082d41c054030303140001e011103c82c46204030a40c00600000b1050f4003103800ca0851120144617003811449900c4441c0b00312001c1c12050007500c1c15034001c4000c9482c060189001c0c0c103440303000400e501e150480c1d25502c034036400c020713500c01c861a85d11140 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 705257077 1250 705255827 705255871
    0x9061508041e030e030d080c1801031517061302030a030516021002010f15140f0a0902071b060f090515090301060f060e060f0702040f0b0910030201031a03120a0302040e 74
    0x800054401b010786401c60305424072800a81003807003141c1209248112501c4040c0b0700e41d003c0e810441d102003148807403400207552406694188400c03409440c011340101c0300094104000b00400b41c401c150050001c02144200d56800c0d96a5440801e2403e08800d000d01103400507600c08001280f95000c07076001265548003419048140c4011a441e8003035101004810b1111141410440c85403020450f488000c40eaa0100440d00004040d0410702d5041e000140d20001d11030f8014010707003061500f00400d00c03081c0d501e034402c5907580c4000000d42c0000c2c20f40f0720100103500d403d0120306014070031558602d00d40303008000020308441c1140d01a00c0c0c9034000002c1045001d41180311b8106800e000da80d0a440c00a03c030745c00c2e451620884200070b101e0f40d61000d00c40150742031503120100b1000f01604450050410480740b034000034440c4400c0380000d00304800607200c046007003090b81b04240068002c100d0754800b65130780300b011b82002a0840c10190700744000598100348180c000e020700141d880c10f80c180390b802c00c = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 705258327 1250 705257077 705257083
    0xd0317070207051302071a16090504090809040f110a020705090702030310062f03220807030807051501150908151f03050d02070e0109061508041e030e03 67
    0x80421080d9001140b04006035110500c00030780092103801c0050f178a0042d850a204448040a20040e00a4100c0104140084400c5080000c8107561301c96000f0280c0c0c940400095410584004000e18001d0100070b44a09264100d10801c4613407110101d04074000c1004030002c0e070040e402042c0181d00090040100d1304001d994241c1011b5144017461451a100c0241c444910b8640f28203020021003a02c18000b00825140c1c0202c1400303024041100e036075909440940d01c0d04289108140a5030b00032282c0070300600140e0380801c0302c009201a01c5035610310740f0381440507004840182c44501400400349903241e400032400f030103480d1141c4a104041031500009005650a41201e180c0e9031049140345004091803c01c1a4003078130044880551803200c120904240000740c0c0020210700c40c4160280c1c0940c3c003c034a00003901c0301c1410103401c580c0d0710011201591014826494040d01e00c01da410141442000659482806881c00102030301c0d40d00c00c50301c440307103412909800040c83c04d6a0b40320245014 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 705259577 1250 705258327 705258331
    0x240d051609060914060d060b03030a0305070f03060602100917070f0309080327130606050405030c0102161e0806040302010b0909030c0705011b061b0e0a0303090501080a0b0d0317 78
    0x700c2c408200f13200002c0303541c48641d9405424944992050210502000301a81045143d0303c0040e0560b519011100ad0141c045c000c00e68001e0041245141c54042c3e4500c248200022181c040c1d006040c504540b070328810080180c5202070724184036486000f54501c0c046401400d650f032250300d410b00c1241e6607007001000e80285410007003080d0002c2144110a4041e4103020f2094040c004280504981d0800015031803d00300301114041411301c0e80000b001604000900116042034058800303944600004988074039141c100d0800035060381c0c03400d0040b0041c0306a43c000e060300000d40b20b4a055110003140c0d10b030500071102280140c0d151140226581020819250041240da00850400c103c84506a803205524040c2a04211418041401c1c404965200040c0e6a8121f2030820a2541d1589a140c01010445495006c0f035001c5100005508084500104a941513a1a0208607042900444a2800242c4030200300e82e200e01c00b403070b035540d2840150500980300e0388504140c01c850650110300c2c0800 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 705260827 1250 705259577 705259589
    0x80703050f190c030206090d020907030b1005070c030b0a1d06090d0915080a0b0d031d0a0e0a181a1015021203040f050607020303100b03240d05160906 66
    0x848942c00911000452020b503507040700d40a40300c1c1d1103000852880e902440000e503003c0b007840300744503045800d80d00c24580e400c1c00303490b040c021401240c015199440781001c009c25078034608004101140500c05915040340a1010201c3d901171202002d1400801b000511002508007005002403900c0401240340c0c8105d06080166180303140401c243d241088080740c1605000680c0c0000340d0145965103c0164240700811003240300c840750030010071400d4401081ca0b880e8625180c00d500354600140000308685602c00318032800da07141c410301d90141044035a180140c545201d04000020068030203400301c0208802890340518201100c8083c0305920740c055030219078804a0071840c01d42c041031520118102d140c0840ea00e884503c1c20801d00d100d0520090003c1c09101c081c018038130790110003140200c901c514502c0d10710383c030381409205d144000d4510641106000881810304200304020040400e4014045c248646940e103d150518034001c0022a48240030030050102595610038440a0a0 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 705262077 1250 705260827 705260863
    0x60a09170319020d0b030114160f0e0301020d02090f040603030504060c030905060408030c0607020303010e0112140d090915080303130c0b1c061d010b03090106080703050f 75
    0x11640c484000068203008640605100000082d210701e80c900301d03603281006601011075403a401200130328020805407803000e1295003444504c0069801c440030a80c0a0641c440001c0450340c10900180c4150460014120600c840c1800c2210720359020301c080c1c0744d14030b2204000740e6607520781401c100c0c034054910459841145007003000e00100360300809440c2035071064103180c0030300e2171750741016140482e8580c04071b90b01000c0001c01082d403040100c00742104184a030100c030b60517101d911040e41c80740424000c1085041120004100c10000d505003044074038003444070414000d207e00650ba0408162240040102d10221410030603600740d0b102c1c10908807520703c00086500d0400a10644030310000d41001b1303081c0c00c1c44440105100c0145001001071011004050b561b2191209020030124011401540350303241c00d600188141ca002081c41401e0701080b10200940c0c2000f00b12542ca40001d0f050558565a442d4041207a803410451800550f000d5030061800403014243c40341ba0030080351756034159a13 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 705263327 1250 705262077 705262091
    0x40608060102191b0909050d091d06014b2c04060519030201030f021602120f01150302150a0f030b03010902090106080a1b0f0509151902060a 62
    0x4010700c0500403095840b11040c074001c100352020881d80584d41d000785006619250650b400c025000400146041081d11400000344d0b480c103111030801100385e000b10a10602c41c0c0098006e40c401c080ca01070550450020328007000e01000c58840908040118100c2803801455034510500c000b03904249541191400c4250b240245d0b80114400c480d03c0f88100740e0340c11401c40030707070107035032300d401003805040040d00c01c0601400111203040c01d0503d038441a800329182c602d000100c50300318000c483c001c80040219100c0d9402c03543c03d00002d240a0860b0f2156070080c03c0c0720844000d03082c001c0c200d65000f15200701c1c2019055004111004030940c0309110340c1c46080002c80d201a07082501c0d50309070402c504000615400030710220780541880f42d0029400541000042146600304241e207014030032110b8100700e40f42c8413030200020090381100103804103c0c01d81c40d400300c551145c00242030401000d0310314103191a03c108040c60603041242c290201d540520300303000585a0400c10341d6441415840180194 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 705264577 1250 705263327 705263353
    0x20609010b06092b05070e01050307050105220b0d240e041202012423010509060d090605040b040b130f061109100518040b1507050a1205040608060102 66
    0xf4031a01c0b609030302a40844085440111119403060683c04038003071484135541092800584405860240702c003c594000004201341c140002c5500c2902e1040c0c5400c0d107040450344107130190103032270607502407400081000030800301e0304039010340007402c1004004141510807032420700d4540000280300004205007201044400075042001b6001174001400003968000c0d10070407405840501404001c508615440d250091090700038034084498811100c8203d9419204200c001140225040c0c0003c0c0103001c449a00d00e0168003c00c500546045c002603000345556500003618022a025504680180200024803996003913890703200991804001000e812582c8850342504605e501410150751884010a0600ca000072a6000c0400070301c2012142d050030001032007903014081c240048056080c08103501e0071b15001c2e25080344001452044d08819013684c111580d08002003d60360f6202e842c0300700012400c0341644450202c0d05c1d035141c80d911800c040018112080c060401411907001a480c0000c3d = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 705265827 1250 705264577 705264589
    0x7060e280e040305120f060f0102460c0303140304050d05030414011b020f0106050f100504050a0906050301060e09191103120403050d05040f061211071101020609010b 73
    0x2541d2041030125850740300c42c181240c1d0740c0a40f08106510f102500e05014002844c002c0503482500100c500e6604120804012070b10f60f003503081c42d01645041074039464050060490754a4104202180811440900084045850003030305000ea4901400040610500d41c0c00100d00d0401c900080700c05155050507070710f4a940c2c490794001d142c200800032020900b04000c0350000100000311800900c88500300100f884c0c44441003c03094030151250241c1e08090880c11301030701c421148010300106125901506008100c0103503c2c040080000402020031f9541c2d07086102009403808120000b0013900785000d143c210390035500503d5403280311008100b4003410000c3e401007001d030300082400038190645020780b01003080c0d541850b858041c46c031480b00201500c6000c1c00c00c80b03000f44200e03415900d4002040d1240e129a01030700da40303880c918a0500186e400740c4d01d8030a10b8071541000081d211100d0407284225002800c0c00c0301c0c2ca96076030040000740d41e410004a03800c10309042c0204074400700c40000401d = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 705267077 1250 705265827 705265829
    0x503030a090303060909050c0f03060601020a150e0114040c0603060e1f050a08030d1a0105090108040816060902010e04060509060f0d050a030e100e09040b0c0c07060e28 74
    0x30045031541d04203010107201c0e40090b402403402090a001200f00e901d4469102c00030724407454016400325400388030900e80011128003581d07041e0042c00c0c45150949901c1030300760845405414103071300c54800500d0101c00f40701d02c1f15401400d42c072400d07050030903240504820116520150405051200a00c107a0b140480e410b9000281c03001000b84900e0008210304426209900441c1d12000102c00040d03884000300c02881141002a4100103048007916240e00350302c030040e6228001641404004815402000543e40050185000905005141a85045c0312040780001c480103601d6030904011941c0140411a4006044900340320305400c0601003003003140018281807050100000c8644039403507514200b10000d801c03030309a5890013031504000e003864040d01502c90040e1858600c103450315104000f0802030043c0100131a2190729991680044c014001e80030b0702c2c84038000c200f48154010200a030600803c50764a030800183c0e208020020900f00079041402800c0c000110070903a00d50400e2548 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 705268327 1250 705267077 705267091
    0x303020304050f030a0b090c190e0a0b130c020a02101706150706110702150a05180a051201061503061a0c0c06041403010b040b0315070e04111308030403050303 70
    0xf4051120300103468151080d0b07001d410710702c10206010017150301080d00300e91007000f5103040c08482407003484180500d0107403240010005064010800910064101c40441400104a2212400f4038801035085841c0428003001690102c01c04000310b081607000c00c1e8032044c042c1840c14103003403101f4a5000c0c1010041841c1c0c030036140001140c0c100c10120050300e803090b0300540d040150500d00300d039022031540718040a034460032a10080c1101c2404d2282107070031100081d92000d060141d140800c400503200007071030b103038031400141000c501c42c0c03580c030354103003001480f03c0002c036145280019011120480c02a008101410228180701000074035404200720f0030f0300c815040d524150100307503509041d01c0b40c0312554000b000043c006200e540085d000207241c074084000b00b240701142c10420045404000707003103815030811186120301e0170f011825181d01c21018240410740c14030350341c001030880e901c01c010341d43e04000c080740c0c1801078281c1460a030701034116040250700d401c0c10368480c01d65130b0100601d00 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 705269577 1250 705268327 705268339
    0x60f0c170907080d020615220e07051815010806030c151e181e060904110d060f050303030105150319090f020907090b0406032a02010e1501030302030405 67
    0x201d40c0060781002400300400002003a501e42d8000008029116241602e060004002920240410b85841da5003001c0c45564449402c04900d010041103001d4000c071411080300303009400001903d0340b642d4140c103010305c500c03149002e803a11b820009500f2a11090100a041190032020000140c40004050029400441d007803000c64000945001d008d2160030140d0a900460401110765015100080c2c10300316022840d80021744104030034485c3c000d0b1003420503c50004150010f2901c1d0070604014409601e0140002c544810140c0074550a030340f01c3c0c052203501a90304c0004010b070030714080c60030014100071006545103500d0030000407818521a688460300c120f002021445d0f04200303928110720640c43c50409d00c100782c40340c10584444043d0500581c007808480002510040c421325a24054504404215041c1420200100d0040c8001000040c2c40d103e07107058501d140d03d4000d01c402d074219180d8004034100d01d86542c03c50610380041c00d440c01c440b84000060000980200568013a01c10035100 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 705270827 1250 705269577 705269581
    0x308072901210f05030c0d030b060307030f0b0a0e010512030702031b12070b0a09060e0a14060d020f030726010e100b0307020c0f060c07090c030902120109060f0c17 72
    0x10a80710700d000e190005001d240e1030340003d0200540400a08445010717041551007010b0802c1d03041d4259075440c6d4003035a11407810000510034034000e03402010413840750b0000143d1000c1680100c5d0461086800040319014400c0c0108401e20308440500b2000b00c1c400c020714100300407580820350310041c00180075a500038200c600e640c0c0d6107800d0030741d504681c400821140b81c0c80e03a13800600003590100384c0b201c002a8502030041201800f071400088142e030040c048801061801d910064003042c040d641c560b2050041100042008150018000740d01c0c002194641d6824072501c0500145074041c001e401c19031341700c628100c02440d40c0140504480410920811a66a60a109c6001a110f4020541e8864003000f4060170359800038540d070740b04606480c03101c01c0420f80810081c940c010750031020201d03070082d841030040c02c1060f0000840b004250401050341441c2e540000ca030600c60081c4c21949030340d00d031801c2003403000c60b006404500400d000208501e01d140710f8014981da015101c13201c440c0d122040 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 705272077 1250 705270827 705270869
    0xf0303040b131a1e0403021f06090c05130f030308041b260f1c0e040605060a11060c071a0601020c0402041d0907140d03020c0a0308072901 61
    0x1542801c0c0c00d60203c401c20200303446441c02e062070001540d0034031261112030700f4034032001001c8003460301458154006080c00c15040c988003003c2c91007864640ca1898417200d001a028049020b000c00c03161413600c459485028004054100c82e0b00342d404941e00c0604180100086500440481d821a400c10000d032200041078203d411412102c1d4020080d41c7c88060b42180300c00400d01c01c903c0a1403054040d0b42c01126041803560b5200d8103400c03a140551b440c01100c20501e030040080151000010b0000305145589a0020b0140d40204945202084100c829801d02e200700b8441c140e40310311803c410508102050300c480308291580031100c0450b00721200450000e0703001704111001000000d20035903075aa201c5c4412440401420255001d407800f060109452060202c0c500301900c4411002d060100c0c030700c50801c0039a8081d05815425801a05034410b001e44030303040c07220041c0d4090070340595188900c1c503151580c9a00c003480d44400c0001036411107051603400e02d00d82d0465a000036011040d808a01d = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 705273327 1250 705272077 705272101
    0x1104050a03020d030e0a0f0e100806240a030605070809030c0304030f050102070b01090e0f030c1c12020331020901030803150909012a0c0b040303020d0c020604140f0303040b 76
    0x240403281d228802c0350000990b0a4240000130689415108c00f40850b26862070088912100f80202e024681100740000c003100f0b02600140038240140c1e1811940300d5042011070390919194006031134454644041065036178101761015044002038005500c0d041300903141c5501c81c002d0b408001d05842e41648040309001094064400c403070f0300039200701c2d041d507922402d0700c1c0103000440440e500740c01903010076014040040142c600c00d911143c0a021000d208039440000307492a10a400b00344824131800f45100502c0d840076600c0390040c2454400d819110030301c02d0080400360501d00810880d03101c001700c0103886141846045950010b845074403512a408000650b221507030010741c104001200700070484d8070540150450205d0a181071707a804051080c40580403800e400c40d480400e00021101d0001135a114205500c00c1c0203240c01801c0008610198055588009000005a01450a000a01110083e80f100d030211941c0200100200c0041d1644c41e800003e0014001070640e50005541c05840 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 705274577 1250 705273327 705273347
    0x1120b070f09091803110111040b030c121f0b0a1e021e06041109090d0e03030d05090a11030d0f111005010b120f040c1715100305011104050a03020d03 66
    0x8000140013400003c81102078060300407200341c000408005c2c00300c100e00b106100e801c40540503448824030305420900440b034143d01c0a040c011200d6010007200a041e1030b4000c442d03004500c045038201c4480034590220800100b10303002010b400344104011074005401c46068480d280c4a51001c17017407000200402d9040541800400c0028010388021034082040425038a1040e03100711080000581e04106101c07450408403100e0002c5e40c07040c48102c400e540111102d010000c40241280d1801000c80a010140d40c002d84a07018940d1240302000300308907201c40d0720300351039000f0340060034405103000000741882c1c064600081400000070003a1916400ec4c8482000d003c0c082c1d6081c0903d581d1000041c0007035000305603105c4ad5501c0d403c04900c0e03050700201507a00840e003006090407900d08100aa0034006050401c103982c52140f81e025038984100340038494480c80d07244000046113442c5081c25825a44000384200f2460000c020070300981c0e03107208000054075015580c40d0507404081c90141c40c8200d01c = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 705275827 1250 705274577 705274589
    0xd0803190606170a1b050a02010e19080c0c0a0b0417060f0601030b0307050603040308060306101505030c0d0603060c1d1011390904030c06020d090204110a030501120b070f09 76
    0x10745c11605a00b500a00289980241540204001004001c003151076144010300804403204c0d148400340860500d8000c2c00b000c0d40000b0030b40c1d0b8680c0d00c0c400052100340641e0305c13510300c070324022504110654984401b0003028188502034029494010050a01084010031060605603622042c20040d01c00700309180240c0005403030260f40341480d04011f4207540c001c0311107510921442c00082c01c1e001c4103108140c01c036106041900e503541708600040e220f42c1c00041445100540c180550b08801c40d46004c0c5034001d6010b41000101680b856800818070117604102c1d814800981c1880c0d00d55860b0162002e045011610300041c40120341c00c400c80c141b54507441c1005102c0090030081d0120044150900104200030078041d02107410340c024018100780464014010811440020000c500107030004c0051045503140000c08032690b03800a4110f40580310b201036440743c0440da1215440d098415036001d011000c24203102556181da5011011000401314420410312400300102c10703001e02454000741031 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 705277077 1250 705275827 705275861
    0x2091b070803040605010801050106050f18010c06090f02030c0a120809010c02060301030506160309030f0309080c030a030501030c050303031b210c031618090e0c0d0803190606170a 79
    0x41c01c4c28803e02400081c01150f81c55445d00000288680c0580119003c940c030300c40c0c540e03091034511030340040075403080d110860512490011480001d4090f04c508081c4903c80c04d28815101218014585003a030000b4150380079140f002e2050194042d0b04a881401c0d50b4445501d6955030b070b400340101c0c0c02c0b0f040c0710750007900000301000200c1000400300e00c0a100c0d002807181d501c01c6900844041b4140c801e4018003502250034800e41d8030304248a0382000d10704d0740c0942251858064042d1000e0319650050f007100e000a50f41e103005100300840082c5581c000c000440040d803c50502c1d580304001660b002820220450000401076031901202064089090350911016201d24112002001c540d000b1555054403020320445401d45c0360007600b0000000c8040074608440500b010741c0303c4001e011240d0040110700c60741e41200075695900c981070240d144603103030190301c2e801d010003c0703a28444803c0c1038516107800d0090500100d42c0c006101000114101d00c030b43d4160b100c3c400400d008000110794071808031 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 705278327 1250 705277077 705277081
    0x60618040911150a020609030f042303030409021806130b0d0605091005210c13110c030403150c0212030c070b0108060601120e0715021e071401030902091b070803 71
    0x710001c01405510071117400b969600c3c0e817690b401945a2055924445001740c06000034042002000101d0b40a10b803d000c45140044050000034510380055216101d2103400144813007a84c40341c0a21044c491406491944c2444070042040502502c0381c081c0010080010034140c10071740181d00094010f00c4041c2030841d59081c0740505940304001c40c09881d000d03011030034902803011526080509551885005801c0403a43c80c1d0400024000702503c40ca1115101c812540303140c8074800044c4240b004030001981d03914a50303e09a51401e0300c00484010807071800f0880015260045916041c42190f1072105540c1e549850040501d030290b120301419046401001041120300041c025004100c241c82d064901720802d00342c48151100124440700980009208103c80c10b44180c1c114400425030058400c103442044e081c1200300111420030200c2d0380402400c01500c0c1c804500b14254443c00c3c82d0501400c016500401d5021902070200703140801c1000080c140040300700c0541d0300569010120315a68 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 705279577 1250 705278327 705278359
    0x50d0b0606131401030605061c0b030a02190608070807050307031503150f180206040b070203071e1a0c03190909060608010f09050603060a02090d08070f0605060618040911 75
    0x500c012403c03603010a11745a004101c07441e05000b0358904241100000b030368681c8203003000014183c0484600d4041c40380c80b40c6480160344288031001000e18410411415903d0000000e100b801d000c2c200c44184205601803041e003030381c041b00b00c0b94400c649003000b14940c2402031441060300001e51010305101ca1004020040c0003880e0020455a600007806101184849d08007030015001100c000354440420001000148c880101812000b4002010f50b03804076075a801c01c0a503a0140d02440da045803080a052084501c001641142801c0d0801c8031814485e440c1d86d003990b070b0700c140e8441c5948611070070122a1054464038030741010307019881c410f000301b660f2084050040c0c84280920602082610004038111703c052080500ca03e40080c0105003540744c407100031300258003000c241a04a02c070a42c603a004941d01000130159644205007105640c0c18034140101111030103444640705d00e0080000903615210040c200721107550868000074141d030240b46c0180011079072402030383c1000c0707800c52192030 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 705280827 1250 705279577 705279599
    0x111314270f0601030e0706201603050607081501051e0406090602070806090a1e1a0601030e01051620060406021201061803060c1b050c040c09050d0b060613 68
    0x1941c48014400e45a240c07540198103076901100008050b5120140800145100e403050b004960f0101f82000b45d003020040d106400c00343c944400940d41124100c0400412038100314040c3c0c000900e14007000300b070421540c03082e44800220026410401c011404107188070300c60041d881c901c0e0a900a095589039100c5000e0100400c502c54a0091300551000150341440403511920481061020381200c03400d9594060140001103103404080035a01110310000300822034080180720303800c3c00b40c1401d240002c0014181c800008102e030701c90b418502801b00c100715103100e4040000003410b240040107011910410300c8401c41005c2c11b802e01c903138024001842042e0b401806901c928480e80a6260780f51601580c1c0d181961038040b0500343d01074401c00102e03020394800c0c4580000d03440d015416096800800100740e100b040c06030340721341080d07046540d00c0c40c152003403000c00030300d6042c9000c0d903516060008600c4881c1400141c401d109960003d0100c1da54202140d070300c0128450111080d640340e00000306 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 705282077 1250 705280827 705280831
    0xc01020d06090605180c09061e0307170a0e07140d020a1d011703091908030310150c0b1303030e0609030426030711150f03040611131427 60
    0x102400c0030203411105c03c8440c060052141c1c00c480c01d032a00d00200441801050b41c481c2c103060b20800380d5450001c1c0207900300c000450164800784d41d1040c0d05400341040d03138040704015203010f40051410003c40300b4000f000c60200c049840c85005124214140c00100300500c0145600030341c809100c01c00856049540045a8034001d0a240d1681c016a290000e01c460721754110303070403005a401440100da403450100311400c4039183c3c0c0d0306d1518030705907200441861074100340c1c0c400315000c0040c542440012046101107001018910f801800d4540c6516041e004680240402400a40312500b45091501a8118001248080c0c086444901d4003880c850f03101d070007030701030030030010741d20b0302a44000710361403c007080400c5c00b41d80a10325140c520f0b03840b920040e8418a0b102d400c0304440e02c44050407041c0c800580345000000703641650300e140c01d15280040b5120612040d10b0344801b4407451041009843d50751042d114005400c0507400b482d480060080280c1400110a0b12261203401d9400c054000361a8 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 705283327 1250 705282077 705282079
    0xc0a021f020d06120b2a072105031b040501140708210f060312030a021b060c0d11040e0609040c03021c020f0d031e090305010e01020316081b0c01020d06090605 70
    0x808a506c0d280e185902d48250542000482420000e200001c284179000134040340c0d00c86d0343c00d00300c3e4056806101800f02e40110b51400803400100801454039a6040000c42280340204100d244c14140350003c1d04d042404155504810300c00f054400c2040300c01c004541204c002c001d503c4c103044c0c5552451101501c002c440003a600204603001c55150304000a410018440c0c1141e0349040d81c1c1d400120070029000860400d0080d107042c1e4006071085c0043c0106800303010001031595031410140f44810944100d03043c6d41e80b4110301040104080036083c1912070b000602100c00038a907844600b4042d9864607a40c101a50080c000d002d4404680c0c0c0355002200024401d403500011411031804200180c507402102074045001c103921303a0703410300b40b00307680000ca08411309160291170748a440e42401c441d110400b1080310780d0300105001505000c0c80c841c882040a924010080c1d2921240b14603003888014912185680302081081d60b4003801e40590310708202d40402004055541d02101000d00350030300c502 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 705284577 1250 705283327 705283343
    0x270e011b11010203040507060f17090d14030f0604092906151207030216050a150605090702030d23160e03160e04050a0f06140c0a021f020d0612 63
    0x1ca903484410b00a90b44110f805c0b0000d0602c04d85000c00c1a5500c0c0030201030786040118600302e9804092004010b213004502c0c1e440103007003c0ca4065000341c01d1106101c602110000140200990603483d02e5540382d11150a44011605803c0c43c9440079484035100708001c00e07090701c03007200f104410070282d105108940c115068902c1585081c10000e140c402c03c0c440c03000c024000f030000303a04640641c000b451030319040d54407025030540d0f54661908041c03903110103c0e18007051207004e0344030030386038060f8501610b0122560700b103904000b94069624401c4601084050380c440d40801100c0c6080c9100700301c4040300700c0248800e403400c0d10009145105000250002c03e4015000320000c0c04c0006207400712400710304001d00500d04040039180b10201c02002203980340b14106210001981507600d10b608688294004204011040388040e501000104150f9034181c0c1070181c04103031036001901c50403120000c0d040b11014036003110f082c0082d20441100100c0c16041070400100c0c105101c095240e01401000d607 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 705285827 1250 705284577 705284597
    0xf1309050402030a0201030e0f030703052d040e0907050d030201021306090b070b100302061b010506010e13020a090f0b30070f0201290910270e011b 65
    0x105421a941560081c1d010351003202e90a0040d4001c3d231000c1002c0e50f06c3c1e01181c1c4110810000c0f1403455000b0801100003440c0891170250b00042c0d4820741011403000c281e804020480408903202902079881865070080c0c4450100b06144070a10184010f82009030000310702100303030305000e03010b54050900c00014044c421300018a0911544143c02520b50340000c0034906107035500d5440f0382000c01f030948016210010300000042c4c0e0394100516401007600000c102c0626005a02421120000c1c3701505000141d00902e0f1580c0d2864607607842c120000f000143c07a01c0d00e60900720703000091600701908010900c9004920807940001424400c011300101c491320381e08014580342c180704418044410942e24202141c54107009410080f04211076100000305641e020b550740100c2492864800a801480d100e40202e5003407401c5207940c046860141c40c0f05440c509040c004240b1241c2200210303640d88510382038014070440d040240b581c22950020b0050146407140000c3c004403a418120100f004502 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 705287077 1250 705285827 705285839
    0x91505031606020d05280c0b37090c060315091503020432221101030b06040f0b0309010c140a08040204090f051506010c110609150f13 59
    0x640030180c0705140d0203090042e490950690350754001819646c03008500c01190401142d600d203031145140030955a003000301351a41010003450b903003d041510754a003048a40401403050b48401009080c483e440020001d021905800c020403441500038030700f0b4080c00c40002d80307680c950800c8501105040c400c240242d91914a081107520340b201010703550403245000c1000d440c0c254064203041200303401e0070005002609040c0907901c418002c078a403c1d2001400d0280c481068100482150011700c840034480407aa152038440c0801c400300c4504240e1599140801901c40e1003e650007400b08421240005031111800e4000e50411035510540b0741c0b9101c51000d0551182c890030b042205050a4a46484616807007100e181d200100280d03003140d26a88450300003200410014943c9021700003a003d01401190400f002103006042c8904000204600703201117080007aa2400e0640121030071a03841c14204045900d80c100c43e12114299040031500700c202c03901d054000c2103e0301c0c88004980400307440300 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 705288327 1250 705287077 705287113
    0x6090c0a1805100506042405161212020a110613020108161b08070c06050309120705121b06060303030f071b020a0f050a05090603032209150503 63
    0x100c64080c400d0740801d00c55010440950045400200d5000010305003a00c4402042440e4407680c08803034400351041180078a2811141a0800080d10349007a80c034024140d01d504640c01e001e00c1e0090100d401d1012410340660141080a00740130036140155166030304400050f0002820650400d0f20b402542c0005545501180c113854840d07030305031070b881410b8803089041c564000c0b52040d81d206000c21075064a407200900b0f07110615180c8182d40141c2e90341554600303240412807170f03070020003031003000c0c000d00a841c400880c0c41d01c1e81004517400c40751034004d682011440c0c80c00c02d001e1040b03260000110504000d800300c0c8201a10a100d00860b003881c0c58100901d6502d1108444100448100c5404200d103184241c031031000354018540d4031801c00c00c56800049401d0303c5544410780c8080e1083c070070081803c084030864000c120441ea05d100c3c3d480d01402180d00d92040e003800c51901c00320ba00d0101c103803600c0c4112400c06404503d10401c52040c40050b250703a0904280251480b91080700342031003000082c0 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 705289577 1250 705288327 705288329
    0xd02040632090f07030621050c03160603090503090402030901061d0408030a050c13090f0c1b030503060a030606060302090f0d02010c1211061314030301080c09250206090c0a 76
    0xb034010b0601d60b450b1440048281c001601c0c8030101500c94000203440a100b00249480c840040c5402040707002500d0f0451402001c828100d00940014950300c06180803409032404854041c14045620b001c01d181050942c4100c2c2499a40140f010090003d490710542c00281600c00411006c001591802d90103140725401b00c1f40100007241c00c0000171507005444c0c2217945c000071241400d40c10a4240c440d0409a20320715044094a01e545030b00503074060b50035010349094242582030801500c0c181c164040d54100d502d10380030307052003400000305510b0344843c05104011034000c0000c0000d0b03034440c0d00c010080c0d0b003e41c068602c50081560f480140786040500401c00b40e905031038040c040b10081e541c034802c10501a0484003801007104c1c180b00b03c1c0c2010f01255200c1c14965001c1c1c100103505103084452010030038903039500e9a10510042c00b00c510300040700006074108464446580c1d07261520114202000ca001c0031451000c501d00d807981980000d01385010341017080c00d407149560710b10140078001040e = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 705290827 1250 705289577 705289579
    0x301050601050315042d090506181515030a0605010317090f041a042c0102040b030f06030a021f27030605060a05031926090f0d02040632 60
    0x40d001003135216141603800100c0b40d00c64a409080c0d80b0b4900003200d81c80602003c030350944540c94403448000c001d81800b044e07900c072000e61103401b0320790080312125903075a911086002d001700202c4049000d80d84001407011003a41c00904a80420304545040c2001c0c100c280300441e4001c1113810115040103003903080d41c101a0010b0407410240800710104009401022205070050b096440b0190082c1c485d0f00480645113095070350305107108108521500031844001c1c000b07280d40d1060100b40401c49100d0101e80d00400501c0098405071204030000741403079500f0138003e62221030060a044c002c07100c0d8003091502411a1200c001c071004020810064544001016143e0705040307a040c000500d03a54040e9030001e10207418901c83c02d4070740c00480d29000504546405018003000414100403103011b800380100c58101031260f0030f04103883c0b0ac8105001c1d81500c04c0c815004a010542c298880c0c02e4504000c0b6001001400020b507151403c0044810411004001038400102c0c0c01c03601519080005440d50 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 705292077 1250 705290827 705290851
    0xd0c03050f011a090703110c03250206091908011e050901110f0711040c030e1006030309181e05060102011103040b01360b1f0f0f17100503010506010503 67
    0x210f25400c00000f03020082c000002d05503640c0c0515002002000908401280c44c0011540c8080c1c881c00421001c110450306188241069194401070300c0e80815210320600941d40c80d001c541820020103010341003900302c0500b6600c0c0100290498240d00c100b070000c8940010100016103400f80e4203400d076090074070b42d05110901040300c0040c00c3c99900c0201081c50080085490103101e2a0008040d0fa007503080e00400a5102c015a02000c8030034420300000300e4140c00c08021407442c654010b800d144844c49290301d0b00068040c10326420320a0f8004242c10a070595604085401c05840c0900505041d112540150710302540001740c14040002c40740100e4012003058101ea181004001c24030400b5100130040f00d650300050301c0b280101d04102d600701c2205a42c00720f00c601c03800c07040c0030f04442c00c080301354400c030620012718990f190000800311070032241c2c0c030f8030055049040074180d030000958130f41091901010400c0200d4000003d41200036280210000c0c00300d600d0382c07401183c2900003501c10131030080f = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 705293327 1250 705292077 705292121
    0x3030507020a0b22061d19050604320610050117060f01050c0a0507031a060105070219121a0a0b2d090a0e0c060a120b0f0d0c03050f01 59
    0xc002200c4c2c4041208440c10030b119040c807151340700c005a4a115500304603503041d081803009052424002c03108040c134902c03115250f0700c1054850340d60700e000280014004c40f01e8660210000c6071040d02d48060141007000c40301c0d0300380c600304600d0703a40c1a04440c440c0454000c1c41003c0303000d40c483c4d43c0252000d5001100000761f0f440366810045407104207031146043c07000c2004070104400e02071103001e40c41030107100500301c068a941131407203c034000c030060101e00d00c048074100901740ea00072091b1084503405485c004440003075480a1700ea1161141c05c14541c0064100000007002550f055034440310070554000b070602c0d02d5684c03043d000c0d2400c980a25a00c25030b090482c180440800c20f54900030121908009028040940400d244030816524120300c5a111021030b44080c004110b031041d441c000b0f07264a4903201e004140141911000d0b40c5034441c80303444800704142d0f81e8170349002260201c001000407041d620700c0d1600310306e188082c0c030046070180510000b031000e5540620a1a400100e5110350380008 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 705294577 1250 705293327 705293341
    0xa0b030a1407030506090d020609031c0213080105132f090a1515180303090501030902040b090702030a08160e010c060222090f020f09040c05120703060303030507020a0b 74
    0x2031005000d018403901c610b9000002081040020901448450015242d04100030000a0420500400b5860306604c204880c0c402900121181075a0060494005858285e0135144000c0040140d01140d5590f0070715090100034603290006402c10341c403030441c2c0440c0302d10f040c0c03000c1d03020801d50303041c40281c07140d0000c04100c40c2080081d42c0d900290740b5000044110a9040ca802942829000b44000a06000451031040d07004483d08805105c3c104507000c000e49180c0e002041c8052900490303042644845035a01191a0358000c540c0c1c00800030000003035407800e410000d6036508908800000034004002103201c081070100401d94041c016510240320b820000c00540b48001c0485080364182e83c01c02c0b10300381c0d426460718002400c00d1000e0b074002c251480d0102c0001941c4100e048803040354410001c041c5281c000d0011160108800d0b03c0104044907444000d4072103020318100c140c8140422810045e241d03038150b1010050724801d071010001a201c100342280d0f01c0403510b00042c48500031402044036 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 705295827 1250 705294577 705294593
    0x203030301091e090b100506030f06060a0e06070503030f0f1504050408040905040b0105190e130201020f070605030a150e18011d01061409090703080304031205041101080a0b030a 78
    0x1660580410300303040f818400c2c0400898203c610142c0c2c3c480490806e12646001c240114030003044112001820350038081421000902c2c040d2034544200c00001e1516415401103006142c1c50800034032460700c62a450820f0f0750ac9502c12100103018001c017100113010150135011690190701c41c0c0c0c05019800d5910ba051100500002e04161075094007800006031558490041034400d52040c00d000301207500d40f00034400182c0304000140034080190805014030345030071071410341c0020301c0070445590242d0307400182d041c0341c1c200c000c21800d4000c1c000c0c08914160000e00a40c090305030321604100d0b41021200001e40d08500c1c0c0580581c0c803d0500104910445140c280b0038030040060000034002003648040c903075444102d81034442171351145010481000d0084030650305000c01c1d100c0b10030790310300302412545070f140740d000040100300040081010f05200720300002e01034244000c2000701c1c0c102030504602881800d0070240c00a011400024608a4180114118207001034001c14401c0c00c03956038040 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 705297077 1250 705295827 705295841
    0x90204090b1c061a10030b030c010302210a09080c0f070b040f090e011e14130305040b07030e0a170c0f01202410060203030705030c03090f1b100309020303030109 71
    0x311155101c44e072140300da0301d02d10b08400f040302d9034500050440015050504100c20b5500c0701d03041c1841802400020b0021080700030f040543c000c051151540c1d14401603008003805c02024004190101e00d00d6813500300041c600902c519180200e814543c0d031800021264480c0c0d015041c903060803a030040041285940110746200c50020010421031695001c0041d1890300098010340962145018840d1550000140e60421101d05102c00040015200904144240c3c41000245640016a4018544900382a540c880001405a096103650b00d842042d03154148808001c0750140003440d52462409401c01402c0c3c1754103031149204071448180b4100c551402c1d580800d041d00824803804070b04854180c4100300c501e0201403003003144c02c10008621804c03420790040000d540c020010721031010307040402d4a40c040083c41d503d5a6a9685805240c06c0c0041c14040510900c075100e442c490340480e030307029090390000c15034080c0009420b00c0780c11000d40b05140c1019405d600104018070201c075203034205107 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 705298327 1250 705297077 705297101
    0x1c0506060c061501230a181d0601110c15090a090228081e04170c060f090712080c210403030305010e04020907081f090204090b1c06 58
    0x26040c0240c200215040003821103c1d0140b1a0b0b00401c140240d6030018032032407150038000c2d84851a20280a0218043d01c11810744806000064041e555002c50300746904014001e81a551019a0810440500c0c0706406036140c0307020800640407100c0c06100002c0888071501c00402e8420803c150418031400c0368424690150030100b0001d000c51000d020b40001c0c00b00e010742410404507544420381c1c60b059401d0301e10900080024a0080c007440c01c410f01449522070a8500c0e03158801d0321549020324045401c802460509040814a903108020200b1501e2055841d2441002256181c0040c59100c1c0720358015101030140303d02c0c1703040c00728605070054615045400f04031051700303030002000300d0b401303091300850040403c0c00101801007690501400e0700500c10040850351905299000030190f00000741301030100300c003880c000361408102d0003190101c06d4100300c2c080c0945850f15413090103036206001d001c1031075040c607005c84030700e040c8401e8811a9003c000c07c03002c102e120b41d40da00710190603034816003 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 705299577 1250 705298327 705298339
    0x1b1018021e041b20010b01020730030807021c090e1b031303020111070f0f0624090501050609150a030209031501030b0a0e0316061d06010513021c0506 66
    0x4103209030b15007088a01440d1079458454a500c00c0d0302031002c03031301a0340c103101501c2e90400d0f003030090a03600003e414040d140322540602d0840c030401d02c140241d01c1d1034031403d440ca80c0c81c0841482450b8004a9182c0a400075500f642e0351f54440c6920800340850400d6004002000002d0820141601403405500400000c5007500f186a00c0c58800c01c0a0700190f4041c0c40405200c1d2000301095024400e102c40304001a00c8a424442c650320b60034440d84a0040103040281d105004c2c608101440c1d11034820386400c0d060700742c8500141148031542404030300480c04564500703070000c40d081c5800800d03a800502e00801c3d00000c1c80001c440700d5025040819141c06064080c00038803616902400f00b10b40501020981149542c9113040c20004240080c240c020410725101c1c01054010000c41102c0851841e10b08550514410380303400c01c000c00000d4055003101400c0d21410300c003240d001c19643d0403624100c0d01ca21400a181070600100d10841ca42d0212600010f8480d800b28100c0e9000258004401071038 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 705300827 1250 705299577 705299591
    0xb0910020a02030a08030906240f01021006030c050f011103031f0b030108010f110a09060f050409051303020c010810090c17150a06170105060f1b1018021e04 69
    0xb091070044840404c172075807034011080103000030040101d00c0d40035501c1c6a0611040a0724040094080401e64884c4d010380d00b1010362110a900800034224050009803040010341ea40c2e00f0300c66201401801010700c40c0781240746400e001c0d84192081000351441c08040d600d145c031102da403144038000420101500701015540020405014400365000b010b1003030021072140e0724050310038110381944428003a07030740c01400590161584801e28605403106400c2002200030350790400d40300c2d80900e51254441034285400c108440d000f580e40c1c801158426001c80f0302d501031410055401c0c40d0201c1e41c5100d0304280d44410000282c03180c00c0302d03401e4407050811440c4a150258800324400d000c5031500c0c5000d0a072a481d10f040c0c1007412a40c0000c1c0810b00c0d142505080c0c881840c1280e403c10300c02c4910450005c59a020a000d20300704070390808544d00c40f4808000d0003500c8144e00d1300702c50003012070224505003079108010344440b154404554018088041d50944030244421000029200c0790090303907a00c8 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 705302077 1250 705300827 705300829
    0xa050d170c0604030f0903080703030504060216030e0f03070509150d02120d17060321040f06090306060b090d060207150e010e07080f060601050d14040804050f0306010b0910020a02 79
    0x200421641c0c1030035018000b2840c10341030240c0b50000ca1760300d60301048440481000403c4810081d6109140d01d86004a200e450700d05015001c1e000c0c8281301c41c0c211658105134801c042d00580108640d8000740c0e9506080808070041588803240c510a041d0000410300009108003040c12401350401001014280040003a0300421008001441483c0d8a41d020fa100d09055607004000c4e83c150b045034081c500c01c24070303055003c25140d40e0350401031200310546480c410501d0380100107a80140c80c680085550b442d0303480384001c040c04014802616200c0c505400412802c1742e9004480c90b4840160a8110030060b81d5160002548890000c0d078540c0d001fa11a08202c00c1240a076400380702ca004004500800e240d000380d801d2110301c0d0f01240c1c21b5400222011184a4013003100340c0d00c41400d09101d40c1702c50b21104000d000d40800d9401240724001e241c108010012507201402c141e0708190f07401c0410121100c285030780d460080c0601d95801a0520401069141450b446181c4042c68819034500340b000341c1c = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 705303327 1250 705302077 705302123
    0x60305030d060914012d0e1608010f030503040b0723071a0909070c0f0b040b0a06060c0302060412030b030319140a0813020109240e0f0a050d 62
    0x70920003402911880100002c260301c1c01407403003012003d01c1411030381d40341100d840c0d188014941125040640c1c003806500300310440302440c2c000c1510550f841000d14240120350390403048000028082007040001040840194038844140c0ba40400254030b801d0806000344c5440e005004200c80c2200024480c6d14a10b1a071020000c801050f00010104c0318104030b4024070000300011800d00c1c6c0742051041e180c1c0c540e2150107042e00f015084c2405e804642c0d85041804d1600300c41080a4400200c20040c442005405201301d0b1180491000402404c0e0300d5110480c1c441209410140040c1c1c4000086030204a0001959a429031a401c0006070750510501090454000c1c540c8200a03159155030908110f42040380041d03000807903034a4500c0c042140b6030286c0300d1035014040c0d2100c00b40c40d210f18000c5900030302020002d4460074031420149001ca4a9240c5d4080c448413480c0c00040c121f1013611110b080071800300c810703400002c000c84240da00300418042410741420381600e03050015009600c40d04108 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 705304577 1250 705303327 705303337
    0x702061509180a05070602060c070816020619110606010503040b0a1d0f0307020324010909110913030f2c27240a23031b040516020c010f0306030503 65
    0x1240917080e02498800301030704008005186240f0144e003000300740002081902112852006c8034a036111921150000c00d00d07900170250120b070303480015100f0102c2280c02001d002c10001c403120898440340e4604004403421f020540f0001d0040c070744400070588240e0306411001c1c0e00c4200c01c81c014260400300650b140340409071645240c0540002a036002541414030241c40090900000e41041a2659015550640c4140f20f40f100d0b05a41d0544038040103240c000610741018020221001411b00d036880b414607035100c50088003c00c81d461105145540902d808000d42e03502500226489402d410fa100c039918108154240d00450700e0280c080d6085200c807800c1003042d90100c61601c14a0030390018920941d0340c8070031400b201d2400300110481d03074440440c0c0064440c8040c44640f02c180c142d9400c1040003040c40011751602982c08203100d0f0708000c108407111010115400e00032912000691b0150b0b400c3c00203424010b0300f0010130005a540200807500d00d102032440d0000380d070765494680c54155045 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 705305827 1250 705304577 705304583
    0x3150430050a090b0723031c0c1b0c121704030309050a09060f180e0f1f051e19050a0606090801051e1e01031a0702061509180a 56
    0xc0740000c02290300c941d03040043c0000c40804c610b4000700d42c840014000340c80e103a1155892503125891951740003030007503400000340070801035400014821102c01402000120b000020720100120810922140d0b242d051b1235003101001c00c09071304042d1017030b2000052036010b440242c603a5603111042543e50b0014001503021355122809141010104625840780b98400340c401d5040400a104030310701e08c1c1981317003101d15074000c12124200720703055a40076046030244a001401440c103460720440000c1281d4000d6600384010f03914012a000c480400c40e0720036100c0c1c00144084003160744d241005103880070340207145104010501c00000d0311344010703103000300c0c0c00c00075a58994804002440d00910608041d181d03000c02801203181c4420441d50b4516044299120500c00b5004540c0c00000080101d5030841c0440b0818072541e12400c04c400d0740442120f003242e4040c10340002420b40391001c01c00c1400340c003580c82c1a4102034034503020402403c0010b0071004000b01020752410741d030f21040100288142c8 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 705307077 1250 705305827 705305837
    0x70203090612101508070513091b03051803040b070212030d09020a0e071d0f1207181515050d0606110706090b0a1101091e0c0503150430 60
    0x90007084412283c46280d01101000c03e407444044a03003a00320300c03581d43c440440c0c50007644400050041000102140d0300034807c413807502c0280c1c13614242c4088190449035282d1414002500d13150b502038113000c10b4a010100b40e070002c2c0402d100c4450980c00821051b80001e1007080c00c00400d4207910b040d41d024000d0031110554a000210450525108030701c01041c03070842c400150300d440100500000c030862552110302800c1c20b082240b6584080300000981c0d0050821068080d04075101079803000705000700700d91781041400d1a02006658020708480d510380c08401840a0b140486408031020443d080c0f006000c024041036010121500c1100000d15840c1d4654000301381e501085030805405030860400c200a410003800104041d10464200360845d00e00641d0006884005500501c01130350020541c652158007000c02007500300002034000d00503e41b84280c1030356282059074031010a41240e41034241c450015020608172155140d00484130442a030f080706a540511703084800300007074100414 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 705308327 1250 705307077 705307081
    0x9020f0402130f0501020c0f090601170c0c070b18061308030a0c0201030b0a030507210c080c01140909010902030a090c1e08010b0a090c021009061b0c0201080f070203090612 76
    0xc0328083c84100500c0d0038000707010049101d9007c6044c50494042c154005c401e0b41c400f0403816403141c1118048000c0802d0051803509203e80e10b0401c0d54003511034403480b4401c0001c0401ca132500001194489100700d904c02031443d940509011058019181d9001044664180081c0c4400140002d0100301c0450352801640f480301c1c4005070444107080803a600542d4540000e00c0010000194403003984c61281c0b130649147c607228403c92004241e018010560002e103000000c10030b0703000400c104015400d886050301c558203d202c1c0e40c0703d80195152a42d100118400402c15030059a0040d034010b41d041d4404562904103449402e1502c51650040c5541c00c2c694a01d50420070400701d555005d801c010000f03020042800001031403274042d501030781c1d581075600c030030380c1c0381c43c074020003844030345403104842804000b186080440040001094240c4c00c0b402144032a041035209501d020503882d03050310b420385991145030182c81907540040014041d403104000703401c0c8960703900c0301401a03415454110b01e528 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 705309577 1250 705308327 705308339
    0x18100c08010b07170c0a05072c04210908030a020607030609230c1b0a0c0b0a0c15180c03060b0904030c060c1403070305040b161209020f040213 63
    0xc00c1059126050201040c402e900c002203800348400010781801c00c0003616040c0d44240141019100000104075200344400001d06c8090b0340d11003c8003041e541290004904104120305122401701c50050010203260105500d000d200d080c00c550340386c107138600f00c1d0102e41c0b242d412920710390001c10b850300907030b0041d002c11541c0eaa043c01007401400325034405101444001000c800591114881083c00b000b5500010304401c50350b500703540118880e01d6003240090744800589440da5100a42911a80034240b40070031403041c1c00049414454190f640e82a4a007282d0b264031940912210140c0296078468668031540440c0c84143d0542c9800b814240c81ea80340345190003811100c0e005025406081a03030b0410000c00e4100d21681e45041c0c00c52000f240000010b50700303c40d292000184003110560100c2841040b0b58075a000760710444c82005001510f44a0b6030f0180c0b60000c80054100002d03103121982c41c070303481040d00894165440601000c2440c0d517044001000ea802821078071070126002e417810000 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 705310827 1250 705309577 705309587
    0x40e070216080c0d020402180406120506070c02090f0601170108280c062a0f020103181106070804080a050d35090c04110a0314060d0b18100c 62
    0x1000c0700e42c010101c4801c0c03100440e60300604610f010b4450369001c0b400c1048440103240c5a40003840c000d02c100900f5480d00220303003840038880415540c0e4841d03500001c00b0a4013500002468076001000c014869a45542151080340001d01c80f40c1009410040d881c022705900030030502800412000c1e06041c2c0710b0503004402c00c910200079161400c0c000041d01d000c505045002816101c0a243c00c8406844041d10304684e00c03485000319200a4450381c00509004402c1c500685241c403da800b4413252031100320005404000d0701c0043d1400880328205045c524000c402004500c3c42150380c00d06190382c0b20003550405141d0601640c898029050046c0f40c80e5210742050012070a000380c4900d03503c0d08502042c424070707003081d50304001008500420a00c0c402007010040140d0020020b1000301600c0200f091590094054180440e0070184901d5090f1441c400d014072031840580182d12007030340c68031000c2d10703800054101e0308140070b0300400f03080b00c9900f03100707030300600d200003602090516616000400c = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 705312077 1250 705310827 705310829
    0x10501170c0a0e030f0a0507030303061d010509060d1a01170316120c02030115090e19080310260d08040503070605101809050c04020703021e03040e070216 68
    0xc019603054100445a2201c0060b41c400d00400e14041403100d060030080307807030714038281e10083c418440d40044078204600041c440e0107032803207940d0607c000c2e07039910f030845c042c81904020b090701c00084500510081c1064280603502002c000d1000300c12440e80d0321403e0004240d0041c85408031004001401105100e81a0300f400310980c20083d071402c52500048404a56900c01c020103c1d018404914a1148114401c40890750010002c206c0220001062402d041c03052080b102c03043d00b00180c4115042c0c0c0407501070850100d8103928003200e070b1a9521110142d0000f09003010352809088040f544451210f00d004000c0525a105c207214101503010b03c1c0703040180c0294000701300da140c080100161000c0300f50b81e4007a41c802e00101c0d0030f0300c0305018840c40184075000703209486850400c591703020b0f40a822100b603081c0981c040d0b8a03a4558602440140e206154000d000340c1d01c03038012a1450400039540c0c2c050954090256410140c03a0b07401168a5441610000c00507402500c11803419054200190 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 705313327 1250 705312077 705312107
    0x51008041101050405031b01020718020d0e07050d140a0b01180f2d060e1e100f030b1b1303060c0801050114161208010e130f020f12060f010501 63
    0x2e8189445c0100090750360070400c510018400f0303172001354002039000f001313070780040c0c049100c141007070390801c819000080d0040390362000101d00700001c044240d1000b103052416140060610003101c600340d00c407c3c04440010341001c24912468502c0c0300071854072640c0c0c5000c3d240403801c02200f61414070691701600c0741041c038520710518040c1c807030120441d0400c1c103000c50580c0006421103640008140c000070071060380300742008084001080f4100c0090340240d001001c02c02002011134039041803088040300d040c0104541c0d02000c810505c0801c0784210f20b994009041002061140c3c030810740d204940d00101a1510b030821101024403c00c6858040d11064080c241742000440d032500d00000c0c03618100c00106503442c1c8001804616038000c591002c419582c0140c440d0410310070710b01d0b0041004400344500010420b12902085407030705481201010740ea0450903800340036a894080101c0055502c22050340241c0035001044201c070705000040c828580424982610362406c0005010382c2c003211420 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 705314577 1250 705313327 705313337
    0x20604260403030318060e07080714030706030b06070f0b16050315040e0705181602030a05041e030609060905070503010e030d09080c070b030105010e0409051510051008041101 77
    0x591111a5688151002c4942501e004102c408030641c1125240f90900000383c04c3c01d060460b460083d0500080e017008444980080311003169950340d80004850b000440c0f40d91640041c1000c0100e18400e41100c0d0078500010241c4d032511440d555041a0a08451411100941c03030600f00462610580a81c2c01d140b0740606001b403135450b080225901030f449007102d582c8a0b42c0d40d0a603441e0f1403c020071900000c0d001c05054045010362010728002030002c1160301c60f07200f6800300000c804583c8088242c07000d603070440c1c41d00e138101410003000e001140d119944048100c105080c000020898a01950121034000d2000155000780c6041c014209034003500f041d80242c1c1800c03005042020300004560a010800400140300100d03403a28075950310540074402514420400e011400b29180300045041740c4023603c448800c500120300b44803d45a00c000050203a80080440c04000c039500c0401903840810b03020304100317254441000468225200d4002000180c40703400700010001d1020102500c03079424240 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 705315827 1250 705314577 705314633
    0xf200f25090c0c06050901110f0c01150503070b0703051e0c01060602030412060e01110307050a020f0606060d1a040c0203090901170606150d0c030c120504120e180106020604 76
    0x15051140f4140010000e642d00c0000030710f00c2400b0341c401d00f42c20102d6012180d0360541513400c600c542c0c200340c0407000303030354607048142001c40900149081120001760160100070300d002c0200d9401c0e0032850095080c0b210800c40c00c01442098504511a0f500340c80d61a1b465980c8420340d5070031213a09400003000d640c0100003d202824076420f55040d41030f4024404204601c8421886000d015062070703400c00c0803000b00a128025030444060000c1c3c1e0300c40d5085030100c0301c60408107a03403504240d400d02c0d088401044100090506500411001e071680641641c0501491000c80c085400c05140c070381c01030b040401e1196a43c500b03000000c0c01000701c1c2d01489580300c10f50028a03100e4001604052040c0c01d8596858000462081501c0304854080001c00c030051441001030080c000701d000d0200001e2248541e0b440e0700c40c0b070f8400d890240390050360589080301001010f8503030f003034a103a84a85c444816004011030340040d010850180190313a0191140d03003418a40381607d40c00b510035200c00e283d98100c2c = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 705317077 1250 705315827 705315851
    0x4050f0a1d12210705071205070f030507050a0b0c180105070c1415030901061406130e1503012c0f0a06020d02190914010f200f2509 58
    0x500300c00b0702d00403a0710a40e0b42c1d584000c003080707000d25402103803202070302d0300410071100d1904000a40043c6000c1c1c1100c4440f44544501143c00b03200f585d1000709101c0d11582070303001182c8140d018180b0079120317008076218001c2a840c0c030303c8446412295200000c80003d01800c0e4104902d81c10a81c560003806d055040800540e00d21080707607003034002c000c401c0301195240c000e103648d07249010b101c0040300d006003580c80c10511135045c040e09282c000d10b90301c0110003410000a041200807503081c0201d082c440688a4104207040244180144c040000054001e8403141030703541c20710800d0030020001c0041c0d040d4403101c0c000351003886c0d402c050903141900090420304001e8000308001d002c0e00d50001c40181c4c0c0b6050303011701d10000e00662080600c6100300c41e16104060703030881c40b12410364414200045d500d0f2000d100441d529405401a4400101c0d000e0f08642d44815101d62640800b880034180c941c0036209241c0c4514250840e40303409100d805602c4480c16507000d401079407002d4040000c040c0002e0b1710000d = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 705318327 1250 705317077 705317083
    0xc0d09060f0c090501211b030c03200706052a07020f030a08040b0906070c030f0501061e0501030b060c0f1e0a0c2303030301141305040b130f0204050f0a1d 68
    0x103621851b078903035490400c115091540a402c5218150a889004840050f0000d00900303813081500c0c042460480e01000c1d03480444041440300789506090b034035086c0c1d5540d80c030f0060070000d4801920794048182a20b00c4070302d400c0c0101c0201da000c0604685940e031500401800141d03404045000313801c19484030012403a00000c035402d0300c0d4061403885d90b5407084800305281e88101540645586003080c80801081041c0050300070450069000b4440c0301e840e150031003108000400d1141035411082810842540030b80c00603440c0b044000e1191381030028000069040080ca1107110031079401045203060078900e070400d560800e00401c0d00416054200d60303206641c1046d940511a104a42c00c0121f4110500340c000c4130011034405000c1d02e0300c0c0c0d65903501f403050940300318964a00c00c2200c1081c13102c4241d02807180d9441127800c1030318a0311944a4030158411004100c1007501e2034460101d0020161b15103019032802408074242650151500b180700408450040401349514500c51916555400c000 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 705319577 1250 705318327 705318347
    0x14070305030a05210915070903051f0c02010b1003090c0e0c07050f06100e06270603121303170c030307050304020f06031005090604020408010608100c090b0a03050c0d09060f0c090501 80
    0x1000340312046d0f031102c510075141e181180e40010420712801c0d2401c8031003400c158050f20410b00f46001801200700d07000c030a900f038904c41a0f04a401442500d0b003240e1161182d00600f03007860040c0c099055480d101d021110b600003080b9600c40306a94002000420410100b01d501006400707440944000c1c213000d030030301071128403500c01d000c0180440000714081c0d954800381000c40c03803a07000c0c281c00345c7c064001c0004e200700c1b01114010f1180c0a0050f200c80c6000c0d00604a4090b031100440820101d421559221042d850307010042c2c04044041c40b18080021042004500691441e2211512441c0910400440170415440180100e0b81401401000d00041c80044103a5000701c420030382c987c3d00c20011500074000c41d44012201d43c2020400900010003003200e410954420307900788541202161301f40ca00e01d04502c074032000301e0020003203e8100c074440d51005401038081031100d0700c0e01c10310380e40c0502581c000d0502a50720f69503aa00c003100c514010300c41c0c411901c1c0c85061000e03c240c40c120002e000d100c00 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 705320827 1250 705319577 705319603
    0x4020d020f04090302060105030c0307180c020a02030a030915050f0306040b060906121f1a090303130e0a060515040e060f0414070206011d010314070305030a052109 72
    0x5004454000c540e00c5031070032010410050003c0000070014100203590f0031080c0f0a00e8003c0c0904c0c88401407908000c621f48040d500d001601042c00c00416007a540103180f8403041108601902c0c1b07010006943c01c0c03100407000f03030081e80e50380c2d00c00341441c50b0802c0320852046d65a00348031b801c0004c600761040c072005990340910100c400080c40c900b00c00110351248517258062340e104000042d5103900504204015004000c0080201000b01900c13010415000c0c10340034031082c4034a1480e00d1816035003690000c100b02c24018094a05011039484145003007002900200ca141c4039070000c100c0300603c0c5205010060400b1100006501014091010702e0300c550b000c0c0ca08130703d18280000701191a5441e8040000d00098007c104103900c0c0d0b0840c10620400f030746c1d5100140610400060a0b818581d2488401018002c941d140307a480c3d6501c5401d80140d00200444034014624008045201030018190220940d1075440eaa00c121180441d010480f10b02d44000b200c02c0103003400034400d4006038481078100e03 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 705322077 1250 705320827 705320839
    0x30d0c020108040f290603010905031b120712020d0905062d0301030501091a091f09140105010f06050c03030402010302400819120e12010209180f0402 66
    0x459044c0151044501080901882d41d800c0a0200030340265401d0500102d1400e80000700d91940002c040c02d0301c03d161b0002d01154018400942a10480b0700c640b4202041c8500f1621500769800c04600d664101d40340964980f01040310b5601e5451301070100b0980040c1616140720b616080c040001e03514001e120780b03c21009840900580142e0907660600591081d40280c5522980e5929015028000307507281100c41000103054607601c1c0544030865802104007902800e803040007000a50031290b612883c1c07083c0d00340c07100b40c0c80d0040b640d80c003100764040100000110342e544c100035115034810710030b40c0104100b14040000c40404030b40030040d01d820950910300540d030746c859045000f06010b41801c0c100c20201c012428030740c5816070005031044856040c8209103015540d00c60b0f054698042901042010050a07150310000f0001c000c48400728400b814408042010b481c0411000103c20300c0035a9141c0d03000400c448545001102d61140072520b04a00103e0b10b0000000b0b00401400381c00240961 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 705323327 1250 705322077 705322081
    0x30c031719050918061f030f1d120c0d030c0507020907030603020f10080c0a0915050a0318050c040c0315030305070c0f0f090c03020d2d0c0e0d0c12050f0c030d0c020108 74
    0x40c4a5006408c0c61800c0300780601c42060301c0400e412607400c0307480b4013880350311484c1e50000110318580d090f207041095810142c030009040801c160090b0000c04490030420900300048030050b614148507038060001070f5030005000d400c42c4141306256411301485480341203032a45100c1c11591100c202c1c0e9001d01410b00e45134903210592810303580240d4a4000d0788820308444503580505510034081c001c0040c542d9003d001e401c214a0000802d10710401f800b62240d001303014290698205a001080404802e1030000340c1100000f1055812207030325081140011400100c1c0030a02010400400c081e1503d80039180d107552030480306688010241c41074100443e1180d540c0705010707000c0e9054a119090701c580604c8400400740710207140041489502c00010f03100e03c0041440303030082c89005401d41260b1a4501c0d280501000c04c07054000c001d2084900104590010a200f20411010041075105800905200c6020b41109041510000d074213402030388100c448441640c0d0085540c00b8164081c2491684d039 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 705324577 1250 705323327 705323389
    0x180e01050f061e132d0b0607061505361611070b1303020102010c0806010f03090203010e01020f0a1709070b0a020f121306030204030c03171905091806 66
    0x82c440000051001d6281010740c20140745281e000a0910b0740c8483c4414007802c17402c80480899044041c019041030041c440c00000038201e5115134030f6400c60140c6540c00c16660710000d081c0d079401502042c0c040c0e020b032144069081e250455001e1041c50741030320314003a01e000d0b641034003981502245c003010000080010403065030240981c1c0058201d0800003960341c503107403004400034400d51000720300641c82d000e000256544204451802100140d48003810b520b5812400c40142c00751510070780c0e065580310903100121400f44010007190055086283e101d00c1c9250001d0700c0c03a4084e03401188070035800000c000808102044003020b417590b01c83c1c1c040c0c81e0114030354101e2070700700c901888880307520a006d038004c41650700202902c01c8840c129041c4c0c1c0d015407125411000e900803488020007448d24881c0a000040c801104100418001101141080042054204001501e91a2001096000603103000c0360801082e408405014600d4030015800c00c400820125911242c203212066201084c20300382d = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 705325827 1250 705324577 705324589
    0x1b020d021c0c120b06040c1d0130050903041202061305100908010e1f0e150f04050d080402011220040602010e07150f080601020106180e01050f061e 65
    0x1000b60071200d0821510b45554001c0b40c0c0f030808200c1620704500300e4000980b58030f400d01070741caa0305c4d06565a160030124404039210001031755880c409d05000480240b0000441d88a511400d0302644000141c070105c452040c2908450b03010700f614095400821007400045c001e0f0804040241c0c2c1520340d00d9070b032540040c403c40d6800040c1c2005a01000095459561a031300c42e0040d03042e80d0480f8020494011580400c40c1e03103031804200c106100d40442c5147c582440709501856502c0c0f004810b913500461542100d030b005070012903c0d0b00c1d40758243d030280700501c901006000d80c40390540c14000481e082c6a00040d10b90100944c030703501c49984a2200c40828607040c4d515171080c1d00081d44843e22140c1f10400031340a4030070504a50309504c100d1400003408502944a580c100d40c0781d1f140d5420700d00c2401004c0b204036600402082c10b540d00e89600250f00a030108586c9403011000d080005e0900075404e0203820f50b0000b07411409603104210501115543d0030a41c08440500b6040c1d0160950740c040100714 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 705327077 1250 705325827 705325879
    0x20a020a380307020f07080706180801020c10061a04090203150604080c1201090b180708061305010f090c14040e06040302060f070f080c03070519030c1b020d02 70
    0x50040003880740100c00d0810980a140540e21a400351441921211728481d550310840c40b514070340341e1108030704001080c00b51040740680c2c0440c0b868044600c1e15110010b01760390040f070212000341c3c0030b4031207010010420f128600183c011441084000628103c2c131401a01503030081000307041d0b0000114011406100300d00e58400000703030640b030321290303102c14040d150f500c0c00c2c00c201e0040301c0300070303104500070418410007010640c0003002d06a5501c0702e85e422290320714800c880b001d4520840e0404203580a003000304610902c8010004068900140b07031060070b55200420000700c06041a141a001403c3c20302c4005c16203502a000c0c6a5160016001a010b8400350382d054400b401924148414141d002c5081486071107150302510203501d0325941118018110755803e4002504030001c180300c01410760003590021a2440e015091500d00c030140e000006000c9900000320366108640c1d291650080c500c010282c20841105007000c4440d0042409042c038403000034810344881c00d800f112462081c2000c8 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 705328327 1250 705327077 705327149
    0xc0d0b041103180a1e02031603080904060e060d121202070f061d0c0105280804060b0402040b0f0901051b010b150c0a0201030c02031903060f0501020a020a 68
    0x1000700d150301c0e4580900340e8401c1c3d414110003441c818680900c05800543c0440595205d401544031413140c07110450070107117050f001c0340d00d4080c200305000311440904036000650300800c0210358030a00b8004100c00c981481d4000c00f100220030041105950303d441c40044010380200b503d040f071504e112000c0f030341881c3c030440312041e480c4045145028059840410004944502c0e002c100c22130000005110780314041c022029142d20010690205520074005040a5400042040521001568850984c0008041000000361268200428400d0a024101e0159800d540440c80d00f41090900c4151f4400d0001d001490760000640032040d91244017120340e84009501920202a000840c07540a00600d8010034410090741749820ba4940b4840c084072802c100c4000100006101030380150003410b800c0d20303000c0950100b400290a80303207619001e0307419101c0ca0341d00090f081d0f0a00380b9907101110150802411540055280c2d40103031a0a00240305a440e140e106160361100912000b401c2d04103440701c0 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 705329577 1250 705328327 705328331
    0xd020f01031d060a0b060306060d0f060f060c0605010e1302061308120a0305162a060e03040602070b0705061b13030f0b0a0b060406050904090218010323060c0d0b04 72
    0x202e511401003030b1540240300014061000c11340e131408028071800b05a4406920010400110145d0109684408103400c540800803a407140c0d200f0805032117640315480100450343e22034001e010490140308090141c040c0001481407802c00c084280120486100001e00407000094010409c856400a030002058080c049038680c1e2224046207440e0b4016480c030001003400c103008601c540790039500035030112000d070380d0f07070000c101d51445003080118205044032034021032451010081072407030190340e402c00e41c000d0096907110700e03105009181181640c000103600c641440007a0001d140410016040704102a2560341403164005d41d07985071041a442c0d080446080c40c1c00030070000a41d01440d80c15015840b0744000740c3d00da01440e42600c01095040341c1c441400c00c070078401035018502070010b00902410001d010106036001c92800c0c485e8081c006031540348000104104804100c100c0c0300b6000d84803c1100c550f09665030710307964040141680703003a880c000c100145a205c0c15030007108503940003002 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 705330827 1250 705329577 705329621
    0x90405090703030212030c09010c06091524080303070c0236090c01021005150a03210507080904090807021e090a02091c020402040e010801060915050d020f0103 70
    0x369550405032100710050301844101124001d100d5095034401d0190070035140c601450f4600448041c0820340003144d9103695003021070301084040710900c02c0c02580340c030000750740104d0000b81d103035004010030729940d01300007543c09003c011400310580340c1001c03c9007041001600300340300041603203241080d1003042d0b200d14000c0103408032600401d44071140ea45031036010076880d07000d01181c8619041c801d9a015906c41124030b9130404050780a2540003582d5071204004103407a00001c2c40c0a002c0e5801621101803004c1e0380700783c03c030440d01c0092824100f0f0403c00d2400b02296a031000c2d80c02040d05103486107130346510a0742400001411164200e900408074141c1443c0400303282c040700ea04587d000c1c0a840004000390540b030720391003183e0300403034000e0034650300004031170343d40c80841c50300602260056003c0c4000200e068012310740d00e000c0c08110001058035070500c616581124903000c444800300580004c208600e8540e60004202036070151131104608020400580241000140307040c8400305c00ea039 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 705332077 1250 705330827 705330841
    0x90b07210216050405090a0209220302070518041a0702100903020f0c0303040609141203040b0414090610080727060816021c020703080d0605120607080a020708090405 73
    0x707540b10154404003502001251924240800c43d802140c50030825070200f881003015141404806a03c41c0d1118886000c241d0301046450b090031a450307044003d03a01051040c0244c2c544a80d80ba041c0481d80c3d42d81402c1850542c441300d0143d102c010f0580e1030300c0c000c49e0124040c03503c00e0203d90001e100c3d0b40806c0c00901c0d550b03e40295151403000c0a50301c07901440310041023901e0302100311400ca41c02c980e100c03420305040412901c1c070a055480c18907401102d1485c8401c071410207101910040c0126200e16445506d000c01070101c0f03210300b042091145041c1c10070070185079201448016183c03804d01d0301c2c20281d42c03042025036041d141c002045180a40300c0007100e002c1741503940c1003415113180b613803903c00c10380700c016204044556500540b809a000400125101c22444c518140309503070ac0d03c11100d0b195980d0310713680c15a5000015000342180c07034104c2480542416803180c0c07595000e0030010300c028500000010101b51000d07280104503500054072406000c1c06070280d802284c4014010440d170f0030044 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 705333327 1250 705332077 705332083
    0xb0a05060f1e0c011415060919090603030810180b1c0b0a0f020c060f040c0e04060f05060111210708030a201201030b06120d02060411030a03090b072102 67
    0x18148026545c200070400d540041c9403040c941c007070302c1d800e05c0c00005140c4e000c0400c41690030000140d9003100b21025034100f16000926054010300200f10000307000380c01c506000b2300c00b40f401010000386052181d01040070207081c800c441d00d1158401800204040b4410008480c0c221f0041c0c0d2500d141c01032000481441031284c21540201da15080800101c0040ba00e13280582c0520404240c1c990402c00c00283d040c0000403506500c81d10648611151030346401c0c81d985048270139907041d141c95a03180c0001a04c11b449200b1550428000d0800900801c4890030550382c0312407107a03d155070b00908042504200b0300030811780f1151a0f10050840e102d18150001400410107401d03045950100c0710f100a41549003030b0200c41c2084041d000c4008503030b00b503484080c030100014140301d4001d911222460481d11090003036172403200b25507002d44428105414507101075041c1da410644650898184a80020342152102c0e007151000ea031080e403184042c2c10103604801d42001c4400f0b0300024801c0c1011865408 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 705334577 1250 705333327 705333337
    0x1203050306150d0f0b121216060e19050c0105040b0d0c02030c010f0905010b010e060f0703120e01090c080d0914060910091703030f06330405040608010b0a05060f1e 72
    0x1950603580100031000740941da00e00b100003007008501c0400c0b00811748c1c5840d403208414580a01d00106804080100031850144088aa100c41011041c0801c0800806000800703a072442460000d051606005440340359100d08000d42085a69580084010314000c1c001c0e10500304540c2d000700144003154003842c025295012085900c0c2d46400103480507580525458650010007509250500903104580c000a6004900540902922500404841c0003500031481e042025071b0010421204030300c1d0189440e8040c3e00b00c402d82d41c10860704140c0b07499001c00c4880880360315620400340c940790400481c025200d64198907820902500640c4000780d00500040107d03060089810501c40d10003e0158690200f614585454442c89021078400d29008100c41120b034070f55408207101c00a015142c5440c48000f03441031110030b0001c00c0030403070785c64903202d06001404500001d00214190a000480c0110140100703803080d4400708505000d101c1e54410b4407200e2010708000060303a030882641641507040 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 705335827 1250 705334577 705334579
    0xd0b0114030a241508040609060911091302010e190302040608010203190207030923040c08071b0f1b08010c0e1c0b011710020f12011203050306150d0f0b 67
    0xa0321002c00d8080d0b0b202c81c0318045070414492500244c50710801103c03d10005041a00d85980340c0300c2c0c2c040070030030030700c140b105c1d0520894100c00c0c041d0108042c4582d00c80010111141402000d503141c0150341c10821200c8400310441d0315004884ca040c8104900c0c000355040030390000d00e81580410701c100154011401090030369075184810b401c00d02500c00f0b03440707488402000600820000c01030200f40f40c000d0840000d0790000c65540951a5011508440c04000c0d0080003400312401d2003d181d0304280c142c105030785010403072100d2615a841c0c0c281c0d41c083d6408000c0c648048101003071000303050101843d010b025848024841885845801041c0940110305684900503003501310703102040201d20b822000754800b2040045030310b4120100110b101d59404951a0b001345c080c0070f0040645c2e8401004050314441c1e56a40340d0055000910062a050b086841c1c2030f0709031008000440d230082c3c146c9600103c2220000315903c4009210190b038040c400a0b10402030802d8cc0d400c117078604a801c00d07600020 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 705337077 1250 705335827 705335861
    0x1031721010815090d0e0402040504020705010c0e121507110f07050310062403060b13090f020301030c0b0f0702090106080732090a051011010e010c050d0b0114030a 72
    0x3090480382c12405002c0c3c4030030106170310900242110070300880d26040c0c04800180014245541c07500400c0236030303100c13040480d41655658007104159030007001c0001c5100c016142100004403171080765035202e036144072003508444203800003244d892280148440e42d401e001d0548040f6132444605030f94941480c06140d1007401a01c03003180a4100700e00c40c8a040301c0c50460202030644065140b0040e20704d204402c141010b44458010508880d40c1c070051904110500c2d81149503481d0500b40070031110003804201400d40100010004184c405060806031840d1000955031344100002c0c0c441c05200d009402500400c40100004006810140c6075206060640b5940d2070301481e040c8600d00d0007100540107141c0c41d005507074407060342e007024042c0c545240c0c00707000c104500f6241c1000035400031070702d0300000000306442e0b49032701d00303240a00804a20f290030740000e1040700700001e0050868051788041c070041d00d544402e00703a2940e102d40d10089031682605440c030f44e1303410031400b02c1d8050083d0444448801d1 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 705338327 1250 705337077 705337093
    0x1090609020a0e0108100306060b0a0810031214070b0c03150307050325082509060302060301050d050c09070e0f03120703050a02031c0c0f0203030f010317210108 71
    0x80380c0da0007110340c107101c10380e00c1c41c0725140e084005480150f006800604a07501b80390011000625138400e400192522079140c1d5143c801151005040703e9009140c4003030880190020400148946000314620742c2905108414034171a2000d04c407680101c00d0003610884254060040c10002400158019400000c122245d154908141030343c80a5602c24075070150b01490020744034041943c020784418030324169032040580d03650402c51401030001051a0011f072884046041d040c2036600039401840c0d140000d22805107150005403c6001c140f207503c1c090300743c1103604010407006009007464003600600030340ca2401c20943c02040480702c0323089030f40207418140c4031001615001610300c0702512400c40d0546030103800c0e50101c60071b810507403404065210a00600340140f0300d000c5002c6581440784c500064050100740005c0c000107041f584c800035508100184800f481031050b030281900d0700040b05456601074040100128810042200000f81034245c0c2202c1c110000300c0818101c58144040728441c0b = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 705339577 1250 705338327 705338339
    0xb010506070f1104020d1508070e15091003050a06060f0504060503250302031b1e1c050c2101271b030b0a0e150c0904020d0b0402070b010906 62
    0x140c811034202802d00003030005010009200380c166201c045030080c0001d4100884108084190307810503000c1a07404025800600c0b00700f504211280091403000c030416094188000340700c90420300071151a001d8072001000174145c1d03214000200c000c5030302c0000c8848480d4241400c00c0109101c0c050301300d42c44004040042c107454640150030070b5a000601a010300802c02054014a002c8035000f00c50a6400c0f01000000da035003405106007520000d00f145200c100810108040e0700720b0340d5440308034071803022000141030700c1d004c40b815a400602c1088966484860801c1850142402c00c0650301440e00f2040f06100102140c2196100070200300a02154540407110b2880b901c807070244040e0210f0100c02030002c1081441c220400d51104255401034903169241d0f002081002c54204800340c0d100c6840d090085c2040110702d0101074441018201c3c1d060040d182e045034410142002c0c80790f5000b103085540f0945c2c41c0d11204069200a01c1159514800d10700490300d00740910820700000d18101000030b00d = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 705340827 1250 705339577 705339589
    0xb0915090d09240c0f0b010e0a05090106060e010f020f0105150414090c01080a1b170f040b160e0d0501090210051c1e0e0f010b1503040308061f09030b0105 68
    0x100402d403a540041401d011101118a807801c804140c1e0854146000d40006c11401d4048078040c1a200400510341e2030f241c1e20304401e4403001707441c030003441c0e15100040105591188281e0007003442407902c8103891480d40c4049290080582c00031015519041c03e01c40080041d4403142c01c115016141070210403030040c4280c40003101242c085042c0d401c43c82c03541c00386601c50380d0103a610210707040001035256410950b43d00044480c07403140c00410a801c681c0300b1044096080130b03600182810241d11303103240c150707680c01c0056000740018212907c4102560001801148440d142ca000036181803044682400c01034043c00381008168020080004c101c11000d103d88115800003a04c402c0390141800030306081c00060030340301c4100524003c880044034034146036014210b0340c001d000d0024046401c110b10f000c0d0844030f00840c528411184129003e0741009050140e983c06500350414400c0303503035003101042c1d2440011151714500b05580348050703c210380015104094034010050380166a03295814045 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 705342077 1250 705340827 705340859
    0x1a16020a11010c08070605010b0901090503030a14090a05030f24090718140a050a060807060c1b0b0f0d0b0d020d02040b01091707050f0117040b0915090d09 68
    0x41c0c0c1812007a1155940100c002240607840303000b0207460843c245e114a01190741c00e804c1200b1203500001c1e100311640e40092100c000d088114059850105804000303048654000d409031000305c008200300400b0ba540f459101c4c0200400b400f6520300010f810425034a604410800b804640d91086100c1011407071041c43c10300c02d0030340c440201031050400003007038040440340341606002503c4006a0138940644074a26024221418010585090140d0b208d01600c3d15904201129417102104000715544a4140031260b0380010310a8411070411141106200007a00061043d080004900c0740041500340101211142400b0810004041d03c0400c10500403498019512001810444000d442e055006592904050400d114103990b01d868000d54015081c101c1380d51900200e5007045942031040c416611503400b40303400300e001e200f18415203145035070141010b8a540204400078104c4c01c2d042100d20100e00845006120a180111900741e50b2004109140b002404500300060058441c074a118 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 705343327 1250 705342077 705342083
    0xc10050105100e03191b0b0912160e0c070b01030506040506090105040201091e17010605030105011a0f0d0209090c2203021005130515070b070507050c0402030406091a16020a 76
    0x450554124401175203038200422060300c13008041418a5981e182c01410100141000c80040b41c46490801c2008241410a20441501e4000007101031072101020070b0701040d900000000d4005440d81507228815000d127440084c41151342100100c00d00a0005225200d41d10660484250b0781da00203e090a07124244c50003404a16020b1040c4140841c21000e42214070810618014040c0c1c2c407000f003c0e0f8821640e04e0f400481c0d644107401d02c6581428003651b4050001c0048050181441c10b00e03003800e91150540c06462032030007140450403900e264044804002000b000c11146041c00e03009000150301c641e403403e5407601880058405545020b00704002c51340c00a103400e0752200203034401d855907070140050307212506102d24003007156510301042910071864074403440c0e240c114905d410790140e10701400c1c00c810b003d400d0160710000782000428035014102a5030258403521149032200240070000c0e0010403d0400c5c01d0788405a00c01c04401511400d040d581080e5609403056080e610f4000c0c656001d = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 705344577 1250 705343327 705343333
    0x1213170a030806061314040c02060906061c12030203010906060c15020309011103010306020d24030305090d140c040f0c0c021c080a0206150a0b0d0903050c10050105100e03 75
    0x903010034011482c95a001c03101421031482c08080c50710156010202d82c016280c039000c407080b030744502c1c182441540c110800c00d000520090415000711503070713403000802c40303882600e1100c5550482e6461140c0d0310426039108401a244031101e00c401f6010b5002409101000c2d8039250000500900c0380c100b801d540e641145000e0010416803c42c90041c3d0700042804149640f21000e58401c00300010007540298050580161620125202681034881003020148152490b1241181e030000c48684082200d83c142030a9540d42d0b0740f00081489090794500c041c099024866542e00b85440220f00c3c8450460b0450381003020491a02e01ca134104c4041000300c02c002035504160303c006040c51182d2007c030244030600000611916a6400020b501440814005801c8230f010f010600020540540782c11104a9007000c4060806101105a014101c54081d58a4aa43c01c0e00145070051080301d0141614000351380d490340c00005010040e150078030505000d00d00300d280e1404a14410b54084103c1d000c0100a = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 705345827 1250 705344577 705344593
    0x9210f0b0711190f0b1b0d1a040603031709010f111b0d0e150c1207061505060a120906021308151303210207030806030d020105090c0d0311121317 64
    0xa0701c0300508024100c0000c000e2501e8402d6546c20140d0143c0000b00c40c40801080c4102503100144140141141341030040d070800c102032000a80141d50507850303000007184418103950303a0042902400c00d1404c01182686000d200d180750300031713580003460b11650b00030030b8032062078030a0100b40c1d0300c16070301e00d0355000258aa0480b0303e01d407404100c0040e0ba581c041c0c01c2e4034100030703003507815904100080c2caa450f84001d00184000c10098503029a22100314942881d807000c62a000204006204290750320b17042000d285070030421000c450303018840d0503810507001c540395200c9119084600c00c06004900d05407051078103032480200139035540e030b00c2401649200024400e40e40c0e01522980c00e1040081c040700012121004150003074400390030b1190280e03031540e01d641005d209250034014114844011a4145010040d03010b83c00200c1031103580054640000d006c05a040844044220011300803590184c03400c16151490500c02a00002e01903800c20091a669000c4802a07042c008101c61a40d40000031 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 705347077 1250 705345827 705345833
    0x1f0210090c030209011205120301030b0402060d230108120711041e050405030301150e0f1203070f0b01090c090602060c092106090d09210f0b0711190f 66
    0x395005100300310503200d0507126070000d92160001d030032000780f944a803038004041c05070400c11443c004410043c41c4d071943d411a112442c000c40000d00c06406498001200404011150307c81400b85880112a0751501e09445c19031204060a10900e0200d100d0000d41c50510b0807076108584031181e02408030420030407241e050001411080d030311742088001c03810490341402200d0189510482c4240c01550740c0e50305000e1504a0a40b050030100c04210703a13114500d0b80303612240c00c64608580c0481d0031100b2540307400f40b014a10302c2207800c000c0000f108144803404006052443c1c80c10386016801c2403010705404402103505100d98130a0200503800031000c01c48440e4100028030701244050070f010f0000e043d40c003c4640c03624041c099006141e101c5400c000b1040c1003840602d4200200785411325540d868030080350109403025520003070f400703003002e1250204400819001c030b9180d4860100d10306c901d4140ca01800b1b07125120303d000c00030302400d4161000e0400d009480501c490780300050172403004c1e043e1 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 705348327 1250 705347077 705347081
    0xf04140f10211109040f030801060503061c020406081f0605010f02070b0901021911010306090b0a050103110c0a1a0619091d1c1407020907080405011b0e1f0210 70
    0x114281c500c807a000c4500f810703680324071200c01d1003a801001e60303003c6a40746240003000c04105900c1101081001d009000b000e03940c514150780ba0040000c07800703860b000309000280c000d0542c3c0e44440903030702c64881186006000c10490581e003104c001001c00c451565640103407103200f00c0d102d1080041e0021003081c04a1070707890000d020041810320403901e85041303100a041c03240e00c0360f20043c1c40449000303641416940c1e0500071580a013039144805d20600d4520004900302c54068012541455101e001d4640c0c0c080c42407064070600030301a000c441c1e89000a00b001d000700c1000c081d000111144000028a007400c1200c5140b4a5054903140000c1142c90a40d04400501c000115080750254846041c440380100300199101950900840807120b00d4006014091002d41c07041401d6030703e001d001060140c1e68403c41580c1c40091824015465613551030003c4c0109280380d400008107003401c465580c001d41c4a10b20b00301c280e105460210990b99a03141c1401c400c0e10712007210380160310010100d80862015 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 705349577 1250 705348327 705348389
    0x1f1d0307030c0f030c02091e090d020c13090c0f080d14031b09030d051903091104050c04090204180b0103050405070b09030307080f07060c1d0f0f04140f10 68
    0x1905c1c0c00888001e050380021030046081c2c1740301240c248407411400900c22010015500444070f000140b204200c5207030044c0d01caa402c002c0003072044078100c848040440c4d05412800d000303680b040c6048100d58403142113a40305020b5004641d40e034481c5517030144d0344902030302095043e0740c2c0750b00c94641150340c3d26204101c40d81402c0d040182d038910600c960160b68030300b00141901188913072200740d02c2d40e175400489024107040781d14500c01c160609a180010401128506e0400c4105550204031552030f07200741a02d0f48115030140c1c12aa01c000b80015000313804641286110007003031410f0181c020342e4001182915015240601a07410404003001a511400005d1030002009003da03802c210b100c1d02c81c5442a0080865261105800540841089611b22512400c2c858500305107488920400e15210071034203940320340b4080e5101604100d21913a41c40c034904001c140c014014000040c003140c81e040d503480140c031154030388031100000c5a243c0b80050f07100d40c150f42041d01d24894494003132a503c4001044 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 705350827 1250 705349577 705349583
    0xc0215011a0d0e16081c080109110918061302030c0909060312070f02090c13090c0315093c090c0509090319050a0e0d051f1d0307030c0f 60
    0x140d543c20b103903042414007000d42c60b50050740204041525041d01c00b0304054072410707000e0542444004041c1039030342003480241500c0c2012800181e20380b00d01c0404900c0d02c2401c0700550300c10009502c08000c081d8980f030013440707050f09446001032170251101c0c178801d90200b0741d601a020000bd00203400c1c0c60a1038003240d540008001c08645c408503440aa94803250300150083e42c0014a40c03440300d0a500f018206260080c00c04840d8910301600c1c18140b100401a030302842a000d13481d48808051076210f07810245500e500615246480d90303443e01800020100000c86642c00031241c40203001108030341c200c04480070300c0082d21414044a440c00c030802400b1000d02203e03100003494021450351200f9044902c121907803070017140e0b00c550022a02806450000306442044000c02500030313200e90ac80107401c5030080c01e5989501d0302c0c81c05e140080c1001044405036400c04c9400400d000000e18603002a0710901d000d01c1641406502080a69224455010040d021600c201100f1000404800d554002180 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 705352077 1250 705350827 705350831
    0xc1c1b11010923030114090a12020f160816241103030106090302090a150e0705071208180102070f02010e1c1a0609060307090c050c0a05010c0215011a0d 67
    0x24881d44402c03c202001c2e104042104090246809241003d03c0b8880351500050603041c001d1070441c4c04103603602d40001c4018a0350302c54030055942e5030f00070000d01d240c0e0801c2005031191184900d0030b81e0055201c512540e500e511403951035074044207083c84040d080e911131002d09016200e42a50b40740f110a07c080300380040000c034480c0704130b42980601c040c0d07000c1d045959800325000d140d8010803603100800b41030f20241078640818070a40003502e6801030308485948a40382c68654800d5400d580c603005080380500f40420018445020583c0285824410b030070071150901801d104c00209801c0380541c1d800240304014006065002d50301840443d114064020040601c89a01c0749108c2e004007510706c411102c07200c061212420f400030442c181507125000b562540e1841c907081d80007070761300c0050b44940c2c06602e50310342c0540c000a220b60704690340400400c00319207801d1001e18041c0c0c000c085001841c4014050340d80c001c02105079400700d203412079485203a540c004901c407401c1200c060b407184404946840e = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 705353327 1250 705352077 705352079
    0x50a0209360c0d05060615040f060806041b17070207031713123206060d03051e04091d1b060904060311040f051b1b030c1c1b110109 58
    0x76503048400101c852240300940070071b043c0341d01030088445402d5840c0340500c0301440705011550100c1001c0f001c490040c0390183ca030f83c90f01c901180c01370814005d044041d29090b1035807880142c0103101c0c5042107510750401c070020b544500e4101e0303e0385002c1c0401084012200b910341c8280e02100050111500040800c1030003d81e60642485140c0c2590811030b801403d0003000f00d034156601c0c840f09910f03019285244092500e150225480d010010300d591f00c206446084481030510581c140c0f517001c082d40d251155100115030b40f50103290403030302c180800c650601046d02d040044203850040401d03900001080c3d20048007000e081350340c0314620f4603500241c0070720400c8001d40d51030098800860259603110720f090000310034001901c4030400800e5555040c10180900c115400001d12039224280c51050384800c0c0605e021a03408000c20f103610060303c000b14494962142c0818806288040040741500103250240150792000d58543e040c20410011500c81c0003040c0502070350610800c052400b00025 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 705354577 1250 705353327 705353329
    0x160c02042a1106130803191e06030203010b0646031e090c0506070614010605090307061e1115010603020406090815040611070807050a0209360c 63
    0x50140703034403880300203504148200090a000e001c0b064000641481e282100341d403588603500d40303110283c4240300c0010710f9002d009140f070444d40714410403100d4241010814100d0380020010340210300080e8440e5190030f00b100c0c003518002045601c0c40c80111840000d80314003514461800006043c3d516802c00065100044081c9801c046949100070345c0b40001e094000090041060422044d407155841c5402803120204003072040c80e0044400450310a07560b1700180c608103024002c40d010360054010918008079110360400041d1202e50b6040e401c07a2070080e5106000c403442d400c000200312014543c00060800c03140b140c41c42d40c10740c2131804102c0e1310008003407401030b1640b40242d000d400060760108092240650102c0d5a03001482c0d01d500818100c1e4566101c82e400e0003000e400100b466540f04d080303070a900801c0d415128810382040c0c2281d165510b5090071600c9a400e010101e02c0307400c4560004c0e840c50450101100300010f1881e4600c2c0101e5218083d4a01d001c0f218a810420701c174540d50b6100b2 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 705355827 1250 705354577 705354641
    0x1201060e120d0305010e0106030c02370b07030b0d08030105040207060e2407110601090b0102070509012310020a030c020307080718140601020307110a0f1d160c0204 72
    0x2640b030301c0b0303500000c3e6585030841d441c165070b50603040042094106120800b03a10760000d01e00e030304c000f0040e16241c161010158004d40c2012911014018810068403000500c194400213901c220f51640301480812910810030800b181c602a0041034032000340014001400c043c3d0290070765510a04000411549050810b8940041c081700d400b45001402c001e121401801c40c0000d42250f00c5050814078210642c0800b81c4032681401400c100303690300d140c412441c1e8420001d10009240140100748156150300c8018030035041280c6146a51a01c070705c81030a1420303c1a000140c000030f42e405801c40d114030307aa04503014200342c041a83d251158110200c1c403c6c1003403026000400d40c043c1b590140800c09070f100707400d0f19424480e54102d00c1c0100100b0642e83d80210445840030752118040e1520030305800020245120754005800d14034502d40085030401040c614401c1e0060905c000003c1581d440e20588980c42d03840301384000040345207910100508058001c41404080b14103540c0d000c180510040e25 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 705357077 1250 705355827 705355843
    0x170303091e07120c0932070f08040501020d0510061b0b060607060f180b0604090f02060a030f151811040504020d0207050a0506070f02030703140d02090a1401030b061201060e12 77
    0xa036404580441c6817950b1503185001b68141d0a1940043d1919010b0000352828551504074414881400000380400c6020f504641481c80000001c00c543d0a01c0b2203480700d031503854001c1d1400300340c13a2900c2081041c1c4c803015042040d035009034100380c29520703101030081a40100b041201d5094442500d042e800d00c1c00e006401900c01803024240c06000d990030a07940500c400f0b419540110710b400c1621010854102500780040d4054440c03640e200310701c410880042c0b0b0380794920b000302c81c540032101031030404400010080b140c8200354500720b001e07483d10b110101c3d400d43c160181d240b002003004000c0c90070a50003800c1400d0700d5144c01405e010302510384605029035140d040300e080e0041010050125001000810b42d0121480154240201075502074144410400b01c0750301c402010404d08002942601124034115024107412499039960701d80d00c001d400f2090040e8086420103004d10010305098044e2294815220a411040c3c0d2070070005a40c0c07503c4410360b00e07810008400b0006881310040040391 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 705358327 1250 705357077 705357101
    0x40e0106090209010e0a03020a090e0a0609053901030f0603230712030e0d231b0102030a09090b04091e02090a0b0d060510170303091e07120c09 63
    0x2580d9003880030001031005c4d210240300c510078141000180050b859042c03440c4140c2c1d80e480800244d000d090000d4500c1d000072421300410440c2041541d1042010100740b40c25199405040314152140807800c8100102040090340d070b10038503042e4030307101c40c1d8070a0300105a201402c0200083d1151070380c448410441c3c2101c692202c0701c913507000007104a00c0c20843c0400502c0111f4200710180c034103071340c010030b40c000e500e4103684220400b03010403041c4010702841c1c802c0030040b00c00c070b580c1440c1080800c6481d981105101c14005166000c1a8080d50011044900102180c0d4812800d282058103002c01081d030543c149404c140d8074003100f000180002d40002d05034102074182440c0c00034a204001d9400300050100d03540b9414100c140e80151540071206050315804600460a0b50b2684014040d68503d075202c1c00300780c1c281c0300c4040d41035403002c0002c60081130a141994150b2080c5000c54404422544074030344d86a1241c0d10070440c1da20203040c80e88110784035400e000c5640303980700c03010320694030965106 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 705359577 1250 705358327 705358331
    0x5062715060a060806090a020d0b040c0314060907021009170a051201050402040308070809030a0219060311030c1c02090d030f023d1121010605032202040e010609 71
    0x100660786406082c100042445182502552a080c0302203140030030080d08200300b050b0042410700400d035542d04000729041c400351003000000850800100644a200184030101016a002c540c0c541001c00314588a485980c0041c45041c89145032213000b00034080e01a50141c0c25401c519005c40380080040a20500c0e50361019280c1084400520001106a01682c8541e104010030000a01c800d002c0c0c03880036805c601d105456400c8034020070705000c039401000794000b1502c1400c200c0404412000800e0f1042c0399410080201001c1d2074503500c2c8000d0754460020070b03003440402c0c02c94000000d881c09604071210090704240e00030010400785a4510400c41c0442d4024044515042e410070003c10a010015803014100c61107a19554000c24001d103145019840108440c001c008145c00002109140d80c00080d520013440601240b0700106055038164148031200001d81640724074241c07801240c0040c91815031911903034070400f50841700c80e0103d821584462210179264001e10642d0001c2041d2540 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 705360827 1250 705359577 705359581
    0x8030306090906102105011d07050a0503030d0b0a0b0d0c2a080a0e09090d0306060f02190c05030f06060f06040807121a100305060a0905062715 63
    0x1c00c0036951004180ca601d07540f01d80c08100c6001002000ca0044441da550303041e01c100307102a00c441c142c020001026110b9802d22110700580301e0b601c00540c2c4100349070f00654203896114020000c0c1c3c07404520035594103900034402000e0004c015400050b120b08010014140180c0d5081c0d4040b0350b0701300d9082c82d0300c229034440801d02c00303a40080300480002c0555074901c5100c454510807500c06504070300043e1054902041030b0035414011000c144080d1001800d8802500d446e240309640e42c110f0b507030b80c04006800e00c81d00281f514010480f115200f011a00580a880200107942d20072039611070f02568600191800020707281c0b01849045039410b021400340440e4607005007800b4600840ca529a40101800c1200700701e50758021400c00d0580e40c0345c09010f1032210340d41c24061010072010410450141d064421f0041b8904a04610403c417486001035915a503180b00142c021503001b550080c000c1c0c0c0018000646280815840080b401044000d00290a800d0268285031603c8220034000700782507981 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 705362077 1250 705360827 705360829
    0x409020f28030501050a050616060b04020403050a1e0f1e08071203050108030a0504170a1209180624020a140c030606030f0c1c02060a090303032319090c08030306 71
    0x43e14054401a035030514254a042c000c900e03944180d90118580a125044003820403820342c01c40002da4000400654445440f41091030304c41941079401c8498a03810b040c4401d88404ca00c485041d245d0b0009915440d03102c55440f0b41031943d01c400c01c2e120f0112140c44096000480d4030002d00b14080c012031701c0c1000004442ca000d811500182c03c103001c103038800d102403075410b0382c044116015500c2943c0416164070054005a103000c2054100a03c00c00f101080d0200d0980c2c0a403a03801103900d00d941d40210b01d00302d00d01360b400311142c0340903554801d0110700c02046600131140c000601c3d1201481141c04031000703921840c4052078650381c45c0400d40c104064140c5035140402c0360302c0e0444800c80c09046046070680815654490703108003540585400341555030450041c1850385c1500750081c08050380c5d0740c0304a07002045400c0f203000882c0440d1425100d01404607040e0344010184640c1c072100031440e26011442d40e108041d64000380d43e17698903503524000082d07180200070000c110b80d000844c2c46e400c11078 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 705363327 1250 705362077 705362081
    0xc0a050708040e151f031a03150f0a0516030207020105071a3304090309080102030a0c08090102091e0a120804030201020d02061003080d090506180d02030f0409020f2803 74
    0x16030302e10700c26842d90300f4224040d203600c50f0340413045609003070015040701c00c44000c01154047e044119818003400280ca00500c030080545840341e0b0100c143c900385952146a00412a482912141c6104c1805039900768018065402080c140d0b0050405506208207650f48290015610031a0b4019080613024420140c0c4c44840b08581200c1c02c503350025800c1c81d0400748030324401460b40900c10f035100c0800340289409020b2010150164400070340d9646003000c4000702524403d0300303220010300c4480c0003c1c007001c03040c82035426010004003140071401c05007004102803c0c0f2030a043e50301c00e50910340051070060320984020294450001551180e1550002a08000ea07108807030056401510803c5000300064009a0541380d12200403038490304d0200405000f486c40c108003c0144c80741005100780000000c0075032040103003e5040740c5400e00600c40c120384900811004141c3c689040c0002d0080c00301d190050030301d88003021101410800030b80c01d10003001c503150411400f2210059000c40c1a03070303414 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 705364577 1250 705363327 705363361
    0x9060b03010c020c010c02101103071103150f070e19090f060f1a0715052712090906030a02091608010e011a031e0108031c140c0a050708040e 62
    0x35001602203000f0084c00a03180c0034004900910a0003c0090480028010781c00040807001ca5070849448040d0b5182c03000d076000410b03404038030911825420390343c0c82e100700c414136200300d05030042c143c5252652102600c08001404940354401145182c0303500f540301420fa0700c1d00518040340040f84c441004000350080340e4407504034900a1042c582c0910848404190900880b07284044083d03450b141030810b0418035031200501d018a504107030500842170000c503911196a4596030150044465440003113644400d52030b500720203030209109500b45841e0000841d035104030042c040c0c0d425020180d000034140601155507c517003490071002c24080c0c88d44084850b014102c007003000e490039410000c4100c40f104026012042d400c00000001390700581c16800d0b80c0304240c008400d2141c55850ba504151a41c21103414542440280c0950300300c80d284501036100d00040004041c41a601d44040d407620544c4110541d1080c82810845030000640d400001d01c024582c000e0900074605088040100032112 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 705365827 1250 705364577 705364601
    0x3031a0603101409090a0201080a2703030b0103051501030b1201050c040f0617341d03030702090403050a0903050f07170a030206070305091f0203040b061e01120f09060b0301 76
    0x7200c02000050b01c0c00186c0702d0900342d0242040301c416038510314140060000c48a406c1c0e6030501c1d84c0c040c0780c3d90344504183c908805200c1d032028068041d18100460880d601120300800007101c6806580a55009500190800501030321280400c2c0702d441c043d50958200703607004480d9580000c3c0130030007248840803000c0500704a15111828070303440c5030304602007180a48111440444403980001804002071102c0c101e1001070280108001505d101030030f400007040c43c0041d03410701d034040715000c5e160100071580d4041d40100032950765103840e1400c50f0a9000303000300c2070503c0f41185c404070208004000d50510115160700402c1202e0030040d80d28803030142c040070016250300c038007143c0c3c0001e034001c2915503104515241c000741c150b58417100c0174900360188a6035070340c421456142c40c21440d41c035002144101c1c005c0c11546c0d02a104c40e01840301c007242003099062090a210707200c00c800e41c480d001443c011024124007040180340380014000b19078400390708440344c641c2d4120050203414207001300410510 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 705367077 1250 705365827 705365839
    0x90102010e0706081b04150c03091d0c0c030f07050105010302010f050c1c140c0115150206040f02010c0614061201060f1403010e01110c06010504051303031a06031014 73
    0x890700101074405040038060740c1041c13125802404074170000c94180c500404610b0701050310840481405411000e1105040c0c0000c4c0c0c0ca0000800d111a00070341208003603070403103540419943c415a40d0703d2282c200d000070009070f020410064000304184806040d129005800000d001c0d451440050181e6103044d41d141c040c80700501280d20490b8000c07511141820102c400100d840c50041c5048400440b2588100125507000ca8012450b0105500945440c0181e28075280c469496070404079000c510040c0030401079011900080004618040c00c1201c588107051800101529580702070035241c4500c0c200d849100b0381c504000281ca44002e0f80401d00649100801459051500800e640d08050040741c9020000a1550505481c00d40c410314111110310000c01c045072500b50a0000d82d0f00c20380101c12140b140c42c00116a502d040e10813280107070691402002c0f80002560180e0213031078122014040d45854240840c50364560000552140384106a1980c460b070034002100c0030000896a1140210 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 705368327 1250 705367077 705367079
    0xe06010e0603010e04020a0b03010605130b04050609060f04080106121b080c010e2704120e01020a02121606020607090e0903030c030907150f030c0806010903021905030102030c090102010e07 83
    0x3072151002c0741d040d641c40320340d9212a03654600104440300340c540c1c480c03400362000000001d40180e02c5405040c001070000d51200075607542e07050310110350082e801000c1d403000b0300300640728a03840c01c60000c1602c1094190b100f401c0550301c1c06231034210340555100c440b0f10942c15141c0420411124891300782843d9907014900348506201a1079601e2041c18103040c1800f010242241d11651500400c6006410800581f0864500082403081e40042035408913004200104960900da01400208076135500603801009074510a4003000140baa00c00c80040c51030048403031803000701d10301e03c01c1c80d409400c0700d800a101a013808032009003000c140d541303d0384030303d038105080c000c0800b800b0045942092000e14001d86946800500a09143c0d159028800102a0040014040340c112203500344110958070200890031003100c0645403810121100c900003403118405100610344040308081d01910000e00225030303901e8030f0202c3d0072a0f01c151401c8410700c001041c0035107150790901880d0028a280d03405002c2c49 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 705369577 1250 705368327 705368329
    0x51e07091e0b1215060d020904060b011b0b070302070602040e040605011a040b16061415010f0914010f1b0f0b0108030a0c0b070c0c0611060c041406030907030204150e06010e 76
    0x104100824a0012401c07413000c98060369030001840642c5070020f1901610b400d041c5441d40080c0900d58200d40440c1003001101007160051209000d401e41011498081d41e680d034400f10300075840313000300315506503090002240c0148010642849680720300300018a40d4103006030022008090642c00000c04402c10040c09901d50300c00584030b40d03041c0e0740c14034184c0c01c8080c901203020b4800458066070010030344c03003000900020303006085007102c0d0070f8940714503070303071480b40112a9032031540a40700345101030794047c19481d40302d1000720880c0d08003440c0100c0c00e1902440c0d0b129504070140003d81e0341c5940e6500d501d0601100c0703001a8018041b10008503d410f002c0c11014110700b055000161440c0034038000640424052000341d408513900821000d5580e445a03005448505806086141031242d20002041c881c0c040040b18151707641c1e000d1981e030248600b8108205940000c1909945010b281000401130b12240a502e4800c000128040c1c0d196041c21074401d04901d0040c4880c0c10404400c01c06034603 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 705370827 1250 705369577 705369583
    0x204030506092a0409150905071403010b10050a030e0106080c01170f0711070503121902010c0e060a0215090a0b0919060e0c1207060e030703051e07091e0b12 69
    0xc201004c0c1c8000c20305032005e003403401e6504000441850a00d003844080d50410001168110580b01c1c04400c0616105c2c50340300781422907010a8040d50044007c500403142c150092016040c410000c0c5800b10b007108080800714250754043e4040c2c142d5034003a464019003581c01100005a03402444901100d42ca0110004404450003515000600900080d0105078201c240800c030068540a021200c0c205600c8201e511582d1100900c200d800c20212203c4000078810301626107003410307903506e50100d0740310002008a01e50082d003081e825481250550050811b5024596125107403880103402601400d04100480d5840245500e603079400000303c1050001500301100300694011500050740740d01050084e143c011000145540044124081d80800f280081c85100781c031107540d6544031100c040c000349a950041c60000a260750481a0b55001e604040c91800d00a04108000c40301d00701e83c1c480c1708804444854043e00d4420f07600c1d145a0101c14080d0180d2007241c1001d41e01d49003110b0541c524152 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 705372077 1250 705370827 705370903
    0x81203040b010b0319060e190c02060402061c050405030c0106170d0f030e031b0c01140304020f0a03020d03020105100e010311040b041113080d0f0c24020403050609 72
    0x80c440901001048000e8a401407086500c5c0d500034041012540f03030400b0507050307882164003640c69089041c2c0642c0c444554059281c412500341c006000c2900d0302d134200b00a541061480c0e829600004134400200d41860080310301480c0640c2c06107030303a02c0030040712909458968105542544080722040d0001d480020f00c09218409480c201a4810a600044000d050180f20b0078225110101d0035004d02125000e10f82c0c134a034241812515050101e0005481c454194540703403144d00340900c002005401c0180081d00c415900801c4060303142d07140c0e1300091142c1582c55040d80140c0d950400c014604003500b00000180c840210400041e42c510383e10040c0401100b4840340c050740d00c0d02e01d803081c651034075086a940c06d0001d610703064903801102028003040000b8415000c1c50322611070311200507030280c002c0c9980211207668081c40c1d80640d44030714611b031196450b000015080030003021070032801440078201852081026000381e0404400d007914084e0200801d0010305e0501652501c112200c0e0785c000 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 705373327 1250 705372077 705372089
    0x301050603190503040b0d1b090f060305060a08030327060c0703180e0106031a0d1707031101050703060914091f11070b0403080f1504050c090d0309081203040b01 71
    0x2052000320f02e001402c500880c0c2c410001c1d103c000c16034503103d401070342184003800d80b01b240103007001903170540132145907140344150740b403c00a4210034480103119400480d072086d0081c0c142c2103000d03590a061440d55100719043c80f0098a0000100c1c4424240c690000c078030f50780e1000400d0907050407074000001c0d00c1640c1005050150190256800d51440603404004010540c0311140b2907a41d0240900a404229140c180491400c0101c20740d42c508030000313844040c1c0040030511400300d10214025030742d20030441942889181800030805030024040c16200d00340d07991f0080f81003442c003e01d04056400b50f55046145401603820091f0519000071071401c0c148900703440d543c01442464000004042c4464035400000d000100d2400303014411034100d00840c469035079204107948926901200385019104403455445100c031840c80d5103001d4000b150440c0d80d240b07038a450414810000350240380542007c40110318204420014032400f40000c100884c402c86801d49149010b03500c201214005019035 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 705374577 1250 705373327 705373363
    0x2060306090a0b0301050f06040c020303010b0906130306020424020a1208070e120615010c031b0c090f060e060105070839030415030605010e0f060d09060203060f0301050603 76
    0x50700c0320115402118503c00c015000700401e09012001a0307062404894040c0124104240c000c80700d44000107c0b4102c4940415450401406004004203540b0921345d0040d1a8401c40020022070746510043c030081c59059980800c00342682c00280d42040d22640400a5400015080d00031a400050301e0041e0300203403915811a40c5c40500507201002021002d58214203100b40d01014410002000717809040d4100619030b80284e40401182e00d68036a80d0000e001400f5280e508000745402c0300701800b01c034801d414800364252a0b261030811680d404e40105151a103844041120280003004030303811000a01c0c145180c00c0725502c9640b846d2250031007140040d0040007990424000d2501e00e00d400b2a03803090060b0f03640e282003643d00da0342d0300140503520542d036500b0b4090282c28021310400084500c1038448510310625481080550005ca642c21900100100012000307035aa500c1103040407881480011b07102d0a08109002001c06e41c1144140a40c1c589010710555590004824149030f00c90064 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 705375827 1250 705374577 705374581
    0x60d090507080a06050f10030302120f1e07030e0901050114070f02040c020304060801080309010807080703060801021318050915190c110c0d20150d0c08090a0206030609 74
    0x441807401559920240690003006041801c01026800240c00358002401c800242d854012100090003030500c40140541c0c000080300c00012800006401d801c4070b600483c1d03041801444090b09042140e41011480d10380c00141c8804040c0c205003074031610340d0142c0315880190304020010f409041c00303916456201c0350104031001044586070415a055030302070300500c150000244041e540340c01c50301541c40800d00c2c07440086142100007040e94013024050b517504400e922035070025034800401808502c200f40d00c522011550380024002420349a082c03117540d81c1c541c1c0c5041265024a8102995034442e2810003041c0b000d60b410028460f07415000c1b0390150002a102c002c41c07120103151042e00069034508281603411001d0300301c048035007420301d0001610007803a983c0c020045801c008410081807801d0102c200c001100110700d0b0a05020000b419121100c61184801211038020940c80c00c1010344681c030719104258040c01454200c0b010000070101c240841d0700042c1580030050102d8050602d00d00 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 705377077 1250 705375827 705375833
    0x11060c1c0e1e121206130e030702120a12051b0303250c0c030b04060605060c0a0b060109030f0605010503011104030c0302010804230a11010f0c0f02040e070603020408070e06060d09 79
    0x1c3e80a401c041c442510b0f41c850005404d82600041207481c217201c0c801c40001d541600095020380c40d6203c9041003d585000344590030408544401c0803403020b44e105d01d0070140b00065000807000002c00300c80d20342a444840107080d28800300b1155128402e160800e00502003083c5581407070304200c07010001c001d1710464410504a80328000a00d01400c0080b60310320010a006011003d54002d40c0600018040c0545800500900d40b060700e000300900d900408050700407d803401d001070b030000d005240c01d80300140e503511a00c01040f64854240c0d90f0558440042020b0700e402d10821040d80ea00b0300e030f060b04280c9107481e08488a0030511001e4148502140050b0401c0001441d040700c51008100024a01e004200c03000e980d102206c0003100c03a0300d000c250101c10b540c000c0704513114040c201d0b0b8403844100c1e5280d540c80c0e160341c0103c2c412a000358071143c0003624500c040c803d15003e825603580c0140c580c1e2410460a1501c0c140758401032003220f00f60103100c02600c400080302e100720900340c40811003022510b = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 705378327 1250 705377077 705377083
    0xd0203151e030a230313094205130e060906040c0905061c08030403182106090506280504031707180b0a08060a0f05010f11060c1c0e1e 59
    0x26209130280e020024404282c3c0c00544919400d554950400300b1071820419580045107040d80c8071101640e5405140c0304c4002060340c02e968024410041c0003041c03030f64850114032084c181c40c000b04489611840c0514003114208042c50380300704240d004044505180d11951600c0003503008607585542c803800001d0302525402e01a03001000c580705a0700c138092860900c2902c41d00182c40c1100007034a0119004240405803201c54103444030300741803088411940c1031800c507100c64040700701c40250300c5805010104400f846424450860350f18185002c5010103070340030030841000c2c1c0b40d20391546010b00340004640d000c01010a003500081c001d1645813100102a80d0000c140c04d412015900443c601144108011005d400e004a05840360819a10340303400b00100c0200a008003c200d005110040010750f01c20350401e10b92600c0c42c2030080200701615151810301a08032004c01c820307400003805280100b0046400380070b900000c40200445038a030300219490b80362158481000800c16101519455000c0c = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 705379577 1250 705378327 705378383
    0x601110a0f0b07030506030714040b1909050108070602151303020c10031e020c030f13030602030a0b090c0a090501050903010f02161e03080601140d0203151e030a 71
    0x50003105480c91146003202d0b8040080f52110002401d05c000704800707060004080007900c12070700c800e545624400003400010840d400040798002c1c1c4151310303204008250b00c8400040c001e540d80100e42581401c02c203034a4156103074494001c560041004101c1601e8480d030307154000d1081d0083c2c00e0908200c0c20101c0c41c0800c07554039140d1048005078035080094040d44149032a000341c0201c00100c00b00e40010b1070032401031300422075840d00204500406c2014110041030f140e82000524050302d51a42c41d40e40498004540b65403c0c00d948180110007890604412503002001104162900049100080411800380705040c1800070126242405580c20341116207071000103181151941d10320f45030981181e090f054241c952030340c0c0d14840841c05280c1b40d071404040360907844005454540100458500c401c2076200d05545c0c07024070070f51222003550b000660081480b00000d0120140500c2003040308146204108842d229900502109860100e8540d6074150085840c481000250581484c00004 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 705380827 1250 705379577 705379583
    0xa03020f032403030c152503020306040b090103020315060f121b03070605030708100b120703062117040e0106200601050d080705010615110c06040e0601110a 69
    0x1c800c00542d01c503800604082550203119441c20700329200c0606481380700700b910070a055048074001055900e85c0c014030301e4105c11a81c0022900509560109680107a081314030740010342c0001c01d00019240c0f27406000b00400040b643c0c14400d516542c006690b0342180800c0070fa44100000009509540740300030284143d501510020303192049061454980c44085551550070540807940c0e0101c1c2000101107041c3d41603a00d070703103103180ca9250040d2a01040103000080c00c108a83d40803c040513417401401c520305411a401100c0c0c20090307005000d0312043d8000c2c124440c4000040c2c0c0c01042080107200115420102146002565001720b45091146421002401081400001d2030960003261155103500c10714800145081c1d420b42c0f182c8404080c46803580c17120842c28100040f41c114001000702074030503400001d15654a07040b02c80c1030703080c03c041200441d00c0d1241061004005001100768500c04440707651406040100310780301e407500948242d04000400d50352502c959000c10802c103007250 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 705382077 1250 705380827 705380857
    0xb07050c040b01092d090b0405130c17030c0a060c110d020c010c1106030106020a1505040c0e0c120720010b10050310120f02120c09160504170c0906010813080a0302 72
    0x14680002902511f10640000c0c01249010b0010740c8021840703140700c00e40c41d0320040303208141e881d156586160456413082c0d4030041c04104614100e5240c200a82d28281e80f00b003030f000c41c180f02d0024005c4d0944501600b00340642d0000d6450703107030b11075010a080304400c0c9e0909120b48080801d003426051100420003403a08820000000f00d000e40e00003581c000709a200352a405280300b5105c0c038003000c1d03410949008080300c58184003800040e82c417004542d070103003a04210504203c01c00000300c0c04000c1c01c0d100400415000030910300420803a400d41451400301100078440d1274001808104c15202500105041000200c0400c1c232401c203545090009000070442c440044071b50303007005070151a6143c6e0480c4030700341c02000015140e02c04669a800c4110041140b1010b1351800481d040201d482803e03d000c01004000110304180062140d4007410801401090f20340745031030602480020162400b030510090208029200a1b90340300182056070020380c01d80c69003010503044e0040d008018441c04516 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 705383327 1250 705382077 705382079
    0x207090e03091005040e060d061e06061803031403060105070f05060a0b0d030203191b0302070509070e100e0f100519140d021b070b07050c040b01092d 66
    0x10400102910445030b040382c2510501c000f059058400d80f10354498040407900d210b0020b1020700c0c0c058510440d00b40507550105070030a481d01c5008010807e001c10700344d4266208014020242c1c0503815210444103400d07564411411510094000c2c0800846000c40c40300004c0060104e174494020340381a681d12484501b046242d9140164841208441f00079034945010402d1025140034605218680c0d0140c000e1490900d4055600c1480c05842024406010602c40e0400642c2000c0f0001502980281e029050607400c2c001049052000980107078200310008080c2205035452000210700d01c98035007003c036010403172240030070350b442e002c640380750350044a9007890308809402000030300409480c2d42450060109000094400f0841059020546142401100b0400306294010414201003422610240c180c0c4e01102c0c0c6824055080908084008184201006000c2100a00462007107138244101e0161b0350008000e40340c2d600c9860761820740ea00505500d10140d0000c2d8000d442441305542c889 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 705384577 1250 705383327 705383351
    0x804120818040209010f030c032c10050106020606010f0908010f0203010329011412010203130210020f100c0318030e0a09050c070b0402031014040308011512020307020709 75
    0x9500580210154119146141c820034035107442181c010010503101c0800310340c0c081104800406042c1d21307560605542c0c943c001c1180200d500149100d80000020144006607017401c64100044880c01703024090803c4010301042d0b401044255122a00307107410003034420303a800c08440c0c02a0b581d120b1504d5501e080201581c0802c0742c0c0065050728050780c05111107a0580c1c5204140446044a805003001c14030014010000c4101d039501454100800015044001d2459582283e2050355142011307600c8021420440c1030080080c03000c11050b0014001140c80c1d0402e04ea02c0b51012807890b1042540c450840301a00e00030b500446001a501070403513090b40c41490042d01941080a02c00c0c4910b4608030b00094980440c00703198410203110400ea41001003941d55422440f101030f01c00c0f1303414018501b0070f50440c0751a00c41c5918960036503070f1b04429401c1c9424040d2028806820500b0300d59040401c00e03140d2604007000c0300180d034140f4801a0360f0350705c40700d00700d0030081c441e00903040789828000d0420388 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 705385827 1250 705384577 705384593
    0x106030605091602060f06030a02060c0312063f010e1501080d020304050d11090403120b0d0f0b150a0f090b0103051b03040f0b040b0f060301020f16080412 68
    0x2521402d80b0590201d4403210342400d0140c48a00356580180d00100c00903c00106411429070031003000b40c11541000c2035540050740d42c0c0c2200221400c1e650000c10100d0100e1880c560142d04260180e44868a0440d0201903090350726108581103090310525502070311802c004468116810b5400c402004142c0d081417034261200355640d00c80c1c078014032880010907154404133007002181c05075001103180c145460244480c420314000240c81c01550800c128050f6103e0801084c0300d0351007541c0d1090950311075000c40048030f052404644c054425845103600060b0b98010030b0201c10b8100c008056540d07a500380083ca4001038041c00fa03040703801c0d0100010005123550003071054401d02d00f41031004050300d00c0110700b03c4408450007407007074a08100d5246a2070200f001150824080c1c214071000400b162a0340070f446206880460304030f805441084803400c2002101d0343c02010850080d407806003ca1040d051a00076000b41a01c1600c000c2e403000c08100030f0400720345c024003c000130700da03900c0041d04000c09 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 705387077 1250 705385827 705385829
    0x1d0d0302031308040e09010b030105090714030304170304030314130308071112010c031b080105130f090f05100920010905041122080601140303090a1415090a05040c1701060306 77
    0x303000e60030030803231040364501809604e1040a4000003402e00c80d1500306856a9041001080b0742c140c0010000843c144c50301c081104600220b0b03000640d07580c1d295150050961502501142c030300c603400d201200c002c014010b076160840390000d004584800003800d24107260480245402c3d0302c410030340e461070510b04041d040848141b4494404100e450201c3c00d0510b4001800819200050241c00050141e460170104614110183c1000050300d040d261090382c04448146509031703405540049400c041040400c40081803030502003040c00b0703030b00269503610220603c1c40d20310341c40c04402e000817406513440703046a0303001003400074400d118000581280c001d0039800380002d21014100320f1542d407403000520420508903808a8014403460703180c480c001202a801c1040190305000803c100c0095507542e00303203040070b80000b160186807648000204100018080c9030920183d8051081c440145e03503448510b003c5030f20503500810104d40d80c070400c44901c2c0721400d80721010610f000000c100d240c0d255002c40 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 705388327 1250 705387077 705387091
    0x11b02060136090503130305031905090a060f111510080316030c020d0b0a1410050d06111204080409050a0e0a0f030203210a1d0d0302031308040e 64
    0x40440d00345401109010080319845040491030302d10b0200e0280300950102c5101c82c00385040d00d0503c115400810110501541306880c2c560004c00c00c0100818580400724080441e814411703c7d003000301c4085a85448940304003014003d1000000c08954002da90400c1c1085604054440c0421041c10f0890411800e0714041c41852417003402060301080001154a121800f00c1c418a07036071007a55003110304204d4540102e07040b000741d107000c0c00000c0d0f154154600a421480780410403516501c0c1000108400400c60b140c450f0820714100055111702908084aa81114001c503903010804052000d91182005125100454508001c10b011503400940107a40341c2c050248040c2d101c016440d030640d000041c1910050f00036040702c0000441c09141000460b1103401074a003025001c2c000c2c0102c0c04521034554803000a20020400c00c82c20600c03403070307c0700454510801d409264a03c48103540c1d500d502c00201c1416800804a1038a07400d8850524a150f40908159640c5460390100000d0050a0b2280 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 705389577 1250 705388327 705388349
    0x7111519060609031403160b060d060e06160912080705030c07031406060d020a090c0c140f06100e04260d02092d100c0b040302011d1b12011b020601 65
    0x5d292600340401111303003140c0c0480c062841d02215488400307290340064034841d40a030107403000c400055240d002d103000481101707010b02018905001450501580c01d401002000b01d800d0050108075000d202030511690002110381e181c41261402a00d54400d40c00030385010700c201d0a0000c104000709100b103040103d200180c84064441c00c0c140900f6404c0808002c0d44590380000034050540c00da800500d000c00d0754030340214003940301d48400d0f01c032003007036007030030240fa0005d00314030401d201d0802a99410440100f14640c03054980f85104900c420b01810007007080c0d01340002280c210040c0d01480c0c10908001400c1543c0d0283c0c1d0a40c0402540002c41c2d5500404680d00494001101c8054807040b000c001c00c84012880d010400b04881da04826001100f4000e03803a81000104207080e406030700c079074402d400000c0c07603048500c0c1640000340103201da9841684045810001032000c81c000b004984e205841c002d0b030721060408501e0241c00501c1c4800040030003c8413480c03181e540011007074101ea03401095 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 705390827 1250 705389577 705389603
    0x2703020109090507050412030219030305270a061517030a0813020d030f140706060609080a080921010c0216080304030819050c060703060602060711151906060903 71
    0x542d0050701c03c101d9040010030b90a000c10407010b01c105c0104a44a4403d01c140c0c2d170780340d0142242400700b0b495007d0941c00070f0f68035070400642030125058801482c01c0340041c0c250502e02e40c42a03964802e0544001440b2685401120b2014070034060700a010304841d68400818098100c2c43c640d0b2038110400540003c2d0284011030440c0324820802d0300416009442c810a070481c0307450980d0a0b1000c941e0040400c1982801e5000100800c0081d01080380718000114401d4a8410000c1000e0030f1a04110215000140d11000041d0000b00302c403000c4c8030948580003503401311a4450640411001c2454442d401d12110150b03447e030208031200f00c4044400d4040d8943c3d20b0b451030311340e42e015500009052600410400f04022543d0180e500341c40c19a280040c9080740c4118414100036048d141c02d00400c1d00c80030b040c002c054040c0304442d80400341d860414071048855600035035420410426000013501e80c03010811000781304002c0c804620269209001031943c030200101542c41c04c0c0310554851494607a = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 705392077 1250 705390827 705390839
    0x30f061401081c020f0109140d0207060522050d0501090201030c050a0210020c031308030715050c120a0e1b0a08060f1815070f0e1219032703020109 65
    0x852141030b101c100004100e0450f541d480001d0301a101c141c04810b43c400c5400e0404071607400d001304000d480c03080c5900411040019420351501071412610025500b01d510140001548141074410042028a0f124030458000448100c640019001241c201c0e4400008805110054201808107031003070380c082041e804000b0049031a4054040020016089188075102402c0aa009800b01c040420107981c580340308d04084c0e0001d0400703031344400e10707a40002c5418800c0c05001e00c120080443c000001b44491320f1300b000142420b00c56004810071010302c140c0850101807950740103650204110302101c0d6401c1c6c0314246a4a1010000c08607441340800e81d60105404401091450150601902c0e844a51b25501c2e180000c40d60099000040e42c85007104030140004284d030315500030481a1900c40700e40d01002c1004007401c04228105007d510f040d400f4a01c0e2a8000901d4030349a40703581e441040c0742c012032800301c0f59a13000c4009411154903503807200c002c0c003240c4e002e10002c4a100b600e48410306070b40e40c0b03 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 705393327 1250 705392077 705392111
    0x31d040504111e0a0e240303070201050d02130b190201091109040f08030a0b132313021e19030f0b100306050f160302180d020a0807030f06 61
    0x1ca0041000800c0e4049030141d090100100320000702400380d80309440143c80c04242110429408030345601c44400900c4640c2d600f07441140301502c400002110000e400b00c0109035248a011070007410400e0000b40c8400841140c0d0548030042c00f4011560016952080394a500360003150b189010700c0d01e40340034100014014410300c08540c0d031007a28402c1507125003080014402000b4419501022801d02c3c1000261a440065204003c081000113004000a0600c83d065104144106241c2d2038084500c0240310800700070006900544002030301d50f40e440b0710340d07035200e06101002034100310b100c124a4501207a0360340b100125441915120410909000c11000b042d103641300c060300d00390000c0344e51000319103004e600550080c0940c040d071000030f035030303944090840d02e045803d190a02d004034207200389010040b1b104510440540380a40c24064440e40214251042e40c2c0031b10304c0740004128803011516a424840c00622503001030711502552420a04064039104d071301115211318140990360040d04503 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 705394577 1250 705393327 705393331
    0x507050a08190e0d0201050f010b070206180f030307060603122102070201030b0d0516050109060906081504022b020a05030a0b0a1e06030e0f030a2109031d0405 70
    0x6a40c0300c0100c2e032141950390403107000c14800ca0706101d444041443d03035110100b00c13851684000780d00010319464120301d1050384881c1a0011915140104944c401586e503020560b1140070094103d10f000b480c42d1000106403c08900b0680d0700741c013003c15803c0602000307034024401c030707402840300d441042c3c01d880d0103c2d4900300c0e00c3e03c050502a0780c0748070046203d0082c2c0c0a080c5aa1041c1000154071042e000001c280b400c085104403255400b10001038807040d164003509000f04170a082000d580350400c00003404070b03007650040008000caa000090040a5809121042424058011996002050b00e00e0108519009040e1724a145072080f000100703000c0d200321600d0086994401d415512658601d20203010b60f10b20702540500c1050b00800d45422034407500700c0a0402840310482a89400c40207400d403a400505e90b4201c2d00300b1258002d049001004881c088901850b1a01203c4000002c01c0c1410b0344c010451001c061030414a02c00301a08148041c0030303c80f680c4030a101110034601008140d0b542 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 705395683 1106 705394577 705394597
    0x40309030213020306100e1014040b041502211207030e010609050a0e0304030c0b0901180603060315090201021b030a02030615040b0307030803190f180501050705 71
    0x2561030049212046d080c11f81ca0fa00c0a4000540101c5958504105005540000814950989080f580504543c03810720b511a41c0721500e5092100f45c01e462503005d8402d0086404030350049601d10250440f4806416151a907104000e002001000d000c0c0000d01d03031070300c00a000403e828000c1e5005810000c02c0010340b4070301006200d0a07100750302e09441d100e400410090021843c0c80c00518255000100b1095403518090012610300101d210100354202c213510000c40c01c2640b680000007120b02500404034407003042016002121180d480c000e001d41d00140d00d08a601c040c00208100c5207070300400781d54a0010f40d4001c0f9051031070455890402070000b021103601c0d850300e03200b10614040d085d4000c2008a096a60309100b5205c0035081c1c4990a802100c1040940410380101100d848000801c1c480c800d40b00a19609000320048100c4d529400c0c40c00082c2d03800d00c80e03801e031441c00170 = true := by decide +kernel

theorem cover : BRFrame.Cov 705215827 705395683 := by
  have h0 := BRFrame.cov_init 705215827
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 705215827 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 705215827 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 705215827 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 705215827 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 705215827 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 705215827 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 705215827 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 705215827 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 705215827 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 705215827 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 705215827 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 705215827 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 705215827 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 705215827 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 705215827 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 705215827 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 705215827 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 705215827 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 705215827 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 705215827 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 705215827 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 705215827 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 705215827 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 705215827 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 705215827 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 705215827 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 705215827 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 705215827 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 705215827 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 705215827 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 705215827 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 705215827 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 705215827 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 705215827 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 705215827 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 705215827 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 705215827 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 705215827 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 705215827 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 705215827 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 705215827 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 705215827 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 705215827 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 705215827 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 705215827 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 705215827 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 705215827 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 705215827 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 705215827 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 705215827 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 705215827 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 705215827 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 705215827 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 705215827 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 705215827 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 705215827 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 705215827 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 705215827 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 705215827 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 705215827 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 705215827 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 705215827 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 705215827 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 705215827 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 705215827 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 705215827 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 705215827 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 705215827 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 705215827 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 705215827 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 705215827 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 705215827 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 705215827 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 705215827 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 705215827 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 705215827 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 705215827 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 705215827 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 705215827 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 705215827 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 705215827 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 705215827 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 705215827 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 705215827 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 705215827 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 705215827 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 705215827 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 705215827 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 705215827 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 705215827 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 705215827 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 705215827 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 705215827 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 705215827 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 705215827 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 705215827 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 705215827 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 705215827 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 705215827 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 705215827 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 705215827 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 705215827 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 705215827 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 705215827 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 705215827 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 705215827 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 705215827 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 705215827 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 705215827 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 705215827 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 705215827 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 705215827 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 705215827 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 705215827 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 705215827 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 705215827 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 705215827 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 705215827 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 705215827 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 705215827 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 705215827 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 705215827 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 705215827 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 705215827 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 705215827 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 705215827 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 705215827 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 705215827 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 705215827 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 705215827 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 705215827 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 705215827 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 705215827 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 705215827 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 705215827 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 705215827 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 705215827 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 705215827 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 705215827 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 705215827 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 705215827 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 705215827 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 705215827 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 705215827 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 705215827 ≤ n) (h2 : n < 705395683) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
