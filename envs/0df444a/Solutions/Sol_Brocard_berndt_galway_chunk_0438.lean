-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_0438
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-13T19:48:55.054851+00:00
-- url     : https://prove2.me/submissions/9bfde0bf-b778-4d2b-a670-2894f3e7b288

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 78597124 ≤ n < 78776980 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 78598374 1250 78597124 78597131
    0x50415050f010f120f020d0212100e01151a03090a06060603022a030d1119020102120f010806180c1003020901030b03120403081b010c05040302091305070b090f030a0c0306 75
    0xf0134031090115000c04a40101102e496124941d0820540e80842e101c01c9800580b8450029a800010b10030307004201c40d54070000c01c540003182103260858030000410710a1040c045010b100400c3c10f0740411010003080c076121945c9840c0c000a10346403070420a00103003c00d0400310049109545500504038200c20b15100c100700e0400401142d0041d9604070201e4860b0f4000d204200742c00e8099002184038941680301c492a0a5071203100c01c110120003807034080940e4001421803260b5a48003100c60740f01c240000c282a065041a81036600c0b500040c00d40c00c001140c07000e040010090078004214036030f030300902c8801c04842d907001c050041c1d0404810b05010900e0300c03131051218200400c0d02c54032840c1d541e824501e424250382e03888102e40c1100316a02034049218a8401030401c00b48102d0418045549409131241e20307510401ca0607960042141844a003040d0708800059000584072054410303003015142c0740e02000f0b010072490002020310640c10310078a0021020302c841032500c503081d2409400c051 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 78599624 1250 78598374 78598379
    0x60e01050607030e011202120109090c0b07050307060c030b09070e04050907050f0d05071a0d0518060703050a0e03070c03050f0102030c041401141207021b06040504050415050f010f 79
    0x740c0e0240c1000500032a503a4040910150f00c1801480c0310302e44111401070602e440300aa11380c604000340c20484030b943e0b071607500e40c0611030540d2498006105040010786892092b5030342a48a00032035400420710360f101c1e46440b071200d0098000c4000d000000c0e00d008803e02c4c184e01c00402c09110f421a5178090340c0781c42c0114000100114543d03003901c002821034010385072090709101ca6419800c01c00c0d5110b000d0742d180855200903c00c0703401221600d0511964030707404108040300840e2000b80c040401107440c040c04018440c00862401d0707000c6281d040006147d6220650700b006400d03101a0b110440c08001051010408510b6480e8180e0340110101c40c80c2c0c4022203126801c0f8401502e01810440040c4410080303040c0d03900300d94120f600c0625142041165009280d10b1700d4000090300b951420701002001845175040140503281040c0c8207a1900441212000c210141308602a107030040b030710327030000a06010110444017100b40c05010100f0103860515072030b01d6400c2d0700303005200c04c802481800 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 78600874 1250 78599624 78599629
    0xf11010806010e01080606190c1106040e060402090d0506011805160c140c0a090903030f050402151303050313050a060207051807180e0a2007080708120109060e0105 72
    0x1845960180c44003083c1152010064a50b2000200701641c03202c41005103002c0e40071005260901d032340c05130300e64284c813041e24030388500848107008055001c6e07001800100020030801a105802220990300140d41b6803800c0d0209485a20011000c0c02900c10306c000082c040740750ba0b092420b15500d1501c100080e4035901d80301004080d101e040e050001c0d100902d8080411400c0c841c08030b0020100080314178040b20a80402d81c074070f0742940010304803a0b51f1100030044c160103008145051091072010001850554005000c1c0342c2040e0301d00003691008102103485a0700460320700041e5400c0390403240c88840c0b6804c0100b400c501400b4143c02102018000a407180c000920f100079202d004181d1580e981c01201004840c5200510760701c1001100d030b116809030b161007910507003d00703242d2420a5907440c08460601c1500c005001c40c5a06d0035150000d2961400403905032002198000c40d0559541003508004c103d6020b4549030030346025183e00000780409880d845001190721041c01c100050707998104 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 78602124 1250 78600874 78600887
    0x224091309050d0806064e01060e0f040906060306060e1603090309121203061a090609180a050f0c0a080f1017160807030203100b0109120f1101 63
    0x1070041c426403002c400d01c00098003600f045684130401800050920340640303006104090444419a10310800c08001e0806c00300320342c05225030f5000f101c4007a5006c60100b140742c0d11400c0c1407140341c0400201710b4600c1c986559401541c140c0900041090009014a00341440100014801124030f1403914100180001d0114210b610070815000102007141c011007065016106550088042040344403000c91007212030f10100c4d00e8130380160903500350301d08880700280480d0015000710302962950b8940719000700200044808054040d210746898648880101314650042d888080244000d03d0800004600036032090348030b620610f40c2814242c590074a122451310800c618007002170031410002e8010407020300f96a8001a0380802d65000d9a941d100c0301100541d41e80c0c45040b1500b090402040a4039200e8001001e0300750840900341d11441d5a0002e92b40d18007206000c0720980d00d409d07518131284e0160340d9440040a02c060011000c81c001e00e00342403180741c0c04c4402ca85a4480100d4084107511415 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 78603374 1250 78602124 78602141
    0x306040f0516050c07241d061606272109270203130303150f170f010903030b130605060414030f03070c150c0b0105090402240913 57
    0x103148028802e590445032540480342111151250300340c00245032030000c0c0d00c9a046e4118402c860086610424001c14213540c0e1a4401504011038545c0e0300d00d42ea4020031600011101440c0c001220410710f4510050f004400c420f10f0220070301c2c8440300307441e49070032008142244190081c500f200b808440c5882010764800d0101d0018610b60b20070b2100403482603425090b649c4201141004040c40c0810324242e0b40103c403044180c411101c605000c06400d4050380100024802c0c8070004c0702e041100e13210b000d507400c0c89100107504017510480300d0080140020705407d0700500c024030800000c0d0034042c000d071034081012401200722900c20301a60003a441150300b036407802000c083c6820305c1c00d06140035a0300c0c0d01c44400e516000d007100704090711900700002e001300340c8a00e4603051014500300581c1000b80815500f101801513420410b0300180c04400c45605461382210841c1c016140c60002c1443c00c40700304103658015000034401e4800d40b00c1400a0b100402080355590800031035a405542524040c0 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 78604624 1250 78603374 78603391
    0x50c030f030f030106120f09030315301a09060f01150c030f0203040b03010e0106090602030f1213021e100c0506060d03140a03020306040c0f020c01080a060801110306040f05 76
    0xa000520800c1d02c503400c0541c6d012200040860303485a10841c520444c0ca06a4046000c00d5803942010095001039121900401030094426955048500c1da205918172802900c4c203100720400d40041041140784001d000710044000b010824a014a07940ea521007059039442150120f8500011700d600411118102e40c180d29038819141103110760741a1041090b4881d1030056001c10301c40411803640441c00380d4020080c0360a0703a01213500d801c40280c0f2400c6160448000c5420400542811580c1d00040b603817a102101009950b42d5541c411400241d00c01040c02036100e100c48070751103e1014031854001c04c0c120202c915080d0b20448030380564240c20404030040c83c0e0f4111034002000361428001e00100c46019003000035030010b13030170030300417483c1d10040014021a9010003030088030300b0326200b502e03001035090504134000001a40040c2d901ca80e14042d040c10010320000050203c1000e030003010041581d00000d11020001d490318450541080f14150301131440d0a540f4424100340340152400b0301c514 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 78605874 1250 78604624 78604627
    0x1404080d090c05030d050702041104032001031b050a020c1c06020d020903070609060305012310020c1201140a060e0105150903100c0813020a12020418050c030f030f 72
    0x48200328409007000000945582424000025244d281400160a08800340c4c0d66650b0b9801948100001c88038030391605c54a144060005000181010b402022a40800d9440070343c0010080012000f40c050080264039100e402942c500440780c0010140600704c2850f000d40e4210003100d0240200180291003800700b40d51109a0100418000e030300a1a842c210040098075002110020034503129569001b00005180c800040183e181c0c50b11a56000d4118000d0108065061680144019042100783c0344500c25051030712540702e008004e00d07540030001800b852a103600c4103800c18002c100d0980054000000c0800090b149003651280100380c07200296a003889034200302c28480014907030002e01262440400c045e088aa0341040175015002411402064440d00003000501041c409001c803036552180f02c84000040e5901c04000341601c217655240160108180001400342040c40d403113024048070400030005010700403512005d0480103808445615a21142e000e80d203125000311403904410 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 78607124 1250 78605874 78605887
    0x204090b1002012a02010608060f01060908060103020123090406080619020909070c0f051f0c050a0c02010e06040b07050c04112502040905031803010605040b030601030602071b12020301140408 84
    0x100000c10600c01491172000050030307515003803120301e080c1065a89a0b610071544004001c0c031680302d910748020700704880240c901945503a0000e09814070078052104001012540c00c2411100d0314180c4001040c020402d102480d41c84403865200d003c01c4c0e94680002d0f004280005a620850089440c0818068050740c240c0d0384040f02100c06641d600700449020742c3c41030540e0041a010000b0790030340c1007a42c6503491005100c1d8034101c21600e01410403000d012041c4490700c03d864000a030b1489960702030810b00c148504074030004807144625040021025004152360302808000640701c0a134020942c3c082118503074616480000d80200601d202121800c5070100c0072208200c0a2103c45030320150012a0ba1a4280e465a0850b001940410304440c918245c02020303140c02d0248000624064070708024460340e4a001c203481301d030b050002030071542d0005a40790412082e20503044100c3c50341c85800709440d84420350301c84c0721602e411041e4030a60034502c0500c054800c075140da500031540140070b07914144 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 78608374 1250 78607124 78607181
    0xf020f04050f041404030315120b1b040f080f07060c05060a0b04110a020f15011802130b0301030507180203070c1401090204050c130f060c170705010204090b100201 72
    0x20b205122094210f51103003403603c048001404102c1c0501e100ba1004200c1c0b00c41e490403500e02e1030301d0754001000340c0c0b252038814020403040d400040e000341203204621084030f458000d000030f510840e03201c4405c00751101800200780c0c1020420600002c0c4c020181d980e40d580d109411100141081d8001c0c1c8950481000304040c0181d03907010400203c0d01034070202c1c00b610440d2000c0d07816041200c1340b0006d40c115008000c00c031301c0140800459038206011a0704154101607042000340c40c2148410045540050040703098245001c0c02d01c0100a001d902503501c0d038407841c000b40c41e03a142d403140c1511271a070070080c09100c400b80d000b03030392060420340c2d10b909130340e4039548480414003449075103103595559400c0d0501c09031302c8900446124802c083d1440b40d4170540c0b040b0406042102c1e134440d007582c0140803c10300046070305c5640c0c810402d8004800b200725900e0500c082d441071003868401422503100180008145102e03800800d100302c4101e400e0682264500700c203034280c076440d440c3c0c0d801c061a0313241a1084c09 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 78609624 1250 78608374 78608389
    0xc01110a1b03030618090b090105040507060c02010e03120405030d05040602100c030e0a050616020c0319080c0d030902040f0c0c03080a0608010f05040c050a03080901050f19090302040f020f0405 85
    0x1c81c060725010480964800c10704800e0508450700844480e2108072540611000b403c10540200559008120900d01612500d8480415008007003c001299003213009681c0700c1c03460f003040c210b0b0003015100d0740450000c50101550291041902a0051510140c201800740702903c04580094001d491840e108a00410003403031034a0b100c100741503503810361241102d01003115400451055001709000c0c10020000200b032542c0441000440d1302042c0c81a50360340303000c555054006e0f030141c4c2081c0c0c1c42d505c40ca00808079020300340c002c006a11a0403840d04003181e05421545507030b4000d40c0d042000f405650351500030384002d00d540c00c000c00d0316141441c000130300c103425160740041740c240700090090700ca1001c24292010341c40c4441c0d06075210703000e0009200303040d09840c0c000c08044544182031480d41e510500c2074080d44400074103100011403032100c1c100c0c51200b142e0000705450103003038402c03030032260103006194180002d034002c6290402c4030781e0080080c402c840104d020002340c0c500740382c507010802200c0b = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 78610874 1250 78609624 78609677
    0x203030a020904061706070207050a080712031403090610050108010312140c07080c091006020a0f02010309060c08071206080c15040302030a0c0815130308100b030901020c01110a 78
    0x1076894800085c840011246a0000303181d2801600907802c0c103440c001e180003096000386109541d0140c0130020305000180708070849003849003091401021b81400c1e0348000619400d100b000c2000420002082d801007140e900c50f812000c0c00c00c114030340390001140c40c0c072000d0000074108040060b07541181b60103490307800404000190500e20b4100c04002a608009113039001c1031696000c440c80341410314005030b40c241d00004600d034082d07030b5030325180d0000d6452400300000f8145407605012035041d039200750003030350f181504010f0920801d284468020503903007040303a0800002d10f100103008a0700449010b0b84e000c0b501d0007402030110426900401c2020144291070b0501c511040100000580301403050044a5008240031802545072049583c00c0192901c1910000e045480070041260207810f210030307031103804d4600004e160342c403204080d8040e412038000c44210000801000f400a505400400c3c0504484009105440007078480d030802c1d004084420300485c070803620024071504041c84401c0d0 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 78612124 1250 78610874 78610879
    0x70201090f1e020a090b0f06070203030a180306051e100e060111070e0a0e0d020601030b040803090309090103060f0c0e0f04020f04090e01060905090a02151e0f0705010b0604060203030a0209 83
    0x4052500d030f80080c60080c07155100ca00f050ba1101300d503114914000b402143e209078159003003403402c4030316030004c0d4a83c41807401c41403d00ca0030041059203004016100300245a01050802990508007020202d0700007904161030f01c94480c1001403c068942181c1c0b500300c0e0b442501c01807040d201c0c1d60054520542e0010007034103d104040c00042d010209500d0b25004094803071001030b454002c41000b40c1000f02d0840c45405560042004000040c120f09000d80c0c06a08034480340d44949803078000900f14828800c0d07042d40940140000310900c011940300c1d428581c0380400811400c060300c0c0c010351b18440b000c03a20940c44102180c0c05041418240c0051203464401600107203015154000c030b1080711030310304500c83c043c0c0d5581410300c9680c08038400d0980101a2500410030207149900150200342408200d4550b5600802c00e0030561031103480030490064086246030b15503403030300f0064400340c00206003903500b50300b03100300540170f420400c0840d802d541895010314595a03c414180e806584040403180c0c = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 78613374 1250 78612124 78612173
    0xc020f010f02190c2d060221010803031b160f0b0601030f0b01020705090403050c190201121107060e0c04111207050c060406020309120f0706050603060c0a1d12030301030b070201090f 80
    0x17800180e0900c010540750704811004060051003080401d0b002d68160010101a172080003030002c0e80220000003510b800300807114507518142100742251403000300c40001c01c080c0240a1000800048020f4036110301c1d400e03682001060340c907019860580303801050090150308054428042420020940d40d880780c000e083c51807802d840007905031300c0c100e00180001005400240d03c20215a80000b40d442c405040f41d006102000f64100c215006118004004000b195600c03a00461001c080c0924801d242d0010010003039943d43c00c03200140795005082c00b480711040d4031b00084c52a40900f0230340c3c1c10101c1c2d200040010355103640e2107038025440541280c8640c071075034648410301c3e2a403d00403c0069000c1c0211600c1c0c036001c0c54101c080d61409005103119411820401400030024810760309507145a00d019080e8008003102358000b000c91040241d002401d1030f00c0600940000402141224810503000050b561591002c070308072090504010f04c11580940c10501160301c036590507080310301c00d11100 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 78614624 1250 78613374 78613463
    0x5010e0a0b030c030a050a1a240a0e0406090606140d02040801060311010f020c030606041d0106030c031205070312020a27081605030a060c020f010f02190c 68
    0x401c0507081250020021440003040103854072a6000b61500148003600c2481540c500007515020f000d4002d14041c001c1c0c103034039140181168008030001c0c1606080520540c2c48015450081103000c03041801070140d81070403c0010311100910440048600c00d0f80d560324100089000440316030720407410b4000c0c0799020700000c58414000c0c810b40700150f10480f8100c41041d100000542017800f003810660a41d000a12441215100896000e60008040710002618080310003403205408504c41d1280196292040100811231030400e0001a0703405404490181001540b00300da80707100d48440240052031900c0d1403841504141c0280c858040d540c2081044115400811816212413644125184a18410810a038041440f400408002ca0085144d1035070030304002c40e1341e501c85000300810341344ea40d072540700d8558801c0c80b000e000103644200900c0301c010001e01e020080d40043c0d9240407505000616842c41c240106820030001e0380c88140c00b14003020030a081501950120b02a50610310420040d = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 78615874 1250 78614624 78614639
    0x9010c08040b0304060501050d0312020a0215090703020102011b090b090f06120a0e01020a1403060d0b0106030501060e0108090a030f030f0212040b060f010c1b03080403030e03012405010e0a 83
    0x40c0c000b400d40021125201d240900b040c0e13099400690100d8001c488940308500031030b03800070306410580f50104000d03946442e03602040349407070003010321074407480554810700040c000045607000c1141d000740c2c020700001e207050b01c61031030140854800e8408524000810401560b080c0d0217441e010070020007842403034801078040740c2c10741c0c0321610448110340f11000300120f10b0294030401402c81900d4008508102401002804905d8003c5102d030059201200181d42c560b50100150000c5603c101c4148882d42e48402c00f5000d44020f01030300000c0380103204c1c2c00e0340729481105858450703030075540200103220740ca4400b51f0301400c0343c650071030806498000b1712411003441e00041024200e999203c00e01840c0c6400c1420484401900071889400620214503440c0c0c0d00c40311f814041c0341c00c20400401070155140940080b1055803004203d0400410000107040d000011050903440c1507000b400f05a080002c1058554240c514401119103c0d450600c425441082001c006650180800380c00d42e1300c6014 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 78617124 1250 78615874 78615877
    0x609060c150e0f01061a1204050705040c1d0103140406020d0b060a09050321030402090a0b0d030f1d24090409050c15160212010212010306050108070f0b0405010509010c08 75
    0x11600164400c00c200d0010300d40074840d5800030400c4240e064250140701b84070001030700c604a9002c110282100c08601408000d10445004100040c8100b21034054040c0241c0410b10741058411012881c0001c0304095020303016940c91510700d81d40d1280207903a01c1c1c0d83c14001b5003010003030000281d60b404914007661203070001424141e1154491408a901d094209031520301090076050380c1600041100132951240c000752500281d04850301e01e00f984d030b80555800144a4400c006034854141120f40f0145074000c840e81319030b82e851390341c0c0d03007501d940204943c40303800c46070810070750400000c0703d01402d85026484035540e0101420703903031454580e032040003900342e074103241003170350550488446103c803071a10792800c00228441801c01420b090b0000c1a0042402c00b129029010300040c0d0300d00d8461500030350403542c806803002561001da58503802c0050003042c3c24020800300d442009004550031000d070120400701c0e44441213441c40e10341000d0044403150403c6a4181c180110b1031801c4000481c0d440 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 78618374 1250 78617124 78617141
    0x6040305160f080405030d0e0303030612100204031a0f0603120901030908070b01080d0903080d0c0903060e0601081b030604060c1704050c100c052505030706170c03010609060c15 78
    0x40c2940d13251824642050305200d05480c01409000580d2642003e0361400305c00c2d40d922000c1110040c070240c040205007800c0804800c16591003510000b008002c2182020a40482082d8030340c90342250390f5510b2104242c0c010130b5504e294582c1c817010010701030b44035110041a0001d010300d00450040702d81e55800c40150001130b801c03107030106244c00612004c001005140c3c280196850036408643c43e50712614501c0c401c5000303545401d92103d96003400f050003904814011603122108200304004240b505450701020b001d800714a000310020580100c00d944402c40c84880000c0240444e61a10f5850000501c89906603406102d08c1030034410807c0c1840013501c3c07059004402610034403181404011441038528550014828151480004164001000c0c0c68400c00e410060304138480c541e141440e04180c5601013030781072041701c1010a0b001d5000c94401c4580360542c0c01342d1000c0d2280d03048183c0501003409020001101c40c501000354a1184290005460040044d202c00001d0080c0d40c40603a61080c = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 78619624 1250 78618374 78618383
    0x2090d0506180109080a08090106051e0f0102010c1d0a05030d110c010203041203110106180606080c07020904020105031305070e0916061e0306050405070e090a020a0206040305160f 79
    0x7010440701c2e00c502e42aa004240780d4400803c0b542410380d460000ca40140143c01e000c04c01c2e51070008901c2c500960288000d00402441c03102d12901000c601501d6000c8902070710701800d103621024425500500800c8108500e9403500d00650001400602400c00c2581083c0d034005a605c1c8000f400d43c030180040f92a1340129928030b00c0c001d0703001c40d005142c1f400344a0910b04642c0100030070065210810040000d01d0383c54508a0855200c03080e1881c00b611554001d00b80c00d030342e1001541c490070541d50246080364400d803501001a039130140d4154882c065400e0185d00540803000190040d84228001c5901a211402e4440040c02c00d0315841d18065075a0840302024000400b408144c0c0e07030401c04080d001c8240207001041c3c9050820040000b120345140080c0c001e02920501045801b03600700c0ca01508024104201514003001d0040000c2c46a030320080c0605030030004160014824000c8400c0d2403040e800610590320780d03540449160b8014082c6420211031040440009160602072004c0c45008 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 78620874 1250 78619624 78619633
    0x2040e0a0510080c0f010309021809160506030603030405151605010204060311090123120a050a0e0a030801180623040c09050f0603040206130e07090608070e0f030102090d05 76
    0x90038801d034062454001c00f846521212081c001385d0f403807004507005c2c0d44003807071b011891502a1021030260388034641000010fa04e10b03130400c5a5103d0009a6100812042240e06461503940c0140251440280c1344a505038004010501c0103041000540a41d44e5100544500c2c01d9011801d8a4110041d040101c5640c0d400040030046a54035005840035400d060311000d10703010094001038811003400d4005000461080c100e4074003946040d00341c80b910f0241c100466204d103800c420200040000716100c4c4140c0307280024050b403a0350001840140e440d0305848403d200d07424040c08002c0303d0451385030603084e0b0391581804281400c010303843d00091516404084103005052040005441c42d0340e02e040c0800c01000000c12080e959003014010008041e82c0055072604d490011440703901c50b8231241012a0850302002441d41000d18955100e49004e956070340c80c0d56110001294640001c1da0b029000840090076201c0a10302441030940320710f8018001031400803110b0200f00244000c450a5909402 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 78622124 1250 78620874 78620881
    0x110712080c0a24050114100302090607080c01240b03090a0606090b030615030714060d0c0c05070501020102030c030a020a031407050403030327030804030c0b04080a1112040b07020402040e0a05 84
    0x2190005900780008403c01400198104000c41030003803180038a4500c105409040000c08034001c2d4102e88803414041c181e10755842803410700c90469405100480c031035600e80341c03131980600c070043e0107201c14141c080d240c41051860103003404075580010b86018030170b008440d1107800041d150302c520801010505c00c04035a425404080500784100103040c00c0c11541c440019812560380410380c039041d00d000045150382900003a0200d40c83e8054940120000317031030001c42414642d0070200b140d4a142c03089040300c40707039926030b0012401d030f0000303544614480d441070001c40c12014040e009020010010b00d40084c10b843c6141d08210703c01b4065400b2808207900007018000d045c1e02d030050001d113850080c05e52000c201c01c4803400d12540103502c000380801c10144041000c2510810300d400115821091000040c02c240c2001c502c1c56000113001004034103035402da068510008114030409510301c03000d1905151400c07030045c4003640608400c0368425405c110119040d09895a43c0d0b00408001d800062070380b4 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 78623374 1250 78622124 78622163
    0x7060908010b010237150902120a0b1305030c0a0605161b020d030507122c01020a0b270106030215040e01140a03061803080601110712080c0a 62
    0x303400c00241c43c11900302c1c640c0140203241c5403082d1034071a114094940b070300e1013010380301070441c0b02200d1000308103a002107480440300c106138002000441c002c840000d00750b075040903e15501d000c00c480060040301c1d210300260300d01001030b203103224541c00344040c1c0f40307030043c2c107801d450138101d524008407180d40c0e6842c103208510043c05041507140545080c03080301d6004d84440700921551220000348a400758455181c2014825401d443c142d070750105034a0004601c101000d80f80415882610080075001c55040311040c800b03d4010588880c10380240c040d2000c00c0e00d90042c00c54008043d26049100a41001c20840c48904601d000c904190b00006a07507095104200d403c00a4111644d43d44030107110034860225031300c51443c112001604400e1a02600c1d50114842945550001c0e02d058a44041016010310028203c0365640c840d58076003101e55a0070006458604004070322403595440f002041c030818510b28030020300a0b004260031402c105081001c00c1c40e00390440c0c4200d91003001400b83c240241e = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 78624624 1250 78623374 78623381
    0x306130c060e03100b030a290c03010b1206040b13050103020a050a0e070807170c070c080102040807030b09010e07080706030c0e011e03110a050c0f0106350706090801 73
    0x1d107a035240a4104000c101d001070f58408602d00101101655401010034640e4200700d01407100b076200e685510031004203866001e8243c82c03140c0c1d40800302c0c1580005145ea804100449040e10301440b4068141194003008803111f40000b010b40d40c225554020804080e03440c10000003000c1c0060b000070442e90704620600000e90a560b00c1140190301e204c6090000e83c0140041550200b10386c9014101c0ea074545100322118000141c26452245003801806030850144000300051801895005002c40d524894a0300305d101e503224400c6160840c0106100207403180c04c030150030007001c1c0c3c000300307807000041c502c241007201a0f441042903901800c0100071603501801383d100c000f030303060500d414140b0584001a1201d001e0b4541f501001a20100c032840590095202c1c5a050104170710b440e4845688510103002680500c03809650b03031040c8101d60b100240140649001d60752a104107070300100c040d03a10078100c10784000d1450501c4510301d1f42d680c4100400c01c8a01d00501b526606c803001245020021801c5 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 78625874 1250 78624624 78624629
    0xd060b0f0408190206030115140a03020301140a03080904020f120109020a12050402010206040f030314270109110906060408120304110d0314031e010803070204050702030703170402010e0306130c 85
    0x410030001c6140000d85d688600380c0341118a80b10480d0176a200c4000d080390380c0742c03082003404400040412881240383d416805141640c41c8030350440750003921a000c0004900070b6100041c0750b440100100072103410f02e500a4040d002290499a0402901017510781820009820070388000d0741c0451100e0145e94040450500c0d035002c042c04129909203500000e484440003040542410040d552400c101440b0340d11604082c40f28070311071096418091941100043c05109405054010340c144034040031040c4a2940055407103007080250701c80c52820f100d00c1160003022039510040c20b00000030303804000d0005030313414061018802e0b42d034079061614001800d18140780c00d00568083c15407400098126010829888513a00c0b81c945903030320704203450154070f1448480c0100484040001410004c000050000d0340d10071142444140c0e1840b03012a6130f0700400c1e10240007d11a086000d51008030761b08050b421034010b1510501400207030010914150055500d40c1d102d1180341d800100307000c0000000da02 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 78627124 1250 78625874 78625903
    0x30c030f0218130605062e0f1110050c0c03030a06030c0b0306010c02011107050d05030705060a021e0918040f060506010806011d040b1206070201051303140d060b0f0408 74
    0xd90f041615415100080c82d4100400302c030394400104a89a0300c0c0300940010f881460b1410031582082c8a40c108001c11640080c000320305545c05c0504d0080c0102404280119800000c060741c00071085814003800010f40644510001006003c54414040c8000d40c41041c076002c0104802e4030314503044a02c5111580f00402c40c103420300074000541e038040f112051050302403800115074078000c0400ea080c03500540c0f0040c0d00419005d1036500300320001c00a006041c2c06902510010b6482403141016031041175002c180c107a07000c0505050705107103040034003948400604020140507001140b015504801d03101651019540f150b890204140c80c01000d43c407100030310700120701d03003441d4002801c0340715039400a8406203038010003030441c3d480300d512609460754000c0441007c0c80105c1e611640754031040d1030034001942040d0005140300a94003031603c40580c15502e0841540c82c00041d00000d4000c84100d0105640300d590008850310880b0103821040c01200c2e0450361780e807601004510f40801c203410400f = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 78628374 1250 78627124 78627169
    0x10f0e010b0f0a031e050a09031d030705060d0204211101030b091503030c0d0507020108070e06030c03071701030c06020d03050f01031e151d0f0a1b030c030f02 70
    0x703005400b0300c010703509124441c0c20301040480441840c3c44071494200c0c035000c000741c03800042080148070303500301c0340c4854003949031411901001818820102c09010120390560300c03c190400c01c1c1e0070017900030400c0b83d111240c01030802e5190241c410000c181c00b012101002c4091a40905210350f00c0300818085809080800425195201003108400b004103510f030700b0040d00c0e001e9100c5880c14812502c4901e1002d096604441e9508800340c250381015a0685c0042d40360320000d510030340a0300140415400c010082400c541d01d00303918241da80e0000b00480c6c02c2200300b081c402122804a041d25001c0c51040382c004008900b401002442c1400d540e0741c0800305810402031020480040320400e054980000f101d061a1050b00300700303249010178840c02020080141c8160218030701c103600c00349041e45c2000140c1105144001000d5a80b07100c034403908415045070858000155140304280c840368054003100980c9650303030315078010034402030b4401c0d107a9000c46040340045140041400f0103400c84220f402 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 78629624 1250 78628374 78628387
    0x70f030c151a01030c02031c0501032108040803100305060702060615122409040b0f01060e10120b1002030706060509131101090302040f090c140f09040c0509010f0e010b 74
    0x700310b506000005410300d5030784d10078004294170034000c40c0d07603c121000c030072403400c2510b00b00b94000b000244010768060040000000c8003c2d03a0300c01103488554242e842c1c07280313519aa15002e110354005040e8040b00c640c0c00c04000b0010318240581449040160042e00c40c900c1c1c02c00c00d110f89031004500c510000c030b004000d001049400200041d40144030000c0218074cc49803103941c2d0101401100d01654032542c2c24040004100c10a900c281c071440024004810a0366100c00c240d074030049048105a10040000f58034100c0c51240040749074040c50070340c0c04100a401000498555800e124940c40188c100155007000d01982c3c0c02124001d1109030b442004900d00076940e1a540c451459000384403130514460302e541030b03116881d103001454006004000012511200740014103150300c0450343d000a8500008005641014115114102803c40710001c0b104400304401c1480c011703c100d0f101780d010781021500e5150411081e0280070780000000c08541050f0a11075a918164461480d01000b0001b0703 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 78630874 1250 78629624 78629651
    0x14070e0a030305030a0e011b0f1409060903010605040e0d08060a0f03030f111c02061b0412020102100c0905090112031205090f011401060e0411120c070f030c15 70
    0x100c8007103a406280042c0c0f6a204e5080c0f8001401c40080c07480819070030409580110884001301205584064035114600700e602401582d101506c04100c0e00d54503000d200780c036007a00380741c2d0040881d00d500030000100301d51110000742c03c8885032040da505541c1310942b07180003d40c0190340c581d0426400ca804440040c9071034140b50448840e408001c041180c45040c541c00c0340e01866441c40301000390380a9802c051290548000080a07a070344450042c8115008684000d83d040003c040100e00402c00c2490541852014507403c03892a00881c1103120700c00180c03484042501c81c408a41110b566031403007491401080082021060b0410091401e00c3e02442c00040d030003146200c40d054900001180030744d102140c05042107118a0050503a5007007027841c2002d1208039102030b0685010b900c0c1c0c8200c1c11140300521049603126641c3c0b50b500481004070100c5102440c480a074841d40e6101c0c6280b5081540e035078080c1008072058200c010030100391025042041d446e04640e01010803040810074174410205 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 78632124 1250 78630874 78630889
    0x306040b0406030b13030512010b09100302180402160510051f0e0610030b18040507080304290f07050604020906090408090906030304080d09170c060409020306061c14070e 75
    0x68010a030107200101703040502031000e880c1030100074840d21000350303524890000d055008822003803003036000d000d4000e1461300034400d58074003118a2202c14141c60f80032003884025031040d80d20b24142d840701021075002520030170610f113a007180e0280c0032540d8100f03400e000306001400460f201e851381d2003803010301a40000244490b80003604035004401120790100641c01000c8031403010340c00924024920b0a41d80f003010000780914458802c0f00d000650700c40c005600ca0085008000740000061a00c00803003101100007000d844800c55414640440010a030895a105010031078441d0440d404200940c540dd4419651000c2e082e02d1a41482c41c01d0790b102e400350721071500c0c440c0c030401e008408030710503407020026140500010000c9480000d051500604441c400d8032506030350701d21100c103048a080000c03e100340c1c1000b0141065040900b0885810f0203500001d225580224091168406880603400c1c80b844090500c2d00005142d0030b0750007099140fa0008003142d040c455202e0b680740c8103440b40364 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 78633374 1250 78632124 78632131
    0xc030f06070f0e15031501110c10050c030d051e0a0c050409020c0a140102090a050f01230702061908070306080d0c06090602040303030b090714090d02011803080306040b0406030b 78
    0x940200126500c1e0009008109018074a8001301408010403c001c0c003903c020003901c0c2d80176210440680b5503103c0060f076420401c003809410160103051b0002090280028118a008401c19607007810080000d9408444044803c2110301038a40c00398041542401841600040e80c584140090410081c000c1c01d180f04511800c0c86069000805403904002070011002d52035106100d121140210395100c0d0207900f02c03032082445174a41740c41c00141071030319440404048006031103040903182a00320b80040a000801c070040c0d0b68408010103001642c60728000e1444401030b004511085840070801411180000e01c80001e042c9850701c144201040060500d60492450be006c810310340f0b49103401c40150030000c200905890010802200301b5400d070708580903a01c0203840702e0faa599205041243d40b000c42064140c80c248042140c480360742440c0200c09492030040c106081820038020b403154500c1407645c81034802003004003e1114500e000e004120b104176003100c0501849003151120003ca62015 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 78634624 1250 78633374 78633377
    0x20310030807050c0918010605180a09050703050a0c030b0105010503070c020603060402041d0a2a0c080705030d050f0109020403030512070c02190801050c070308060d050f0d020c030f06070f 83
    0x314a550420400b0004c803180c400c0003a000454504003000d440800b00104140142c00c1e50901801203298101120001c016000d06115000b041d2140000407000b0240080c4c01d0755640600800800442d2007045154821440307992100d1541e4954140003a034420103030406c6042090410500c84280c0d88034007a26030780750301124100d070389846900000d0000c2c46598403002c10030034034460061046003903140062048403618006d2045044c010026101d99801c0700f500b8005200f4101c0d103110306403003041e030051054407603004a45006000d4803154915003142c40d08840e100e8550040241451400092500500c4041015400c0c582569409407440c000c0c1c0701ca99146103d6280000c2c5030a220707804102d030071600079001c11150a03006102402951446c0100d41c1c2c19800c00001ca1480309100d807c5443c070740d80580d10120662a8901000700c0c189070a1016910b51081c0789003203004079028004548526201d40040004480040c14141072140d48082ca881c0c603040501000742c0aa004041c808100025 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 78635874 1250 78634624 78634627
    0xf01060512060a111b010207050708010c05030a020a050d111306110a0803130206040305100b0901320405090f061803030112080408010906050a0e0a0818041805070302010906030203100308 82
    0x43c12605050140013190f05c2542d03548034440000c2c3d1410741c01841c8090255040d01e81c040c2d101c2640c01d00703a03a48000c0c400002002000020a5500345501604d95040a0b14020f0f140800c0d00c480c0320180d5070b803c0d03a0741c502618001030b803119550b031078005140148850b0030013690074482e8440040e213807125000c000e84a82030000020b13051031502c01c0d0144020740e0003001d80b6100c680b241085503451070850000e1003280d26107003015400d440c18001440c1200c03030160910640310000035500c0d1069112120f141e00c2c02d000450ba54040d0761340c5004080c46403a100001306401050140e2032458904060301402d0f101407261a0b10700d5034000441140c0c19500e01e4040351658903c1450080d070b0328800e0f940007101e55442c000c80e2030200810b035000350b40140b01030395050101403580070b01a9160482420f005051392070800401c101c210212158460408000b40000303840c030101e02c807034004102814005c80d91904468010300840da0400300c00c001a002710702d000c40c21480c10303040080400c0d05a000283c1000030 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 78637124 1250 78635874 78635891
    0x4150e070305191b030c060309050309041109030c010318060519020711090105030c09040b130203010203040602091f0903320106090f0207080f07140f0f01060512060a 73
    0x2020030040d001150301030122400b08107620380c083c4000001c1d803000c0b5014121038100d2264890584090001d40e81c02c8030401c2000c0d460020150020700394628211600d020503c41140d865503940305145880b0600034019503250803800c01c04d81445050103ca5050514084160381c01c104241e8580c18500d40c4800e0004040c1c4400d1080380b406540a65000090f43c000101d00c0b04100000000000511007560780b40a0342e622039040507100c030341c100c2c13040340c00003959000100821100b40005070052014040e081d82040d45801080c01d83e0301c2110151a1150005004109070500c050903040982c60b1f0405402c2c00400000e00600da00b0282c480680060142e04824580c0340b01d0349034420794030518080054440440c0c409080c080c14081c85490025031902d0030880d03014641e8002c4811040c3e0141560f864507481c1d030b2040c0507030f0b0410082680d82c2e0411824420210104211850f03600d00481d00520100c0144100c0c0c0d400e42c0d80e1608202e0041d80158000c280e9101c0c0043c046412820f00900440d0006 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 78638374 1250 78637124 78637151
    0x7080712030908160c0f050904060b040b030d1e05070b0a0509150703051b13060302030c040f0803030406050105031506330904110a0509010c150c091d0415 68
    0x440b034000900b10701e000040c000c54070a40002c0010150344a0000300d0011555150b904403290043d114a98000714170000260006003158850554180003d000060440440340480c2c6021080025030001c580c480a11001c2082500d0307005445e11010f1910301e150a600d0303641c440c20704001074081c80b05161128003148240f03a0a00c50b490581d005140c007481c079440c0000008014040680e103032803038920a40814041142032808580c0c8120248000c40300403403418008800030340c001440c0c0100090140004070f400f00d0585002801007003079000558403070916082807811540181c0c006842588405003200600341c011003482d42c000012101020040c040e20030310342400001c0035031f251418026040f0f50b2900c10846002d04480030095074108809409007810040511441448101040303042c000303180070b90320900050b500284240d0207450311095582c100001d4134026060800462081c080c144040c8200b65450307401d000307800305840300604007911a14035402e03a0343d640e4032003661220241e00100 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 78639624 1250 78638374 78638381
    0x17090a02130603060f02030601030c080c030115090e0f010510020a1a0a090b01060f0e040902091803040803040807150215041b03080c030a0e0a0b0a081504180c05060708071203 77
    0x85030000c401740300c02c00c041c154550007540211692804207140400d84040070f8401d03e441d500c26010807014500c3d51b42480e942c2214090306001e0582000300c0c0b0800030644d45140032045010304071454441d40e00d54103000070030003201d504c030040360215030202d03140c10040350011010300f61600e075072200c000c42a25030621044c05007140080152408048400020300140e000345885c0500426503510403140100d5070400041c0d5250301d0029610040308070100340711648840c803082d40303407240001b260318280e80c4904050658209034030441043c0c102c04000c2040c1d2907070f00121182404a403010f4a403c0c440d1700d842210759140944003900d040c403600e000603239912850221001075a048001c03d81c0b100312407807107156283c0c171280030000001c1c003146c1407c602d402c205620800740c0b9012a00b203030420008010444444d10f000740110301c10528aa082d425980300c1d40716a4404003440d040d0341d4048201800c12100200c1b40d07a02c02400341404019100100d8407880c10354000d9030b0300485039812007205401c210082c = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 78640874 1250 78639624 78639629
    0x110d15022a101116080a020a140106050f06070b1306150305030d0e01020403081c15120201080709061b0606050901060903110109031104020306120709020a17090a021306 74
    0x2a00700480080c598000842e04201c0b00816001d0040b0950003101c02c40a020752950841c0540c4900d80c0e481c00150b0800291250240510482e400c2e0400d648031500301c4030141c82c044640365510902446241000c020303c00c51502c1c20b850300d5280280300d541d0140082c0c03004081110220300d07440b280302000100c1e0000c0145d1003188000242c00c549905005490b5031100b00c0d400051440e02c070080b41e1983e01030003a141240c3c0c2064240c3c1c10003503900a120007501c00e044101441c2903681880c400070000091441015040b80300d401a6804c5031440003605190780a401c813000d2141f0614104030240d03010f20046c00c100e9030f107286026480494504900540340540001d54441410300c0041402039002c4508000c03a4021114442000034023401502ca80445000281074492895410103046c00e05d5001580c204c40c010300214031041038000d8590030280c2641140c0400b80e00091850700040c1d2040261141c00c9510300400454204a0301041d502c07040040c00138054424101100f02d40e50751941310400 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 78642124 1250 78640874 78640927
    0x1050f0f060d240c02060907030c0e040312110909070306150f09031e03090902070b0402041a0409030e1311040603051902070c06030c05030f06060c010906020d0603110d1502 76
    0x43c1c0c2c0c0814801000a08031030916403005105400c0001c40500000484408907070300841e526a0041c1819005200c01d600100250140207580c100340d080120039200c1c02c100489890819900d90210b9010404005c3d0081c11000801d0309221042c80418081c0f0070408080030320381040340d050714065900f6074140003160f0000c1d0229002c2d00c1c1c0c0d902004003c1000641d2284242d0f038000b00240c0b2011143d00328000c40c04060300c0f03d00e07107c00007030060030f05070b106c549400d48080c51081030030305074000101910712140c0b0440016941c0810307000c15040c030000c01d410305044d2080501c83e010b151440c00501c0c0c00749210301010162110302062220380c80245140b4000154802551780d408142084040102c0340d00c580c03070000c1c1c981110340c050607108605503801580b6441d41c4079400c4d203d1100f0000300347c01002e2100700555844014400040f81e5100070400c1c08038071600403900c540795050200380e980e0f070340244900851380d0110900004640c03102c2c8961001801400680707448001208503030700c0c0c1d4440802003 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 78643374 1250 78642124 78642173
    0x3040b01090239070e010e0106051e03060103060806040f021c08030a09030513030b0423250b13050f010503130305070f0206070f06060f0501020a02040e0114010f030501050f0f060d 79
    0x6140c500c841d41081c1070307074802e0383c440347e40b0790342c0e00c0c000c0365503106255100c07010bd0391180701c1c480c00d040950005c5400c61014500072070482e4650709a24149001914202c81c803500b000071440450802044900c8111130140e480d404071600d0791501100d81c0b100601324100241d4450b90001094098020b58110280b441d0741e080d070440d01ca1501f10031448094030291044d11506060781d01071003811607010500105603010780f807800f4044103020103081e090b00500c50341d0380d140381d00840c0707001404001d0f150050789243c00004135443d106c244544156000e20850411408208020788081c1c1c0800c251405a45481c1540ea00c3e40c0c01d050209000302f450030300030b500a03000544002484002d040c8082903900846040140594591720107804a059105590258018210030009483c01d64400110003810100101e0f1020340040c00351610a4242c00840a84201c4003042c024400709109260f40591207003161181410000d1040315030000c020203040c4940b81420602081040700460041c880d048038820303a = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 78644624 1250 78643374 78643379
    0x6021f1806110403140102091c0f050d020c010e030303010305151504180b240111030f13060206010602030403020a05130e06090717060c030a0506060403080a0503040b0109023907 78
    0x9490f405480b00342c448100507110800c03007880620850304a02c0d0b0003400350702c1c42d0b0b12100c071400c10f4142042095400c1002c406c11400803440a01013a844201030ba03010f80550237503c000903100c6903400c015640a50302c207000603c0001c5002402c941030064010b03981381103554900100040e2140c0440700e5410a0904e0401c550b510902c0075091b50305031064504010642d1152800c02c8480d9805669003121080700e1072820b044e5014240d15084038892400380d0745031200d140c94554040c0c0c4107a00c0d440381c6da440180c00308440c0b64140481c0d405860280702461030546142c0000b01100c8460094510921000c10381d4214000340f130b80607044141b0400c1c1902c3c80361034140700032a01c5610a200b41c0d01018800340000048942c0071612910400c50103481c5800d54036080e00c2d800051100400300c1e03420031001c20000c000705521030080c20191026680d02d036601d10303061030480c288900c103900c81c6411900620810b10105143d581c0b441030081d0302c0c6022141d40c003500c18a40c00c4543c2c81c0c0d00348403660260350b40c00b = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 78645874 1250 78644624 78644651
    0x61905030106030e01020a08011703070501050f010e010b0c0318040209190305010e0c03150a060305060a1b03110a141e04050f030d02030a14040f0806090706021f1806 73
    0xa0350480d1241d440c208150100078180f02d0903031107000c802100240840b40140581c961071820020584c0711801100d042058940d40d00742114400c0c2c0c1c419100001d658010008030420140c118090425404c006090031001050780d580c80c00380410b0018005584080030340e0301e4075241c0c1500c06d0302d2001082100c840c1107030030040c140078500e03000070354503035090050b03160390201d001611036042080030b40101200100b1100c19404000c01424103a00e80d6118500000419010040e8600508084900040100d007805210017125880b88402d0300349801c110107044850100f1080e41d01c4440c031410300b06001010160407480b10701c62914919040540b0592046448007808013070002e82da4107854100c071407801d400426584240e60f00c48400148d0041004509041c424604040182680b00180d0304003a1030b0b40c0002820089074018290700d900280401038a0182040084020022130001e401240b50b43c0b000e001c000604001070700b01d40d23a102c91908030921010705003003008a402c0b10003040300050780b495 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 78647124 1250 78645874 78645877
    0x8030a050a0c090605040b1b010519060e100b0a0e090c0a2303011e030f030309050d0903120f0c080703020606010807050906120a0e0708010c090e0405100209061905 72
    0x2080c0d084a4500014030114900510f0703080b042c0c40341500e030309041070314041c000c0c002c1e50700240e02c01c144100709581012840d5400d00545000e03500700c00500810506032184c0000700c9145d5803114525055040a11951a4244106078103551071100c0d011b68410000c40c007a00c1c42c2c110301044a8010106c07000b048112004400039102020041d41c4910100d140d011410b1551480000c1500486200b00300402100001918000c00b101c03200c441e00441036a20f880e0511185805e01c400d80209841d12400f80400909024501040c403450070800180ca086446500c0d2002c2c0401c81403090100c90148805018000c20703c110341c4a610165840e81c0b8001454002d40318002910802d021480d54400300324040e0049003590003154020308194203094800352100640d44004c1d045288003507070750000496010702840352201a22556001080003a1951401000300703c065100075040c40e021381c2440b00154000c264040000e14003030b00507031540514400100e66205030143c03d481100400046000e0580000 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 78648374 1250 78647124 78647131
    0xb0d030207050a0e0919030c2f180a020c011e0c0201050907080d031505040f0501081c0203120408090a0306050105010806040c051c021303060e0c010c032a08030a05 72
    0xf40c01c41aa550f41d19440b80354104180d40d010450340241c10500c1810503d1106950b000c1c0c0a450b100e15241c130030ba200c20940c1c081200201c1d0140c024268030f2034501d030f42c83e140c50300e01007002d4404429406031401164100d00b030103070003143d00980000d280d4180601c2508040304151610901c0380410008100c6000140211249140994241400620341d41703030201e102021203168034043c149101310004210300401414900c16400c45201b840401c00d9116481209031030500640c0006555040c1520145088807042c54140300c500c030003045c00728150740881510100e407a541242116500c40b846c0c180518002c01c0c4c5510b8200141810001c10f01c0b81700d401c2039040740d8080e02c95202a032210402d02c001d6070001440ca0000c91800c0002158102001c015640648054a001401e000b07000351a01304e0401c155209840c2c4c20b896049030b10300d000040c42815a8203009091441030501c0d25500070b00a100750340c102c1d2070401c07074441d509441c9042e1003010b0141590712404181e0f403864a865140018201038 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 78649624 1250 78648374 78648379
    0x130e030706140601080a0903050d1b0e030c010e09100e100614070803040312060816050108011409130503090307030b07080f04030e0607060603020901090c080c03010b04030303020306040b0d03020705 87
    0x10010b1004400720044050040c0300603520310180d69281424200a403404120881c20440200960031503402244106402e49043e40c0301e510408106941c0184903403090003c0a203c2c0e000180d8034aa40d80e0004c072902a81034007960380c500565160a2490011841903100420240104c820400855030101c542d40076140c01d91561080c0c18510030050300305005510004080d007908101060101c0c0c014904207105880742e8402103440e60f1035510762400d000001001c0c2103110b984420512066030410030050162070800810610411300c3c0700090f6020001802090000801401480502c401030080320b09406024049900559032481d1840c0745002c00c4070040002007294000c240d450280050322802150581d0702c8100c482403900821074103030f0012038100d81284d0348050000040e02c464822a00801400710005513a100e02800501045002049085880000c10040c041041000c06032000d40341c05150050310f80c0da610b004100281000c489055024409801c1c2c0d800b0542d0003c0d00798140c4506 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 78650874 1250 78649624 78649631
    0x3030e0706081509040501090f08030114010509030304120f06020304111513030201200a0803060411070506190b03100c030f090201021c050f0a0503010906060f02060403030506130e030706 82
    0x15900e084480b000192540b09000300301041c48201c0b45072514040f43c016006400005000c200b554440c0b540c4c2403040001c0792408004401009030b03c40361822846410b00a003000752926141b207000079240d00c5030b805040c6007902c94003440b10600c0700700d042c1d12000540c00942107542c0c0c249820034104405101c03088510a1222000101c8081a160192241c0a40c0c4000f5140ca060440c2d0055a02015850414281e11503038003c402201c041003004085107405451419640c2c1440c005000556000d00c01c0c034040c002003000380c0070005000090300750f407000d000c1150300c0d4007140010f001000360601071340e8164140310301c0e10619426501c9038061040c085407514200303c810021f060f813109940c1000c4010780540c0280d208000303000b00054003a60301c3c440c2440d2035071401c01c10f0b0001404a0304003560f17501c00200040014400040d081c0302d1240a410141490900b920030040c00954426008000408064403500441c00680704c40088409049a0354410b110280000214950b01e4110540981e2110708 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 78652124 1250 78650874 78650879
    0xe030d1707090501170c0c0a080705010b03031204120c06020a0302130515090607060f14040b0c0711010c0218011202090f060f09100e0709061e020304061101090602030403030e07 78
    0x6a00b000100c07007041e15038010505045002d6082c0d2940281499503040c010800004000000d011130f05d42503104c4c4d800103885100c00d080503401c544040c4581c902a070310401440c160300c039408000e0366005030320846c070010350207200f0000c4442d11706841c00200303550300102c1c003404210703015000f504140401d40707508618a030b5184100549419007071506207400b041040b100400e410450b00403c00075000b00740128034408103114040880f1241c9842507620710620741800100301161581c59044600c10400508080c0c540d2211406928114102814002c03408099021521036030100104031450740e20101c0a50394030341d003054820049641c12445424032000180f4a8016010702c00d00032500903002200c000c020506011402e400074042c00d401d009040800140c65081d0310390706115007070381c2c0c2d541204180340880103881601e42210107004000d03604403071905598000190780456100c0d00e02141c0d0300380da2103011401480e0b01e4401428181c000801c10080c19003540010f280c0c1103d41c0c00319400c85c0d9 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 78653374 1250 78652124 78652127
    0x201050402060a0e0409080309061006020307030e010f1808010c0905041a15070f0302030d0e1908030a020403060e0d180b0301030b0612060702100501090c02031204030e030d1707 78
    0x10011500294802c1d0244074a444261050440024101c00a00002401007054913000100d8200f1104811103030b101c04104054543c807a2022002042180000c40c10038a490350044c000106006003c0d04200529403220715251056045c980c215035484030400040f80c4881d08030740138191081040010884032040041c003818a40301d120881c1e00b12000d00d0a06412010401c0300c94103804021840910303041c00400082521481c54444052080d0025a40d804219082030150340414a241c0c11940242030500d4002682540d00044c19034005085943d0b503480841000c024007442d0400341c100b9160203600098004002501d50360143e84da120325112242c20a21900d81d2200350141440340101440100001542095240c0d081040140041c00500394000c86900c0d000c0c085500740c0060380b00c02540c000c680102d202d5a4050591010144480041000c0295a0b807003222441148200c00100042c203052190010744003680c8020242c80b181000301c000140540d1f10b01e5010840c034114103000c40c0070301e0b = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 78654624 1250 78653374 78653381
    0xb01090501081f0b0a08060310050103050303040303110d02120f06040c05040b030a0b040218190f03030503060f03071205060109050f010308090a03050607050403050f01111b0111040b040905070201 86
    0x3540165200360065a800b4610051022400038096248a00c614041105a018009400484003130307920505140350200405d407a1107000da1808040c985020700602c04035002104881e4059010300300482e100c20302c1003c100c02407148040118030a44081f60030030b03400302071203005030240f007980e05111420707110380003040b040725003510304d20020a400300b00030410311000030042c551044038240005550a01040804c0a90b880801106016032104900402c1860301a07040c1075602e62040000480300e04140c000c1118a82500001e010b000303002c00064645d9640320b4120310340350800b80540703400c035a480c101c4082071200d001080721240075040010034440d41d58441d00c0c4c821000710902c0c0c20f840c1d1854842e2000c030b601c071101c8260400c41004000c400b0550400c8468000c88941e520580d60b9481c505041d4242404040709002a0341015034219001c2c110000b954030581019141450030b200c00f40d503160040c2103c21180e0b000c0390001c100083e0011544025200b19103007810140304030b03501c004049088 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 78655874 1250 78654624 78654629
    0x30b100905014a0709170106080d030f0209060a05070b09031305010c0303090c0b09151602010e031f1b03090c0306020a020f010e0d170103032109020405040c090b0109 73
    0x204441080c2c2183c40c80c9594180104030401d20380c0743e011480c04184040c1100c0d00303d0700b02001c90602c9404010007880780e80010300d04a035410080008a0902c3c079416214003650441c01d0402d510f450018800d200280e040b20300241c0000c3c0744c107030b42d04065500600305070420113096681d11882400500c030b401c8040111654000200c4d0507250440c01c06c4015941e001a0403001c1c4c04041c0d0345c1d4501000035014840301005042582c403400e44441140c0100980c01d5407402c60010820000c0c0080c07040100001001c60b1002d83c2400d020500f424007002091407d0b513411394050007000402d00b22406004c4580c0708040611613040d4150a00425150a905940c014080201030b80c0d10701d102000829a107601910380303c0b20610503a03907a280f0301c0ca00c0b03a00b501c0d9190801c05007600000c042c007100540011000315410a0301802d807141d90701d9610098074441e100c86844803650000f142c084000781135580a502e420354001c00800c028186420011031181c00c038050410030134940328640b88550302a812aa04 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 78657124 1250 78655874 78655919
    0x26030904020d02070206070b10080f030306040209010219060f0b040506060d1a0a0611070816030f06090b131b05061c0e0307030210060506030106050f0310030b10090501 74
    0xa04560441440000d5129500b00500c5070b0b400d10640005a866000030310589018282d003401c9820300d07a240c441501005d900c8102c2552101b0070040b400540441507a40c0600c0803540142c5440b440c50050b4103190002c3c0d800038200080c03190f40c0040042e0365001e56015001da14003080448040c00c2400100d0744240c80c1c0581c802018040012043c13010380280c41d4202c4100f469104d04007828011600b5a8a2904075401240f08852500f84150017080328100402621004151100c104419048802000d00020703040c015034600d100c06000d030603000301020582c0404404907070314020100b202d0b40707a88e10a00f01c403260b01e00c071440d001b030005410004095900061806141140800701d066035110035080a89056807140c201e44078078030060000c4c011840c000d40150060241c41042502124501c0d00300622904041c001806466031200c02d81e01c0c0c40b01c0d01c2c00060b550b5140c046001032202c8050b03000a00d040e48100800c1213250745030311380e00304075265690103115507600c604681b4012071061141c2d90 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 78658374 1250 78657124 78657127
    0x9060c0b040609080a0906031112040b090304030819110109050c06090301060b030f0405150702210c060108010209040e0c15070212060718080606010801151b0c2603 72
    0x100850340c00c000d100c0c1c01c20310599000a40210690311455550001e89101c400300c1e1040300304000a9815000d12806600b03803003805031920611103000344405001404c0a01746c10011800601c0b8550104200c40203150800000c41c2c0b91550012062014809107281c03100013554454076485a44050241c020302c0e075070240250500c0c0050100340125500903403281da62564071408001505450f000042d8050041c540300c0036414034103820328518150031400080016040c500802016070b601007004038510110801842e0800643e041a132050700840c1c20300c0da000e0245030000514404150f00500244805813400d00c883d2240300300c81a12088000405600602d40c0004521040c04c02001810300700e01c01807080c1141d50701200c0c07261404508440310382c00b14003118200c142d060283e040000040c0381c0d42000300054509440000e01070201031182401d000701d0368010061141c081d5110b0b1f0910042c00c10b881d14040c0c5c06090624003880c01c1c0c8105210380032503d40b1208805440740c00d054000c8181c40065 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 78659624 1250 78658374 78658397
    0x25150206070807050f040f09050f040809010804020105070501140405010e030405010509040c1b030903021905010e0d02010e06070503030117121204030e0406080f0106050603150f0a080109120f0906 86
    0x90b203034008018002400c22030200407040203e03000d9400352000e001c1d80202c1c0d0036044d0420b04c50b8011070b50080e021100f00108541008001b80e000c4040b00c1c405203084c40c00c55400d03100c0e40b0040e200d600810000030040e50030844001c07000c0ca2102d01582c4682e0080c00284103070344107401c10588030321480c003c1c580000d108204040e03a40c1490703000140f100f0460720300072100810b10300b030204400201140403000100740c20010015890300c0541d60714514240c48107484614a070000190584c07003100e121314041e0110700701c80c8040d6800b926030f0040215001c1c1559503104814036101c0e403247d2003405011500032017880004414240090a0f00042c095040c00380e1402070005181003500070001d1046041014031404135203141c07107502612004142100c01014010300065500d03003962402c0e08024001c00c030030310400c400c0c0504001d0b07107690600c0a60714240c84c0c032541c1c80071441209581e0441030702907081101040400c00d51801e0300c01c58a074070341d46183c4403260424080703803082d20074030501002842c2060007 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 78660874 1250 78659624 78659627
    0xe041a03060709061403100801110a020705010e01080118090206030106020f0712030507030503040c091505040f1103010909050c04151e0b1c1803050915090d0602030c0c2515020607 79
    0x319044409020a687d4941e5a00c1301da5095508400b10750442042c040342044640f03030108082c6020b0107003402e011009000403000200780f5041446000c2e440106c0d404180c02038000e5501034080340380c01030a429500d60312100c0280d6126104d02003400a44100e01300000c0d0003031100c06050741c05500d0b40d07076186000a80d0b1000c407001d400c050025036000681c44e000191002c1e141c4518040201010982422070749010308100031181409140b030030f018200015580700200080407a030640340d0178000059020100e0802d140b034200e4200940ea00320785814400d070840000c6002840072945110032581c80c12803030b8084200d00620610a5800c6040188030701240c4445a001c44001c598240c040003901b5814013a80400040f02444150003192000460134890705060700c1801324099000e9103c1e01e0841100003081d201d000c231130380c040c20079640800400c03640034260080781c241800000480b4028a82142ea22a448070350341c0c10145125507000002480e4007107603038074900914140c0c014002a5440050 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 78662124 1250 78660874 78660877
    0x204081b1306030b06040507030203060108072a061d070312030c26010612061211042903100b0906041509020c070519050d080a0e041a030607090614 65
    0x11090341c0045007008103440218544a00b40045001e0280340a5600b0720a040c0801c031440900721a0406004008001060b604144030310341003101c40ca0a42e50a51800321041042c0510a003101d01d9a05c100c0d80050500000b600000c4003000400c4030b05410390031f031000f000d0742c030308813444010900c0c0a00041640b405000360b1200c40c40c411a030502d08902d10745101c81381800b4045a417070100701c1e01c1110061106943c080c00c00580400c0c000740800c003003030030020422485c400e040c41c01050620400350350200b030340303503904801d580f00c2c0c5006c410340342800071164803460203a0304140c00d4000c1c03251036441400710a09000d0044d50900260507141c2603118142404060008003000c6c05550504180028894102e8401008070340284001b6051060500c000c00c0b06d041c400e00d002a490203008041804186c0c2c1d400718a040e03107a800061a139071420b441005035a009040c0740c203aa071181c5081030610514080349040051410200c083d2145552646015100741c4070900407035000500c0342d459040082e501e0350 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 78663374 1250 78662124 78662173
    0x71a0309010603020a03150b01020706140f0f0403200103050727032a05030303040c17070504020a0804121d0105160602191211030606030601050c010608030307090504020408 76
    0x200710b80d51607070003146102030706500c02c44003d00c118055800c5030a40340700d0583c412100b40b0141aa4510300711008041c1c00c05100c804108050024840000b810f01d8030445101c0c144070214071307803210341da401d01c0c54280e009045d84404928211002c10910362013441641e02c107503916124002041800d02074542003221131240d11329a04504440400860840c2c8071000150340314406440a100c0f13400300d003140c8100207a000714040d034070a00602000030031104250041c1c41140192001145d85600f40705d2a1440e2640000c2e0071610000d919400c441d030003036015216034041c00c00390402030300c0f4103002c540c071010316082c401c0700f4000034050b24060340c8540000c1030807084000c00d081075902c841c0c9a04040342e000600720030401180c80403040705250401c420080c402114081000010000c00a082040c40000d000a220703410000005405030300960a444400c22a00020000561280c0007581d80340c1c0103440d81030104808070000219460b01d80201ca06840d074901c050003401c0800942001e0004104 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 78664624 1250 78663374 78663391
    0x3010f1503092307060c020904020d240207030f0c030e01030c0203070215040905090d05070209180f0105010608060a0f0b130305030c01060e060a150c05031c060305010c02071a03 78
    0xa0742d140c408104221000c10541070024000034030480f03209086407038068554400f509210520b4213160241c2c1d501d080041e84240c050b28816030f10707035242c40c000b40c0881005401b500f040c1c1c96542004090265a070282900c0c45c030036280e0100160952400307480c03074801c0150040c0080c0c81d40512015651003600034021400d1a801106d0800c0301d280d00052850061181c0f07800700010128080144190038007a05420140c03080203800d040d00112002030191207913903070290040c0c030003001041e502844511050045a0a1420303a0f5029410000c480d0280100b071103043c0021f200440030810900c0e04d00e07264000c0303444024140e100140b41550400c0c1030b804c20004544281200c900c00804141c007440101801e11800000040d0341d03061500b20703030030701d040500306034081e200500d0b0900108001c11030001080d00c850601c4540b050403464618918841c414141d0140341c810038150403040d07050717002002501c2c1700b01c0081c00040c100c16022661f602144c495002d2004440c12111052084d000044d0f401c903824 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 78665874 1250 78664624 78664631
    0x3031906140120100b03010b040917031e040503031b030127061a030a1a0609061b0d03140906040c0b0f0702190519030206030a020c0703050d020d08090303010f1503 72
    0x80f00c1880c2001050b181d910140c40e10b4030b000d00786502d002e2003604100801211f0400044049460341d0004144a40c6004603500000009c603645204005142d0306036140002e10150074500341c0307051500c940040d2008044500001c08c1d1031642d60005e0f00f52816213814034130819070781c0c1c03a000114a001c1089062554820780d08d5801144482400c528a00044030008655036a0b0804038007003011600030500050821020174101005a43c030303082180c2d840c2034103d034041d45558600d00c003041e046841b104092410310602c0d107003610391901504907402119407110406510342da288180768a0f0b840c122002482103450120602490180801411800c09104c001c2e504101844c0d02040c500388a00c007100b80c502010039410002d91070700c0c0340e01d070212807180d1402c96903c82c07031540424850f010151803070f0101e076000f01d0b1400c002403003086044002c603001002c03288065032844020f9210b04619240d05c00003038100001500d038540000480c0d0480b078002e030010214901d8090000c2005205003005000c1644 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 78667124 1250 78665874 78665927
    0x70b0f0c18120307050a03110601030812040203151014010e181305030a030515030d020703030f030905060a020309010506010504080d050703200706090609080a0f0615030302030319061401 82
    0x82c00c0001d4810b051042006001c0d1501c1401d01504000e07a0344a00b01042d88010010701c0002c00320020b80b40d03c0c141d104d20228081e2541d100007401e00d0300349182e108880349540c0400c40411201700c0084204d0300380691044500d5600360044a0000012200b9500880c24402940601c82071107891a0301448580c1c02c803407410403c0c0c0c0c4c0e250840e071014110500003030311141400300110008800c1400142c0460082090169042c0003079141c004070311019040c010070b0001e000c40740e4040e800c01c0421a41c00307026079240b881c0900c4840b00075041903482c2a80340d8645400614254065402c94007500c0180c0000c2150003080345d400c45176035000c2807044082105140904011000d021569000c0d8210440544480c2c0c0c249400144000d10aa00100401c160f12000b00030880011840305400c940012501d0b030f40d0703087d80c200308001c1d080b510509641c0f0000c2c2074001060544c00310155004803094920030207071000b2590b403d4240c0d0064005c4c40a0784070203035090f1400e5805031000070380040e800d1551030680030 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 78668374 1250 78667124 78667159
    0x101b020406050d05030d1805150603100204030503071104060b0304291501020d03050c1b01110f03040b0f0705030a0b03071e03060f050c0717040803030705070b0f0c18 73
    0x1d4090f00225615400803803c042401d109010701000750030081001aa0010251203003603884a40341155129502c1000114211391010700c00301d6242004014195900c50307623440c0aa43d81e038072102017503c01e047e1103c20300005180900800049a8a03030082c6429911103841d04184502ca000ea0030700741c0c0d80300410f8180503a40710082a0f01c1081c841c4014240e9444040001e4103000a0b01404810940380604108054151805031980d01d42c0d1440001600c1403003001300f60040041301a8049004004142d1140a401401c0214031031403081d245040c9540741c40c0002c0960040a641d0240072071000e00009002c0b01075a4840c41c1c0101d0010215484580e8442e2400e801b04001481c4030324141081c80144180300450140c0781d118030003201c00300306901c1c00790044455070040f03d800030300c904208a10000040107000564002d4103000b025203035241422200502241d1110304101c440800c4503000a402d110b9121803a8426400c3e10001c500c1c00800e014002d80110300800300550103040c21007865041d0 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 78669624 1250 78668374 78668389
    0x30c0311190b0a0506030604121d060d05060a0801020c0a110d0204060e070212070b060d05100f32150a03050703050606030c0d030e01080a0608010e1b101b02040605 72
    0xc90089480b00200d007829940902540c400401c3c803030096002d00d05201c0018204a030170b80740c45d0814a0507824000c2150302d0850fa152451010725405500490b400d0101e0020b0392046004480c201c0e85100200c0d95031040b20b090307020305001641a5007105c02030b0400f04080301040d01e104c91000307054802010080d80000c003160030342d801c403140082690082142c502d03010008164500c0c501d9280764144041070351524014000244041e0084901102d0242081010810803c2000c1000000e104480d0048a40310041c04d90303059801d000300e20b05000c04c12001640107541d1000292543d515001d036206002d4044103100503e440e600722400c00c1001000c12024803a0601451140c4081c009604104042500c1c03c078110340058450764502030608002500f007404010403901c28240316074266241c5074520300030420b5500c840595400e22240040d402e04c007040c000c545031800b0700350244e0981000144014190444000c00c00f155101c80890103000e88001c230748151a1004002040e11070700c850204910703 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 78670874 1250 78669624 78669673
    0x1150e060a0f080106170a0902030a0206070605040507091413020a050607050102041a0301050303160201020a0c030b0a1406030307060b03070f0b0408010507080601140304021207061101050f0103030c0311 89
    0x2440b0804115580d40c0c403101181c01481c161a25114504840c0c0100e800400090b20481076240d6411401c41103480c2400b090710380c190000d10340c9880d500349050000203008100c908480301d0060b0000400c948200d071044e111007941c02800c41009950b50820902e804035040800d9900031001c070000a056030724840108007551040e0000741c8c6440c5420540c038020020700030880c440c2c420a20040c426510000306403860407490703141083c500041800140c0c1010314135400a01091005c00e004000d0280b4280c20f40e01503500c020007001001c01c50b2841d90420b120540e00c09515400401014020840c82d400200790f2440060a4412035917079141d070350400f42c07040c3c0e10041c041c01c0d003c42c04016a803001e204060340b042880c20202048c0c40d11800003400c5c41414503058809840210100782036480d490300c9138081407100001c8a40780c40c1c403844080c102100c0785003a01e66560801000030030742d490b4080180d04070b0b54107132034100c5418940d980c203807082c00c81c441100140e442038260400f40c1e203819014001c075 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 78672124 1250 78670874 78670877
    0x608060f030f15100503030f13050a030b0118140c090103060902040602010b0a0e06031005040f12080919050601050105030403020f010504150e0d1709010204050405090606040e0703050601150e060a 86
    0x49503194000035104a50004c00300b0b02c000c20103039803c0007591400302c200d0700e501c4025003030740d540c0d424034043d010200d80c0c0342c0d0401508001c0140020080048201103035060b950102a03a000c895a1000c2c1081510880c409150030149600b012407034055404010388940003050501141954840340341a00b02d070010f912180050707444287c40c0102d414614240800303000c0f0740c1c1c10300002c2c1ca020300119aaa107000e90480646903501d200103001d01050103a51640350350b20dc00701181c04200c00c00c00400e10170040d190300007203009481c280d1804d00b40258401c1030807540706005d080030381e00c0c01e4019101900001c00c02d50540c045c06208001c2c5172020321400d4400d6115010060000428100e0369084880c94240380c98580e10459585505a0304030515031030b102e102200c001402d03581c0c480301740d002e4062036006039001b600b00400e00281034000320300705100780029101003107607035040d44000d65584854440030380b40f50131000050050a00018001e00c0074850f9040c410000044500170501603409000ca200 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 78673374 1250 78672124 78672133
    0x90406060e010506070c06050a0c0f0f03090803040509010905180a0c03051e060a1a03071827030305040507030b07020f100606050a03020903010908030405070e0601020d090608060f030f 81
    0x1c044071a19400d10702404059901a042002c165104c0d00180d00070f003e10000d200c000f00350007000c2e910810308c0c00e0704540e12070a01340307014100b071510351070520350140214042030b0480804a1600000010f450488100501002080c1d103030040c104005c0c0000391541c22880043c1c0c4d51511000003c0080b64803081c4981c02c9443c1031859400d000d81081c10218600ea994103040c01100000240003a485e50018403a040c0003c010300c400f01240022a610001150540501c060000b01d144203901e40d40a0070703640d04020722200c107607050301080001c054806984154181c00c2d507040400e10950100e94007901c58412a1040d40c2c0b03d0312038800141e011225080140d216602a04010605022030341c4409039070541840140c0c14400060b040c0e0040003080010540e000c501a0125a805d4104441e055040504940d4909090500d40d031140058010100d80e40b2894001c500399502c0000c030400c82440e0b5903620106142044411031303400d20068500341c2d1005c0442003c2c00300341d90034008140a104444000d0 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 78674624 1250 78673374 78673379
    0xa030806190806070f080f071101061707030501060b0a210e06040803150a0503030f0f090d03050c16120b040501090b2a070c06050a02070308040306060608011202130e0c09040606 78
    0x5010308800181c58003040346c0c40040c4403c00c042ca0101c0d0317801c4449824003503070201501c8100760047c45164000202c0480503044044120004540300c030940b401b4000a101c2c03151140340c0040c5030f00c100782e034a80010311b5103401140ca07901c008404107041100310030081000d00d00414031034500502a41e0035211b02000009100e20700107603441c6c03180b1009090706c87e030b5480e174540070011b501c3e40502600c500e0141800202100b043c0690401c448444400800d07041c5c06034520f040040464110003500c01851040c40490344001c60802019001c941801d010890300c410150b4442c0380d20b100140084070159203483d120720010f45d95401c8288542422140030103088070484000001e540110301684202c0c2d800c00c004e40200c0c420408034001d94280d401e2283d030300c1510300f500b245000300d664000f410460340820080700300009a000301003113803403950381c5040c583d8032b03030f035100d903a0340c1d20290b00039841840340f801034030103051a030400b0b2080c0c1c2e40041910560741040d070100300c540300101e40446109944030800d = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 78675874 1250 78674624 78674627
    0x51308040609140927101e060608010b0906090a030807060f0615051209070302060304030518041a090a0f09060b030d0e0303030106140412051605030c030a03080619080607 75
    0x150703c3d6201088852100300d0800050044a010019085800b011640c10880110000c100254059102040c8041042280d1201c01e401652440e203511542c00303041c44000150170344286c0150741a201c0341860307d03240010450401c22258809a80c041d0040c0c002140080480c8403080603051141c0900c6020136030782803494243c001c03500e860b04400080400c04c242444941e501c24143c0f0300c202c0341002e11103650b883d07044590f8540002944000e5010390000100402c0543c82805081c034020024203681d1800b800b44100016070350342095070007651035291410b041e10f150140c41f6036000780700c0960014000c16402480700a4460901c806d0301e080e82c407003200500030700341040030314084030345441e0503d0500182d400081e181d110601c1440104000c070703020780042e10004012200244403802001ca402401841c00684400e01d81200c3c40071000c6841000407642400f00380030a25040c0100544a54078450782c0c2a00d004102912003604a0207250869041d5a004000080a00704881c014092490003040 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 78677124 1250 78675874 78675899
    0x30c090203070f111009050c0d080c01051e060409140f030a0207090624050903010212040b06090403091a1303140d140904090206070605010303030b0a08031309051308040609 76
    0x15440100320414009004c00c44020030011000c035a44840032441480364248145499010200e25612126403000e03601044101001090b0f800f1584000303100d0f907a1031000b0801b61940c3c3c1407003410a407201ca000184903150560090720002c1c4590740b00407054918403802854a5410141030603650b200040340c640c181c0d01044601c004244070b03a005e001250405860200d04841d400c030545046040100148549020700c1c02da600c070b200044c00071034803401d058103d400c4808058030300b52849118030000c00d032036043c480395991180c0d4044e10303424402ca00c0c2070607a45040d2600704c0071049400c02444408181e0041d004004011401015141c59221058000c0c1e41441003c60b180d40a00c903e802341c408046400d03c095454000048074009040703a800d001181e068414003800401d541d2805001004058059020741c080c1c40301030301c12003038581e166072a00f962849180c6e440c084c0d490580398200a01c10b055081107500040c6810181410203907a40d69a4164020b07800100205034802c43c01c1c03107050040d04 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 78678374 1250 78677124 78677147
    0x90609020c0a1101020f06130b010b07051b0103060803040e0f060d05281a010603050c120a1503020904060605030c18130816060605090702060403091806030c09020307 73
    0x2404600d03001038035049503615410744400900400d5070b942203d8441c0e00921200901c04201005d40340e10380b070a800c07504072505031000111100710100d40003058414128060700e20140d841030003003d0f05520f0010308003d041186240e181010b88400c808660081c052001d000140703d400380540b00707410120014001c2d5603009200754040e01a5141c0007021410004210780d0651841580702c40242e011240700810003100c94022380030303003041440c44041c1c07040e103001c9a048882550723041045884580800403d441061180891600204081500034506601107540e03442d00c0e000507501180e580d40400d0080e03000303c405030f810701ea03a600d081000b800c045c08969070980b400c131136100f07444080000c0b640001002600c00400c864048070548104a030074804c907200d048041491042c111042d25010003e424140035850042c150325010070a52400098018050f56141d200c220540d410311115069025103901d000d9081c0e03450780f00c004080307078007070035046d0281402910150746c2e80350203070002d06000c2840307 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 78679624 1250 78678374 78678389
    0xd110309100e0d030c18080c03060105030d05270d03050d050105010903030504091505040e010e1608030a0f180905041208010303022a03030c1e0303070e09130f0c0906 73
    0x9501402440c000300340c5244260f294200000c450240391404c94034099440c1c245c5035008545840814940d60014114501c2e4100710212440f030381e26141403684800c014515400031910034003400c44004060502c03070b035001d42052204c0c50320848090002d002c0707070780003507040e00403a0b4000740038082000a030040030301404c401c0c20700c040b40c1441d60780c00500500c81d602c0b80c00003440d17a90403140c0131440000b4600d001800010024070444940e11241802040f91910380d014521482034505001480424160304a0301101c1c051402c1400c0400d0944500324034040ca8820001d101503030a00e0401207164083c05030035000b80015080c41c040c41e08825948004103d41d040c0459000100300103940040d441c02000f4059900c514009a9000014519528203200c9941400301090700b4a520000284030f180305a9084400d1a02c00904250b09489110607101c40001646130707486900c00e0704007021119000761150740900920080340d2075004a5084064048410f2100c6000c00c0102c03803650300801c005042d51 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 78680874 1250 78679624 78679631
    0x3030414100902101b172104020604090e1006090516050c1e0309060301081006470705060601180e13081b0a050d030209060a0e04020d11030910 63
    0x203600003c5502c0c013000d10f000c0c10402140e040b91090403442205400b00d6621046003e6520800d844441300c03030300055003620300f24402032a01d0003c0405c0d445582e000b0782e009003d1a14180c249040a40545545907460840d0f1203016080740d6152001e1142d070300184043d0070001840d0502600100d110b1500d05410300410005000c007c03203040f00480c003c1c0910b40301c1000c0030040c100454183c0e013140911b1400c41da019001100005440c4c102048801c05521f400c44100400c3c0c0d02d54102c0e00701c841c440d4166115065489034644d80b010700b440c6100041c8090743e01c0309080e640b6000c2030358002e9800754608a500b1380114091010702e50700400b981c00e228800c82ca4002500381007010301c580303480d00100b1901c00f85803031228140600007444111141c02c0e03019000042c0040c04c040c00036903030302d45070081146c852044045c40c0f0211442442690036049000f80f441d40340014a8404555040c401040304c2e40c40343e800c101891441c0c80a00c039064101030001012500e81c901605114100f80c40c1100381300b0400d04 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 78682124 1250 78680874 78680891
    0x1b1f060b0909090705031501050f010807021c020102070818040c14070f081201060801060908070f06030e0c040c090501080c03040210050a1206060c12140d0218030303041410 76
    0x40d0380036a80054000d4032440b07202e03961141c0c518a8561140d20840d058080c0c942c8244100d0781d4401074a06894003683c9065800360b0101c011521504112203100c0140c01400c82044070000d01c5c1642843c3c2c0c01c403403001500b002086e4032091403650184d504428043d0310160048107604081c018030003458004c0c00e107854409000c4007803280300d11483c8001410042001054010000302c207040e103d2800115990f1045507854680c040c018500a00a00d0f01007502d01000041d4900000f8150080c0d0b42e0703030701001e05030324500103059010309110a1100c05c50b02400211000d02c0d141c511a04400e09140d58400c840286440005007213004060310040351002c2c10810070016803606003003240540d0a40c40e20750780d10f20404108582240380000c114804034206800002c1c040d50041c03504003101e005410f02900c442038800140c4600702c0c0007441780350040302400340e0049a52540d014200031842c2d040d49400813030fa0b03c000a070860344101e404603881c691280081c00341c400304008042d200c001c000c04c05c001500 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 78683374 1250 78682124 78682139
    0x30b07030e0c010c020402120903070506090a0507060f020a05100515010e09010303050901090806010b1806090a05061303050f0d02011b020307020603060d061b080a20030c1b1f06 78
    0x50b2050601030215800c80071900c1e1a8116003d40700982d02c01c0c0080c1c102500f0300c6031030790301200301508e1520400004c07410701000401c420320704980c8880203282052401000381c80b0b10010a03916000c0d030186550b0b035000b04d8424440340030740d648400c400080d00d2400101a541030401901140d0410462800200707168584090003415a41c050801da0b480c0c2c50030400480e040f000c0d6411440c0b840c01070340d000140206e03509026001030542c0032a01c1c00c10002d08014050103005808410341d01281c081410000d40c10581e004008085100d074117041900d469407503091901400341e5410f0b10951060f10030003086982131241c40c0c000e26022294892007a8001c1c1c00950342d0040318006841220b0010100d00c007a039800b0034102c202d690100c0140000f600f1120300d80aa08600121715010615180010306001c0151041080c105900500c0740c905001e985820402c541005004001440c001c0240354404001c0c0410045400800c070001c04c01d60030001e07854589180d00e55103e4902c1c9082410500a42 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 78684624 1250 78683374 78683383
    0xf05120a05060d12030c0e010302030f040b090c1915022407180306020d060f06020d0c060e060129090f06090a090f02040302040b1e060a0e0a060306030b07030e 70
    0x280040402107216203801d80069030201d46040000c10408152001c001c01c1078042e04482410203007621030901603814000158140e100c02c0722020510aa0b2500090004180c1e440e6075800c21284001c03034084000c041c0100f107030342c82c01103a0300d03036141d41e000010807604001c00301d040250300080c800340650214042c443c1d500107404d0131204118650640c00540e5035441041c000d42000f0724400c544245944c0c9007085002940041c5503801c00e6800e0100c082541414158028111001da9004101d020a6444110303480740041204441c0c03961100c0ba031240c0b014080001c075000c0d0800039404c0300110620a844114200b10f000d10010015080c1301e40c0101e075890b40d603010b10340c0f401038400c02d07941c1d171280700001d500c84110f400507100c1e14903001c19102030310540d50103001924802d4034100402d000000c100b00211030081100705400120100500403800c03d04040c2c045490242010f000e00c1400302e000607501d031500c2d04030b1000a0359550b410000d200c0c0c040c0034580c118003d424200b10b20040d00190390b48a = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 78685874 1250 78684624 78684631
    0x60f021b03210c0702061305100207032105090603041a100302030a030e0121060f0501030b0f0f120601090c1b05071a090303070507030b010605120118020702040c030902010f0512 78
    0x960541c0000a07040760000c4101c0b184c855006003120b955482c1d250710110844444d0245034007a911210707128600500002d5010281e9420464203c01d204218a07200076001c0100070320000c011090164030302ca42c43d02e030055405140b050380a00750a1900c3d080310b004d807031001400705903405020841000541c0f0085038910390703030f0307054544541c81d900c0707007030042c0d86288500c140b050245d0002c642140c86424a540040c0544007448855203801e07946800450036940b0341c00c41150b118001c90400c2201d450005120381d11140b02400c204540e1034055041804c0050980c4505c185a803035481090038540c0c89044180c00303c0b0030701c0364200ba0b0f1265441d201e6480c2d050b405403e861503103020b03084098030411000c0d9a440781009044947c0c855091a0003511540180700885001c0d04d448004107480d80079900750b80074001d030307890854456031030700350341400c035202c0c2d44a00c00c21682c2c00c001d03950150305c90340500300008072591004a0141924130004100100394581e0300204201803150304200005091020740 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 78687124 1250 78685874 78685927
    0x102180d0c030611190801030308090106030b01050409020a030803130b1b03040219080a1407060807050304060b0a1203031506050a02030a080402040e0303040516060201090804050904050703060f021b03 88
    0x294004509013420181c4510748618807001591118aa40160710051047c1602c0c40b0f65600b51643d203078001401d090710200d0000806280301400107010f10f081c5640b083d1003c50001340542c00f2550b581e200d0000341d5006881c9401010410301c2c0c03d4041c032010346035454020f00f000400f0641040d00484e0300b0704600024000902c103e40241d003511103902040b010002510012064400f07035001460b0490410300e14084003151030145410018043e4024402188980000d4941e83c5c590b0791035645c1c03d1300400d401080540e102d2410800490510148610007251038442e484c0000d1005102d801e00c0c2684080d03910a800b00207080001e03080d81c030307404400daa00003809805c00e0111500c40b03100040160803540758000311380c4001304c100400c0c40000505250b4458840625620264540380228241c81981d4005054030204110400050a204a0656016008005507020705880751b03110b1003611911010030229980115122140c03180f048240b02d0762401000003545840c00c1010380c01c09214005040d002e = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 78688374 1250 78687124 78687131
    0x90f0b0711040e0102030c0c011a0916021203070c02130b060d02070f170901080a0b0d0305030c090a090c0e0307050f040b031906090b0f1018020408010207050102180d0c0306 76
    0xc20352601c3c1c002501407800c460080d516440c0c4400000f00030f81003140c0721841c1350f0800882c0c20100310030364044490001c000d00f0500c640d60f0399001c4400301c40740c2c00c04074804510404810b855400e402902a42c000d04003591030844501c4c080c0100843c05102c04080e0070b070300d4640035400840b5a10f9004803840c41c41360300c00140c0c451400f401d100c81f40400b01c42014101d0044801040b040c400c14400810f56034500740c9410791283c50b008640720452f02e40c0080d0613044030080e41c100c0c010034000c40145501060080c00316151620a001040001e0110341c020074403a6124030000c500103800000c02c600c0a50150000c048440c589000103600e28106c0d41224050f41d900c6200200945061241c1130f4400c07400d054400f40600036180072801005540d0080d500e50b0380d6140450122108005010300402030b42d4050b401c000c0c2400d8512a00c048812130f03014019a08100015841e8405e00203404124090000143c8800300c00381d444119039a40741d101e501c00c1070901c007141c0002c0ca00861480c140ca80190000 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 78689624 1250 78688374 78688403
    0x914160c0602040e040c080706050304110a12030c0c06050f040515040803030708060a0f05010206070f200303040b0105060406091403070e0901090302010614061605070b0f0307090f0b07 81
    0x3514598000080604410b000140101315528140116400780748a00e1400b04c901e40e032040102c1d11038000b4018040040c9003000800d001ca4419400096010b20040c006c091243d541c0344480201002c4900032030125010254803400c1c014054041001000d035820200d103071520032560042c40d8807490151500c1541c900301013415981c1e01205a030080e005082c1120790702d00781510042c0400d00c04480c868410324500313a001c61100c115000d000c08444068009000302d883c1d100042e1038000d0368015030001c2294950310182c00e94001c0402e10354091202000d180e4a00f040e00707000f031101e18140c20190040d002000b0401205500c0050b080480c1c0b84008440c1c41d20000200081c00c19845034003000b050442002880f00742881940316a00c1148660020407036143e80f05c070708005816505070f13590390244040c400d01150742c0040c1c0700c0b08842403141c802d0351f404980312070703441029404c2000000300f030709808420070031010740006002000e4800c0c448004289460003040340024401c145006140748000a0107 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 78690874 1250 78689624 78689627
    0x1104081b06180d050111130f0b18120a150902011d0312030a1e1b0f090513180809190302060d0f0207050a030201020309010b01030203100605030c0c1c09091416 70
    0x10b0311b0000140c0b05140d03a00c1507001ca40c1e6a2141060241c0401c0c807100740e800095242c0c1a00c211880301c2180e040c854018102d400404c03041d520300714890740060040b064041d0001d140e80840103c403242808000a10710b171203000041c000d01c0000030440e00d24110b050040c40d00d6034002404c030101101100d06507500d03541e03550b0283c00f610505c1400f0484d2a0b00118004050300e182c1c00018080801403c20810318a201300220b802c0d10214508401081601178280924209a001060041100b030008154018401e501002c104403101c003d44c0d44035400704489500d850f10410341808140e0b0b00c00024009429034001950a1081b4840001010b81d1072241c00f003048059015100340b41c0e00b0006440c52490320f8203010b4040c2d84201c403800130039482c10500d014250b0007842034074042ca444001e1040b085040000c00d0b581c1d81d20140601120b402d082c0724888a1080401100740310840c2807007a40141611001c014080034200d80103504400d0500121164045c040703d01d0941c852490784940d0980201404e0 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 78692124 1250 78690874 78690881
    0x16080615120f010515090721181e05120c0d0e010306051003050108010e0d02120a0203071709040501050904030f2a0506180a03120b041104081b06180d0501 68
    0xba5030101c0d42001c0030402c20001080007001c0184040d560000b0546e81c8400c00c4a0984403a4210142440503206803140210503502441c60020301d0011340700030310410b0b207940100780c0f00d5a868030f041861241403803042000921038840c249400c601c0250400844500c055102c0416502070410003d4007403855515038400e4014800030b08001d00501100014000d004018000900480c10340c0d42c01c20340c00c40c2c104600051081d080403d26400b80001403052050001d01da03108442c401c0851000703002500104e0f809007038400716041e8100c81030380e8541f000414041070b240160302c0244104110b1040002090b00301d80310041044070391800e80309240020b20040c0c1064103a000e90417803c050558680b04000002500d140600750401185441d25070f540d1140d0b546002c40c4c00014005501a081070086880715040240d01600081001ca206601080c0c180195082540044c509a029454241c00500890011000c0034019103006181c480038910340312486243c107070340c2c5024032038100100303040c42020350 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 78693374 1250 78692124 78692143
    0x60b03010b1e0304060c090e0903090d0c050a120303060603020412060513080313030311090a060f030b04090308040308071e0f030207060203010e0609010608070f030b060c0f1608061512 81
    0x210b40343d0b22400d042c2060001052183c80900114000c10070108182d044580482c1c441e440741e40003907240c03410700f00a200c0809140a400c0b036091000000c0440c05907209100c140190401ca103003003409070181d040040940e080c07507104600780b41c03040000340000740c26501c44040b070b01e8200c000170565807201800682406a069400f4240450210a205040000321024240b00740203507014003030f001e051030f00b001151040b000c40b150301c00902242042420f00500d9205c0450b2a10700b00010034450f800082425544010412000222070004000406421038030207904840d241c80d250f58041c0b00d8402001140f035081c10f220302807069a54001c911036110b50106e0f61a141d2018056449580d2041e480410000644460740b141545900104c0c0c4c140c0310383c03011440345007140d072030107100000c0e51000d40040800340d000940100381089542d080440400803d010000e6890040c0316a60700200b4201148130580c0106000740c10440503c00c2c1c1c100d9a12400d60110400c030f41c0010300c102c4801e00c8a10f062041d6 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 78694624 1250 78693374 78693427
    0x2100c0e0a0f080115050904020405100b0c0a0303141302010302030903070f081b0303071205060a05040207050607020706030c0819271a0601021b061b031309060b03010b 74
    0x840442c0c0c10a07140e0345001262507480003030040c03075800c6488101c025000e0007034981001d420000100940341a41286800005000810039095265429084a40d016409200b029400724001008256040c400c03054405070100141089051100140040b01c2c0c002d0b8000e030401d1b801002003458040d051044a502691042242e603080d000e41c0b401481c280c20004254800300981802c0c0d03805110040100da10890f5a80c0d9105200340c03006a085004100c06440c103500164000400b1038540c86a1004000440c000d200501c100d10341084020301d80480c40e00b02600300350800c0c2c280f01100b0303040b4410300c1e00039854140c1c1220154140d040f07140201035008400ca02000b4070a454a0380d020003107a01820035000e581e10311101c0d11404212042e1400075a142c500582c0941600444000707039031141410a030300100410f2070041d00107009200f0685204010708941c00010340300900e00707290001b550052101c0c15040c00034620704101003c0c10b000c144144070217450000344890104048000a86000551 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 78695874 1250 78694624 78694639
    0x30c0201110f0f0a1b0b04030b070c0209070201051501020f15060310020a17220807050a14010605090609040809060a020319080420061812060f040314030702100c0e 72
    0x10b0b8643e240d44070425002910061040c00707034580418500c00c00007080e03940140d4083d1034070b45142d071442e1003600010300e030800f0018030340c9032035006070703a15400c907030181400b940042440c0c2440100701d00e680048000407810340d4014005200c0582c004076440c103500742d620000010555901011905021500b50f005400c6ca02c0001e00140050700100081c034002090b50020702c056840c0035490409550507082d00b1101c00501002400042014004104070703481981031300c80c030440d41e607100000c00041d000c8108042e5120035040c800380c01c1809046034403130f10454a1052604054a0b040000cbc8103845005000c1e11000400390340c80340c003c0049030140e4148521894240c8100400100034075003d0300c00710b81c00c0c0c00704655042144021100c400010800420f101d01c0e000614100000ca4445801c49941010710300e25605606030062210f01d10982924821805070314060ad0010034040c400b02508038500001e009102d00d01c0c3e8001a81005501046400900703900044001d07518103d007528801da11201 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 78697124 1250 78695874 78695893
    0x70513050d0803160903030203070b0406020702150301060f020a02100e03191a0901090b0a051f0902030105120601030c12080706150f05040605031b0d02090a020a0e0a03030c0201110f 80
    0xe202000f5449000c603107104a80d8254128001c50b9180724500c0058010780c0240f0070240481e0608900e6608140f08440040c0743c00c04650214030300310310340114600000c0c070220040040d039401c14000c2c0d204906510180c0200c141c59800510030307001c03488800d401c0210f040280c1c0c10540b42046804480701c0e41d2040c00311451010307c0c03c60042541c0c085440031401c85680460b501040501885e9007560b800040e44040c1d42d07441c1ca024004002c020030b0744551090100040011107958100310001e84681c034405a030b69030400d400e01c407030360600035002081c0d9880180104003184ca242c900c142650625040098108828249100039014403080500041d280280070340d10701007618030340f070200e03003902201d08481641d910070441110014401d050701901324000d540e0340c0440340103030361140c00d000401070115642c0179004070b00c5105084440380140f41d8001181217085401c000c442d4170700d01007210980101070660b0707001004804400c0c03009040c400800100d400020080c001c040b80d408681044400000 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 78698374 1250 78697124 78697133
    0x102010b03030c0a0524040b0703110406051e0301030b040618080d0b150406090509092e05061507110a0510020c04050a020a05030c0c011107030306140315070513050d 73
    0xc0f4010480b15841001b0031070005d2000d0044110b1901000a0308100603525511840600c807002801c0b8420035a070b500411400441d03000180024003425034030162290908001c042e01c2c22000018419900c0c01031004000140c0034203111944540d206401003101001c08900da451203e81030001810380070302240c03010780b01150b030f442040c4d0003004580000d0a000a0900340b401c034881c03402a5800110f030900140118104155a142c001c0c40100c00c50b02e1514181c003500c640c460001c10482011030300c8008030b403510130b003c1c0582a0424003c44601100076180ca21204240c03180c10070091480c0c42d10300c9150b01555802c01c140b0000d10010b031058890402c000030083d140e4060070003051040d450b0038045071541260340b082c2d41c884403080c3c840a2568a407186110400d81210350170b60360355900e0316540c008100b204c2014003252403098402050f260700b4004a1600202551505806a070180039a50a00300700f200400390030411505003180da650b80a82100601c0c0141d400403a000f6410f81300070001c11 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 78699624 1250 78698374 78698383
    0x504060531061409071d01110c040e01020c061605180402070b10090e0102040807140a030507060c02150306031b0d050a15060509150112020c1906060602030906070803060102010b03030c 81
    0x9002c40b0544405d5a4603d003c1d52100303102c4403842e104c030000802e039000d07a50003142c136210600601e50840d03818440d41c0d00041d0545003d030102e80950f940100b5010400392040104a41003c000410502c03020344040c401000e0740200e107110442034a4031100303502142c4466044601035034000c42080c5240c03900d01c0311401d0605080c800c8445440c903000071440a4032040c420345050700c0447c1e000c0d040803440d1024241d9552102560168407144180000000030400c0201100400013515000b01c0300d07015004101c00e00c420750a160900d032000308100000c95a0200c0c1005039401c540c100501c40300110720105d103c201400da001002c038460161640b0a01411402c1e03031315040c448150500c00710342c54009100d000501510043c03190030500600820390742c002d202600081c10303c0300c4014108020070801504d003905a141d60040c40d9045010039045c0041170180343c01401c0f0a0000307503d85400500840c40314441c01c0301c09407820718007001081b0f2681c401e401c80e411940d0b0080031a5110420101c54948a = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 78700874 1250 78699624 78699659
    0x90801020c060f0a060302060f07020315010905100f030809040e01060f0305010518010b01050304150906110a0f030204081009020f0402040e0a0e010c051c0b0910030309050406053106 80
    0x280214400000d02c844c04500943c01501d44c003400d007074100181000980303050f402c01d00c0d040380c1c10b0080721144804000000c6e03a41d4000c1000513030100340d0b4103081e03104107802d00182d001b0300c170040500c6200b4004100f0301003c4400e400c40c1070300e00107001540950485e0041060f0b42204501074621480041400015004140241c0300c01614604403042c0c048203a003201d101180850201d030090000401165150010368844109100042210140c940e582c1044610030b00b074011104501042d00310445621140103829080c00d81000c40c42d1500381031519658101c800080001d0300c0c0c03909400000c40d1602c031081001660054406e649907902c0714500c1d50346090131122011214078258194a000e00c05010f4151104070035190145031401342e1561810215000c0c44020b10300740c90b0003004040b9128511501d00c00e540d01c2e18860b15160443c5001491030700c040c0e110910031401c04009002580d5032810048010118440000000441d4080c1c569481c14460f420700707807a4507150002400c0240303202580358 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 78702124 1250 78700874 78700891
    0x8030c0c010f0e0a17040902120a0c090503120a0c0605010608010315050103030c0b090c0a0801020c071703040504151a0d0f05040f0803060f040e0102070201021608150601090801020c06 81
    0x611003040c5590b8110b68002c0b50b00d005039030100c0000d10100d12021690035048403201d490070301d0183c0f140303010030507a0b2200c00b09036000c520712410040070030560321450303202918070b240c0715031a1454500001d03910114041c0116203028000741840e4241e0040180540d641e03800101030010b50381d561005441704d10f0900c0b0554039199440706460a0043c46c0c170455050383c1e4541c56840e14880c0a840d1203a54640040800455128080c1100001d9580d1482d0b00c000b0510a4005030ba6601041415400c2c284a540301c0b040c2c0100722190f0100000000c0300761029290706031340006010001411810350030b0410341c8400b400100c00310184d032281c900c2e040100345002001406024144501c402a801c41e102190003a1003080310101c4400020122001560070440060100d10030f42d00c0e00001400300d546800740004241e60000f00c2030b007156010300c1424000080545203540e100d1401c091b0035158a80d01c036000100c010050002400344e0700800f41a005002600d0086440e030078928280341c0d4403034040d83c6511 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 78703374 1250 78702124 78702131
    0x91b0a2c030d0206070813080705012903010207030c080d2a030507080105011d030309060a11061308070303050402300708060601090608040c030b1614030c04030f02010c08030c0c01 79
    0x42d5107000107031103800740000707070b5a02441d0f640703442c000da03d21407001c03100b01d80388602000182c0100310240580800c10404000900c2102001800d00320000d81c4c001d07142d40240d0040c003032807000c41d4120002c52051500200781c2c42e600e0740d140c45180002c00f003442c0200303184490090076403110304041003c084140710944080001d5102c402069950903024410f2a0014540e010004a0b01c1f20000c1460200c0801404130b80c00c081c100800501190800d201000005100b189840b80d10309040002c00e400c070b40360442499911425407944407052140c00340203803d02da00d41010508644640b951101342542d02c0368440f449400c05103110244540c1242c14107051311821001059440c4045038013802001c05841d85800c42e0724015007039840460092003510070f010282000400b04a030010090710031040e00039520300b801c03400140a0900708000c00105032002c41482042106007541b4119000d0b84c1e0040c1c5445222070031480122120070100600411145001c0b00784101071607050043e2040442c0c0400a0 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 78704624 1250 78703374 78703393
    0xd0f0905031b0a0b041b0b0408010207020a050901030206070314191707080c04120503090d0c061e09050d060e100509070501020c031018082205091b0a2c03 68
    0x25a81e01c00e02800500500304c04404280014a540380a032141d007151495805030640e101c04841d0756400079449101ca99400003010011031400700380f41005080f0849050b00306505503000f0401500485c1401003d100030281e500c40c0000000c010344800f800b941401849407881d03118000e1044881201d820014400000440c07002c0b4082d10000b481510310100380f0b41410300c0e002023842ca04001c1c000540d03850004100e884144d4540f004102605406075007214200e074903119005001031400c84480d07203400c02800418007901d506c9580c403003c9940c121210304155080d407c0440c0144800d01004c04648990041c1c0140d41c0c040c0c0d00094814010b8505540380540d0350b000580e1500c62042da17035903050f040441c41c0516001070380d03c24800098426861040b002e0b89640d00080c50b4800300c451040d0b0b90815081020001110384042301a1400340c840c1c0070300342006040260f00441ca400e041e842c0440c04201c0c406074904c0b6240f00c210030300100000c032201c03208104c40318506505140c4620b0290250004a = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 78705874 1250 78704624 78704677
    0x803030c16050d09140d031202031009060e040317161812150e0a021f0e060c0a0b060f130504030311070b04020301050a020a020d0305062101020309010f06060e060d0f090503 76
    0x71b00c1c4c0d40584410441070300c203c512100a500007031580340d2555800d8408102c240043c8280c8000c0c14082030501c0060030142000750145c1ca4048264071107004010420412444280b444205490309050a009080300c1c0e400101c072800194101a0b100306010f216202884054092034240d05c165002c20014503503603080580d15042035a60180d00200380812030840c3d03151281d010b140c002820320b00411070201c0e02001580d241d0281c0f800c070485a00180e059401d21105001d0f140e0450740c00c072001e6414040810120b00540c1490440024440c4c0d0f0300000380030316009070050301c11058501001c07691844146030280101d882650b05901a41c602000115021010303c00c940181d4051b80040103052540c0c481100902001807000d60000801299041088901545100d885410500140c0c403440c19035113031400c41ea104412014030909200c404c00600f038110800612168042e00c060380e82d5440c0b00c0030700d0013a20040440310748440c40e20300e0300c40034404040007414040c040400700840b0701d101d4030390 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 78707124 1250 78705874 78705889
    0x1d040f11220825080607080702060703060302011e21140906040209010b0c010e060703020307020c03070608070318020d0303050603100902060909091c0905030c0306010803030c16050d0914 82
    0xb192001c0d84030350056252100c441c1c07046410b40c0c00350624080e0142e260740b180c90a1807000c0c0c0d943c202040000c02442485601409030720b5204c00289400c2046070701d940c000811031607100c52103e41c9402d000240c070980c18842c1e0a11410032540c1c1e0035643e9480b6092515000034121001810340c10425000420202d000104205002d6031b00280b5854090342040e19a04c80c41d4400b040c080d90b550340e101004031301c804040c0f055501c5030185450058480c98820006400c0c600e09400b281e20a800c0704d203007840f002c2d810123202ea820100524000401964404010007403140200000e54805041002c50702007540c16005a8482c0c80180e05413120840304000d680c0544403ca080254000414080b14500303060075036021340c0c0005040704681588207039070103000220403039101007000110041e0b8207100c02c1c241002a074100a00a400400c0590b24040c84151640006400c08101e0b12000812502081d40203c1138203800d50444159007050200b40c4028101f100075105011240f0090306c1d07070031307141c0c5407948 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 78708374 1250 78707124 78707129
    0x20f010605030304090e0a0b0406150b07020d06051e0405011a0307080a020d031403090f1207050604120215010b040519050306061012020d0203040506090d1d040f1122 73
    0x800031804d0504100e010405405c441c40c482c0b22034850381d40346602282000034401d0003503000e40341c002040b401c51201d1741c03c01c00d5160041c3c01841401c0142e040141c86001a0b54686600702c5000907403904c4004025281d640c001e6100c3d0826141c44050005010381035120f0684080054103500f0016115000e064655105204181068001c086000e0250921071081d0745154840c1c070b00306549260344504d0500d80e410175504a20241d100b0000c030030442000b0401e5054091030107040304d00f04030741580c519548000041c0020080582540344101103170081003030241c1202c0c4030003409115a104d031900940ca0700140301c0c4910803079100c04600d9948141c5900c2d01c040d201c01601510555a80c00e050003401c507020b040c1d490800c550b0701402d006005a5102411034030b24802000343c0d0b40e0400c1e04001b8546800a840700f01d254000c00501e100c03103030f048200305d007000884041000340058038600243c0280703204ca05800010741440950001141d00e540103041e04064418011202825049003402c100d40c5070 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 78709624 1250 78708374 78708379
    0x1206091b052101080d1409060f0f0d050408070b010b0f37030f050f0907050907031503110123030604090203100c05090a0b030c0306060f0c01050c0901020f010605 71
    0xc40d040300451044000307203500040501c2580041400e0704101e99a68400d038003900898011032011494103174028200054240b06140d05410711803180000f44c02c2d84900720540315494000074442e031006061806480030f0318403104080100345071900b0311651550080d54121880c080c0c900003c503460814100f954049041541e19500f070030600c4503503c1204289044001c150710501c42181c103038020703c0c0008600d19505640120310404e045108000303440000d000c0911102c040070800c070210100040c00c10454504031003140031502d4009050300205001107000c0049801307103101200384102c910040000c1eaa0a90b02e056040c034030444021070310503c07440d44c1c44000c1010400b04566213400d401010f80d41d40018281c45150700352408150403500d0004901c0046030004c20f40180c64600f0081040c020701d80c141d0580d00d14a80102414170920008103da4401c101c080b030030500301c0c0320007020703030700c0e02c4005c100200402d0504248110071a0400700300140144103200301c1c00c0003502306000303c800300c4102 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 78710874 1250 78709624 78709661
    0x30609230a060c1701080f010b09060f01030213030f050c0f030102090d0b060f0904061a1005030105010c080c06090708010e031201030b0402012303010f0509010305060f060406090c120609 82
    0x560340d5a8020b00002d003e00810072180c00c081d800a07154030503516008054440040820010030060306003999440108588150060000c100d09500e4130301c00354199900920b00165a0503040c800c011031052a5007010301200070305d5002c2810403500146c6d144207d1030803a0b01490003040c100805081c0d00c42e40c0d0503260010400300c0720328000307028a4101a0041d0005010545820002c0046004580c0c04c85080c0c4440d611041c02012210788100305c800340d00c0d01510041300e0b440c502d4402500c2840b040c0307d15070400200c0018a000c1c450801c0035100c07400403180954105051421a09584002da40034101c095448d0803044038115400108862850302690902c0d03646c0c1e8a10788800741e01480003042a81406401100d410040c902010109420380c034100d0701d107480354105003086480f0300080d0403190141c0200001400887c00004401358000070b008080710450f1346000100d005060303141d02c000c0e865030501e404203e001d908803050036400020703e4810007400c4d584502030400d95400c1c0040a00301400c = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 78712124 1250 78710874 78710893
    0x904080702090601020f0f070504050618010b0d060506070503070605070504181808030907080d020615121608031e03130308070215010303080105030114360102030103060923 76
    0x28840401d643c003c005005540000482d031105c0380c144076030070038004030980007014280300e00e02d45407103000c0c0c01450030f43e404540842c1d030354001c011004060080440361040414a140c05007070a030070800240c0030140c1100e84440103460050b6890304031043c122450381c00d01d00021010341c4204142d908986166501b10107111a0b291541e008200c0c80b0f118000b8403480b200381c4004100400d0080d4081c01e85003004007401460101c01905050503440b540c82190440300074404400c500c00c481003c85542212a0201c88424140c2c941c80c081d4214400c12509400480008107242c01001400d6501d4022000039201c0ce603621291005100441354580180b06200c42400420711503121140c0c40b422600444044404990600005810903481140003070350500052019080a01075494400019824149241040c401820200c116581c03209145802151b08c01e862844c01e007010300c0c00321585802155203503100e04001c005400c0d8001d0a44100040c0003040d4041c8003850029406880d401000e01400c81 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 78713374 1250 78712124 78712129
    0x1503060602011a030d0e01030212091c0311120705120405010f0606140708031306050a051603020921070e010b070309060207060801030b0a2a0206090a0f080310080706030c08060904080702 82
    0x43d15949247d0406500344601000d01070900d0100380a52081802045115148000c00d403004c013101c2000703800c260074545d0f00b402d000c28080989184200061000800313503101002168a405800311f40b0910640c0c003020300c0213109040d80160000034540805000203601c0303000030b8900742041070f100407a803042000204081034011003c4c5170407141b040480c030300c400c04649400c8142ca00c25102c0340e518540d81d1080c8040c0d030780200c040d206a1405405c0c15030800d280c04000a18200541d4440d112105400d518224100000c0c0414806004084482d43c1075585540b86079100360407640d02107010909022000c0740c054000078104d411a5856a02d0709800ea0030346d6101e80c0d4158001d081c500741144c0351030910001040d036041c0594a2064400c403940b0f10303004d40c40024a881c1c000340844031140c00851840001c00c0f000741d0b62945039a00500120365a843c0c58804103800c04081d400b44106000d4200c0100f80c4c140c0c0345d04501a0500c0c0c90f80c41117000d444080c100007aa000940d0000c0040f001008050010b0 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 78714624 1250 78713374 78713387
    0x7020609070509162105150a080312040201030e010f15050105040b1b03120c030714030910020c1e070e0c040e01061d0603071715030a0308040c1503060602011a030d 72
    0x109132850311410314099245800c2c041004008030001c41e980301c03c03c1107000b516006103002a00d5040340c3c008007451034540c0d015140d11440000402c140c8110000600756406074003e5a08010384d00f00800c0b070304421030316000060601c00004041a00140800281e5600c608142e4041e100d8108946240080e01c601c22800c3c06c025101c05501404203210070141082e41c52407061280094002103984c82c45c140303100521010740b40d215421910010710511440c184000740341e100c1030300b41807001680c038402c692040f8039103c82241c0180c00380c40040f200d0510301ca0b020031207004480401d88100217a40740c501102216001b01e000d64900010050010070800c4e10904d200316000c0150b07c02c1070305c03020320b01c004105507030b00c12520b1902003030862000000c050808041540d01284195404040d4510301000135140c2600c44006020813001202040510410b88800e000920600000c00c4034500d07080d0300503000c1c0c41203115942c00742d40b030601c0c02004800c40001c1c0403800040200509540075203900e013130321403 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 78715874 1250 78714624 78714661
    0x309010504060804030e0a0605030a050a0905030405010f0c02041802011107030b0c0d020d060605090a0501090305030901051b0102040602010504020906010c21030e01021b0c06040b040b070f0b0a0507020609070509 93
    0x1b0405409403000581e2900700e1001c02605980e51440e640c1d00e84540c0901c141c230801340618182d5413070104083d01081c40401a60291402444c140341d24400320001102c0c0c1c81800714010303520920344010002241454040d420b8054400e1301d034035a8a06000098a072103081703d210250a48510ba00080d00285204005110b40680090014202480c0d90100030807134025030400804074030300091030441403401c2e45606c4c004000034079005010900315600d03a6201d000d0020103d040c40700115289003040000d10f42c040c59800500c0085403510342d02c20000740a07000a4400b60b01a802c8200400d009501c10908a0b003819005540401410500c2848001001e00c000007403007003641c1d0380241c480c885c5082c0010810400c07842c102500c64010041d00c03e0038001c01c004c0c070503c550004c11040045031130384015103045809081740c503070700c8015034104210004010b002c0140071b04901e50400048020541c041405042160700b01e82d02c0d90791300401594ad130996400b450360701c6560400011a00c600c03801c2000c1c003 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 78717124 1250 78715874 78715877
    0x5030c041406160501061e0b040509060102030f0316033903020417060405060928080702060a030207110301051302040b210709050702070612090302010b190e09030901050406080403 79
    0xa03040803d22440701995075842e04650f01d944840c03041042c1d8908141c0b80e22014090300d0300c03503001490500c003002103114612483e401040e400c0c000a8080e80248143c454009001c001c056980c64003034110556215503184002c0840e29110001c4001d003542c210f13002c41e0464507510301c03c01303a1044600140e1407070b04100d50b400700340c6c08210102d100e4040009003041480490000d0a4034249894051b0824000805004a0740d0200c1509100300c00100544204c1c054022403030740051850b0b090004051041c1200a90460710004604600c4e503410f42c0100f0301c1c14000c40210700281881d81c101070a954007664581484c03092001814050305c0d1070b03801007070f4402c40142043c2d54003e5990030700202c805031000811050300002d408100c1894107004d0654130014520160906d1810844042d040510400d40009015698007c450401d0f000354042600d0000081c003014a26490f4844440c005106004900d00c0108600101c1c641007800810b83d41401d00503191a0305040c1001c200f00d6803410020400d50 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 78718374 1250 78717124 78717127
    0x5010f031d01020c03210411010f03060e0c180108040203030d0b120a03030b0a060908060703020a0201180c0501030e03030621120c0106050103050f04150f02040801180c0605030c041406 81
    0xc0007050244001c10641c1d0455000d141c584005007800b1000c64890700c818500c41031150100400540400c40e0702110a500342171410740c50591400840003024160080308400300d9800c04e100701c00c54050041d018455006034078115094004004440101056174001d40591050105ca503c03520395410440310510003520170f000d8003802d5407005141403900342c0140c0110b40d9a902048880c05d01c00140e001520315401d003003005501e00702074143c0e100001000d0504169010030302052492007904087d001031400f492068002d5424101911041c40c0d520a01303012030b2403c0030541c0f0000010080d6449850003c0000302c1c000300312402d80f44170300c160b02d29110440c0034140701c8090b0081e0013005083d44015040000418600301b400240031500040e01c64803104030b05a00300400a081501502025441880003140030541182c00c040640125040420389500b045c00405012417500807141ca214011030038100c0c0365036125420740700b42c07000380c8004003107070360410003803019035840303524450200005008103 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 78719624 1250 78718374 78718421
    0x91e071101200a08060a03030507020f0a0302180a0c0306060206010510050702030703030806090609040f060b0319140c040c02070902030903040905040b040c05010f02031e1b060901110405010f03 85
    0x10000c00314081c070345407090000300f02d03611102c0d030010106a009a0641306000300c241540c4014101c0d0050394002446288024048440b6454500044d00191b5002e413074010740d07400644100224000444115041515001070030054500c40c0c01751038211420354015201c140d0800b000d200da20b01452600e01d060210401075600161000c00015000b10b000e5a02e40c0b0540c01c1480030086001805000c9a114140c500144004075040c80702104481d507004000183c200f1200010a01744441500c0040007000c0407210001401a11100036042603038a50543d0452203d14007000201c0c1e10418444c0c005a0000d14280320401040e030085070012455000c690401703603121011026607500300c0d0304940640c0708009101c108a41d1768901c0d4050315090030002d44021020800a40e03d014455004850003254060120804c9000301110207003098580c03040c003201e1401d81c4107580ca40d0199288403856182250310a404460182504e0650308143d4481e100415282d00c01c5000d8039881099015403120500e40 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 78720874 1250 78719624 78719651
    0x905010c1b0f0312050f0904051e1806010812030c0705070b0d020901020f07180209040204030b070903020a0e24040b0a090b0a0b0903030a050703210b091e071101 71
    0xc0400505040c94880d41c8541140707130140c060391900c02000700703002c0305000040c803001e95241031300c0c500c03007007a14000340700d41c2c50031200c400950720180c51801e4800b1030400d2000e14880c084090010344416811908540d03070383c40310166950849070740303e80840c00c144040b0f0742500d062802003401e140268111020a521164030103510380c4141100e00440f50700085c5e070106940c050117103d0b50f580800000d811039526003100c0568140f01480c1d07012405a00282584dc5030382c070360b8161005580c101840191900d8503110180c00300029000030b03842100c409000080c04084000400d100d5410f00200500702040142003490344040c9242d1594016151400e49015403602003004008201000000c02c407810b210042c851101140d800500c03d031001080ba280b55a03c0c008100e07006400a0b141480e86c41c4040c0c24221840c0240420755528651010030a81007815a600511002d503421140c4103407a44400c400d500100b00b600e91400703c6400040b00007040c181c001c1e014005c0840d0790200201d20150740c44070703 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 78722124 1250 78720874 78720923
    0xe0c07080409060e0f010b03070c1101051c051803160b060406150c060501050102070803180a0e010902040f090e100e030f040810050a021c0c120203040f1a01060905010c 74
    0x4c413003103586400301000310303035400f6100d41c90040411110541c030350306184900901240154078041c0215240c01c8015489034400d20440d4a088149121908114515044070001d403100340e5407041811600340743c02c00c40c3c45c0040220307a204010794081c03450440896855940c403c80040078154032a40d511400125200c800c4c41c200e58220383c55540f0184101140303041d400321030068100a04541c00901b00344001b20001044400c010660710001b15408114030000712460085d401a2420401200002a445039150003400c2a03d0540d4052146c1985548a01c4101c50303143c00d074078565500a80003403501445907481030388290381107000d8078948991115070b460958050360000c180d95001e03c106112481d018401d094000031050003d52500e894000010b00e6101c2c0102071011550f40e030048040300358001c03c8260000008020290b461340707002d051900c0100100c2c0c3c01954609101c0821aa05100080000c1c3c1a070f00e503500c44850203810200111040b41699808036968484c131040070011040021 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 78723374 1250 78722124 78722129
    0x50d1103100c0f020105010608091504050f0a0c031a100905060a270b0306130305031807030803160c02030304060318060219121b0503061305040c0f0f0e0c0708040906 73
    0x45440c1401c582043e8020301316141640480d04010850b420300404d040042103a609242132404d60701e5464036181001410500c0da4100c00c101c81c0310300150407082045600700130f811640144801106007400c102441e01d68141102d0030058203611500030300814a0329481181c00c460090210b503100c6450300140103d650300d003100004100c40c24030b41d1014000b49401595490384096000c0c00113400e003901c401d0000120040700505104012000454150b004a621881d100108017121003540d41c90418003401e9200f528800200310501c005141c900d0302031401340110030740c041e004500d80352424400310300518101c41420141c910395114200807482c1d07400030700b940940c2c0032181c2800e8114040c02170460b810146a82001c2414104040e100740f600d07921034880701d010b60900c15640d940e9240007401309210001140c68603442d1006000074000070848820075910303145196515a5180d503030320340c4008510300c41d1500c080c40c4100010b0007100e000c0e014104561280d004503060031380f9140c60006460070380c1c = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 78724624 1250 78723374 78723377
    0x909180c0d080306040e01060b07061d1203190506030c090c0912030405010305071701031e060c17060433050603010603050403020c0d0b1305070803040b0304051006050d1103100c 78
    0x1005200545c0340c14800c540008102100810526150840161544c065007801400003545c0703080380c20801084030320041440d10640300b6030340100c68100c40b038040c6800c161410444076422100004640345640703d03040c007601004000740442c041c00d008220700c1c820004d180908a91050090809640319a26000c0e1040104000366485a09120004003100e0b40180003e0030041c6000d0b100d4102101050704a040d80d4204105c0c070190820b000e080b56562082180c0240b02074504481000c2040e031111240344074250912803054240ca5035401c010541d14064104c1000c454404807a0304210381c10210741d8040911040d4a808096803500020507a0f0001d0f40300030040390302c52080100300b540c10310003000c0e451412038080100010988a40308802c0009001c041c4080e2003500d60001d012041010500410144c8202d0b951552142d00f4030800d40c105440480e114410341380581d01c400154042c00040c0c400141060480d482161201400c45c0081d40c1c400ea058081d0031104d140c03107581c5000c4c0c6540e00005 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 78725874 1250 78724624 78724627
    0x102040902181003052701140f04050601060e0105040605090f21210403080a031103090a0c080604030e06070305040305060a051f030503031b041e06020f01020909180c0d08 75
    0x24020300503d20084200c20342018508001c101901100f16a00c070aa0b40641d501c41000707035409250b481c0140040b10026650040c0c41c8104150b650300c805c0760512036480382040c0c9103640d0b07917070409a0340c2144125000c0d001c20300520060000500ca0000707003440d640001c12417442e188082d808541126040740c0c0d00341007010507002e100d050440c10015985005814801c1900b541d807880d051182c01c0c040c600000300380780b40000303030000030b81d00c282c1200007095009186190b4030300304510750300d03541c003c2c00300c003118a85104080041e100c03002203003451003035030903031a84c0981842000c1045010760102c4030440c18400140404008508100a003034400d8000e00c00028450a111104c05604014600d0717a00c650344140006100085010094a8010100040121241c0c1c0e20b01142c11060050360001c80c80a5009558940d9440342e008160007268115000d80754102d504042c403500381d1045580264209209602042039403420b8081c2c0c5c02003e008005132030800c56090005050380f15688002e4800520 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 78727124 1250 78725874 78725917
    0xd0804030b07050415030c12050a051b0c0606040504031407030203030708090d090306020a0e060f04060e0108101413050708040203010c0f0e13111c0501050d030e120102040902 77
    0xa0500410b401241c1c2c0d0402d28145445c126001c030b8000540503441d010561200d110070700300d6000348c4a00c9170311041c0410610147c0b901c112105c0003400101c501135180401060448449050304080799802400c003030252410346e4403081880040c00010300118104030310040410000c03003100b009032039110303c282d0186030b503418150801400c0c010701601c2a000d0350403a468a092460308070100300d046a170700c1403000da110b2091580c2135a039044a0700c200c40d000140003031030039030300d1840800410540d51684c07118020301c505580119a0a5000c039030105485142803414413400c512044100403104009012a0fa516085055581076840503150310003ca194030007030008515007070040040c441402d2920f284a064100070040449261006490040c200c2507201c04c80034003560000405950030003041f40e0f442d448812884404a80803250340c0880c0d1401001003202c1c90072103804080c03590190341c0e924807400704000300700c1c0000202803401d10b1994204800240c0344103600141907484442c103501c00f00241e = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 78728374 1250 78727124 78727133
    0x1e0807030f050405100806060c0709091a010305030304030e060f0a0f120516030f0e060c07140c0f04021308060108070302030f07080d05070f02090f1905160e0f0d080403 74
    0x15601d507880c40500805101c00d1003961118a80202c0700c1c00180740000c4a9200d02c8003040f51442405020f403003a0007840000300e03548055800c440810752042c8096810303040c8400742049031290a0000500c0c0f03800800206001c070b4412403078505440d0004120300e01d010881801608079501c00c141d01c00104510305402080c191300701042c10300700b020004043c4860718203104400c060b40d000031078080c1411782c0e4031002c0600c0341c00c3e68800d03c01951070400701c4086042c107120b050040d810180d07044604040e80915410b1489000c201c60440c904040c00c98a07000c4140001c01c03000e1b410101d14050015640140043c0c203410400295000b015080090540c0c00c0c1540141410810240300311030050707102c3c1408102201d00080c030083d0081d02407600a03102d6840745070203815103800c0d5101039484405071050101500b2103940c2c2074064a41000080070074004046d403101034820455100b8000c800c5000c0b0703120100c0c01000306a5136044000d080051110703002e40010074220180c4c01c00c0c2c400e490085024010403 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 78729624 1250 78728374 78728387
    0xb07020c010201090b0115090314030909011706060607020112050106081504140705031305010e06010f06030504030f0e04060504060b072f0d03050405030604060e160506040504091e080703 82
    0x152082c8000e0102e200c1c241c03225030803100c040c80f07411070350f50720b00071000e15091250b101c16000d950f01c0260702d6903000120305919a680c2001c500c480c82020814000038180b05688400074907066010090249940c412040200a03041880240e0503c002a03480503c4500548121406002d4075210f034a81400c0410100d06041108210180180e161130f40c02100c0300300a107078103544002d9910f02503990f603584152a0030080b07c1c2d644018403075801c1960031700030040003160140c10f035130089402200d019590300c0100c054440035030700039012039481a403a0052074822000b0010125000d400400c005a0782c101150850354961b10800c1000c1c00442d000c7c0812150b95100f0803d01041000742c030301054103c8000d488440a41175441c8515000302c06641018015020f0b00d0051a00500f510460b15041c00c1000c00340503020f14200c0103008924a00d010081080524810364078007400301400c003801d00c028440108103852050b518101801c000706032030390b03106941071040303445400c19945584151030041c010 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 78730874 1250 78729624 78729643
    0x30a0c06020d1b0f14211b03040b071418040b0105040f030303020904060e0108060f091c020a15180807050a0c0b0403060b010302030c180a03050d09081e07180b04090b0702 75
    0x20b0345c13820803858248618034400165028441d62903148503813111104180800c0c891001e060390054040208001d00c580a0001d41c411209a1500701c111070116844008602c074460b01010794880c0240d0302205800c00350b0041d07030203c1043c140246059101e04a2220300409980b080b000607400241910b0b131030606018180c01003411800d990901e50600c0301c00703516040c0c004c1092000802c0c05002034030301c880c05c0008644440000b9032800c2c8042c0740703100080d19001d010a0030b446000d00210b01b0202c01520380309140304d02ca6129002c0320180c0071039403070807055440001c0c01c0c0d600c0d2060b600d5100200d801040120000c0507080401da6440d40345141c00c6043d5001d017910b141c18140306004100c0c1626001c0201c030000b140c000401e0581d040500001b0300c00d04250b410203040e074131907100015505500140007800ba201e003502100c0c0170682e50082c036010300200310dc0d10442c58004640422603d510781c00440704100700318402169003a000341c00b05044510080c4142c1301c00401400b8040d10039010700c140b800 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 78732124 1250 78730874 78730907
    0x4080d020c040b0a05010c08070f150506010815010c03020a080c070f060e0307090b060d0618060504090503070b2208070c05042306010203070501051305060702030a0c06020d1b0f 78
    0x1a10329080028101e001c64031403176061152200801c004c2000e400c00300e80c1141c0d805110345807400c25605141c1140701d00500005421031802d0049500c540c0607401702071182a82440d000980200c450045903200c4900c94114194465001d840b030000d07a881001e020b00c00a40303030081446600e04560100c1555069001809020544000300b10588011800c2c42c25564078180108403c030581010079510b110f030645805030a445c00c1380c00300302c808007843d5450440340ba031442030110715110030400c01210140034004240c1d600c2084451300041d1300e0341c12982d120700e002454030000e40d82c1510485121000c2c1d1070490b00d00174006026410800c2000a00d07000e44011384040250b10b030b50b1082c205e850810301d50305404486000700090010780c400c00880704030380d0b0300000034440c6041007075003450401c19140d01120b00e4000e1900003a0264030010640f01c0c40c410348d543c1c018040d400c1d519640020360203048524021621540041500084a09244110b00711607032401d1074182c07583c1000704a000528a03048 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 78733374 1250 78732124 78732131
    0x1050906100b0405010c080d05040c0311040c0206040b0a0e060c0301060807080601050d0b0a0503010f0501050301060506090102100c0201061214070618030206030901090204050405060411010e06071b03060204080d020c04 96
    0x140d40000c0a80f03054440078242850b40700040d060644041c0204405002e0712410309003007108004505a0110840f88a14261074041c00b046007000251000c03845803400590000001074040b8008024032500031208140008182d05442c0c07030141890340c1151030301c009500001c0100000313a031082c0c60550021840c40c18680710b08011000034020310840e030449030403a458081100656650300d0200000300300060007041910100d01884028200900c242d80c840d520f480c0700001e1a041c420201c81d00039505a007d4000380300c00c03000ca03000401400e03124030115942c0346008120400c6440b4101c02081c05402250119405422560714102c859040310042001d040912030000752982d403000c081d00c0e030403100c007900d82da40c1d480396500410075100040d601505100500003440b40100e41d030780c020350040459040250000006451320018010f09542101c0200020340c0444c885400d1202200c0d0641c94a40714103950762152004d80e001364000050030b0308000f4040d00721580400c442c014441099a051 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 78734624 1250 78733374 78733379
    0x2103020c01080615090102010e0f010b0112020c03070b040606050d0b0f060d02010909020703050d060f05120604030e0904050a12020318090412052b020315120616020f0601080105090610 81
    0xc0b100c58907550541d40411004c01c451715540e002303400902c03c40c00c14008943c410900300d00c1c0c80d8041d11040161300d01090950750751400b44111402240c1005460000561a05180c0d9031841c2e104400244140c5019540f0369010070139130740c0d0070140708415000c5c605074045401e0401c0842c4c6500d5028100c2c80c800c03a1500030f507100503604981003404803840340c5070043e142e141a08056803184280007492011510704000800c00e02c0a282e020341c26200c1c1503811a440c80c80074505d8568810f000e95010f400f01e428445c810174640340100d142d075071081c40703502a6442410503070790382446400c04240c1030015070404984900f4100601c0301e40f2829140846a40e0304508107500d84181e204c2c2c03002e00b001c00f003000004251001d1765016840c1a0035114854450200803480f188110094006550f01d5070380c00c900c0341c02d6820781c5c5000e840c41d0320041d01c0000545140d856802c08050442014810f1005600480075040f844600610480d8024816000081a20701e0b100d06224101400100500c07552981582c1c10b = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 78735874 1250 78734624 78734629
    0x50f0f0610090c0207051302070b0f0a0c051c0213080615030c040603020f040207050111030103080418060b09010f091805090105070c050a031407020d05010b030c010203210406062103020c010806 85
    0x20381d41246c0003070303c2040c862080711825601070f00c9202000790803001e0003001d101320043c0d0002c899100c1c02e0049400c1140010842c1c0c00c03520307032290000916500302100c49000104403282c1c0200b403951448560580601d80e03035001c143c20300504554011205210b40c040c5030703080c1018020325039903960444041080500b0355000910b83e0541d80308080c0100d5021400d06d00b0803609500c070b0b400d80030003030340781c00e80b01d41e960b11b031202c041c0d44980a00d07207000a80100201c24a1682d000b01c0e020f9480780c071101814004400d00442c0c201d105900039900f044043d001c00a005100a488600000b04014010510b0b203007000b249400e480018044008000421000c403001c03a10106002c448241e00d40340081d4501e840c0300c40842580142d140103980131040c3c0b400300c810450154494143c204041d270030f0754070162840005985901960280f656040c041042001161103007400080d07029206000000b0019120166602403a510212090982d100450443c05240d01040000b210200901e0021024a8800c01 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 78737124 1250 78735874 78735883
    0x103061a04031704082e05060616110a080a020306060d08040e090703060c0e0315010e071209050a1b09050402030a0b0903070b100611030705070e04050f0f0610090c02 73
    0x34000441c25000b00b00001150b0f41203400604152089800c00162005d5410191201d81c40c448080c04c05440f4281c060611401428450580140700d0303400c7c03880c1c21200c0d404810708145c007182c2d50401030a9501190340c401c509070000d408010020101004240305042c54108040e050f11710440c0101401e100061003841110180d901c204100c1d50940c407420364840c681107040d04000d12690411202082c4a81c0c000755449038200308500711101d40044000c80010144207000e1901d181070316000140d4860f004441076048001a0b210000c0c064041d0384030703c0d0070210300720000c0b82c00103440c0840764002c4601c0954980a005210003c2080d41019070000307039294550070000b0701e407420940002c1c0c5106002e005a40e401d07a0040d0110078240703402c120a054100250080e071020403180304404c0100da400200750b603011540180200360f0740d41003c14600a208004104403218425412800e0816505002c607042c070040c541e000744081d0034804006c60120035036400040b0510324141c0b01518039a030024 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 78738374 1250 78737124 78737129
    0x60c0910050f070204091403070609020f0111060c03060315040c080708120418061e0609080d090504050c0415050a0318120804080f040308180405060a15180909020103061a04 76
    0x280e0004402a0318a0b01b10004004900745101f580030124031081441402e4002c400c41c207100700e4031107a0201d014001510a60204a44000d01d41e10010015504069010095070001d1006044070000e88000e1111910844100c0301102c80d00d030310207002c04c165041002241702034100760001d0624405611103413070b0305002c0c0c0d1240e140c3c80c180555440003664165804540506501c40e00081d0601e50024a454400d00358030811000440c1e09000240b180303004a620752099031107540b0050003d240c1401c11014000181c940c00321040304000000b10b0181044110000310215214152642080d000103012034903001501e030039003000c80b40f142c000509141447d1109400303504001c000d644946c144109680265076500d10903500c00038000c0280405000079282c51742a281400107170003590011310080e1801626202c0d04038400007401e125040c00b41019060780d202c603281103294800e000c0c40c641e640720400e9014142e81684c94981c5400e550340750080310050500c614001c0840d01540b401c000041c4102d1 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 78739624 1250 78738374 78738379
    0x21c090b03070c170a02010b030c01140d110f031008010615080c03090c0316140a0b070312020702043204030219030c08130e09060402030304060e01030e060c0910050f0702 75
    0x20440f40030031403141c00c140c04200140c80070a446000d10040079001384242081036100b403140c00c11800303840d0320841d02920312810b00707201581001031440300d501c007608128074005c081100a12040d616403100801952140016a0a02d0700306071400301c0c00c0b800c45407070350000c0c1803880b0b00303600204c101d94000102c65000b07510311601e640c1e01da0300c0c0300d85c580c04c041c0244003056042c0105074040c018500c01c2d0901209a0700c070b0451000c117501549080160910951107070001c40b01c821b00c2140003007402a0741010641603101009458200103a0016084031b81d205422581c49600718028411018090002180c2c03800ccc40d03008001034142a00c1c060341c0c81c00f072445101c1408040220040c101441011000b11481d40b1a2003036440310411101c0ca032208400c2d0141166000c481c0001031295900080c10900840d000b801540c0b4160511400b11160504c41414038141601d40310074041004003005a584a60a00b0900d40c3e2039540711010421002c42000c4032604010003445a51031480d40c2c01c00316a004c9904 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 78740874 1250 78739624 78739637
    0x702060a180806061f020a0c0b031005010302041508040201020709060305100c0305070c02090603030904020705063102040b0a1e0303121a0f01020111030108030301030c0b03010b090405041b0303021c090b0307 91
    0x17005000c134034003490a00024481000c0d4071000034400480f6001e540144c40d4254124240c40c3c40d54011030481c05107210b5040241303100241c146030709000e40e860640060043c41a01e0600351540d4001040c0c8005a0003182c0b10360000742c0840140000d44140034141e41c40c1c0c98144a5810010340041a000c02c540f80644a41c0a10020400c6603808100321950700c03501520a64540340c0c14106130384c481c0030440c1ca0b00c0c1300c0c01514a200a44106641880c03044800e0303000000001c180ca07800b0702c001040b0820342a600100d04180c0030644403180026002014101c3c000040202d0031454020310a000018032406500d00b0b0860701105142ca400341141c40c0e000a556002e201524040106e01611a041c4600510400040040b901040c0880150b050b02e02541d42c0741e41e1540d41b40c00009040c40240302e8891f500ba0284400d0106250075000b40c0d42103401141c0200720102110b442400a014550044000d139000c1c2594000501d00402408910700c2d8509020045925151000240b480004d04010400c0403 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 78742124 1250 78740874 78740929
    0x403021315080111120c0306210703020a03080a020c09090d03020c0c0a030309060e090c0307080603070305120d060504020406091a04080105040f0b150f04110702060a18080606 77
    0x1410012500144088002800740390701043d0104c405510180309008002c0c0000001000300816104a1703001d05000b9140680b01810b2104111800003006000685030154070340c000f0169598109141c051400398031010741d5486c2c140310103440c01410b8440d0a0040302020208002048082400024403545040160791440840700403030500d4144080c156207c1c94990010040c550700c03442c000141c0703001da2248440455a0400c012005800302e580d140c45810800010b50302d40c0c13255400540050000d0101c07000e4a031641d5406007014a5100d543d0751180002c02c111417050400e000e408000d100030fa42c110b14050801c2401401001c80b07005108102a140315204e10f0b481200301190f00030414400200454241494000d04285000c10705075400c8100e8008140c0301e50a0030300c1d0400d0104000c0080400c000b148003444098450028002c04040b8144560805078407a080107100e042c1c1c0b00d1b03841d180206540b46d2241c3c14051150403050703c40e0b104a041001030380780d1040c1d04a2101041c03540421800 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 78743374 1250 78742124 78742151
    0x60a060f050702030c130b010f0201020f03010510021e1b01030612080f07080d0c0e040c200102040308030c04170706050f070602090d060b0406170703060e070503120d0f0204030213 79
    0x411010820350410a9080c0d2a06032842c603500041c4541f000343da503e0151450f101c400c03420703409540d02000d5503940801c010007452900403081c401912450064030300501d25103500040a61540c41040072640100143c3c010400054820b602c0341402400c0421070360b4180707203100120701100fa10062100703400007020b13190881444191911640e0008003a9515400606000e0181405100120101d10380950b812418070349800303a0700080c0c2140d583e000461800c4c1d041d04420440000014550f035508200200104803241c0055110ba1101c5014954035440c0220510180c0d4100c1102241c2e234102ca00180318a55004040380e00090780c2d1503550342c44070494100b0800922030048095400701c05081c008c0304008090300900c4400c02c040f10302300022941c551800d54141c0d00000166416000418103000141c5130303034003865a0312070850456900e25119000700c1d14100780151241c0b407406011070403c408405e14010a411406002001e60600789140d021486544081c091200302c2d035110224800b420 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 78744624 1250 78743374 78743383
    0x1090209010c1218050603010b090f01120c09030b010e0915040c0e01230604140d050109020d03051201080d0f1209050d05090a1205060402091003080406050d05060a060f05070203 78
    0x80d40280380050f00010f000c60140000101319541899a0075011000a0b20b14110040e0380c125044030420714a4520110304000044d207050240740c0c18884205d04000d0f20b215180b144403002c540c02d407100c80b966400e44c00c14218001d8143c0c8480300300f0040004200c2c8808001c074400e2000c0c076404003c030300191528070702000d0380c00c0301c1d81000ca000030a100000640d0400d180070903051412200000242074008000d0000501c03480c000d881e09003108800c0041d1600b001d02a1a4030540540000941c03144a03500145040d0340c0f407a4185d00050740814104001c108070354003540100006001040d821090240c042c0540080340292404e1081e100c00703a1030808040d80208280e00c0c0d021054401d24891010003a000380c00120656004807415103010543c002ea10a06401c3d207a000300042480d940c5035030030420360543c002c25000c034201d003c1500000203186100039001a062a45880e500ca00b17401e1000d0702280c0004003c0b0f4400c2c450800c0420150f604082204656003651030309542e100f2907400460b142 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 78745874 1250 78744624 78744647
    0x30408090d031e0305180708060105130f0c03090218040b010303110f01050a020406180e18030c0706030b130b010801050112060509130302010e030304170304030e04020d0501060908070602060109020901 88
    0x24440c40c1d00c0f102220b943c0365205a00c190b246c0d10300c19188401059046039244068001c2040c00d03884100140460301c0c1c1500d0200c81c920b10300001242e010364082c82e82e001e6401c40710015004c03076120a003000451900c210340c580c2081d4141c1001c806454036844080300008184005400e025401050700305402e03040c010100f0f01c410950092180c0c0c1815071070b44000394030603c0343e2000210005142285040c40600400c1200c1030f058440c40c05841e1030005c2541d02c08841e04014851208000302e560003c0b00b4840100101050b0300e000070041044400c0c032844605240703403244810304d44020010305030f800104c1e60f81074034000e2801500904070341078407e0050500b50030180c0d2081030b00c41000351540038580f0340014144a40e000340060310000c1c401ca41d0b079000c01da0300101078036490403090003070300000406580c0c4103000e40b80085008081c0ac000c07408907840014036244164443c0300600a882d0000442001801d100006120140c5000c030020744526042c000d202c040c0b81c00180040b11a885104132010 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 78747124 1250 78745874 78745907
    0x11010c05010e060114012c01090e040302010605011706010c0f06060503071205070b030c0d020a0306090203040809150c030a050d1b020f0d081302010509150313060b0303030408090d03 80
    0x31003202c0740c441d0b03541c0710402d12804203820310f40303c100611541b1410f07031094000820039401481c403a00c0810f03001c2c840c04c412403050421081400000d00d0381d01d0098054040d9010b41c00005015042100040c1003d10201d06d0550005142040c0500c3d40d0b0320001c1c40036a0750b0810099500d1089614003c1d0141085602c41a818440d400b40449c0401d817240c1100c03507072841a400c03074206c141d440300c4240c518007003210380e240d21a0040c00032405d448240d4005105201c074501d40041c1413038985030183c04070307082a0f409032103521006c070780f48846003080a00c4400807805495154200402603010300e035070341706401e000c1c4100400850101e50000203604110000c204800d0344140211070b41030300a603540452a9402d515205103000d8850301402000c440c2c0c01500c4030310268400703c00300d40055a013584012000d0307030061000301e440300e820000000030354020a003103075881554400508100069070101c0381c400e0b100743c104000340b1000420010460740049030580c0c0c610241e00c0203013401c0d140380300c0e000e44021 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 78748374 1250 78747124 78747131
    0x13050301050106020d020c0a05091306020d020a030c27060c02060c0a0602070201080a0e2d0a140c010314040204150306020a0f09120209070806060706150305060105011b11010c0501 79
    0x144498003c284c2990890003542103e100c0c40b047d00400502c5c03d10b80c4182034200c001c03080402c0700701000355018400e40c2c0c01600b01510742003070300080e0800c0740d00c86002e2000080e0740c1c0c400708003003980c003035071000c0f58201e1103036400c140440c1600c0c29089280307148500018000b00525240454a425064888644c00001610109507803400d1a4001e0750160204a002421041c0060b541c403206100d01e84040c0c01d00130003441d054940840001036030191190303105c4103204041302001d4000081080005003441014644480305e10480ba0620307109040d14940c1c1414104129a02c000800c0d80780240d1158040354040340e240d042003141086000603800103807046000040c4c3c6031000e5040b0300a1b0440015544e5190909540e80c260114a01081c080081d84070000700c0224890318841c0c0e40f00d0380c000000622071031401409070380d2170302102c01d105100001600740c00010400d0280a015907401440282444950308011700e40942842041c4e4a0061080c50403078144440f5034450765191850303990040081 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 78749624 1250 78748374 78748379
    0xa090302040207060614030a05030304030513030203010c0f1d0102060a09170d0603200f0f01030b030a03110609010c090306050702010209060301180b1002070501030b06070512130b071106130503010501 88
    0x44c4094919400b0b000e0300c2a040103034080950038001400e5011b40c0d0000080c509544071a541200c0070f03407015204009142c070303049000c800b50780c0a2048854a148640769448221404900a0503a0083c00d070b543c44040c094441c1402ca90360007080955001400c80d500142440e0180351107102c880540700300302c550b0f0780041007000000c1c03100d920940980b03011300b10000c00c40043e20000e02504041c8150f00e81c00c001e41595070505803c00c00d03040a03241c401410702060381c194020110345441c40201c402c0d00000c00c0d0100c0b10900380c0b824840550465842e000a2050001500015188c1c0c1194800100717596a40c0740020500c920039416102c0b0310100a011a41d6560748240ca03048034001c0c0d1800060007494006405018038050701e101c0c03d81e6030650098883c1034a410b00560003422041c0b22650410010000440051030601c003a451144000c0c0d9080d8440c0382580d5006410071154120034107000c0b0421068000c103210054041c0e04040c00caa0301541c944000002a401d0072040d4801c0b034040d824240003 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 78750874 1250 78749624 78749633
    0x90803070207140a050105040621240509100b21010306060611060106080c0c0a0807050604030212040305070e070c0c08030d0c03140109020a021603050c0901060f140a090302040207 79
    0x20002118650582c034443d00c0c400d28100050140345201e02804035400308003c00545010700d40d11402c08218101e0700241246444405084d1030b00d201c40b8040c4103108400485e50940040d1002028001c2560050043d1815045402c811010790040c0314804002180040480b0f07001000222a400044000419944d4a1401102500090040c200882c00d28415100801c0f00040e01604072620f42d80c80320101d4070789a10303a0500354404200b60342c440c022104400041f4121030010107000b4841d0000340803d2401d82002418000196120a0074078010441040030a02c000354040540d000280000070a840e0107009882c5400008001084030300060000a0b0000d070120180601c203401400c10b0040281d048802c81c01c4035180e04951840807242801030100c180c480e800340003106180d004941c140307103003034840d285c2041840e40104c40303640c4440440d948a0800d4691540100a107007024030b2080607908000c0c005406036212160244000301350505010300c240341c5c036402190050011544c1d41000c3c10b0 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 78752124 1250 78750874 78750883
    0xa0b032806050115020d0e0402220905060d0b0601051602030d0807030b1c060f09080d0207110d0b04030309020321030105120a050a080d0f050a0203040212010c090b09040908030702 79
    0x5094070820301d40703070000030028802a440c01c0889100e5002e054a00d0300c070079043e608000400070450300580c0c28041090900315480b00818011442031860300064a800300d5002a180000c1903039016a60300d40b24000083d1040e609a0780100307007401e02d81d48541d0703800c00000c03110701c0d00030300030394135100d82d00c01c58000e0341d00010308500a40789580e00b44003810100c0c00340142005c6085400080384807500c0c10701c002c5007003a480340f020b00400d800302248848464654a046400004c03000e01150790018164007084030002d00c4211400c800e81b9031a107190b885840c0c181078444010009400e1544a21303580e011903500340305495400340c0d41c1c0300380061084171014028894109009441c0580140080c4002520380001d901c641554000000c1211a030a984c401141f03401c4102403014450701d034000c1550001e80e5020b540c0c4500030341040103813a40b801d401080210710350101c0261007079161a1200103c0c982c03140048040d200704580540d5181122800729000b400a1200500b50600200500030001e50104 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 78753374 1250 78752124 78752203
    0xa06050c0705010e060601050f130503070f15082202010306091d190b01060f2d08070903021c1103010507021f050121080c0a0605011a120a0b03 63
    0x8004c10054030700340140c565410080d07a959001c075006204c850000c044034402000c1c00c0130302e0095142d4a0307503120b000c240750a00a411030408544c181d03600b40110354009090383d1854100c0e1400118a0134840c1052010210455425800710002c204050540e4001d400c224002c0c41845070030040080700e51248603400d8002000702d03940740550005d0801ca81403081507000059000174010711213910b0140255180e803c0076a8400900002c040c10841e009540080f1840c1840034a02481c103880207d10f0040501400520308014440e4222041c40036803120082914901050718101c01600098184020b110352103107480c5506600300f1040040555000c1003500c90a282181d00203c03000300040d4000503100e01740244a03c4210b5030311410180421029402405401080910718144400c52204d00b0620b020205544070f41c2c0722030042004480000b200c0d41203c0411001c2814074030b00e101401d80c100005001d002030b040c0c0341c02050049035018013106046447d4030302c9140c42c9408003c4004000b1480c0c0 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 78754624 1250 78753374 78753383
    0x30b100501050c1b1206091f0e0706030c0903080318011b0c03210c0809060709030b040f1e050c031005010e0402090c13091a0301111b0a06050c07 64
    0x1808002035550040040d00c4418088a01510b4408400441c51104030340c0300c08015031010020380c010184040c207100b064001c0000700c02070150350700841c11039442c0e01008940400c0e1989440c4071002039880c04180c40040e0b881a00c0c0c003058180681c0e41c12903144c803035504058880003001007409500201503000d50400c8035000c00078469070041039014000003000010720340225069140c3c480000384254005088403e0850100b1144201654685c1c1212860030248001c208200c0c280803c0385010002c1a61040d400d1905650700ba0842c2c0e0341000543c40603000a00c0100e0030000f0ba005c200d42414040c04062030781c0000b40c0c030b03a00c0a04110383c4c0c0e0501c203d5402d0103030151680390080d9100034040c16050703a1103541c00c4121600c4580c01d01141c8070004001c50b10410060100221061004810342c0062100b020b0100304501c80052040d5445a5246441e21980c50316080c0848480c80000b070f1842241c00050307504080140d1110715041400d0520000c181d6890001000081c1a0810103410b459008 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 78755874 1250 78754624 78754651
    0x1624020f071d090c1807260406051008120c0f030a0c060501050108011409091005090703020306010519170a0606030c090e070b0d0c090306092102120304031413030b 72
    0x54804441d116010b610345145c00201c1c0c61041503505001a100c260021034610308401c50380d4400112a507c82d0030612101100500c0300248024005c503409820340150845040640f200d242c040056604c0011f01c0c4015001400403c925034003000900c082007107041580d068955806014030004c0c0044002003003201e005d03140034008909544036042d480d042c1ca42c456101960f1134108001c00c1400b42005100c410785200c0e407078044400b40201d014040c05601500c0090140b54110710400d0b041c0300058000078011a01c0c80007000c9601e0b0000c1a04045411402014003000c2d5551801c070304120070400007030700003030902100104000855404170f04440c43c2d00b02c10000b49003140100f070b03210041440344c00240d1b4424010349042d00700340d40c8681405003040c2450314207170350346c3e50714041034581c0f00005451b5080700c85c00350030001c003144020300400ca400d031020f000500032000481c140d47c00b026101400308a00c00e11070f4401c400b00202120052007030128601c1480fa600c2c40d0010000c40c0c226035a40c045d815 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 78757124 1250 78755874 78755881
    0x30f010501030c15050a05031f0803030603070902160b0603030412120306080d0801091a03060906070806030303041e03170a0501030c0605090d02060c031b01090201021624020f071d 79
    0x40315100004c1a039000d5a401e0314001843c2c4084400b0703000641075503184200e08000b8002c00c400c411500c00149090383c082d540742c0c68250200740c101070080e409010800c0c010044501c1d101040c40c17911520075405605511a900d940001c00e145000300d07005880300085525040c020700502c2220f149a01005035400e02c01d00d0f40303036000c054481c14800d41410100780c0c214010300c940c160300c1c0c204000c40c1e108583d0040c0079809650000b881c0000640f0a803055401407070901000540c05861241d11400550040d481d40c1041d982c0d16815074070f8407425203882009a007000d81014800c0401c6003c5441c40041036006c0d051185102d002402c00307100c2100d03d038502d683c00085050140d001da8a00c240020b040d0040da10040d024018664482c90040056010810101c80c1101c0c240300f8075841900e60600018000000d8400079241861441003010403c40c0c0810070440c0c80d40c800700c0c1c54923104440300c1c816582d00b1901000d92408035224884107850045481c041944490403407071044080c041c095408198070b = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 78758374 1250 78757124 78757139
    0x3020d030203030a1a01020303180c0411030402030105060d0510050a090f1a090f070905060a0f0803030a0f0615050a181706010902040f230405010303050c0c030601050303090d11030f010501030c 85
    0x410741da02940075800034030008560464500c6400c43d43c02b12007065a6242c040703400064111221f511541c414200044140015400c00744030311a4402c20a5039212f100b20a01c2e110f1595603001c0320440700c2c010b9100e50001d40c1003880da03080382100d47e9104c0302c0b0b1009d110300c0e80b03010820038058403409500c200d9190001104c0b034034001151400400801c003e010300d94107012014028010050806d50401102c0c080014442048182180180704a401540e200d0400c40501025590b07541080c1c1d00c05400c0070418407801d401035a1203660301c4c1640c144990348582504081d24986510789035402884c40119002030004030210310500e1040911043d0345072a0303260030703050f01240150300900c0d100305ca4181091141c09a01c08002c5401c01000080c0304141103070a0018068070001d0f002140010f8000c01d208a80200c200304a103d003940840151103e5070400c000720343c1e6406403454031071164680d4000c2800340000306000001e960005001c1c1d0b41c0045804006031b020346001c0c0700854104070304035000100c58 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 78759624 1250 78758374 78758411
    0x90c0e19060e0102030f0301141c020105090d2901060f02030304050d0c02011806030615020604020d03050d1d0c01080f010b030103020607081b070e0105010212030103061503020d030203030a 83
    0x980140c86095005810518101c442c400310015950642c4003c02075580b410b030036000518001d017050001c07103040300c0e010414450480c1140d10007500c1581e00c01c0365100181e821109403144c0034420350b0081c180c400f09041000c090b40a014a080141902c8809400c1c0104402d2081d0b040c1d8075181c9801003000302c1c95100300c0c2d80744001ca03000b0384607800000d1202081e5108080d02c03178210340149002c141d001104819110040425440000440c2d130f5040700300a01a48400100c400042a0024105501e01600031032180200c0743d4009003001400501a0581e040310b60194415101e02d001519000036440407071640c604500700c0c442d01088074540003034408540034000314140c0ea40c2000c2542941d1a5600307209198000d01c00c00c0f9000c1c44148040021440001604845031500d4402001503618102c4200000441a0041c03811500490113008404540e001128110b987c403100001e480003c62840c0c4050501980001b58420303000300d403c0050560000240d801103036110010407a42e040c180b00c0c500b80 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 78760874 1250 78759624 78759649
    0x10501140d02040207080c060f0402012d0804140106060c0b060306190b06120f071103030606070809030a0b07110f0105041208090109050303100603060504020304050c09070e060301090c0e 82
    0x80050800e01005041c03e401600b803e900c1b4024260411070003400c06802c0000031908a0f1460603120100419523a11803800e2442400225995080c4041c0114142140e80028880303020300c03407828045010000b105854401c07072020000200655034403007500800b41400c000342078031038204510110b42140b401182440c00703a40050301e1044298505031001d006050106111640184180a00010046400001841448051342c2c6401d00d00e0150b8014010752603005456440354021320400920741c9400045440380e50708080f09035211100722001914080105c000104405075010a20841d19003040c581955081c0d00800e64007802d2035050194200c81003200d01610b00712440886601d0356026103d070a4000b1003440c00807412110035150349146900c1503451680d07800c80100f0401c581a8580708450160000300d03000e620798103180d11441d40e01d4814220700c030301c0f8016401c04074443d24050080910b0301d601c05414280c4943c1c1d40c583c44002415080f5a00021404080c00c0100c1031a2000c3d41411 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 78762124 1250 78760874 78760879
    0xf060b04030b07090f0b030a0e0d091a07060606020d09060314010308090303070f0305031e1b0325020307150b220e0111030610110703110a030f120201050114 69
    0xc207840c540300c030760307040102502c0201449600c04000c20415820714008000d0501c0700f00c02590ba08101204408482e0800460200742d00301582c40b8100ba80d0011014044804484604100d0070b07444803c640284605e040042010b85400d20020307a4a40200b00b440042c0c44036114981456552070342901603881c0d2030008004c1001010052002a040201812110303402400b00c070308044282c0d40300c1000000d42c4200360301045c03000c020043c0c20b200c0d0b1070302c140070700d080040405c0e001e051901e5000c10180b06000d82c120350f42004400140342800c0002500d103d45800881039850010351003001c2d40341e620080040d00d028992104410056813140280418402c0290600c0c1205150942c4069482c3c00c0c0d42034941c4a6071503660040c1c02400c24007d00e03400e40c0840004c60394074101401044000070001c2c20101c10b2050f82c0c06000700440002c1011400c81350020350454a02d00820b001442008183e08024080356a04400809100d04145019116034207a0001c108998903019920305101a200da4280d = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 78763374 1250 78762124 78762127
    0x6010804080d050a0f0213030b09030a020a23150a06090b0f10020102090414061002012c01111603020c0f0a120602071406090709050c04031212020c0c040f060b 70
    0x54070002d0036071003503502020b000301c000740c56860070b000202a41c3c4240350701c2400c0790040c4400d01c00e102c80c1101554103e60080020751418900e654069101c0d03640e51b0000e09a40d420110260f45031101c41e513440d013114000010790380070589180340c030007203004281c82c404481d902d84240071601c5e45492050641c00d600c000c203c8a0048000001c0040307111302c00c40f0315005c554084c85424229101c902441040d1007260a141042e45001c205005a01c07071844000300440e81400c04643d0101201e560f810803014a05a11482220b1201a400c5c0980705548121070202000a144041c92503044a03054055200343e0036a44a26400800c220b484030724881415480003039402d0401510034051004901c0328031512016040ca0369649951509200005400f80c0a070819001c00a22042c14001030000d07107403001041149040c030510b07451690203180002440e0084c2c0000c01071070365000d01116150b0310200c007815036a80c1e101c0076225854000d030603466801a0b0034072043c40302c1580280610400ea07080c508215 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 78764624 1250 78763374 78763387
    0xf14010506031003060e0a1502090105090d0f0506070f17010e010b07051203091608060408030f0406090204151505090303030a1805030a020102040303080f10060f02010e010e0105040b0601080408 85
    0x1003141d82c0003a2082c1c012102e140d50000c0001c01c240240c89031400d60714090415030b403140c01d10401000d41c200da2200300610410410b403032a038000d0241c405500b4140c4038010400114602200e20020521020b84140f061508219a00e13a0090324683d40b002c095803440c007446440078240078441001c0c083d100364259800c0052002c000240080e03c0002d0180f012509400e03072034415402c00d94400d80d0014010742100500407050291190000300803c0c086000341864901600c1d040761038000038296110f20321010010800784841030700090400340d0010301c10401049212a800c040e1030451141c11183c11207502090b00303c3d400b81080e1908440c0c040c015514580c4e50781201c2004200004d82500300c0151031141070302144003003000d840307504059000140d0350307811818080d0a000d0020b0141e4540038580c001c01942e0060b030003a003003c0703071041d0070034104d40d403103803001640580220f00e6251030941c81d100e251084400150041d0340524010b41e00c031312054035101700440b4004022074001c0d10703441d13040029 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 78765874 1250 78764624 78764629
    0x150405070203040302150408060702030406020604120e10090509060604030201021905070b0310060e100c02040f060b0c07300b13060e0f01060b040f05130612050d030f140105 76
    0x296601504500c192031901d80c80b0390004d004010150710f02d00001202280600044808100813500481140001c5041515140740255199001400101101a00c00d050b00d01c0764001c800b0b02c080c1100c0145040006c0091200003041002e17144107a9100303100110100c1c40b1401d000040742e007a2038060b07010300100030b00c7c1c00b50001c0b1110a010708440d00c0c45603120002e40d02943e2800b035070007081c01d20a448801841d14500404409051075a02c0c40f481e50191410b03c102e40014020300280d030b041c4d8021446000da2203803100240745940c040340c1127510018414000340408a100010b9406146043d40c1040103041080c03010304042105400080c458030702d541c080303401c02c81034540c82894060b40c90b01c0d0008a60310103050720002088400c182e803240801e070310011420b00541c40034020001405040618000054800c09840e05c01c090013425140901c240006950300039070003514000c181602c1042103031a040e69544400340020002918150542d000c01019006040e18002d50325a0010390703900345001c = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 78767124 1250 78765874 78765881
    0x4060507030e0d020405180105061f030f110418050c090d14030c1e06090d080c0d150b040f0e1501050c0f010c0201060602070b040e0a09050f030f070c0e1504 69
    0xd085a03c0f079000300540b00140c1d182c1c041c0354850884031488402c40c03801a000d49080d03c08c0900100d101b02c0e0f00000100301401200741c004011586403901040c0c0a802482c4440140641000181b0f83c800008011a240c10140b1000c100c941000d0000c003c0c942e03039460165050b0244000c560340c041d502e46008000304030103001e0350341c402e0510000d480ca0a1f26601c04145003071400390025610350601106800781341c1081c000035030b1044880f03010741440868000010203400000306000c0d042e1402003644920030b81654409041c80b064000012155603c40402c84a030360024440d04994007228a000700303803004400001401a51501ea840281903200c000660b04c0350014241000b191242c50740142c955182401030340110380040c0c0000510900b0800300905142c1e03150000108090100300c20404043e81031001030f48804040300c001000c500900d0300ea82031200b440b410301102d10012500055000d03042c1c00a0010301c1c4a80c20030741c4450795032810001d80c1c00013100c0b01510350407000e10002e0070b410180c2 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 78768374 1250 78767124 78767147
    0x9030d030b10050f040b0a0e091305060415061206140105030a1a040f06021317120d0914030f040f0f0308070b04022103041d090a0f05010207060608010207060c050406050703 76
    0x1030b00e0801d501da0b4112001a003081f5001e20015800315000702090a1091107107820a640070b038a40714500268030f03800e0303031880c0180000f46603a9043c1d0b5061a915003a6201c50058540584008140141800c0141c0a0001e801c103143c00c1030001c000029403842c0014050380d00360b034403030304e000082c0390700d16100720000c00020002c1e83c43c50401040c0f100000e10a20003000d02d5401d0b801d60f2440d5909000414590058001d007540544e801000360000401400050390100386401902107003a006a1618004400f2001441c110301d1101082c405030712880900980207968005c40c140b680da903070b903c801080a07911032001501031402080041701207190301040c00c4c0e001d40043c0181000001c8482c91901e50340c0e20b40019a00d581022400f4003441c003003456100c110380c04a9008101c2e506060140a8645c08440c0004011902144200017041000e4054900071500440b007000520b50307401c2058042d610800c411901a0f18007c0034100c2c0c940104151402d686c020b5843ca4200003169a0a680030b501c0da4 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 78769624 1250 78768374 78768397
    0x20319030e0d080a030f060506070602161a091510060509010207180c02100203040209010612090209160f020106060210020c010204091a09090f03030f130b0c09030d030b1005 76
    0x44003111961580c05003180300030301c611500c3e5640d100014008044070b440800144130142056401c10655540c1400d03100a03542181d401640c0d60759918000c0f00113400b80e50020600e50f103032a05160b0100003c560700d841014003400b0f0300c08500114540580c40c4c0030455509010402111082c0a03042c440c0000d00605c00c41030040f03a80d140d031102c1c3e1915aa101c80d504c441c45e0035856204150120b07906010b00e41d80b0200a150a5007941000d50005107402014011901003201101601300c50704402d40060040356000b0b003054500f414101e140018000b5001c190340041047c8000044955105116600c02c0322410b13405840c441d0325504900c1c2c00781d80001c00aa086640030b100124081e400740c420507031302001a6100804104424003800702e07083c1e00401d4080709820242103198998400f100722640540044288580307503440403240c0e0300000420380301a0109400000300b0503294134a200a2040003021401c8a00307441d9141d0084041e91030b0903489030f82040010010b60a0300e8025000340c202c2ca42c11 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 78770874 1250 78769624 78769637
    0x90f0721060f03230d0c080a020f16060f090f0510050d09060207060e061e1812041511031815031302030105240d06022503090e0114090c0d02071109100302031903 71
    0x20460418500382e0360f2f070f44405400340c45550800c0580e80040012004103035901300310200d0752515054508624031841564003070585000901d2101d4403441c00c03640b0b5404000401c114078511030030108000c1d080700008554042c500802d0240ca00c00010340301788141507800d0280a414040c40030510030362006032120003108030400c900e42c94040f0a02031200b040c000d018070b20b0749681c80c09040c0e084504c0341f81540d805005000b10b075072203100d9001c021500b128407030380b1103030000e8028003022410480103107818030b000c6940841408000001c2041e061a003600803030003400765860b040b50b8001801440007104186603290341100c0e4450070805c9800d50060b0280c07030014240700d00c03903108231280260b51903c0d4644040d2210705600f0035801901250281003551907040007903040c90701d510420016200428450003074603001402900c1c4980496109902109041d0f440e00d40c0345c58a459140600314180b481003d003000080c002891030704a00c42105d8000300100000d50003151407000f000f01c820401d5040006 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 78772124 1250 78770874 78770893
    0xf040e0c0d030e041b0906030e120c011509020f1215030303070206090f03180405040f06020a05070c091406090a0b04060e0105090f0721060f03230d0c080a02 69
    0x158032121407403181c007a4a8140b90020303814104400c81e40080760800603410f084402030840b03540408a081075410b2070500007a0002c0701315826280400c0e095800440c51000103401360034030313010740000c507aa00841005205542e00d0306224400da00a0a29501f00324006014041c0c4000c01100b8403604286008070388000e481340309021070308590044076a00e001d07a1054050000820081045150088803440030710f0604c1d5080d988040c010032640c0205101d60385134004130f03041c08110155545807a521540c1150f5810202a01400365080542c042c0c0300312441c0400040c40c16400d016a440d1104218100344040e078a040c02c00c850b100c006011002d00c6540c50b00c40c1661360b140c0e4894000030f003000c02807144441d03140c441080b400080003042400c2c0485110b060100040c1c20040c921014031400c542118560964007a070340082015512840c441c4141301c000005000d071103111804400c00300e5a101051080d40d010243d0f80724106c14464002940310f0040c40d002c1141c0e003000e4480d071100c620541d0b0a400c03 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 78773374 1250 78772124 78772129
    0x1d010e0406140315130201030b0303090a1502190803070c030903080c030409230c03090a0515060f1909050a090204050f060301050a0903050702040c1e03091505060f040e0c 75
    0x80c041d410419402100b05002c1d0040d1800b0090292480304900300041689484c0c007110080c01e03a860304c024189612050749001e00e542c240280d4003004005170102001c01e40d9028104a030340d9421020601500541c2001b1501c60314a20100c2205030b0000012480d40c0c6607000201c451528490301a0100b10f0402c40200004100c14010480303901048011520b86080c102080b0484803c180d81e0550450050310403041d522070a45201e5104007001c1031186c580c0d440003d000d05020f03410000500b640603014100b02c002e00d0f0840383c28040c01041d0780380443c4a41c10790501140010000f5803119180c0c02501c02c00c03c8400d02e4000c2980130400c80c070046080034055000c1800d41d50145e80744503080fa01d6208004907420240300d065442103040320107001e180c0d0b142c0c070702a14521400d940a40919214200440e0443c010030891030400b0030111890700520030307400c005000702629481240e0381c1d01c80e400001e407000c499002d10b42c000d0380c00600c40346100317040d40100001009014170074000c2d805020510703007059 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 78774624 1250 78773374 78773381
    0x11107240e0a1e0605030124020309030102040807031202030408030d0b01020111030f061e06040306050606040e10030312020a05041e230a080604110907020708060106030f0e0601061d010e04 83
    0x1400828043c2400c0160504410522a800d82050007040030a0004021110390780303025030200f200700f41042c1040c5c64041c0c412800d51081455150701503000003000110240d00041741002c5034080d143d01c114165450ba82240c403841203108111150340240000f030300c1c541c000d034044030b402d6205000000d00030b1141d108154060700100d4032050060869810400c1c1c0b42880e101d64103c20078421042d0078018900300c0028564011800060700003540c0d000029419104c0a040307c1c0a8003107011046145c0c5410300c801250f090700390000f14002046858078030798090443c0251031034295503031146804c10742400c0846d04500c2c0501d4844e2024559038000103a1b006904294124160340ba82a0740190841c05050120142c0940d00450f00c5510000402c40482c441311100081c0410403a8414520740303444004916240e41d58010202c140100b8000288003a05544018a071031803a20060100c07020f00e00410762144070920500300031545c503400f003004ca007404e03441040229205041907482d0210b07030313000710b002c4 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 78775874 1250 78774624 78774629
    0xc050616080703060305030f07140a0605061e0a0b030703020d0606050d0e0601050d0b090709020d02030a0506011106043e150711040f110307020705011107240e0a 71
    0x40c003814001010328039034070525090b448411420240151861959401d98030702c07075401140400ca001050301401c12880c90309800d55001008200d58003005141880030080c00305468141c406c56500190b660400c5000040c03910b06800109072442c868600010000e0fa94802000c601c109582008141c00c070300c030303944a00340140c05980d8039a81c0b14199001010119a2201860001c0c2d501002c0104099901d200309030300307580e502109164043d15402e01251600140342c01c05004540049075000844406034041d501c0b42100000901c503640310340e0700644084020324001c0071107400000000c1d0210740500403808048819a101c03120b521107001c0d403110202001d8180451804407403a084e0309500d84041c61601c0c6103940020107280050503991443c0d10544841c46034026078a5844040b881d0346154400302480013042c101a0340e0b0310303081c1002900d400c450b0207000d0225000c214450403c100005aa10642e0240703140142890701079a041e0380d90403034032604a4204044080d145005881e1171204d10300 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 78776980 1106 78775874 78775891
    0x120809040c1106010602060703050c040503100c020c0d05070e0a1b0c02010315140405010e01300203160e0708070504090209030c040509030901030608010b030a0209070c0506 76
    0x21041c0c040c0c02d400300c1900443c070002131000e0300402d00600c900c2031682d040107660344288030502d4a000d0342c0509034040d4001c0051145804041d070180c0c00f16240d0380101c402d011801000191202c103044000c45032070f00b00600801090b20560505a000703084160240074000220048000f40c84c108030044007008050040d80d010b43e4000c0e841000c011080c402c1c8011001d4807800000e05200350101c0182c052460b02d0000148030030300c0a8214143c4a20351040404000103d60107801c214180d403003070364180c0b4412101801a0340820500b641c03d401940c0740a074aa24000c10504441402090b09091050860400800c41d600004490a640c07101600589a2000f1302c08241303040b0740801055081882e180074001003c02c00000b82112190036a01444516203ca68403420b980e01c104250740c01d6400001ca980040c502103070050351240052400356041b02c0640c4500749044025601e542 = true := by decide +kernel

theorem cover : BRFrame.Cov 78597124 78776980 := by
  have h0 := BRFrame.cov_init 78597124
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 78597124 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 78597124 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 78597124 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 78597124 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 78597124 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 78597124 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 78597124 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 78597124 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 78597124 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 78597124 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 78597124 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 78597124 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 78597124 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 78597124 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 78597124 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 78597124 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 78597124 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 78597124 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 78597124 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 78597124 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 78597124 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 78597124 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 78597124 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 78597124 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 78597124 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 78597124 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 78597124 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 78597124 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 78597124 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 78597124 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 78597124 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 78597124 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 78597124 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 78597124 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 78597124 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 78597124 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 78597124 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 78597124 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 78597124 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 78597124 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 78597124 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 78597124 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 78597124 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 78597124 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 78597124 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 78597124 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 78597124 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 78597124 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 78597124 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 78597124 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 78597124 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 78597124 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 78597124 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 78597124 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 78597124 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 78597124 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 78597124 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 78597124 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 78597124 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 78597124 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 78597124 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 78597124 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 78597124 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 78597124 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 78597124 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 78597124 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 78597124 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 78597124 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 78597124 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 78597124 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 78597124 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 78597124 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 78597124 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 78597124 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 78597124 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 78597124 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 78597124 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 78597124 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 78597124 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 78597124 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 78597124 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 78597124 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 78597124 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 78597124 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 78597124 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 78597124 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 78597124 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 78597124 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 78597124 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 78597124 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 78597124 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 78597124 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 78597124 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 78597124 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 78597124 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 78597124 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 78597124 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 78597124 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 78597124 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 78597124 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 78597124 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 78597124 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 78597124 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 78597124 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 78597124 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 78597124 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 78597124 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 78597124 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 78597124 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 78597124 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 78597124 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 78597124 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 78597124 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 78597124 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 78597124 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 78597124 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 78597124 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 78597124 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 78597124 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 78597124 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 78597124 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 78597124 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 78597124 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 78597124 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 78597124 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 78597124 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 78597124 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 78597124 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 78597124 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 78597124 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 78597124 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 78597124 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 78597124 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 78597124 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 78597124 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 78597124 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 78597124 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 78597124 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 78597124 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 78597124 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 78597124 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 78597124 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 78597124 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 78597124 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 78597124 ≤ n) (h2 : n < 78776980) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
