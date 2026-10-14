-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_3449
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T09:41:29.628986+00:00
-- url     : https://prove2.me/submissions/d8509463-d99f-4aec-b15f-1f9869e3908e

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 620143884 ≤ n < 620323741 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 620145134 1250 620143884 620143903
    0x207120e0f0a0302090117120a02070807060c2d05060a0e3c2407120902031b010e0301020d0b101d10030204030f06060302040f0209090c0a0917 63
    0x1605024082000c1c010300110310310600c0041d5000600c600100701c030000001c034191410011000343c03085000a4500100e4552002c8800390040c0e001e81d40030041500d06001c28009050140713402100400c0d9511a00700800c140c6408000c540280002ca038101110209a40c243d180e01c1401d80300c80745021000c2d8070041040c00c42010b400d0203045400342841c0c15050040f5182658095030b4542008041d210351400c4081881003c04c1d8400c3c400000308144412440180064101c0d80d4440e0f00d1826420040802ca178107a0b80301c501c00e0401c0341d003500590300495403a0714500c0c00d5400c000c54000399001281e03021b12070341c10b0941651000070300c103011200c60382010010710b1083c4d070a100d81c140b64001c1107410b903960380035070421a60410b8041d0460702c1c01320741071054289039207000350510b5280d80700daa5240901c4407003218526502c1d803007001142460b004102c65120a0501141000c02c001c000c58038116000304076189102d40064802e440c03500404410001d170420048460500104113074640e694204103 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 620146384 1250 620145134 620145139
    0x90609090a09020a120302060c0c0703050a0b0108100504080a08150607050f0c0904050703060e120406080f0c04050a0605070c210510021908070c05060a0b0f1c02130207120e 76
    0x28000c51401010408172424079030540c01840c0640e26114590f0050b0041c545104039401400000404103504021540005006519030f000071f5161a402d00e2030055003500510219040c1010480418030040586480f22001e0500c403400e0341c0e45108951814260140710390380080c000c078010090000000f00840032035044d800f15a0300c200f0700000c2140c0a0700c1200c0c000d000e90701955050000642c641c220541c1140400d040702d00031404e0b41c20f02c1546421230b42250001400380d000f0400076902d0314100d2504452384200b80c0703240508020114120342500d01a05061100005841040040c00342515004140c0ca0070540e00c1044503402800c0003801c50742d403c0c0ca05201b0700c4002d0485185a00c01c460b01e400404d001692820132030181a621010010141c20074081d01810740000704000303015051152081110004200d0b0351303001008210602100d109000d0817803101c03690144000d00405059254045484090500002400001038481d0103c01020980070a440c81d0720950002c41d1192400001c = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 620147634 1250 620146384 620146399
    0x14011202130204030c0b1c1d1608060c2203080a080a0e0c01030b03101b0906050301140405270a020f04090c15050c070807150f0212090609090a0902 65
    0x30075540c003059024900015180c200b021408001e40080040107040c40c6d0401e046040719a5000700c0d01c0b43c211440d4014548500044030042501004184100740e0360480841c098803100b428405000d5131018010b14015000c4c40001c0d00300c01c0041c4508050b400703000d000f600b4140141d1240f505000035084080300c2800b0584040c0842c40786c8801e40a00c68076024542c0041a5030302200c80114003902c0102d03a02605800343d64400301c00880b25003d1030020004440829252032420707840188a13040030392044d010084188014840b449101c81580c00c1d19204550109a40e10307000c0c280112005050684060ba000314405104070000204402c2040c034002c0350310b045806960401c0c04141d81041100404016140c501442100c2000b114100c501229160503030402c01c440ca0042d01c0c0c1400f58100d0a000e0748100b02c20002d80c42c98681c000030f104014507105083c00401c0c20081d5a4032080c03420f402952402141710403542d107440099400c01c0d40300801c442154104581407100511922001740d000c0c0c1c0d403 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 620148884 1250 620147634 620147659
    0xa030c150c0f030503060a030b13110f010210150b0c062203020604060c0e130203011818081c2d05070c1e0803010b031909030503160314011202 63
    0x4070001c020090b041002d2010b0280d10366000c460662000302425405101da42c800b101080705048410300c6191000000814480e05007040491001c0616900d4840c2c2490800c4600b281da003c1078080d0586a14040428403810440407030b0660030541d0001c140b0340002080c4001030080001710680250828082100904c00c540760405e20000071400180243c1c0c008008100000d032036a215a503001800d1505103413800005001800e070070700c98078201d5100c42e0040010301440503507030b010304800038244030100401c4164039030690340c48030084406480c900c0003049407500182c549a01c0784200140350401c000d02c0c101c0907241c019002461f0001f0b000c0c09542c0b0b0f01e0f0b250141251069a00a00072522449450031f110b41d01c081440c2c001c41070101c2e080003042041000107007554043c40c085d00301c4058040c0c80c0d00d0b0400f01401c420100f00d18100c841b40c28814002c1c00f20fa00701d8110782d0056251418504c0c80a0307208025070262820321007542d140d030384900c000613a28007407452104202e842200d044100c01d8 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 620150134 1250 620148884 620148887
    0x50102030405070e0603030f040605090a03141524010507080d0203010303110d110c0d020f03060103030c020127030f1e0b06041415010e0307080106030807020901050105120408090f0a030c15 83
    0xa58014680c02c450104418070200b40940d010b01244072000b0511441c081c1c0f07940e211120520580d003c0401070b43000c014402c14000350942110381c460749070030451240355050100b62404041006041e414814000385400c2400b940c002198a030480e01c0c08203643d80c4d60340e8030700140001d64903c403180007401186d4400b14040d101da618036211070b4158005240e1904c01310100480004058000c982c812000d00070010141c41c2070024a0080d4000e444046149500380005815400f448003410060010054039540c0700d07042101d20b0341640d1f0010100035a0364542d08d0300c44800c001d000380c112005440d59824a04103c070300c030342d190711600c0141d07803d02c42130208281101d144403042d640100e051025071560442540300c4c1401c2036055030001c0c1101e0115540b8031025085038aa40c0098a21440000301c04042d030501042a41c0140b0b028038009280c0006140301c0b402d5400058001808048001182c048907540d603681e084448100601c50900c0c01d40da4500707460040786500c15812400202d69481f150709 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 620151384 1250 620150134 620150137
    0x140f030105060d17041703040816030b010603050a11070c180209010e0d0f150f0c050f0304020f0307080f01020304060e12030406200307030b0a05041a1c050102030405070e060303 78
    0x102e1020b800c0010092a90742c07180404401140600b101c848180400a00120300b0b51100006c5400e0001540e038841c1090308180c00c1c900010208000031400380010000240316460450448081d4035002a280c1c440c50310803801703080c01c01d00c015400c82012038000244102404090103d81c4030503c1c4c03200b5400318441c401c00343d0040c4505540400ca1507440558141000840c0849151140011000e0880103607541e04031003114020401410b5620554480000110300c18680640e80741d050242c1070171004c0c030000c10a880001c01c001c0c0211003560b0b4000b4030784c4041040c0c202508403401038940744021244168000d40044400703480860070801c840c2807900000ca1800411410003000624540c0c460729002d010f031084d0380e03c841188002040c4101c1c0c0d0031000003c0c1d4000c1c01d16070390116400c044030b010820f80441c16080988a5440e0001202a0003851a001100b1540c103440da12030b040300c9500016440310101d00041e000794000402c1108010b8040390a0054800342d141c801101d031100b405042d944d = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 620152634 1250 620151384 620151391
    0x607031e050414011508060f0417091f0f14070201020307080a05040e0708061807020304090914060a1401090618020d1d030c010c02010506100e19140f030105 69
    0x400e03040c150062414581d0070166105004807907495214140b041c04070708440f00001d11106444c4103e07004d2181d203c044c001d5923080b20101e00c10300141e0900d516130400e918543d15815480503400601c010340380d19503585820741c030107484e0303222a8110703009a800b600c05850880c41400049110a081182e15808800c0d55041901039004504107000d641d61401036501c4007a04070207000c0180000244d0030204400c0c0c6116814903078440780107040681c14454201d03d04030304805280c0565080044c09a40001928211880d058001c06d00900c2414000e50701800c0320304210090241a0800c41d209555030404080112024802400741e0390700d64000080300c025025502c548000410004099011030b00a001d00100c0f007140040d81400e0255152201076041101c82e10039000443ea0115070b4500b80300c4c2c4000511540000d000900d00340e000501148001029002803000d0010b40407400d8468564055102800000d40b40e107403600d480456905103503c5041c00e224000007091500139040c1806014007 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 620153884 1250 620152634 620152661
    0xc022401030b10090e01060303170906040b1b0309010e0705030312010504020304140109060902010305061c1217090c0a05060403031d2206050a0b130303050c03070210080603060703 79
    0x2016421942c404114960240c444250288140760108084240344140d4964464a6000068852461401030050320003580c0b2825404030900801a49040204a00f54820f60110304102c45a81e1007107482c280d0104c600c1c0ca00c010203404010030041000540c1300205e2100360b01c0071038500d1603692042507aa4454101c09400003840d410041001e070425030080c0d60045c0c4036445200c41907200d00141802c580b10000142ea65603150030104003556054403405800c82c405450791413514a19401c40901008910b1004000e4502e400c84400140d00c101400e004e03240819204102e54140310750184d50701c400a040240c8110143c21300000c0c0b916291045508490b4035441c0c180507460f004075200b14100c882e111540d00403403501e00545007070500484000c0f04058603600001c066080209200b40707131034243c12010f5002020000b080b54643d080e502d40e0304403989450300541d6590240078180c11406842d44c0250002c010b25400380010f604404003501c1060243c080342e0142c3c0e1041421010b64400066804 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 620155134 1250 620153884 620153953
    0x706090f082e110f0a0e030d0c0f08090d050607020106060302090f060c10151809020303030f0a06050901030f03180b0f1e040f2d0e090a0203010504060c02 68
    0x1802d165403441d21001c00d184000001400580b003d4611100e50711010030a078004600050032207000b90003183e060f8107083c0a5008007584038000e00d0107880c4800d0000701900e01ca0b106034015040060704401c8603200440904070b0002e004903850f0050351040103a44031030265003080c6011440c00d10a01c2034400c2960001c00380440d0385001ca092041d1540b04134401c0c40d03280038400a2040007031700c5010b11a90304c03119100c8540b00500d040102d8601862403119440050304095890300965000400d882d007241c0041d415007001d440e007850a10081403d94402a0403001c103a0000041c450b251030600c0d0400d0080d158405200c089a424401c402d20b00e00801900d91018422402c01e2240741024041d02c00d00700e44602089160354208030307070a400070b6000300d01038040740009210300e2443c001c84024020380041d02d90540daaa490441c1d6085c41340b80074a0202e04000d034000f5a9600b4104180340400e0780190081216041a0820b08090036030182001c000d8850400c000d1115a210754031950743c243c46a4610 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 620156384 1250 620155134 620155183
    0x60a0c1409010302130b04050a05040e0c09191404061d070b2104061b0c0803010504020d1409150106020a0201050d0b060f04060905030d050403021e120706090f08 71
    0xc0354950000c0040a04040d0301340040683c07210448210005003080301c01c00d5482d546480108040d661040c1c00007401141003022a00040c07000141100c1450302c120f40d4000b880c0c0e6018000c010b00b00c0d542ca01013001d94180042c80c1d103802c1017078071030030b0040c3d020366800e0040c028032022404c8081c2c880b00180403117a001c5442000b07602030000280545081c9030000c03011140440046078a40102502c05860103995108803138040e6404c41220550450a818100d4443c11a80c54100313685c001446150b020310b4000903d9107601c4900e6005100030070341141c0e40d03021400d0101090b035844003c041c000003660700120010990f180009079180f0540d50503551075140110700542003014000d00301c03580e03030410400c0c80802003044c000c80140001d0120b55903001401031070302c0300f054034041d40c803640d11040c41001c00c0148003586070504240d40740c85460741541100c020740f001003010034446804051603030058007404518507500c107603500b0855040540c0d414440392108400360301d9002c112400d0b800100062010b = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 620157634 1250 620156384 620156417
    0x6090f04020307080a0c0504360510051305010606090b07080705071d04060501091a040e0705040f0c1d01020d0804050705030a060b011107061b021507060c02060a0c 72
    0x219403051015040e211100d5072260310510b0009100411a81c0c04a114001e128500b0240308800c054810004072004200301118613020521448032584d8081021a40010030f0000820590348844d0288400700300500c0d00404d00d400d9414000c008451035424050000f0b00140315201500c1030302c120204c0350307203070091030b54031034196a02c44c41c002c030740a008424002801c20f548041604040790038903204182c2d03240c1841c040c0c007124416000920782030f02d0300d24440f44281320b81071900c078280c034160740006401140101075407a007403903a80710b29840381c00d00c040e80008110719080046000f000ea20b030088407100c0d00441140c0c1083c03044200d07005900c5099403c040343c0c0b2803844150850f000310195409951208007103400d2880c1e0840c19920582c4400d41c0c800306590040404003450510300c041d0808609100000b0320040043c0030001d14160141059030a544c1d5007010b002e12540031200c1156a6161403900c500500000030341207002d402002d00042401005004a901d0003c0d940c1e075040703681048004 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 620158884 1250 620157634 620157661
    0x30f0b090f0c210a1d060c090d0302100c021b0102010504080910051b03130501050c060c030a02040b0c0609070f0305150a140a1a100e0d0f050d090f0e0609 68
    0x16181024900c50a2100309030b8203c101c0d042c001c81c2000c40c049581102104864a00611a0101001070344241e003003000032a0031606032004000111020400d00d800380c00d00700d00d845040c19401e5456441c020324040f2803600043c44111900481442820602c4003900585c203c4000312005041d24908200320465803405100c2c80c0c030a0101401d10505081c940d003072003000c00c40c0000e007444c0d296000140c0c2503070040410401c880200030901e4007901d044428103580c0d0702c640c009445007920b084040041400c0104980646004c2c0801111442d2110f101440300c0d5501c041c180c3d144006802101001f040d201107005c0700b00300b0b403038001004258032814901003600061000388503000045e0340d4501c18032100c0c2c1900d041406031040034000b080e03000c100100300d4500c4003280445031203007940d02e03070306100160025a400c2c2113034001c441e6006000f07010f0138950810b0200001c010442d002d40106840906d800c202c5440a0790650600b40f5912a1240c0710fa2062040640b20181e201213180c00203030445200c0031 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 620160134 1250 620158884 620158897
    0x906090507030827010c02010f14070b040b16021b03071a09040c051305040905030d02070b012907060b0d2f0a0e0105010804030c08030106030f0b090f0c 67
    0x51912110340300d2034100a40d6400c01c50340340500040012401c1130708490364640110380e440124200c50010700280110a405400a040c062408085400540225018280100d05007000b6640c0c003001e181006400500311000c60360300c80d1034004a0180c0c041d40072103015100392a0003d200045000103400c511500d082c403103903031610590a000c0b43c01018880b80c00c403800748100859480d10211000c010645007689206801c105040c44540020249610400f003118415600003d4101e02c40c10464103600c00c08032204000c500000d9450104115403840314100c81000c500204c140030103144510041000c814080356440c011700c1b940c2c000c10306a40c01000340c040000e10f0500050040c0d52110f13558210220b032000001403071000b02c602c2d56959510b007080c2020480d40c0c03140641c01d0400480d10300106001e514108401000003504140c005c9525031402600001060f441e51b0f50b4840041c082c150392100102000d0400500400500340300003c4c500900c020200c0c070704940c0c1c82180645054000c00d = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 620161384 1250 620160134 620160143
    0x10b22141e04110a030b0904081e0c060705070309062105090c040603050c01090603060f03080705030f070b01031112060109051302041a0103050903030403050a031515080402120c010801050409 84
    0x105000c0c8120307501c2d4425000000c8090038480d40354104100041d01329032405005500a00c59141000002a184021240c4449030100d40c1c04080303c082111522078082d14107840000c1c032510f01440001ea4012003e002441d100340d680e40202900d54a040b15a5541c440308188501148404401281c2c1641c00055100d24a0740c00c4903002c84600001070103a030300035401951540c000924003a50703035910600c140098400c6c1c2c04e00340044c521705010b503824414a4400079100e51000302d4440100b00f0103004480d0444160702100351151440c0c01d000c5030b045005e110031542ea0606205209103130800b0100c1024010001d030180425a00e001c407250060940200070318103040e880b11018005944d944507140d40303030f00010000908802c00c50005412030f81c0240110b017080c3d109004000c0000e501c881181c4444041d40b40226800003500c20241038901c80741c1141c1382d00051300e240d249100c1da1264070240308500850342c0851130008015100d858951030317103046001640320001130005d0304054112000d00c5116 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 620162634 1250 620161384 620161429
    0x12030504021203030f090d0f020309060702010201060b0f03162a02030f0304031a0a110f09150414030d03061d0405070f0f030606080c090a1503020306010b2214 70
    0x741d0b4940f401c6034811070781040c6a05244050107820345007086180442c5071030742485005103204a8010b9524050300d0f100303d11510001880e102164400e4001d000100303101d40702291907250004844c1102d410440e10a000390586805c1807400d14410304801d180501c3c0e90074002d487d01802c540c6120040e0305100141d03010312038210b03990039000d4104010300040d8024164001c8250400075054a40a40500750f030448a041c01500c0120003070346c0046030001803036203510f1652030100a005c40c00d00044011f2204a551003c10b001a0f04074102c100101600d07001c40c10b0b504510ba20010940484080e40900e00c00700050b45c2036141c00c0b049511615800034052012116060340da8003034a0550b042e6500610010724408030b0070000c000090058402606d04c403806828100c1c80100424201c000c001d004032200c64680c00c4281d90340fa05094810003941e00503095480b02d40e110400c1d150300b640229100c0d02550300c2407145040ea0402040184e00784c2d8040254200d0000b41d00c0e080000c8800d100c0701c00440030b1103 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 620163884 1250 620162634 620162659
    0xa0509190b03090106051504050a060f021c030c032306101e02010606021005040510090f02090c090f030a0203030702012a0f0201030e210f0c06240307031203050402 72
    0x1d000c0265114981890001ca80e160401c400d01503540881191100800f2041c4400c0c452552a040c0d05403c1d01d2051601c01103010111000301c0c900b0b0582d428240340c008858801001c40c9515410201c6480c843d524240a01f18040d24400403090b0b203440f070b080c0000c040da00815210306d44034a00000c02e0704c8610b0100807010f404a00e0070307040418426840050303075551204005242d0140060519140c00340390410861078541c0f80e10340c0740e0111070440e6064980e21034a070400c00ca02804c4a841c8140c020b8000d10803440d10461203240b80d07104445052184d103060300d11100910f03001400c095500c0e8050b01440c1003800e1903006403441441c0795170161000d0f02d0300280d0601d101c81c107040601ea050052495810340c1c6281c2c00003400b12400c4a900c0e4440d87c001460525114540e5400616056814070006079070780c0100c02400c020b401061100c2c0e585000710750921000700c50410006203450084019802003412400402d581d640c005c1c031000b4040181e800d0184000c03802036101700e41c01400136041803054031 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 620165134 1250 620163884 620163899
    0x5090406030c1e1e1e0803120f0604020a1e14160201030506040e210c0d0509040608281109040615080d050f0d0f06150f050a050919 58
    0x4426004091207040200307003480d42d03000c0950340c00000c02e8408002c1e09001201c9841350000042809003442c0c400d4205001c182c0b400003103500e04020441e0000f921349840c403501d044d061110040d9103141280408801240d4649800d1084869051081e00d61a510440791103006118403056010078041c40030410003559501c080c00000c0ca00e039001d4400030205540540f0000d0202c1d00301408042c00f03140b501c4004c000c1d5100001d0080718071141c10140ca03400c00f4243c413086106108084101519001d58104c81411582240180498402c1150705000345503c03180000d5a6034020960340b150591020590b040281880319010181d501440e500407403a411440450000710003a07504580440d0f40b60441042405030303603104d04c0a8119480581440942480700a0040c01205000038503060002203071507201600307610121620b449207400340300080d50f441601505140d034840078004102902e40d9003032120f200302c044480c0c131200741c0ca4880c2806101400c2c4a01203044c500300018242030401c000c00c105 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 620166384 1250 620165134 620165153
    0xf1018030f0507081011160204090c120c0b070c15030f05010f06120c0906120b040e0a0c0f0608011206090215030a0614031203071e0807030515010f0509040603 70
    0x542c021401042c190703150052803458003400c40100e080f150300d0329090741c04210b0f4884c100e515881d0b00d034100f42c20550341400001e00403e02c10b1401400282e58a4002500a0081000a81450086810700c101544d10f0402209505c80d40400420b4264005006d014159030905160203001040c0f0740050300110564808040324001c2e0401006003086101c200b01295000340c21490000000b40240598001424064034403003950050006000907001c5c3c100d0000d900f58070500e07079030500510900c10340e544520800e0300c800f82040150754145100601103a0164028082c0c0219400340e515241386078a00640d88219245140c1c046407180d0b110340d0b510300941d40d1010b000f400c0c1160180010764904260005004483c42070380103000c00010000b10050566020070f2402d041780324400040e0781d03039071206011954090314011480c40d030501d0850360040c0703130b9019045a206504a0b2401c00c002e4031007210f088140181024040d000a007101c8078551958406c0b030280a60740d1025102143c1c1980760b940340c801c2c4 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 620167634 1250 620166384 620166413
    0x6090b0a0515070f030810090902180612030708030103120503070207050f0d21030e0703020f040b030c101e09080a1407051c122102031b0a0302030f060f101803 70
    0x1401c6c09040c88035a12404003084020b20800204015540c55036010800c41600380b00340c0440700c404440040d0071511401d201c82a11a0000306982c0d58600e00e1070603189582017070000f52224003c0460030700802d402441100d0080345280c0042050625000400040e5590034000b681c01001c3c1c000d12800058210105082100040c012102480c07403028005003111a804440e0b5441d500801c402c0026855881100e540072400380c40c08141e095024003c1303454030b0f02400102e9004410312540c45003141c0d20005030010501890691962201e202d6011103407610f0030700900c0e071660000715601c4001000194030359007640c0300800ba96015559200002c112226212190640c5860000755008104807103441e5403401c0054140342c5100c1c0a08c0d000600201d0030860364603c010341c0000403030300d417410589200c2039000000113255038030114924010040e40080d141310228500010200d8410300d08003010707414941d005800e035950200740b40012200c42c0030340754406c0c04400c241100403000c581000144079a = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 620168884 1250 620167634 620167637
    0x3020a230f100c2607181d06041e0b06090603010f1701020715020702030a0506070203130806090604030c03030f0f140901092103090b1e0702060915090321010906090b0a0515070f03 79
    0x40747e03480842e11109210f00800701c43c0b00703902e480100721900202c2c451903245844210400104020102d0116000e13200320008680d000501100025080580003116015640003000f1803540030103214010f802c0c0d00a0701e10046c60300515140c040e80c3e11016034090000240002c04840e0348286c242c40341e9080840545568005030000600d0005c8054000e000f50010b00d5410028082031405070380c83c0791070f5000604020204588025080203252080c3c006240141c50804108810100c0c0c1c1e4001000f00b00290f20001d181d0100400204030a4040c403d690fa000c0d008500f110080c0460a14042d01c118020004000c0c5591002564003203140001040d20610f0b84c582034451091101c1d080081070b4a006080b1400c40d401001041010900425080020004c540004405840700b00825085010b040703070084180c03411000c00d0a05031000d14280303040b10452642001015141d1b5810401e039010112943e401800a90f03003045907040c095901c0041c81c0080310900d0600d0312565800002c4e008540d010760 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 620170134 1250 620168884 620168909
    0x6050a0509180a06091107110906010c0b072607022805030c060901140108030715291212041e0b03070f030c080403020a230f100c260718 60
    0xc4583e03551b206400c56014410400c90038801c45917a5010962400d030000c0740602000004a2016401100c030400b00741da10401100d46d80c50042d00080428011940c1c00040501c10309071000045403035040d940c011800d81d0f0107407100c019000c500500d010b0455010f982c401f07a420b6240d00c013040092000e4444001d41d50098517031070030f0008115003942c05281c1b0581160182c500100305417100082200c004c20b50040880c1103801c42c401e11000104090503881c61000350054a180d03102003103180c1403140c81021203141000510158040769241e810300004c8280c03076070400003800400203d000c5542c2c5500174208100c075843c3c0fa40c0359009140c00c00d031002000b0403071080c401c000c210342601910000070890301d085007403440d040d20300a6503200750040c080c20044c555110030003842d11450038008903105900c01c030740140005154055513041d0028a15400c1c92901103200984c07486100250369480f241c030100c5411402014601c2308034440a02500103000a100700e85840060f482c40c0000200320380340054 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 620171384 1250 620170134 620170139
    0x304060806150f04090905030409110c0f0f1e0c100503040b090c010807270f080f07141c15050a0c0f021b0f040608060105150406050a0509180a06 64
    0x4945216506054404a00144000403400c0c0f4010203440856181c2c03900481d0100031070a00508506ca9504415003680c1403030106e003030003440c00300288482110b00007182d40c002d0404200720384440e691803890300e040e04900d110701d138043d032a0715030901e17030f1021001a60a040c03520000a03130300c06040f40352080490b0001c4200411b02c03410612460740540184050f00d00c0c0400c8a00003031100100824540a01c8100943c1503002c1501a401070840030503000c0e4004900c1d110000c03402c42c227a132846601017034455603840901c0100089100750858640d801141a1800d0340401c002c10f03080d4800d8215045c20881c1c00d680003040c1300001e061695100d40f600003075141003019180007554508090002400303032240807039854a90005285510080c030020b0740c012440001e000901d02031681142d6580306051620101d008100412800e048030300c00c44001e620030511072007a54540c0a288a0140425824070164000c0c502620003041020700040100c030321700390301d861045401c0ca016030b036441c0400c1c0c1d03d1009 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 620172634 1250 620171384 620171389
    0x191205070f0602101a030106061d180402010c140307230a0b0c13030203010203090601170a0c1503020919080105131707030201090c032004021c1d0304060806 69
    0x2501504646900300c00142c101500a583c41c010100010710303060f070ba0907145034101c00c0310b00301348111403005009128440d0fa4100040c004014855074401d00c0c0c80290302004a03240c0008040c2d0141c107800e03c20792942c1d40f00c4d00152481d000c00c080030307921086600b11100701108240000e2580038800c4148107100803e000f1390840481060b041c00203242d011140b28400f1031600e40c0460751001035a80785954504409840396112046940000d41540c004000c0c488075900202d21941a180314094990222140600720b039610080044041c0182960102c140840002c140314407c82110604001d850031034104080740b50741e0071011428211000340103060041150038010150003440030340040047c1030f0a91502c2c510020741c40b00b000d0f400580002c90004050007900040c010300e81054001041d1035990514001c07003e00c050000201c402c45482514007460140300b03607205190980d43c01500741c81858074140007411120481c003140c118814859140d401304100400241178a0b42d103402950a00209 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 620173884 1250 620172634 620172643
    0x31609050c030112060908040b13140d030f050306030a0b04031110050603070b1c0e07080d03020703080601080613020315010201051005031f0b0402041d070305090714191205 76
    0x503051500d4002c00041180a01800d04800403641103640010381c0301c40c03860040f1640c071441c3d001092200002c20030840c0301480c042c26070105e0703240c01c00d45299044803008000c8941104103008001c00c0044841c0c1d81007920400c051940300c2c2c4040d00b190203841d0385880344d10607510104c900b00c0024800101d81c01441030240114404101c028a041c000f0b403c107000000d480300da1a01407105440008200480502c1d86580c00e80c42c21070100328100011505900c1d1580c403501d032405090f109119070074015010324420b00c00c44500075015602e01d0308684540004460b07500000d8000c0c0ea0000d44005403103070040880c8015405407205006851000e2412000a03007920f20040040e5080400c04104000c1e90b02c0204000c100503054482004041040c00c001a00a003248503000341c22070701c082004259100c820296420340c010702d2004800036038404000318160395048443c00c4082d0050207040011800d2442c45c490030440003044a04000341c40300c51a04c609005500509032051a01c4030304c01840428407 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 620175134 1250 620173884 620173891
    0x50c09120d0504121b031118040c0b030403020322140108131101110132090c0906010c0605040f02011e170408070213090606080f0c09100503160905 65
    0x14007800544099080c003406500680c41900b04007800c142d400c40c03c02c44c05c10000c40c1480c40d404054400c481c1c803410030740070701424202c1441c080c40040008044121002d00c1d25403286901c03803c100304250503c2280c01d0316402c040d00c1202544003d00107410b80a02008000c050360f00400c0d00b0000003031801c8410000000ca40903036506000c81a014001c02503e100140c1c0300468018841007448041d210040300d4412218030810102e52070099154045541038050000d003030110b0703c04001c0b1000c0c000b10819049000e41e29641298801440c00415090181035240c1c40071050400d110030900707944415068070005c5504841c0c071400c009a0344c0842d030b00441c4440214503000e4065200c03411306103002d031403103640f1160080341842080028042084603821100c1030355014103851b020201c0b0b108040041c0445060441e1410305091011a030b0f004005180324240c0306140090050340c012505014a0507006082d03181006102100410780d91020080c50b5002c960200c1103102051a06c01c8074001c540014 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 620176384 1250 620175134 620175169
    0x4060509061012061a0d030201020309010f05062d040e060a06060203030903030a0510170607080105191406130608070e0612010510030608120a1701150c060f050c09 72
    0x5540034440c040c400f6154550302c41c1d00000c0000c05c020000340301d04a041c2c00d00c0035103a02103009840e110405034103401450042c100f0100130301500d00159540d2040e214119a4580c200c80c4442c0e65554043c05441000300c1940ba100350003e4103400e0501040580d5050b82004041c4d500c41011700200745424400e48001340300e9403024609505094801645034031018004c0c40895440e50007240e4107028050303c51000700350102d2080b07100e21000520503260f84040341e03046c0c0868900c0000107004d0900700410f202c8036403003114005a1501301100f8900500e80c1d003074840d0b0000d0301071011440701c12411030b03130f003000c0c040540f108079051800540040000410500c4640980030500550115982e018003a41c1900c500f02c1d4501d0540c616928110000e20b01a40b120340c041c0300d8a9051a401036000000342285130850703072200d01c181c040c0820516201c0c800e104e501c8000e03a005111600c01403080b40c0040b07000780302e4031000c25264120843e550660f1402d0702e801d0107001c4001600c500c1858075805001c040000d0 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 620177634 1250 620176384 620176411
    0xa02183601033c0303060312020c0109170a1401020309060a060305030a141207200f03030a020a050d0e0309130c0c0308100e0f010501081b0a0f0e090406050906 70
    0x107540d00c01d006020302030300040b048032070000d040c8040083d0000c01d8041d07030449001d0040c400c0c560f080007000b4041601c4140c82641d40070068200507407005c2a18146042c043e12481d011a1800c202c04144040400c001c450754060041028002100c4e14511829540184005078583c00c1c2200c00d981040c00103010180a140380903410000102c010080d41c080d28943e0501d02102e204401000c00c50344907100820304021010810030442c42c0d0841102421200c84104180b07400603405175483d0380e940a40140c2620303920034000284400030f0380c1c00403e11000d25152140c10110342000e41011307101e0459505402e9000455013002c207040030f01650050403104003003403282ea0030911003c1c1c00c900c900c48002d81084401e800140681881007107102c01000c540d14603d5061400e00052014414203004e451700061b484008501000400c00c0b0400418540c000602c0c54082c0c198006e44400c02660043d80c10f004076a440b0130219035503100721a01c10b50203103001081510300002e8640c1001d030018210043c4610 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 620178884 1250 620177634 620177639
    0x110d0b0f0f2a0a0e06071a0601050f030f0601021c08190b0603060d0606121118010312050d0f050a0f15080a03050d020f16030806040903080a02183601 66
    0x2a10403600e00c545580004a950b540f078418402c890b82540c0a0070117821078000201c42040220b255900e801d075005100c51204141c443c00011680c502c1219010414094140003003079003034040c16070041d0040d0050044444015032200e24811710782030f114100300802c4900041044098480c040350516000c007102c00c010910110000800e9400b01524442c015403c1001c02810880182d2000c0c000c0c0c00d01c60001c04040401d4035101043c030103441a428010140d90703070090382c850000c0004d0b50580341d110310404080c400d03040088a07190005040200425203c41141c0b1980d030151185601655071004007044c107883c10000d44064401c502e0800d1035440000504010000c800701c2c0001d13106a25182440c0d6501c0c0a10001004e03000d00c80c201214103100190740342214018080894a0510949550010303179903403001c100071240000c0018012490610001f090390090303034002e041030036001404400112201010031080112803055204400c01d003540c0401c0301e0314403981d8142c00300446d00200d08035030 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 620180134 1250 620178884 620178931
    0x708160206060108191d010b0103060e04050a080313021c120c050d03020d0204050315071101110703050715110a181815080607053004110d0b0f0f 64
    0x29402007024100110704541d0403170189854100d00740010340e1807400040b14130803070350040c0240700c601c0401d13011a2410b030000606031040925107200b141c005024002e1268984c54481281c2e10085c454900e0320208841d01c0b005035140f00018000902220110032010308919100c0c00801c41e2034400c0042c015211001c5000810010b98180c81d07042500d80961141c0786035501e80d010740166040307250f0502880d00e00881001480264a10607035407a51030b0880c0091003d001400c0782c2000117608001c0e84e01704a01800710b8010402849410304c40c80c41d94405d20785044510040301d075225030355054004d002500010183e0b001d054100d940381014072010030384d403801d40c1c1a0074003008504d04103841615602c60400d029008038441c0d000b41060320aa074058070302001c008041c0e40c49118403409510102d00282d40c030001121010300d4a158131000704c403103a120703070b02c40041c0818640d400d685d104128482c3d410002c3ea52480c0c1c0c40c0608840200c4410504110b0602a00c4403001040290040c00d07140056600c003 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 620181384 1250 620180134 620180147
    0x30050403110c10030c0c05030c030c060711030702010e0604090c021005400c060503070f0504080c040e1c080f0601080708041407090614040f0506150c0f0607081602060601 75
    0x1000d081c100002c17000c0c4410819100725076170003c090420300020451201142c6e012000b007003540c1d580400e0300d0715aa285202a900729030700c1841d58038075910a215020040d4000c402c8817045180040241741040ea0f0f4040500c182c2c0c02001144005800072030465031042041c1c0a140e80004001c003074040000500c1c1c826102c8146411034544001500405032602038104600c01308a584c0c11084c191403083e1a804050304650090b01c4070000511210414900c2034499800d90307066540190140c2803040201040101400741910900c01502030a001c0d0110b0a0320501102070008003900d406c6440c0c51310030b6172120b03803000062149050000f00b504008140d684820031550084d403040f1050104c50100358003514108030340c2c000b490a2480c0c200302285100031001c2d640403280e0100c6081c000e9003d108013120689030107880c0c0036003040803245882080c0003858081e10003490b0050448000032007080100e440c00401381d910707070049802482484107a024000040c2e00340c82c1742d03000400e00c0e07040c0715000070300c1c1 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 620182634 1250 620181384 620181409
    0x5180a020103091a16020f060c1602030c060c1e03131a090d0309081c0504060509030a23100b0319110a06050a171630050403110c 57
    0x1055070340c00f0701200300003003611a4981c0d44134502114007146020340101104001140c1000058410701c81c6020001c1170020300c2c281702d100700150541c10003420707011450040aa1b100d080303070306000742c3c0d130700c00d10a48481000e0806100c9060090941d81c07180c200c04180c04d10144102c19994004110b00d0220000320840c800071940c1c0b108024034183c0b0f0750101042ca43c00740820656000c42c0ca07500703030001d15501c1461402a070b680301068880c9803201c50f10000560aa4a22100204405100c100f00c040d002c0c1000d811480c2e400340607503500134407542c0c1d90300c3d90b0342200194a05c000e0320b14051601c03a0204005030609801c00400c03c1004420040000f544c0d4012800c030b0704160b00c0c07482c100c5030802c2003603402c0d0050100043c1c800c1c01c1c2240c845d2009400307500401c402c200082c070815907150103650013080f01405030566600d04103032680c8680003100c0800f4122521340c00071200b1950114002c8040c03140f10f500f158501d00020316800d0500e070051101c0c4001036040681c0c1d000b221b12400c0c90b591000328444 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 620183884 1250 620182634 620182637
    0x91d0a0803161b0b19020c010b130c0806121e01020c010606020316080310080a1410060621060503030c0a02030105010518240d05030921030f0a0c1203020d05180a0201 73
    0x2190307203410b0420541e6070080054104c1713900128948a40342d1054012464034030f412200c100c1d0014251182c42c049070900b040010014a80c000441c0300c0c0c0c10103008c080081610321058900791210800705040040303420104606030381d80000c00f088443c5083c480c40002e0000e40c17000e5850103400804c55180d42d1030300a00584504c81c000085a0486800807820004100420541c0d11602c51410290444682508201a00e02424080c80c500e20810710030301d402d0394403984450000325080c0100d94200d8402c0d603201107a0130750320b501c081203a130350800c060040c91040d03c000313109031203c80c8181800d484041c3d102602032200011807c074003c079140c0450340e00020544d40b90002000b0704003065051806040d40d07a821404805241c0d09100000c40100b140200540c0c0741c801e240b0059031410f40490100b030070320070944c100388071441200140c0c2c0001c041c0c0201c13a03d00400c801040d17072950103050801890f40008070b507000407215910740b00c0b80a800c2d4029409003036001c1c1c458200441d540c580012004c004e0 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 620185134 1250 620183884 620183903
    0x4050d0908071818030c0317010b0f09060c1c1e080a0b010e043305030a200603070f0206060a05130e0124050108010e04020a091d0a0803161b 62
    0x1603c00351240c0c84000d0561000041d60310340e4445041c040d05207010140140c0000b800d20f40840a40c51804c916141280e80300c4051500d4010034070089112500001e41c40b9900c103900308000d1059010411800c6c0344201e606a01044031014114080c0c48401d0840420815079000007113641443d130090366941e07205050600106942e0140f500498a0100030408543d015160244010314003000f504100e00020080e0b505c115030a516801142e07030002e032071150660680c884102e000004084210905c22304801140d203014408070800080c180b41c00407160f803000074100c211180341c9641d0401c416600176a041d2222011a820071000c21055114444550130b0079841d45407030701711704100f5030100c44024501c40707110514640907009006007003910f01c2a01d000030080707000460300c80102c1d002c05000c1e40e0700501084040e0316080500c0c1c00380c022410000b81c24240756402c850343c3e1106001000755144551000d5035645044600c131036141814000d600200a080c142039180380c140c0c1401403241e5900541c004 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 620186384 1250 620185134 620185169
    0x9170a020a061b1b0503180604030f051605010e030a020103020f040807120203010b0102030a080118090f06140106050a21180c181e090203010f090b04050d090807 71
    0x141d1410403008001000c4030f00c0c01038244900861945800c0c46003181d5501c00391540116244180f80c40030900d00504603800030030080c0c0752500300b03120708911006c0182015082a0303403622100b0220300725039029600c41e04150748140d10a9140e030002809004242064403070b09000c000401d6a801c140900241416400180394a840440e030007998010010711007100d10305a01c0d580b03410140c0140e910100e00941c00e001391100c46d5030003c0203665161380c4980d103840d0310341c0c03800c3d141c49500e0380d6030303492094215a24009640818070702c0c01d10300841805000081014415801200c4000505901131020454244881d01c000d40e403100b0702d0300e00700702c0c040031b44050007141c03801300d4005098012540310355a40d100c01e08005c21101015a20803079003010306030504944440c6510b0140c0f42ea1240e8118031007403484046096105070380c0940d54090000c0c1c00000c0d480400c00503003040318004e80702070711401c511101b00020850b003044001030f001c05502c5c092200501e0116840d85d150031600900070008a4038240 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 620187634 1250 620186384 620186387
    0x390307080c0d091b0f0501080703271a010807080c0904050f0f100c050307051215280923041e0804060e03120a0e0406051806100309170a 60
    0x507180381d00c0a0100400050f40300e89004500900081e41c3c40319082c1c0c0400000038400984483c9004880c0182c590707039880d990b4110304400170702c0c64800c0c21094040541420030029000704500c40350300e100b045900418180620005c003c940160300840c0d00760321400062080410104030000b2021080d2062003080c0c5a0345001d0b8103102c0442841119403240c0c80250b0403038580040c006808150604040111082182c8121050321040703403594082202080240d44080c050b20386503621511710220351007403100c10790000745075942034101c5060f6841c11250703030300c10303001203e81c280e00a0501d103808020105992181c0e08604200c034050070340200e07914000900307201809031040c5c41e4041d42c410455480940d0314151a01c0c1c0c2240c02050700096000307114020754100010668100523010940e542000344040048500e030400c01e40340c941090b00e030309000070b103500d03141c0840c1251100503074410898a0914148450003010313062a40401d801d083d400c00200366600642d000310100300d0300780790b69100902c00 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 620188884 1250 620187634 620187637
    0x3100527010615020105072c010c06020c010912030f090b0c0906041701020a030b0d0f060b01020705031221040c0e040602161b1502061518390307080c 66
    0xc251542560001040f440c0d046d80541c0c840d030b2240d26a140402031507a40c4440f01c04c4032410180d07140001d480785000c1580218006600f03540304030405841c20701400400c030f0964540e18006c4071403441c50a1680f40150b05800780510052115000704014040f544500741c8801e8080e00751004d99a0004007207405840300c80441d0f01410007140c40d031481082c03100100d070003580480032a2000a10f046440b07086860065070035030281e030f0001e1001581e50b0990720f03076400401045485074194400d4240c0082c00340c03002c4c8003030f909580040541d9500d550b011104e03400c0007150025542902881a401c1000243d031a0b03071400300f958104210302c42540e0304c40c1b40000091051805500e401800d803040c02080040a181681c2075000d80c041d14034006a503003030380c844e14040f9842070202503000400004e481c07104980c004c03259100000c0461a4403880c1c00a0411040f10580b103c59a1050301d0340888442122030301490310f00300242200d00da00180003039041e140e0b800041c00c02403c0003207803070200703200f80007040 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 620190134 1250 620188884 620188889
    0x136030509030a08130506040320030c03070f030b0601021606030b01030b060c010e1b03150c090901030305180102120a030207030306030b07090806060409050628051005031005270106 80
    0x1400c580c000f50703840c1080c0c07034280c10201d10f8a0707000b1002c0344c01048030b05158040c0c904503a88900300304c4080c03200c8018091904885824250903105482d000385580c0c2c1c007000404010600390000171102d500758100480c5c00c4c00000c000707a043d9400300b40212045910209840c0440e081c1d0f150025440c0400310048019240319610b81e680524042204034074503a06620041444550000315801c060030340c1c605000c9900700c68075040c5c0c150044094448801080061030754000013510500e864101142c0029402d41e8081e0016000210041182d0503200d1301840c10300003104003400109004000745c0040c0c0c210b842340806d070b0000c15801007500310405021760081406140e100500c201b00b031074045c500800e80341302c81c0b00e0081503102e0140840c80301e0801d4071070a901903800c0006080d07651f4a024a182040d4405454819590181a880b203c0084240300b400c1c0140f0440204071821840c00081601d040d0300101c1c2000380900e403806200300134001d112041c8240c8224480109040c40720300d1040e004142c0d50b17 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 620191384 1250 620190134 620190139
    0x10512150c09010e01140d0209040e0618070e06030307121209060b1305390a02160b030f0a0f09060e0703020a0e070e0d080d14090136030509 62
    0x424440c86880344006060808030031390f1110b007034040e9400112610080e41418140c0c2000070825005015401d030001c0403c24000303030000c500088912140d52400e9000c84028030101c46170311a8005203142800800024800b00b54840d0650929038006902c91084035030041420640c1d4085650f001c0c011000241003c80e941002c01c0322102c40d084c4980609900020300d44506030301c06800030611703113522450f4064501050381d910100c800300f22035928810410462030805d20b0754010443c10080ca40c000b40889003156014090354600e00035901c60380826a0451081000c05002f004040d1150302c2406a105034046030104000150910500040040c0c80020341018185601c6103e440c000051303d80480e48261070607040384e550755820340d41610301a00c0000c0001d09840b15101d2600d41383c0305003640c903402244914030b08000c81301c1c20001c64000c4102a01d005550700d0400031055002c1c80b800c180c613800703001c40302d082400c0e50f0400c40100d242d9009201441d0319565481044c18842c6080e600301f071001 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 620192634 1250 620191384 620191423
    0x310203040f0506180d0c030c060e1e070302040b091311061b150a02070c03082a060402030607182106050c030a0e0c090a230112060e01090209010512 65
    0x1d00c2d40003100c502d4500c1e84c440c070344601409000c18910030b8240007032054041daa0552610384655030840904440c48440d0458880c00b05081c2c800410340c4910a850041f4a0050181e0b501c1c0d4814030080c4c802c42e0a0f0740c3c0c80384461804001078242d2004116130250340c090707126856600d4220014115004034810145100010400d5401030040051204003c0320701031015000395890003000002d07445054401080d02c0000402040024001ca000e09803c00700300c208001d100000c00c2211400200f81440e08a06506c5403040c0000c0d410107004880d00000b003450201c00c8902401810030300c42d88603128101c10014400da40485a180740004512000e0780210288281e0400456000c401d0f0416509030314218600540b84803000e00020320b040e080280500308217071507030764070000000605016580213070101c9003c01250b43c148c0900f9a190103041e100c130303841c84504000d0070000d046034021850584507a02d0f042c40740002da0358521000f030440340103e4911514880443c001420592042d0044020001 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 620193884 1250 620192634 620192641
    0x9080310060206060f0612180102070c23090c1b010204090914070e0105090601030f050405100b0d0503030a020a020307121211030601080a0b0418060506310203040f0506 74
    0x50080c80c0401c4a120758201c0e10241c642004000c140c001103040c650f03010404004480410510600c00b13540041b80600d01100070010f2814242a44d104500848905102800034400703030344030004244000001785a008881080e080c08070301203d4000d082c42d00781c0000170400c01c542c00c2c1c2d0780842c01e1100c18498000d6441d02e5a4030401c0e006014456030803513013851401012200d88400183d04001c5076181e42c82e02089920309030611401503030241019040584407606508020210f028241c0507070f00c50b100406d41075002c082002c0c12104a8541d040c41003441e0b0564074003040001050b04c0d00085241c2006945407001101a031543c811100700424113803c590080380341030b070003000e144070b651010981401900314590801c080c6104c03c0b00c09a011442810115940b00000d40c03004100840c0500002812100200b101000b48d5040c0c40884000c0c1c2c0386e508020403400c10781a140803580e1003007546c2501c1200c0e091141803007400301c0300885000e98080002018007413194035841a090b0094250b41185c00c = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 620195134 1250 620193884 620193901
    0x40807030605060114033409050f01020a0c0902031f0b0408010b040504021e03070801060e16030e0a030c06110c0c03280b0a0605030106170111040f0e070201090803 72
    0x12518802907071080d00c0c06001490035401a0042d0310301c00313124401c01e403541d5614108a201007000c41e0404455a4a00300b1541034080030304400316020381c0586400d40003510f014100000d400036010700b18115040188010001347c0c040840a01b500c3c4909005a02c0ea03a0b604200c44034500104403e4482e65540a400565101c0000080040d1101031001740803a0080d107082c0004e50708162002500002c0c40c02001041810502e40110200d800a042e0741241b0385c1c0d15443c0c0d01795101900074050441202d001c1c80103090b43d03c1c042440c1c2440f1030401f07010a00880d1000c13a158000700002405000140300b00350100029644411441240407003420b440d441c181d4801560307954540a618024454050000e204101c5c2c42c18a014001c6000c51782c03401c0c5081e566810442c0305000c1d20802c190f1351903510201e10360380d0a000314000b0f00b540d00e134003e0039007a16603101c0f806c3d12050201c44100b504200401d00109640e50301000685004062210b29902e410718224010100358402401290011040c0030446 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 620196384 1250 620195134 620195143
    0xd0222030b190216060207051606030c020f0105070e090718060e091e180f0105040503031b0f090d030e1e03010606030203010b030f060121140705070f1e06020408 71
    0x2d181c100780100c0346500b910740e584100d2140404c18000c083c800795020300015129001031040920400c00d4510403100040c4220350756020f6000340011070b4032107143e00c604e154100400141140c081c4000e02175400d160700041c080341005800b60b406030b685100000c10090003000c4580000c00b402d91402d00d001d6892400a2001140f08202c0340300d030020300b01099004400111070800c2005440d202c007019110314103111005a0020300c082d2840c0230304116004081000e21030300d84281e0043c0041d50356490582030021717441c0f0052844800f4600140124a405c2d0b2001060b981c007050140c1c1c2051251089080645407030701174054030f6601c0768802201c4103da04c01003140310b007100410f070f00a21070a61140c1068052707000c01d00805154190030310010b01c245882c0d0b044907400400604010b485d03242101c040354036020314050f5040e1459110150b540d040c2d20343d0341c800390f4420031360710b001402c20b003c564174903004082100004e0800104003d16001c1c0e03954004811000a51180707045503510f90359150030303488 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 620197634 1250 620196384 620196391
    0x120a06090e1f0c0318050c0f0105120c0703110f010f06050a1a0f1209060907050901051804080c010c110610050a0e19020a050c1b060d0222030b 63
    0x140c20109802011100000c90300c000201c2203500c81604a075080c1000018405000fa0703000309500c6010386403111a0003035490714568000c078040c6c8400c0348000140b04212070340d0071881e8104a01007081c140d82540342c104d19900100c4104045540c2c00803400d00300d58107022903442e00c2640c010101080c0314038a05510101c203101c1140014071015680d10b0400c80d0490341441a014101407010b100b0019214903001880703c00c1c10401c5040c02c041c10f079009114140d00031902c1240540c07180c414040251000c0041070020700d007c0302c62042a6040001280088005007201c502c81403a010116003000441c809641d64606488000c20191515030402051101001e4071200540520340200d41e0400f0f40040b5402522030140052480600d01141440140b100610308510485e80305024981d07017031980000c0c0758800880d03641c551503004882055051900c5048001c0844081d030760f0328079980e224402074039102c061210006071aa0354101d08036401d80c3c10746c00d4014003400d02a40110030800510080c500 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 620198884 1250 620197634 620197649
    0x1a06090601081009020304081603020a171303030305090703050d2001270305040329060405040302120706150b0c070b040f0b03071b11040e0309130908120a06 69
    0x201a11580e005541050301520720400014408000344000761980d002103410038841d00e1362920301070541041000002e01d1640407030068000450600030f0196680500c03100d942c9502e100d900e41800c041e1164200d8215100040915071550006240b90800b400400300942e00241604c0c0032110700e060040607100c0c050350703c9450381c010255085900005209401d400f0303007402d540140c4503911000e1600b46285e500021010014104804000103035802502c0700604c1c15100031501020202c1c0d40c00c2c41070340d4010308140c01645854104000b081c1e00042c03080110007000c104aa03202e1450801602501105039a441d0741001d03036000041c0c5088620040000342c84500c01d0307410300c44c0c41e60034201003842240b2441042680800302400f200a035240115044141820701070000991500b400301c094000700000d49a010201c461484503050a025840108071004041e6181c642d0180004881d04400032011542956800b0410b0400c50500e04132845100035031500201460b1440d400da0241c02d240c069050b = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 620200134 1250 620198884 620198899
    0x7090e0d0f17040c0504240614040b19030608010510051c0b041a1003050c0103050a020903010f0b010306080309180a1d0102031515030711101104051008040503040e0903071a06 77
    0x604d04181c058001c5161087c0340001400c0b850017008035009485e40b80c1e020340c0364208000c00124120840000d20016005806142504003d554040e0480700c05601200700c03a410181044003204c403107940981903031011210300c0d59420280041c40c4428030070000c01028103c0356030500c401d01c4030762012181004420f1285024a50b00c290089505d191300c0d200081055000181241c81c66000b500015480030391400c005050100610009003034a060140c109201692840400300e5560705019400107805002c00540c80c11001e2404034000c006082c141050f00340480e03011910031906a0000311070511010401d0109541800340c881c001c0d40141d445844101420040c0a075a04000400b01c484010100700e190440c3d032102d40c140c603500d100e41e42104c640d00800c078981240107000e11401c54600e00d00c0e00015150b07420041030240d0503100b80906001d00c01c01808000c0091f0002048600340c03103c5640f41003043e21101002e61441c010008000d00c0303018000d41150035076044410592084204a40e01d5 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 620201384 1250 620200134 620200151
    0x617010504060f020c030d050402010c23120307141309092301060b030402060a142d070f120909052d0402031c05070605041407090e0d0f17040c0504 65
    0x5108a204005e0780f40465002030140c2d4803100c0e025845030f9031060041c10130444142c45c6a07142020349450001070501c85030702501040c1121020000901c88140c003480251450601040c0544041c94608d80c0e8203000000042c4030340c09465144107031008060114050000c9019440c040d00c020680490781c40451900030450329600c1c0f0140034000c201e8400c5070300246941c950741c003417003a0b03a03000d214240d0a000b007403180030303036807146ca000200900c40c9110722000b507540b00e60800051a24610080380a9505d003800203c1c046041d441844c40c80962040784d00d10140420101504c1c3d1800e01d601c007510b918a042c040141091b17420302d0800c0902400d03525980c24174101c4803840480704041c1d6002e50560710203820203118800c1582c440e021481d02e428007070700b003000b0382e07039440103440007143c0442e078000184494000208c01042000040c4c01c3c002020701c159641558030956070440489100b04024200344901c3e034450003054802d5000072140d410300b203035251604101c0d505c1c0740e5070300c91035001d1450580365 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 620202634 1250 620201384 620201411
    0x50912070804060309020d02150a12090206030f100b1303020f191406040b0c01090b06090405030d021806070b01050f0a3206040e2505030712061701050406 68
    0xc031241958030084032800c0c90f04100040b4010220860105d07003003444034544001503518000c40503402441c1d035020076544c2c90307103040007800c0b1108a070300204020305200c6000016620001a00d6000e410020307159115035a000c400f1440d042c4070350200f40d09800000760038809518140c400300503a40291004040600902c0a01140001b80c005500074141024800e201550641c1c80000103030784020801810a03459213180000d0794032564181703d4513907490009074100800006002e500003421500340e111480c00707803513003a12407040f2600040f0142c1c1c0021030320356103240785070b46890f5800007030300144c1c0301e240901e000340240b9400c0c002c59101304a240c681281900c0c0049000c401d03600b0344409003459201c5402c165000c80554111181c185058695880182e110300e0f000d04010040d022110029090203800030154214448280d442d90301d200004118540e0000c04a03600a0041c0c07610840c4030071520000c2c0300914031354005611902c00c802e01000c031013505400031806680030300703001c2140c0d8084892 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 620203884 1250 620202634 620202637
    0x3120a0204051f2a02040b0102030c01060f0503060601030209011202130e090d02010605040b0604090e07120b040b0105151803072601060506040e040f0303020705190303050f06092205030c01050912 86
    0xc80082075581813103640041c109600492140304040c011a8104008401c110782034880340e400c800c0814500600400580c5420400d207500403000382011807900b14024002005040b003490032a0401c1d400003040c00108400c194900300401203a4501103980c1096040d2548072001c2c0810800150b0a19602140c2841e1a00c11001014402424a0300d424a45250400602080e110f110454000e02c1000181011041c103550440c5108000c54040c0c0d1503d45014248514103070270170303070080c500301121640446c2c985085800410901407400b403802c1040c3e0000c0d00d084013513040f802d26801904020b043c400c01340302c0704800b485242c600031700208e40c0b16020b00c250f43c0100d210740e207070200060700400d01007502e568616100d280a46005450030b00c81e030b11458541180c0071040410b1040840c00c010a15a06100302600320703403080d85450950a2800005290140c050f100520328051070007074403140089984141485a40001941c1c0c0f9015400510750080c10221007841c8180030709003009240100d80740 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 620205134 1250 620203884 620203937
    0x90c0a18052206080303010602210906090f062205040e1c0807050c120403030306060305240f0307030b0105090609010e01090f020d05131401020a0203120a0204051f 72
    0xc0c20b02d14609400302804542201e10400400d285650301030200d40c99a0910055019010700c1d0010031510b9981469042803506101403050703018014445410380b076561608a40130304074100d404002403007d45000800c3e510900202c508440c264050b2a145444459400c0c011030384211000c100702d00c00c1881301c0d42c48441c4040075042864080402c0e00300c56010b00250b035089042c07032802505004c42c2104048c5818440b0f89a8806204042001c100b015854016072001d80b80790301d8148400d003011220039146540101c001003550856005282044c0c4400092030b00e03a00000301207070034041e42ca0416040005c001c0c051303a0301034038804000440e9414000c400604031108a81c40360780581c07804003200000e22440c2c01c40b108003902000100c9050105000780750040440301c51140c03034840075107420700c1182d540a00d150141d03401030081c02502a008425030f01c0350b01881c3c81c02e50341e41e0788443e80d24000f1f01c40c54200e16400201d0034a000980d03445074080a038011403507101d5040f000170805803900041d2101 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 620206384 1250 620205134 620205139
    0xf0e1011010f2309070506070c09180819050d090b04050c04020c070905091603030f0e120a02092212020d020703020f06070f06060b0903120c03030403180302090c0a1805 74
    0x1c0910003c10000300b44203070380880c0c10000d03980d0881c0c4560020341c01d580f20040589581d000c031903060140d411540308a81c9014148231501c80c90f0a5a55988141e500811416401e006c250300c110030302d2503006004480440d074810b0b4041100b4107103444d1002c0c100c0c20642d4140c945219080d100c1e1403038102743c404c442400d10500b008000c01854121000007424008054190703a0041004842e0384901140080c80039601c030342c0310300710502d80c184030080524201d80c24241c45110121100300e0400c10105940c11000d4040d10308032406e0341c40c02c03502003807103404583d000c11070501000281e090100441c58101c0e40c440c0c503400c0e0390203c50740c03140880e41c80e0103034000a5400000034014214910740940240200e034429103407041ca201140d00d44800300e0300c4907880320051060004009045160521500b01000203111070103040c8070b18004050303942e0200420040038031209052a8060102c40046107006540c005d007007000303030302d80108160b80642018004401041c605049210850383c0540c4800541d0b101 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 620207634 1250 620206384 620206421
    0x108070e0105030a0308010e09240402100c0c090c0201090f0f02030706140d1a0307150e06070b010521030307090e1312050a0512010e090706110d0f0e1011010f 70
    0x1c0c0456652554030107400c00f4080c5c412b4004512020018102d205200288282259042d14050041c00040d104210131030f010080c6052105d4001400b000780c00d01079800300400002c520341387c414107030b00408000d00050701c00041c082d03880c410000081c58000c000342c0309400340c0343e1803651120309030f0b81d0720002822601813507424004030071080081e07070008010840c04900e40c5c44400d003d4000ca42060900c1c0c102c400c030250085044403200707030000050000c0210a8072480e2800420380c540404820323040c0281031107400743e800c21038043c4004540500039907a03d501030340c2d5030f03085c42c4c080a040f003901413080000d40007210b40000c1d903410030040b84101c0303150011801802c240cac0201c81240c07564007d81018003481010702008061070010600da501138880c40008070b90501b0000800f52800d8001d500c1001009400080c070040c0341030200f5000440302441c1800e9000407218a81520100d59004140d500b203c80d20307110418250740180d6000d0b048042d900200805401c548441068401c040005901c40c0702 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 620208884 1250 620207634 620207639
    0x130f03050a061802190e15010c0f14060c031906050d0b0c04080106032427170f07030e04051308031005151308070e06010302070314030108070e0105030a030801 70
    0x302d07a04403560759035200d16040e809044680c0042c3d040c4170a040d40507924068280c05008801d0500700541d000700e22602d200b0103100c0403900090a001351801c0040c2000f02180c9000200300e000c90001003440c020005843d0a0714162641d0f1005410071100500000c0b0000f5010f28918107902c100c00a503540075000d030480740681d403a0740c40c3c1c1e114090a03049003c01c0412000510000c00e200310000b1394400c421200a41c2c0e002e1059902c2c1500750703203010304440e1500d14814101018079030b10210f162a180a100d03860b94103418506441c00101030607884030107002401a4040344048001c0154030b1181e100c0c40740c8002d0080510088803c2160607800403481071510390081020300c0051988404011102c0030ac007074485002ca001510891010340c6d10100100b040749403410001c54450107070a401004140031481d24030845030152001d40403d05142c0d000480038103244c801d0900c440304201c101c030707a1a40c039603540b41e04a0359810644540c400d0b03154600004a0313a49000f0400040c01074155640c84903590 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 620210134 1250 620208884 620208893
    0x2010b060a08220507120209010b0f0724020a082509052803050a170a02060402060904090209010b1309060f0302040c02190f0c051f051617130f03050a 66
    0x107624000d51603c1401124000001d0420000c440203055004c0690703540306a24418002c8841040c1c210916032607040c400d100d0780540d640156980160400348c241914000c9005640010f00f01e0209102808c0c00001c402d01034941103560f1501446903462584004208220b00351915642452000b0018102d60800c0040d0318024003982405031002404203007503420b114445070304090940c804c03034103500700b40e1580c400d01c50310500f044101a0106030062908001e0880203480b1007005000911804000c600d055141d11541d12079403019078003402d44681e55840b61141c40302c0d600721070300b10804562120300c00301e1820042c0c0101c10843d41034203881203285056500700405031002c024480114400e4100b100c1840d001c0d000d842290b103008007a222844611f508104100680a410050180c02d0b100c017904201480300601010344204c2d441c2154980d000319016501600e92007034040d18084856050141d100a050018119458050381d0070601596030014484c61050612015113160001901030b000715 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 620211384 1250 620210134 620210161
    0x4240b2d150f0d060e070f1b0804030b1312020c09010e06012c0f0a050319060e0a05060609010812040317041a070b0a0b1c050c100f02010b060a08 64
    0x204a0741c207090010142d82100b46070015001841c0e100d0b2103540401200c003c50344880e0300507800f80f90040440340c0403100903000c008030840c0d101060040c040002c040c40901000e650165610800d182c48074203018034011102d0454482c2554000d12818a018525000041840310504050200a80c40e03203401e034203030110000188114144920646007035941c10f0b01d0b40b031b80450f031002c6101c2c0001403075030401403125a10310172815600600c5201018051580c000034181400c1110445202c0c0a10140c9081c1000d4041c422001d00503114a1400104221010410ba840b4000a0310f88403403c5c0e80e12070106541c0c00c007100310140c1c607490030803080c4042040d110300c01c42501c0910650900c2c041d51030f644c41030319904071010307401760300d1003c580f8404002080c440103070000c150540a2051920610000c0d0068054401d5090641d24103480d10080180c01d01810921010041054150010101025012a8140c101507005528008500201e80f6100301600d600007420760310b49289952342e83c01c04040 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 620212634 1250 620211384 620211409
    0x121b050d020708070b10090c1202070212010e012909060607051603030509091503101802060d022d030a091e05160f031101030504240b2d 60
    0x203036020444034011075810001000070500c00c864440c3d00b40b0301b2940001d0310402c00c1c0c1110b2047d0303061464030781030790380c2c031140403125100c6070840143c0d282d801e4400107075601c00800a1030519428000751140b400b40641c041e40304644511140040b04140813086a038610414508c56400030100c40411080e080800140c440030b480381c002c9600013240d400051030824030a50044000503000079800c2c031b050400c664910b80107030103592002107480081d8000fa46420004050145965a40e500c500180c40c2d18501102116000307050b0035901c3d010308005002a41c401c00d45601070075004030305c000186040030246041c400c1070740307080c50a503200c440c0c041c0081c00040105440c000d841041d04581c0c03002d0101040b480d28882c00060080c03646030407130381e0319002495018070020315601c0c404101003500100c5450f0704407402d18000415548a01e040c541110000c10050301701a00c01e100c8105503600765000c2501040115584070702d48039410b884803034111160300041303950000b008082c0038a00f00f52458500 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 620213884 1250 620212634 620212657
    0x3060a0b070c09110d05010e01260705270c07051c05070618120c02030c01090f03020918060c0a0e0402090d02090a180f0215040f0308030a2a121b05 65
    0x24005110303540e40306a035002e800c20008c0f0010500100040036074001144c030400501c60200030003041c01c2e40e00c80e0b10b07400176201d201c0c010071441c00600b01100c0340b00822411441c0303c1c4090702c10703424841340c03100241e000700a0807102485248040741d0340c140030506000200d803840e030f5220328140c0c450f03071800003504c2040598015070741d072004401b0010b440580c41000000c03007075485541b00c6800e0700405241501c24200307030381404407100c0c4c1440b40d510900000016281c0651700a44e1548460380f60180710120000c208a03e400303803005101303800003100300601c04140d0766521030b0085610f171810081240700e4007026030ba014004016400c01401c00ca131a85602c51a41040020003403805445903100160a800c2103803e400907880380000c52400c002207000c13200e18081003900703260408002030440007541c04040c280040100000d2055071085c0c00c400358079060f40640904090074803031041030400c1d13041030040104241c000c40c14404400f030301c1000b4441c801c2e42c03030726003c1500303c6109554035449140c4240 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 620215134 1250 620213884 620213887
    0x51e0a02060d020703090b04060903060b030309100903030906020303072001060302060319060906050d0206031812041502010b03030a030b0604050628110303040b1305010504030503060a0b070c0911 86
    0x10096a506000350820502041c000f42c0c1d00d54062800030f2540b402900404101d40c804d010501109900400e03c0040c0c9501031800501000400b00080c914000e220300d0b20350040400609076040c60384080010222442601d80e8108151181d03030a903282e0001322101d000090201c0e843e10075100424403c00403106101d800010700039142d03000300700f461f80304076800307880d5002c40c01c00c4000300da181348607030130003030400c501d00b007212604040001d04020f0104402a03c20341c000b00124503c83c2c1010340750201040c100d41101c40340e40c1c840760303c00c6064006114920b0341024203000d2030600380c0180110b100c91400140a58580300d0614000d0740140404107605400035000e01001c00c1c26120680141402040c40c1c803507181030800d07000c001c1150942181c00c44204100340080c05403c10340001502d07001a408044c1000c0355460004d1311a50000992010300550f00786001d001c2419084002140241c8c2c0a460088141d81c60700000c48035803080c1c820050140145403000c0003841c0003940916401190901040d = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 620216384 1250 620215134 620215153
    0x1113091b020723131a030708071a0f0d02030403080a0c031e1109130b03061e06090a0b030616320f160501021c110a1d0613030b070c051e 60
    0xb0044840c64030f82d444420541c0c1d025414146020441c41c0300401e1418000c03c0000d0074022142d031030f003080c03e60b40141d4420108002f491a050750080e01c60382696000c00315242c0c076050a00428000d029122800d44928002800114130b104e400b55404442007624601704903154041c030a402400d0301c4da4201c0e0b55103003e01c10310480c1e079642c03401001c0c010078401c4081a40b000c40004c05051540c082c15801000c5181030195501d1f06685a80592041c1c049a0a50450361150030f02400382440040040e41b6000e40c100b00071030301056031105410a001c40e9030b05401e0241c44002482c240c85040c030a1511002040d00000c40843d0303140040c00e01848411950b03003400910300784810001040b0404840507500800c0802c2d03003800083d44800d2441c2d00320418499401c1744464440e4500c902d05002040001619100c02100e680d44440054140c0180001c2d969030203001c105010590a404200c6032070141c5030104204074420038904044a4020010704401d07580346851205544c0d864800704800c6c000e44084 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 620217634 1250 620216384 620216419
    0x51003052d15030c270702031911070b070b0a06140d140a0506070206070305061903080904092f101704030c060c0314091501091113091b020723 63
    0xd2031a1383d01c80103030794117207001010b42100304203000038040e004560007400594090056060100c1c04840603003440601081c00780101420130040d42c00c01c1010301800030b4080100421400306c0f03485164951010001d140d110b0300b41d080ca4450400d10b4035401203112650b0408074201c546000c49580d0464100c1d0080001c60740c0780344c03c0c000c2c11902d07180580c1002c800c0200c00b80e00350040981c0410211100ec0c2140e445400c00b8840c08414080034080d0b0002041942954440303a2154a03019086900d02c649901c04080034481460500c2042c5134403048110405400c1c2805940041d007045181c51314031403e4000c989800d10968000c0099082103d840c0d1901d001c6a9280300d203060041807503401040074901303070342c4074010307030b00302600c7c6001c80c0d8801210400c0d01c403007288000341520300f00c6801082e142440020b804043c010705200c2c950000c4d80c11000152907070706602020b1481c1800c4100076950400034130598484a040c1f190507031403c0343d0903440100b0001e144484000f05001080f449151580c91003 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 620218884 1250 620217634 620217649
    0x10b040506014b11060403020607030903051209030406031512020d05070905090115050d0b070f0203040b0f090a1706340e0909070b0d0c0306051003052d15030c 70
    0x80c4006014034083c01c0b00441980301e001c203600ca0324140b00074811401c0c1541c0c0207550703840003001c05c81015a104c030413108151003030701280d0b00d0f00813440401c501400c4c000003194490744503100b503602003403a0249840350862503085081c110f40301c010600303010781d0058003032010905200508440d00e01445202150041941c4a440d0040220000001c7e01c103104032664401a4080e8002911a0b5003c5480c04009240d418003035a02000d9803400c0c221200c06c2020503807440c040c642042216130b0000c1511640e1001006c050801600c0c00c8035615a0707540d40e516060445210034001e010940c0140c000607040265600680f1070300c82035400c1140f250b02c2c1141c0c011641c000301410803400100d002c00915013500c0d04606954100c480380d00601103683c900b030404c911511543c0c40b00361a1680313910f030300140d280c060b030700440c014840940b01500c404d8445500034002d00c01150701008210140e101105a0400200c00031001031040342000000e49a61621000401000c0500c1e0b6051080d00c41c6c0801c1c6840307002 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 620220134 1250 620218884 620218997
    0x723090a0b2b05010c1706010f09080a030201143103020309120f011b09090b060c010c05190203040f03080d0b04060603021b0102070201090b0d020c070611010b04050601 74
    0x55020b10599252600301d0a44402017032076020030800008146800340c8502405030060824285031504a40141d401d5030a0a042e41c0803980c0303400b49001c1401459019040001e41c000341091103000c641c0c0c2c3c1c002051324005051480000070208000341001802e00d44000001c0c3c1d4041d00490741004100b00c0003034a1440d0a16603a2125041441381030792000b802d000340e07420704054068803800140e282d07030010021681340c4140341d81d16031150300b0305445482c2c4030100c48600f10502d0003800400d594072000307040c55011191050314140110580c9807554130200c140e07820b45888902417450185107031144402ea40008080d00d0030159216040c0406035198821280182040d4901613254103500d4a010035111007240038091f5a40104044c04c0180e074040580f00540b20200b52068641c06403e000c075009008095010803a0320402c0350214010303130050410002c1038038440c005c1c800050702c10103000640c2e60a40d2028042150a015a26008001c12000c0640f0f00300c0c0340851002c5a01c502d030042400480c5 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 620221384 1250 620220134 620220199
    0x80412030605090103110102012f07061b030902090c04080304170f160614120a0203070216091401090207111e0307090f110307020a030e120f0723090a0b 67
    0x2040049003c0d6020b001d40f0f14000315030494158030748040c01c141e0588800e54006e422074805e000bc1c0d50000c00c00c00d940054004045100c0040300f90441580150040c841904c003a03210360719100004030142c03135080c115415140690007450505240882980024003042158441c5024143d4281c101310000c01031a0a10500c0842c6c0c24116498450060640f10f00105280e40d0004100700c007170b09410045540302e40146070701d400160f9a50319800120f0800c0c86001c614000030440000010b400881c070703040407100203480d02241c5c0080c1d90b030b0300ca40c00c22442140c50043c6064031000100713803141f9010381084c0801c44010410801100e11600007402c00307407a60400f0284641d141c0101300d07001403a200d8003414562148107981f560a003040302940e1129000401010015925884190742d20707200000d110b085004c03000c036400000200401500c4031071074065100700c005e5400340c01381340030300c42440e20a03404000b070038060b80d64907046a1403015041c4000701980010804621510600720a003100d104091030 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 620222634 1250 620221384 620221403
    0x80a0302010603030905151b010605090c0705150f0604050403090b210105060a08040f081902031b0d0e1207081603110a0b0d090221031810080412030605090103 70
    0x6502e809021000246c001d40e00071031400c8220742041c40c15604a810400c840500341c9401e9808510307550141002c0c0d0489030300110640e003130140012013100503010840c450000c2e5112071704182e2918011003c21200c00800b940c140e004140513007050b5021503045030092a0400e4066103403c4024050b80c040746065a0640040001ca00726410f02402c0c00e000d4041280e40e82e141a9400c0c00080601001504c05441d800341525000d081103664400c4440010101d2005d15100300201c00c0a500d81c2c00c1f015141d0480321140005121501002c281d010803640c054a070b0032520350300041801101403115680d0314441c810440701040361702e401c0003100c1d0305c85400010031100a0a52a091110f20044518180030341c0c50200140065040e240644d050030b14004400a403642c040d00004001c07204c45458440921035403480e03070424810100041c8018003005840c60701010070701c0240010146426a4440014981004100007504406507078051f9482d03464041079460300c51002078000c031800c1e401240d092a0 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 620223884 1250 620222634 620222639
    0x9151509012304031b03060908030603250902250f0510110405060702130c2303010b040b1b120d45050109060f050f01210309080a03020106 61
    0x9100300e080705119000c0540030750082c56000d10b000301c0c1c011030100403c50405001491682e00008954000868011000b40700c0c0c491242041076903031744140c43c0c50b8028003460300410303030114080c48508440710b050444c0d042c041d40b070701003000c00030b400c880b070408603070b4040d6000103d541d03010b41c40d030941c558000d68124079000030301d00e085480c050010400c0d4810608002d17990705400d420340700340c83c103c60b4169105591015070340b001400f1942155400d0f0602440c00c8218980698401d80398080c0f40c43d410310f0030003c0b80c0f641d80c02c0085400244039a0042c5201040140140203401021f002c0310b1541c82d02c40322000c003440c580c65041c00c0495100318030720302021a4440f010809401030f10580320350711004a0a10301594160f0b04c03c1501100c4408000f000c941011098508103a15080c0b1190840700070048008e0310300c5c0400180a41400c0000c40c60304203c003003a6107440d510a014126403a941a800d014055001000c0c00c03e1424041501030107054040051101003e0080382d4280344a40d000050307007030 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 620225134 1250 620223884 620223887
    0x62b020d05010b090612061317120105040b040b09130f080a110c0402030106020c310b0f012c06070b010605030a06080714120732030610050915150901 66
    0x1342c00a103c14420f001c194140c46d00d95002007611a084030300c40d05a400001a039007440b20002080c0c042c005c076080c0001410300742083c5d403181c6040c1650003c550600241120038100025148141d00a0350700c0405180460b910701d260060f4548080d00c0b9400703c0c0400b525944501a242c2c101c400e0f0400480e40e050303142c1603007001c24412240f400d02d04840c114119410000020340d1410f242550900030700c60842c0405000e25480d0002c4600c000200000352826041410f040141c001500c0c0140241940c03040b5202039801045140c00c4201ca0b000108003544860703600004079235041c002c25400c02803c00070f10700440e00e1210464003800302c0d9107850b035076400d040c0610300459035a64007400460f0031071141840070b00c0004000d044036001c03c955050304042044411810702009a03ca80041c03558075050308040e110782d40358110b5100140741e06c1040c0c81c3d080010725440d0301e000c0352103030b02d0901c26910a00c01c0d40740508441d034002c031a245100301400b0b55000890991550b0f4480f907030880070003040c2c141d240d6 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 620226384 1250 620225134 620225149
    0xc060a050109090809060a0e13150f080607080a150e0414061510030b030f0c010f030b0f130b04061e0501020309030c010806030a12050a031103062b020d05010b 70
    0x10300c00b5003001c001d03089060b124101e180c021040b006100780345c00601c040140d80b150328403d61201d402411b9010700d03a4020298001011105115130b1011208080000c120388440c240030112402540500010350302c3da0411203820f1401413104a0140d07580c2c200000114402c00c020000d02501d025103940c6080c542003504070644a882d01d01aa54000010403a44c0152403c8440e01d00e8005e403050300070420034401c1074015081412400760580302e1194000030030a8000b80780c1480380001e881d1005da0381c000076000c5041d1116460013540000410490080b1030402050030b200d840100c1d180000d814400030006800e41e4a03642c2b2a020040509000003081404140301d4001407800340000c615118048010075211140690740505002c400c20020b1780c81c0e10203110010b82241d0041050b0703920421000050f2180d04550700c800f00192034040031000300d6410782c045900030400100700075040c01140c2c4228100c41d12007004120a500c01c3d40c800b40060702c40603040c0a20900c102d002041170f403203240910180 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 620227634 1250 620226384 620226389
    0x1020c0d09120c2615220f03081e0702010605010e0607110427060e0705010c030e04050714072a180c03060510050903061005030d0e0d06020c060a0501 66
    0x41240c4807001d840090f80000300e59013180e15030b102198a00d400301541d0103240c01070b4840c1035003c1c094000000005c03254a22150302c01c62050301400a20740f040709180c481d0070a44400180143c5071301d076000e00442d000b807030125446100103030030300009451045103400604080d51500e0241c1e45031401031000c2d680244490901c44030640d641c500708802915075860705120300686134003a56503108000100d0011507200710390640b4413440d070345440c2c0306840d049000f400410b810305503c1c000c0310070104403913100d0041004c6141c0c0503520943c200c10b1150411004100c00b40c07407141400321449400701c18100d01c1000d40000d500070302c00800c41c2d00301c05410030901c0840e0308210300120900081032080c0203002c1c002c05600480400001400429070341c0076002858641c00080c1c4c40300c40750720780582841d4050000c000404050782618101e841d106040500c0c000140203850381a04081c01c0c42031081e101e0805154403e8004100c0c41ca0302c40a40ca511003243e016134202044c03074002a081018080c001d0188500 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 620228884 1250 620227634 620227649
    0x20a02010206280b0a0321031413030e2806090e06150711030a080304111509130605060c010603050d050c1209190b1c1103062101020c0d09 61
    0x2107020515800b05620f0151502207854582e295114070043c0c4440f440c10001d1076000580000350030040e038500707040c0c1d000080e601c00080c0c1080c002c041403041141444c0d00944603101603044100d80350341d098900352044d080c407a4125003040c0884450000d403510349001e0302c941c41c003030500303050a2800080c5080d41c10b0b000005000711070320602c05161100001c402030700401c194104e403100403d00d132414042000c006841d52510904502d8020712103103500071f500440c4a488501040030540003840030a200310422581b04d000203000021a03420060042590f406038410300280c12603c810000310a03420071080d104007607641e80c0043c000c11204210805a41c00c1c0c50500e01c1c00d10040d055181d036500d240c060030030000000400d1400e03c81e102c0480b640522904002d1003410503469428841807500082c801c610b03e00c0189542c0c1d02d2400c060b2040a00050052030150703d50303901c02040c000440c0040c0440211149061a5100c00d076200b88040e1003410132140241c4a55000c0c02001000c04156070403800 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 620230134 1250 620228884 620228911
    0xf0303010f0b030405070e09030d061512020306040608010e0f0f1609021305040203040f110f061602031504060207120f081906080d050c0d11100b030307080a020a02010206 75
    0x20080032403100710401c580744000c2c01550b90380c1d9450110306085440c1d2101d98080388210900c8641d02020010f08542107800700104040d40e901c2800700780740d2108204090100d62200700e6111410280e0f0020369000700c01510124510780d5510b17030315003180d000714110310040d00401c2051104100c180842d454040c07803c00244800c036102c161249004540d0320518100c01d50007d01c4058644009214100400c00104119103920f02410400501c181c01c80d02240c00c00b0078552030180b18901102000102c041c0034085508080c910054060f031414014010307a8540b00342742c0c90f1418040041200c5e44114070030080540c0707440c0707989003049001240b4203100c02800482c010840c03125501007000d540c800712102404010b103030520b00d0000108100c2d0003900d11405481405018540c10174010700f00d1517841c1c41201d1124400e500115550f90300c5140e0342c0115001038528074400c003502c0d00421131400300101a00e140034807994646515a01c040707040d201503001544610203541c3c040c0042540400e1008061 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 620231384 1250 620230134 620230139
    0x23301080a0b01060e010912030206040516080d0e0a1e14060a0e0420030a0915060302010e06210406050106020c0906100f020a020a060e0307140d060c0c12050a020f030301 75
    0x1c2100b0a050040500308400801500c3c0c59078401c3d20314a000f413102c40d035030940c05e080750b00780251618000c440c00e0380c1d188240d40c403103442034031805c1e1444121080d180141940a5054500710b0b10045040c92041c0d0100d045003011030418080f240c41c0205000c10711005a085162154412614280f140440d10a503c28040d0594150300450140e4054100319030000d500200c602c003071403040007098030030b00482c0c80200810040811640c418074100d40110226800c440c90074082e80f098403294040207000404413524040d42e42004800303400c0fa107a95513581181e6103035012001c40719103002c442c1540c2290301d601c01007101c5501800902d030303001000c1d0340d1808986803c00c00328442007100c0c8a904104051a01c107040f07114400c1c8819802294010074a86500340d039904010541c200c6800200e1090180e01c000045109080000c42040040a03040d0080c0008076100da03070060100e40c0c590024004104415800150b600840001480e45912000d8a401c1c0140000f4507080120206052079882000103 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 620232634 1250 620231384 620231393
    0x5010e030a021c051602151c0c17010518040c0e0c040302011d0108012c0f04060b06030f0f06060d0c03060602280204090201030209210d0c03081303023301080a 70
    0x41030741d1901901c11f041c40400300300c01200144149a1b1180d00010080244403a80040f41c1102144e044180e6480002801c90f40c20401002401e20680f64003079190740721000d118a41c208a5a40140100104091641d0790411154068001c40303030346002c20f00000d018000c541c0c02a503d5480044010b5440400301e000c03c002800f00071040c09114408141c5025036103503076244a10501014251003440c1209003445060b02e100c0000c2990104c58403410061408003d05001c42502d2250304020328419060719800c100618240e400381c03225400680030085c17880d4254641c05080042e02c12680c001a049150100003400d0004482e22408d010844d40e60030140c420b210541c1c800b0154040300d00103101d004a1006a000b84100848550000841d41504941000203102a6401c00c1101d0503075900c0c040340d0f402100d00044505005002c1100b40000c200d54000e902640d1000d03500c607004940955240c0c1c0c0c514480048945107626034800c3c000500849091488250b50040000000400380c00005666 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 620233884 1250 620232634 620232667
    0xa06140702031b010e0a060e010509010207051b0102161e0807060e15070605010308070c090b092811040515070f1502251e020f0d05010e030a021c05 65
    0x1070710400110f1040480c1031a07801e50141e0103070942541220041c00c000d1811101400c1c01a9016195502e018001802080f041c0200c80d00d059100f409048a02c03c130300041c100c800e5002d60140e0462080380403441300300718107046030406041801c0e200b24200d84115602e03001c80350350360044139090304907080801456400c2000100d039244100c80300c000600c44114103640300d00800c80081c02c520306000c000024407500702e00505100740920540100c0c0d5445440d29005d6504d0501c0840d007101c51500000c00350226200048500d0000074807107098000424003010a640c2c0611842040802c00070b020011840c0c803640c912400052140032a04003482c07901d48102d1007030803440180481078155107643d81001c040d8102d88545e02511b5560481080c20100c2110421344603004540250f4072520f08442c64068109411003254001c01040c203c264035400e0160443c100c1804469640d02d44d856441c1311002030016042c07514681e4000c240d108080c20ba41d10301d261284c581070702031080400ca255806100b0a0 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 620235134 1250 620233884 620233897
    0x70b090a051009050c0a06170a0507050301030b0402041e0c18030b0c13080a0602120c030f07111f0b09070f02030306010e0d0b0f150415030f030201020909090a0614070203 75
    0x2c0000030f241080e41040350800300504e000c05d901085080000c0344280e0802c40d21210300c0340790902040d69540300c40d602400c60307509840c082d0200704288010000901c9240a455100c1d101400104602d0444207110300308840d01591440819140c05c4044101680305411130030702843c00d0184664076141d80c960b8a401c07200034041070200795000901c800c00c5040b20031044020f11900c401c5410020342401e2400080d0040411810022000000316030391107250010351b40602c89001c0245455160884141c96030065008607001030f004020306140c0000c0b2841d1420301461010501040000e401e00411062100040005043c8103001104130101075000003940c0d030190003800c040c1c0f0300c40800c80c0020f00c044c000c035200501c9042084100312a807440301c490140540c1620b0310524100c0741601c200011703502c6405001803020f00c8590200040740360100301104082c0a03000041c03400e40541e001c622280000ca8528005500842c0d921041020f14400c0442c084001000c400903030030300303a000a48912516 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 620236384 1250 620235134 620235163
    0xb0301110714120c010204090b040603052a0d0b0411011404090902010915030209091501050a4e02071a0907090c0f02070f05010509010507050705060a05070b090a05 72
    0x1858460440b8204903c442440840c0940d6441e613002d80e0449020f903000d030084500c1c240c00d0072440c2145080500680d01a070f940940a0900c0d1800c00507511887d00140300713040030640e00c40c8290006510f48255002056014805064851078a82003070702c00046820f403040c4c10499061041030040080005640548040b00c2e07000c07985090f207000480f4015804e4000c1c882404914051407240d82c1c0580c0148070400741a03031400301540e2452141c6441c0c2028218050100d9010010346e11442c4c4100d0000e60300200300f62450a10706004000e000340c020300c00341c818880c0c8084849440031800485462165420102c034158903101881e510343ca008141249211407440d03c000119255013414010103001c0d0031754a02c100711102c1107041c004d1808032001003e001600601601003003050b0f07414070f140143e48040c7c4a2031b1501b01020b0046481e58031140c070950b018020700001041d40c0ea40c0d400103150f0f0402507036a160704c50351030b420040030800018082c00c0c1e02d58852540030300040e2020807444060380e5007 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 620237634 1250 620236384 620236403
    0xc010804021c050607030203041101090f0b0a1b0503030105150f04120f12020622080405060a11060408030601110d170a020c01061502060f070c020d06020403150f0b03011107 76
    0xb41640303000b010140d2000901038080c040c1084002d5a00d50701440c1318034006c071400c14049038158015280300850703001d5150a90111401404032803e96001400300d5034a5140c20740704104040a02c40003001c5038003044415030000030040040349025006c4071080b140c0c030210b140c07516440100f1882148198815401e100e00d10000060500904d03a106031034076a0881c400d40070040c850706000351200c00071030b400310700113154012940c05003582c0a94040010303400300c00145490700300390030000540c0003010000200b01c03449080011240c018807900c0e01491052640b01e40701c0c1026800945101c11008207061035a002030b422403105a40b0048450710380d41c440c583d0050356221069110045e00c42d4098014040d0308041c000070b1030b1200340e200980030345000d50954680361070304265a6405802500c2800000303007800c10440251410328041180c0c9031213090010324241d03a0390350707680f9486000c5c880300c0b44903541e4189001014106000350615600214002c0000c91030305c220b1508079018004010380140403 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 620238884 1250 620237634 620237659
    0xa03050907141e040203090601030201080106021501052404060806090109092f1509090601020d0f11070e0c091005030907031b0306020412050106080c060406080a1506020705120c01080402 82
    0x890b030040703ca04000190003903580340350031010155201c40a1000720b00042c040b100025055101091003481e40e0b4032100c004011340d29010412800442d00c954179035120040507820031029030024000c2c0002c0607691250002d5141c43c0d010082c211805900103c0024200f11200d400101940098460312040400342089170104003012105404070040710b40d008113481505c040c0e64074201000d40700c0e800c41196004510350b100783c01280c69400c140400f07008070360404c1450842900a00300312b004c400c1c6003800c807075500b07035940d42040540700240e6600020200001e9549460709003500149605803407810480e02d58100704108555400d114403015202c15005020812a201080c2c12400290340110040d900e4603200c0810f0540c0300283d80040350705610b4000d00080340840803070440107008000f810785080030b01c2d02c0c0040d204070380000e217131303075041d550300c0d900c000102d280030010360301070301c280d07401010118145001d0059038200d0001e880315551081c041260030383c0c3c2c00000d0507486541603800061800 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 620240134 1250 620238884 620238919
    0x6080d0c1b090e0318060f0a050d090803070c1506030308190b0405040c05011b02060d0506040905010e0f010f05061c080c0a061406011b0204051005060f0a0305090714 73
    0x3040d50441a5030340d007410541c41c41001c0c0000035201e0080a803001c045054964030400410b845060450106100d09110408c0f01500440c00b5125050041501003950182d6684a113031691003214a4004150404012000d10034111071400d011040c8510800c4540d0a584000c0e190032001401001c1003220945038101c9050981c0000075072000160060015050030300d041c4d14a50310a00070503000491440e11084110074812003108019006006585000307010a00c0f28090b000c002c061603001625403d001c40080c200340304500420385004054984031016007141c5003505c400c1250499071034204420701080b5541c420540350740e500030f6550540c00d01d107280b4000d4410f00503220122143d004d5031200d681404419003140c400010641095460b40e03440308010745030b00d500700303a4226a5400c518400001130601e640b1180c0c020071042c031610319a03a500d200060303940e448030003035075441034021036809005034241c05a1500103c0110142c0802410209915603050024040368800c040c861601c5a019 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 620241384 1250 620240134 620240183
    0xe0117010e10080708010204080c1906120b03060405010605030c0f0a0b0c16270501080a0b04020a0b071a0a2711040f0c0f0203030630061006020106080d0c 68
    0x10180305050b41c40d4250388001750350003074101d8843c024440c001e15050400529000840d000c00c3c421405103044042c0c02c00c40b04561011f20f204140c0ca511b9900c00603403e190360100002c601ca18440d00000c80d0f0b060400c004d040c1000012020107000e80364986c000e10080d5036101d10f03802903c0c0300e01e1096031201307010f148061918101c103d000c80c0454690202044002c4c01185014212500c0c21a03440002a8404081d04071002403081a8190b040101044001050283d01d41e42240c00103064802c49034a650007045107600500080741c140814480a4648034079080209500203191602000307407550400324920302545598400741c22511081c0c0780b401700404882c2c6030741004030103002000300d201300d004c1038401013401e540034401042e00c1000081e032036440082100d11440000d070108982011503c092020054942d0b0721402c41550b08013150342e00b00003040010721809980d90045040391800074042d08481140c1c00c488a150440410410055041024110459484028003850944201104005 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 620242634 1250 620241384 620241389
    0x181e09030f070f030801050303180405040312110405010314011a0d090b0f180111090120030708070213020a0f0e030a05060103140c120c04020309070306020c010603030e0117010e10 79
    0x200602040344010700c003100f080b42d054288252110391007a600e40041590303d00500c41d0040007005000403480180c186508a030780c10511a0420009a038485903800d01503a04c0c01c4002e80e401c04010504006540c0d050044590492144440c070b10701e5410b2035440b61100c6614000d01c0b51a1074005049011802a58031121801d81c100340b00740b501c1e08007800081130498040e114400c4d120500c0c200b000c85201c043c440c20880300110b115103841e00e12810015520b05044402c550f07903c000c840b81d04002d10f00d0620081405910031100c065840c090b503c100510b5644500d440c1c0c02c031741d03c103006190b03a80740c00180410b043d01003814028181d58404001a180055030000188240940c80c000010050503036a002010640781c410f440107001040288400041e0340c00401210307074003111001100e4203040d8000e682001412013a150403d86980b9498166030015004621685d5201004c01c28585d01c4600b4800e005002d00e01007400c0380484507032091410060103000a20740b001008126541d4403140f20200 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 620243884 1250 620242634 620242657
    0x60a110604050d030e0114220b0a02040f1a04140402071203050a0b0d021f020f0a0c06080105061206040b03010216050109020a080c060703080a090c090506181e0903 72
    0xc4914081c5405600c0307200508100d0046170900c1340c10019440d040c0101ea9602c00e00710ba00482503901c100300c2c9800031284640c2440b8142d9402d15040208226240c2c00d889008101c0001d03070b5a910384016032490000d503a12071200141c005000840e01c0c020307241228103c42e000a240a5a05030f1400020000d02c81c0f0071000b440068803d00302d070800f42d01a0421486008407404c00c11200800078140304d111011440c00950005210462015202a407074002043c55414411143c0c00a45035202d075180c50036070304041d42e0040d0303001000c00a03240d1299005000d000d0603034a440c1000e0724841966100034002d82001e200d5030312410100f5954801358140d961181c11100f51040f41525410300c14000d10f02c200050780111020381011034152000a4419100c0c0d60103000c003844c0c529240c40c11500c0d003401900361013880e034440380008042000303850301c84007030045a4000070350350410f9000c20881d5841d805041c12810000020080e05000d00b9500001e0310507e0210b1800654600416900390301c2a00c15a80 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 620245134 1250 620243884 620243893
    0xa0911120109020a0b040f0504020d02041a0438181302040816030b070516020604150201140c0a0c0218010b0c06010902121501170703020a20060105060a11 68
    0x1014180d054110020182c002d0302c58807840741d00c9002c0c480f40b0748030301e000da0841103486040c1080541416801001c00d410003603401820300340c0b0b0b80c102405860f44c0e1110b25100c1c00b00410284201c1b41101c40141ca4110844004200002010700c540411207078844072001c54800403501c0742c040d00c2200101d0030b406030010002c945424402524000a42003030103030080620551101c101c003c24502c1e014000e4a40000750401540d4036080c0803035070b962040c0c2e813601c04501c03000281c0b001a160b41000c0c102412443e07089404030f148002c0b00031308651440c40d102c04982c03480403d000c00b6078030031011600c940c5100d140100301c00001d4000300d038404000184071041c4801c3c020001401401d040e0240c01c541c00c0310300030303904983d0340c2c1c0f524039050380140340c2181c2c0031034580301c082060f152141403281020f00060411074018029a500041003900480e104400300e500041c00210044d0311000c503100000c2803940083c801c0d58a0350610780d07103010500915000d4100090024a034502801020030900000405c8030b = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 620246384 1250 620245134 620245159
    0xf0201150603060f050d02031009021f050304022e08090102041a190503071e0e03060a2a05031b041703041a040b03130809030708060415060605030a0911 67
    0x400500e160f201e200704c0641500320105043c40e06c035150040103600240200801405000d41e10014045404200e9108015400701d0800f003c003641c006d01e18802e56110140c45e40740070300600c030703882520001844000000d10035a07421380032441d01500d07443c1080d241c407401982d2150300d02c5009102c0d075001075480e9064694011410f47c1220003e1007401e2050742c5800b180345d041c0100307032503074001601c4c0e080102d0060480a80095001e50040d00200d00398a840000b007a80074004c01e0900c40e00781d070b035080210b48460380c1e041205200e0071100c0c20000c800c07510079001c20b80c0b610018014040942591040002d00d0714000f55225440d05581c060451107842400100021102d55600d5001d403003118102c07620008828810904201640c0c2100c18450b00d680c5103564502e03112043d9000c841d41102c101d0405d00c090420f0f6201040568050400d42c002009203007001d00b80051222a0038028100c19810900305102d40c8da8090141d9401110004010804501078500354800d2070090900d10b4115a041308503 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 620247634 1250 620246384 620246387
    0x601120204183c0807020a06030209060a0309060209040942020c01060b0c1c0f05071b030c08010c17070203091c05010f020909091209011d0d110306250f02011506 71
    0xb09000d80c0b007104d004034a84c8c0da400040d810303070080a480560285080c070207603014074007a07003040310300ca03100303c2c2c006141079601e000107401c07540c200d241614104019084201d8444070903508403134210740e98402101c807084504018000303403c0c80c4003520845030041407a4155902c250094005420504012070311a03010034551690752020f856002d110303241c3c2000f4849814007640b19400440e206a079824035010083d100c0d22001304068041c200303201e4000e64004046414000c8840181c140c070380c0045909074415100070003010b5030000382d101051005050044040d000400c42d259401c007502c030003110403816800040c0c80050010090402d5003418014441c0764010341c000c00350300400f265400500d803100798040385c0e1404a03a24207412408100070060a03580a07a0b89040f11585034240f4440805440e0040366074170b041c1c2c80044603e828003c0b03c00d805403074280551603002d00a100c102d1321003801410341d03e0b110210410003000740302d40300d587c0191184c0300b90801d8041030201030384043d542d99603850 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 620248884 1250 620247634 620247637
    0x905100612050d0305070e0d08090a03050c03121c0e070b0706091a0601090b0c0703020d1b051509010c0204021b0607080106031a0618030601120204183c08 68
    0x14221228054000c443e00e981c1e00902c25503000b4002d540d41c5d281082e00b2801400803c0b08840740540344850f05100021103580c4a00c0c0050185100310b0141c400c1c1c5010300d091501d0b01e503905925911286051000750b9160f400c14440902c6509454404a8600c058061742802d01d01c5030f0b0040d0441010010f580410300c907140c0c0160076421300c01c042d00048001a2800031341000400d881603800504810401c12141c402c21025000140380c2c1015201b5070380e52a400500388001c041d204440b0030144108543d600e00710122910b0081c00300740c0e00383c013810308041d51089084c031500d8041d43c14020060b0107041591076a80c1501e40082c90185102c242c0d0510a840c01d54809c02150f2100000e41c54800208007240b1078001c5d0200e0030394441c40340188800d04001c01040b1b41000342441c0810341a29009000d0365805c0111900a25801c0604001e000c0c1e03038018001904c68001d10300e10b000355009101d00000e100700c4840c11030500006040a0f5482d035155200c0ca0611100504000c00e50480340d8041c14440042d0 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 620250134 1250 620248884 620248919
    0x14060f0a05060f0c120c37030903050f0a052a1c170a0e010c1509140705030d320301080705010e0a0509040b0414150a0c0c110409051006 60
    0x80460f88101c000f800c1d0b50b90351b0320440400642641205240c0b0b064030f058003030360000304860ba065006204a140304848071400c2104000d8000544604c1c041083c40301c1440200b001e2048a005420ad41d91107072205030761001a510200d803009900303150102d6250300284000410034005017910040e4160343d48005418111500595404c3c0e0b000c0103064102c0c05d000c040702c03c41c101507255010102640d00054800c424080c0c2c040d1400d8401d80910101c80800e803041e075041901c00e148a4070600340403d08a4546200340d00014040c5d13102100c40d2005640111740a00a4800b006001c80c00c94a41e0200207090303115100e14420a02020001151040e0085294029a0002c1c1d030303401b1104000004101e91513115208098004040c0d40200b000b140c030084a4652003801100c001c0d216680d80c1034158500300c03804100080440300c1d07105125518645009440b8500e10501d0a810b845585031030720881842d110034414410703942c1d08108000c0190a00c0840e9180100140800c80d26035918000c0711010b4001 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 620251384 1250 620250134 620250157
    0x908011a0f0108100b090105040e0c0c1501030512030a0b030109050d0311040e07080403020a1b050907020a030210020d0e0304090f05061801450c020114060f0a05060f 73
    0xc0001c1e440d4410381d1a5032098401c0c104c03655890385009091916640000465810040c0402012039040c00c0c1c050014059855011140e6945a441a0050030f15240c0c13800303055045c100d20300400105000280e00e8000d5924941995902c2d11008a460010300c400282c0700e416501301003049060010200d011080790042d070310305006100c046501144e140c81180980c000240100c0301242520348034115003540075200e03004681c41141e0303d032191609441100c6281d291031000c04010300c07043c2040c207003070f42d0400710600081100680e2954040e407501c0c404110131541c1d50340410725040c6402070790009170145612400707036a44e6a84803055a0b018020402c00c0f20b00c2c44e41040c0104095003003004002d221500000369551075a401c10354040d10742c0034840703000066a04509080010740700500440c0f00c01c06d044c00ea211060580c8503c4c10026141c00c99100010359250986001102c00d1000c840d551025040352040c41c115401c0340082d0443c40942c0080f5004603001c1803010030103509600618541c41903 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 620252634 1250 620251384 620251399
    0x3120807030c05160f02030304030f0b0105040b06070203300f040806010b04050901032a17060f070c081e22320301060924150e010f0908011a 62
    0x70b000940d043e210711504146081c444002e680040342c010541e110886100078140e928180d80d030386402d540c0b05400e86091784c0c1a401800108818500307817180741d00b075000595030b403810b107062a000242c554041012801c4003400d50b6082d40141d0140c018800c1c8210141d40031640c0714084880c1380100703504240918043c1c1c0c820f050001c60140405420766040300c01c0203040d40044e07030850f80c0305070850303181a4031100c1c000c001038000300303800c03018030b000c0d00c003a02000071b071203080c0781c200c606480c6041006840115070a8454052266180c2d020510480f1240c01c201902e83d00c3d00000204c19000c1c060714607e150720040414422002d420203078008102d11800036110809a4403500c048809008008000104815044502500448001e003d80d900c150060001540c6a1f80b10102d4098814400c02070114007241c41c0c007010204e44000d06000030b06040001000d400f110b9290103040c4160105806041c041148480c60400348250509000390000200912031441d580c078280c4003140c03245981c14841d41c02c = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 620253884 1250 620252634 620252651
    0x1707020c100c0204060e0108030426030a0f12062303030c030c010608060f091009082b06090b0d11240a0305071b02060c0f07031a01082103100312080703 67
    0x921b080f181030760345500140d0300d030500d09106441550002015804181200d0345c03c00030520003840509044882a1604e0054200168000740205440c0f410722494514017401030060310307600a203407005010290801301241400800081c6075010300000d0010303a200029003069417a2041d000101280c200108461540e25246e180001c2407404440340c0c0195030201421103042181500018203460168041d90b00d8071240f03124100988a80448688142000d4200d80c95040810310452005101120b0100301100291b40000c15900350720b800500351000c0501542036541e10300c5d580e000d4031100c1411040f8050a6004001074903003060000304040b074a0007001408882c0506820f05000420018205e00c05c0056820007030241c00001f034075030340d034416014001000d440400403100518040e140a069060305441c4000c107002c4143c01c103d14030307000391101045500d021f5440200040984204c3e0381ca95840661200d203034070041c0d2000e1b1000380c454054402094104d0039150207240745035000c0c05500e1 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 620255134 1250 620253884 620253899
    0x15121606020a081611120c0a0603020901050702090a110c010c1d09180111130314030c060406020c0c0603011202040501090614010333060f0804031707020c100c020406 73
    0x1000c0c1c00000e0001102000340b0804a095840444000d07445030091828041c151404558801c01401468501f51700070b0340360f1840c40c40c090310504e0043c0f61624095182900f000c000910130700440c10020300940b98480800d0185546401c00c650141e2b1140c401c58440c00d240300082e01a042c1c0c0032440020900f10480181b1448581341e40725441400a0001c40305501c401c112624000707900d40c4048050f5685001022406103680001d008500581074448000e504500b440b44122a1a041900c0300350f0042000546000d00070074141e901c15000640140c440610901c000c1c02c0640c003105c4690721000000020a02c24000d880220005e4003d1710204556a01d5940310000c680789800b40070307030012804540806640c400d81000c6900014580440078008045102c000325801c400d0540100a0300303c1e05c144a6240d100404554041c03051916110a0030701b500d0180003d4800e10b0a90140c0c8904000100c3c40c1d402080300e000484005054044487d12203000200750b80c070031500c200c2c4501e003041d0700025142d = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 620256384 1250 620255134 620255143
    0x50606090411180d08030c0c0a0c060e0f060309070b18030a12030506040c1209082101030b070201180821010e01052412040203071203080f010603051603051512160602 73
    0x345c2e1000c07142d407a5840d005240030b665081846c3e00d203114858031100d6000612108460790003000136844038031203100103001b0004a0f40c039402d07000b0700500c428810055451000644003045440510741c0e5a0744005001d8000c11410480056a802d849561000003c02100d00b060000c0400c15943c204042d0b25450208030586d503020540c0e6000641c654070041010106502940c80244210304e1145000c000c816010240400642e0103005041640f004009000c44a00c03180d50040c4944000c100c04151148455140e90408030060080900401c4d00081c1441443c40e0541c03d0b20103c00e080400d40c1c0d90144071140820034000c0d1401a2403c1ca605120560b200d4850500c080000380d2403070a21740305100505e4906c00042043e42d0521400900280c0100f44001150382603010b59204251882c007010900070040040c0e01c0303801007501e840100451f8404030180205e40d801d0a240225260f2184040100c086003103210340b0b648041c0c0707444000c8440b40300150320396140008142c00c3c40c0d1665584800e82c1c40b03 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 620257634 1250 620256384 620256409
    0x30b01030b1008190509011d06010f0303050a170a0603120905030a0602030a110c1c0e030303070f0207230a05030703020105040e060a17011514030a0605060609041118 73
    0x2040ca80341d2450700142c003d070b11040d07000030840d50a4072080c2d000e00c54401610800c1d90501d125940d500320b400040c040c140314001004403a01e000780b456524060b000d04458480e4480039040140106122114601c114607007802d2080346044190b003800c080310759600a001c284804c490112041083d260481e0069821030219000140907125200c4107413161000703540001c000c0d030552640d522412958032801005040400b030720030000e242441a86d1000045411507100e4102402004503c1420541d400411642d000360145488500124500010b0b85050f80e40d8100303061080410140304800b0b29400800c1810b41811200141ea05654100741602c035102800045c1c0002c074204000e100a0002d03c14064110744050800707102d8030740d56030751410b441e28a41c0c5200900d9450341e00c04a841090341003100040c010301890411030768403020001c0cce035440e104075005080760340300e00025a0980d2001e00b6142c241130050000c0c0b000201c00d00c210503032648460f4600390524642802e2003014281451210207 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 620258884 1250 620257634 620257639
    0xf0a030b0f0a060f080a02070b090303011a190513030b01121506120f1506060503041b0b09040e0a0f03080117010912080c0d0f0b040b01080c0a0e030708070f06030b01030b 75
    0x151002c2403d13080b00c05a60007480c900640d5000c10550000a8041280b9481604088046c648039414252a90714004400c48508044d0300140300c49014003c2d80c5032500801c45148c14607a585040251240318280c505900c0075000140f00c000002e00020500e41c034041040c819090b5070f00c1000301c601c0d06000c55807035000740030000000004100018100c50011414580194440910008800c1c1c82e5001e4075019005000000e40100a00c0104154903140000101c1e00d8009a01c5c076030306041405401e8044d054a59208a8980c102100c0c003003000d1201656042d04a0841081d0701200c1c02c021701002000e10407041c0700c6903d0f50107042d98031010310900c0003c030352103205a0401e0500c0503080342c0b0508040d01419920300708000c1203140701024810105800c00a290100e9078061100821080f110081655410301c040101040800e0940b58200d443c44221401c08130041c0e40b111021915000490308111039510402c0740204600d82220400b6088030840e980900562103640c004405403031304020740302d4 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 620260134 1250 620258884 620258897
    0x3010617040b070c05033c0315041512080a081f0302010c03050c01050411090a02070c0e04081608070b0105100f140f18090604050118050c0f0a030b0f0a06 68
    0x2c01c2203114444d04480d070350203401101e0030404000c4114030001c10f40c80d1035012080310b607034400c80211320303601e034107403601184c911104d0131440c01c20403000d60120313403450340c034030803540c50f0031441c10b40d4481e210942c09006840c0107180c403c0106d103044216540410910f0000c640301000050720b58226009030001c0400e160304041e451440c6500540d502592190308600380001030007400c081000034440e49104a00504030402c0c031290150502c648404090501210b1500400000c0c010451604004007207803246005d01e01c0700c4d034441c1440038460288601074403065a04e00030340300920540002900c40e943c003610701d0b0f4a05980c0c840821400c600450383e5500498170b0140b803c3d0b0b05900503d60900c030481b00c1403d041c9030a082803504002c590000e02074460201803492441e13038504103004520b50140c801d8400300803039410048504812140c900020400f180c85400140c48400e1100945410304c13a40407030f05031207c40441000c2c014048105007a0f02074103820701d642c440c0d46800805082103806684548 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 620261384 1250 620260134 620260141
    0x204260c010207170c040e06040309080303100612090803071d0625062c0105010801051012061e0f0e062203260613020a050f0306120f0303010617040b 66
    0xc880b00d4500c0e413010001402a408450310907100d60007114454034205018146515040c50060041d2405401c40080c6038010720800001500d2070101c58140e550900b08103225123900c01d043c8024100c1240c0041509401006104009400074412214604403030089440100304d6824031445006d031080101c50300003404a5200c403030350b0940b43c560117213004400200b4075600386100100050490b81c1c1d215401080d410141d100b0001c03c3c4983c074050079403030000340241c1c108203d8007104c140311800307102003400502540710200b0500d0703030055806038118580d078801e200c002000c46008204054040c0307003060418600c03007044100418050b101c0c8181061041c01d6440d5102024160003d43d0300c11407e00c619410581c04518038290400307624000062040f079a46041418060f40b540489c44040050f030050010541c40c54104085c1c8903111a44184240c0702d640300400280300c41001c1e5522019402110000400032602000450582e5000e46843c09541c0c890740d00c2c8140804102c030040d000c07610141c0807 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 620262634 1250 620261384 620261399
    0xc0405040f05060702030d0b01080115050307110d1806022109010c02092d011a16060e0105150a0812030c070506070905010e09091506130204260c010207 67
    0x149401034001c100e0000104042d81d585490711006590400142e800811503050305900d9010350400c0b030341c0078a0950080c1d4501500040e21840c2d101b0703402c00344800840010303c0181b1400a0b900201d1420084802c01c0c5600c11014240a42c030107100c0da44802601e0020400c5400010001010904034200c1c22a072030b10424801556081128840e04020314007003c207001d0790301e0f944500e014202a0b0500800124560920b142040b0100c1c201c9054070021001007014441150030554010700c400c8500d036549072554101d07040603030800c2008103d5403401e2304a201c400015800148140006048955042d01d81020000c08206074071506616a00c04d6000221803141c44001d90341190740c0042560810b0441d41d10203041281c01c0380c210000980c0070200300100e40e8004600003d42c4802e444140681c1483d0455540b41c04c5156038240048105101203400e130380390b80c030b030000310703255243c00c115112511066420041c1e803d8081001c204015102c68a00c1710001080c2c0d52081203051f00100720343c51030f100d40c = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 620263884 1250 620262634 620262641
    0x90a050601022d1002090405090a020319110a030b040b060312040504090602090a080a05010c0f0e0f01020f160612180209311407030231060603020403030f0806030c04 73
    0x4030860342006804070500820030206a88100d41c0304c2c0542c41e4503401081c842201c0c8003d0400c03d080d4007181c020f101607100401e480c0c1d2107010003480c000b41d003076150030050464609103100c0703900310180c41740000600403e20000d9002d188110801c0500b51640030816070744403a04010361403903000c2080100550318165100302c000c075108070320150602c8007040018404000d1580b0030101504480c01e2501000028495a401441c0740d00300881d40201054008000022070400c070b500030002100265030a0b80200b080704440c4028134201d8031500400c041c0c042145c5071a00c18030022881c0b040b07802e40c0d1079060340034032a0401d401002889021019408004506030068010075440c10010204000b10305c90340904660001c0ca00c040300044c5880b441e11001e01c1a586860581d2900318210500040e992840d80750700e840c0c50501080703900104401c4003030840900c40124401a4601079002595030b8050700038004482c060b407a1004140c186440030344a03010f0494020b82c0c941c22641c5036000500c3c040d403 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 620265134 1250 620263884 620263933
    0x412260306100206010b0a21052805010311100203070b090709060e040f060b010c051014070e030703080903030903031b0d050406050d150b0a080a05060f011e020f070b030402090a05060102 82
    0x41c60503da9083e4541d05e108642d02a66480d01c070b04cac0e00c0700140b0643d000740c8000c02409142c1c450100a19851a1601e584455880782828130030106e80d0000f0048501c01c100b59801c440c1c09c0720812000b41031a42c1e05a036a800e091040040c4030f824034800043c811002030401e482540c10641d00c2c0e0b000c00740e136039994009261a00c050703414084c00c440003101190040100c8001c0324001540040c1426200042c1c0d01e800c0402084282080072280484469450104900c4200c070752002495840f81da0440019085004280c03a66406120200308000c125803400c0580c07440c110b584d000d0b0b40c1c00ca0b009840442c1d082c42203010f0a80441e0302000f61205040141d0710240c180048100420341180d00c4c1c40203000079511150040001401c1034040c8401d12040e0710845170003101c01c4803c544007160440000c1c2c46480c0d20b0186c0b1031a0f40081040094080c028401c2c8504038914200751040ca5864007204111354100351030503030203401e640c0c0c00101044414820280500700580082c800d0120200800503c2030460 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 620266384 1250 620265134 620265167
    0x604020c010e1903081305030a030b150d2703020303180a08030a0203160302090109050f120f0a0b0604020901171f080703051506060412260306100206010b0a 69
    0x5001c55a50581c09100c80241d400f0042100365410f581810020032052024204040d10440c0c0085040000c40c00402c881c850034050402041221200000507010050300584407484440016036503801501e5500007110075005038270a9000700c2c2ca40d400d0040403102402c00078056403007000820800882d030348100742840e404204849001d865550b890b01703a40c0083e50022207040d00801030112031000c46601414891041c5003c6041540c90300008016488d076104507401041498003c2c1d115031190001c0712114100641180d603440c0303000b9041c994694907118151000c40341034020640e145428001c44401020503500d0007081d80c01085094200f0102900f88554040c01c1486031780144001100c0c040144980000761603c84d10707505146040c220030f4184800002d2180040212560b41c041c180c03402c0d1442e03105648000310b050301c0c1105102d0708104201c007070700c40c1b8400c00001c0d2042a000851180d0f40c02d0300c0340713940c61185400a03030340c404080c010026022420300001d034015105001070805104071 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 620267634 1250 620266384 620266391
    0x60105120a110d1a0111070b0a09090c0519090e0604020a020307020918070509010e0c0702031603150e0a0c06110a06060305070e0c0f04120c0e150306011208030604020c01 75
    0x20002041c15603005119525605495961500721300704140c02401c0600c1c020700700842448211600030703072908598010802c0b000d9001c1b0300c00400c50f1080c03c0c48406024442030800042088003001b030190380003918108200c003901628000d0071441420a136045900100c146c81c2e01c0e0300d8200c100000394102c0c22004003144414020100541ea4402006003d019040308503075a480301d01c41e01c035041020541281d4090018400104040c881404c1916404418940b582e41c03210218400242031101003820140003170440c600c0801407001c0303110501c41710f01180c08200314401901258549801003448040c103440d10340c0208200300340c0903415001d800c41e81601691039030714250303840e00102d41c01500103940f42e501c8070900348005c11008440f40c2e08240c042c0e41c600c0c04d02c41d4407040d46000b44aa80034090010740e1008443d01004106c0c02c0700f45c050886034040d60080e00e4424403a00040728032501f5140b00e0b00c1404000240703000100305400000e50004030b60361840e0f40c2c003070501001e5406070700350380746540d40d = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 620268884 1250 620267634 620267651
    0x51f080c370303030506030d0507120c0c0801051906031101030903110706170f01050a060c02150c0d1403090a1403130303020d0305090d0507121106070c0c0806060105120a 75
    0x80d2000001100781d8038508156215045040c02011144001c042038000c0c0c0c01803107074488a039000001e031340c02070342e01400a1003c0d100c0c0042c01c45502c0e407001c2005000b269040310101d58000d040d04000d00c1041e801072028a51032034103545205481e202c1c8405084100348284050700c80d44690402031040d4040d05040b824041d04480d0185411390503403159001842602c001d04220340c08110454201d46503c281150950415000448a00240c410001400284003080b0219165442e0407a814071020440a444044181c5500e4456603949002d40c001246ca140f0440059964019207005003802001428400203690740c50304801c074118142d41340d510052040c807240c2b0b804844510059446603001d0160030840c610040d01742c403000b07040701600f500301c100038031060f9602c00107640055400070712114451811000c2522445104a50348840d8003074072081094803038101603c0800c50303202d100e41c4021a0741c0c4100582e1524400c0c1d90242c00201d0030000c1000035070550361481d4003c03801e94800100d244 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 620270134 1250 620268884 620268949
    0x603120c01090c1706070813050303010906212d0c060207180605060d090f020406240203041a09030708150a0c081504050a1e051f080c 59
    0x20420310018540703a44846069041080c50000b1100628180c2003040100c201c115415880d11380040c0350000308040c000c0007071002000b00600804d266041802c5d00e50702e50715003c40b90094103040c0038480031072190040300304566100520184000350410f50042d441400409010a01d80c4007420752a440702e03071035171100e001c500d01c003031601e00800b0590014000d02d454102000c200e682c03d00c0c0107070442440c05800704030a840754004c480342e034000c00c20009000041c0e440d00c2600302000700f034041d400c40c0c600342010070090360031405401c1c8185100710761100100d105c18201ea40b48618040c525680240d40b10304140a90b0000140040f041c0007419101c2058407008510325105100ca21090445141c90a00595074800c1c4101d140c1180030b840c200d60b2501d802c40351010341104e1560564042c40c2c1e1640003030242160b55000c0119581c02600850300c6020050010700504816900100d0500c0c07030b10703103c12114020080f1701c001c0b03910304030141c440c1c9400941005030b03454411420400d401806541038078580c = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 620271384 1250 620270134 620270137
    0x5090d081b1b100b010f05030403120615170901020c0c0607061b031b0c031b021f030506190302091614040308071725050f06090703030f0804030c030305060312 70
    0x7403044801400001110a404030681c3c0c4c10f0f080d0181804140c91211110a0b8050300320b9500a0305814a12190210b80c40600c004050307650041c0035038040403841185c91640700d42039500340d40311604a4101034031501c00890803070ac070300921412150b008035907081d050f007044400780580030b0060790001200d62035005d000740c100d00135003801d04c0045d56a9a160301c41100c24060155182442c0c5040040800f59070b5010b090004108010341c000c0d92000c1240045641e495070000c4200210041022040d48940380640a0328040d20390b18855140341e005250801c032412010811250001c02c40c03a61a142c1200c3c1540e4524402000c2c1c04103c0d10070040340001850f07000070401180321380081641e851082c28a84c1c40002d014403d1440c90703504029042280c00c640303110003244800301d4100384c0d03a100d442c41c3c120300d41840441920198007540c000c002d80490301045840449000c0e48403840410707040941100d5118040f00c0045c0400d6401c84c01d040840c1c4a58421a0704c06070182c11140c042c22411040b203002d = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 620272634 1250 620271384 620271427
    0x604050d170415020706020102070b060402030910021c050112120f0c05070f06080f090714061c0519110d0b310e01020403080901030c050706090f02010305090d081b 72
    0x140011100c019605130b60401c0030b40000c003c544002c5040404030340d219041107402030200c80c4199004400710300c40c064280803904440d412480b04542d24451391400f00b0704035892035810304421b4517010001820000401c070708035070a60f1000c80c5224524031144180e0320901c41400c0003040004800015000440420803000a0043c008000303d181e850311100502c05000241020407803500a8280464a9400100311080d070721900c4034102420503c4002c030300240180c000340040c100c0c0e04031807001c950465a200700d02541150803e0841c0080104d080c41c1614100740c054880d0660420005481020690050b51328900042000c5402105120080940034034000c61280000d010350202d4504036007807041c0c04200c84400001d40c20245540c03038424840c05000d1a05040c180c454803c0c2c0d180c01d101c0c2c4111202075512100400440b481e0707041c48201d80a01072012404240f800300810380050b4006200321405109549811443e5201d19403d10859403c0d10707000c40e018414044060f030f059510038030818 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 620273884 1250 620272634 620272649
    0x1b010501060504211205090402270325030204020d020c06090f0d02070308030a021305060315030c0f450604060e04050a1e0f0f0203070605090604050d1704 68
    0x2c9480c02c010010010740d2440c0c11594104c07000480000c0000e604c8000c1d0302c0060b0300d5051150b00c40740c0d0040420040e03c0b60200c100096000c0b19a00c1d02c186400c0301c44025120021380c2250300d586000e202e40400722608ac0c031040b07000300000300c0410051400d60010800c0c800b1401c409420292568035461a14209840d61400ea81140209007180c01c0c00f0803180300200161700c02801d219213140c0315401c46200c06812445150380020f080c2d01803092040011005000181004d030ba28513114821009002c0d11080d00c0d8801d004800846003245007042c09400000380c02020318081058400b44605641c901b24060f00e60101e03401000c0c95032414400400e00f009241c3d16280d0044c0c44c2120070017007120015004180207410703040a2101181000402051840d800290307a070300c682c954005612309107039542e0014540450340303028000f0000240200c01c4054401c3d001c03519003d45400041d20300780101c111140e00210309100c204034501d0686c0103007000c240590b14100900d540c002010b01c25a109800c04030 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 620275134 1250 620273884 620273887
    0x40b0607050d110c2d0307060903060c0e1e030f030307050702181501050706060e010f06030506010e031c1202030c0403030210090f240606020105100503010e0607051b0105010605 78
    0xc410300d410110400701624460b0103030250f509403000207044844170b603c0d141035200f44015600210b00861010a4404070000c08846515680303440003841e441e15408221501808c1c40c0d070319100c150180d0b400c0c40c0043d400420004850700c21258010705001c188030710983c5449040d4110011110030301c01503000e80e906945280d591041801808030481c250380070703680491009010081c0c89022214006203a11090ce040c0ea078030103450618101400c0741344c000010209088000103030b074a04240345142119882c3c2c500340f0207075480c2001503e0056442030786941640210400e820241c0c0c1c0c031140080c0c055002e06143e58550b41c1000b40c40200d0b002190540b070743d000002001d005060b010000724000305c1c040c007018408010150b07510f12005820703270402403c01c544104000c5040c1800c444501e10502c4061040011507622030009010700000c0d203803074414480410020400f82018040e1200b0702e0b01000003000c094542040466507980442c882c001c040d0301c3c00c204a42078003800e00901d402802d03035580b800e = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 620276384 1250 620275134 620275153
    0x191b170706020705060d051f0806040c051f180f29071121191403041a09040b0310020706110424050903010c1106130c0b0306040b060705 60
    0x500e8990316800490a543c0f203540d080050341da0749130440340402d00702c10340411191590420a000c0b80e1400342c00c013404581f4444c011410050000741c0074800c0b130007880880045680c1d80b040c09103c0081c0c45000c09101403900c84028134078020001c040303501e07a002e90284511a0307101d882c0c0c00022150381280d00c0f1201100c0300c8100e8410381a62187c0c80b0b0b25400ccc007003464005290758050b000c200ba03c1c0c200b401070f40301c11400520020a1030b0b0315142c0c00024000d6880c4020a0b5402c1c1940d007040759400c842100801051801a50001068900303840c0009105652038400442c3c10180d43c20012040307a0098444581019680b8140004c500b0b03078440c1c400141e11054a46000405d0300c0c41c28100340c0e21400240300404c14020081c0780b0040c60340526280c440750601c1544112078500c15420101d800d582002860569240e002000c1494180c019060720341d96100e103054640400000040030344015000d8400f4450201c000380103642144004100051800d1917602144a42d0000a070a82d51900406441d = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 620277634 1250 620276384 620276429
    0xa1808010c020619050c0703030c020c221a1509041b090f050609062517090a0914071b120509040510180f060306020c0607020d050a02191b 61
    0x4c503491481a0b00c0140014500118102d015010f840b002500305603c4100700c640a6000340035400002c1360140c01d00d403561445410501c0b0900c0544000000c2919040ca9a600002c85021010b55190001d08040403440c000c0790304207042d00140f2025034003030383c0c81184002c0d000c2c3c154600e02841d021600c1e40000e240c07400c10340c0d55550b900c5a0085010307100400601c512a6900012035401c0195000300810214201058040fa031416040c01017148825000f10701001c1d07a02c8010b0706d458102203032100b0805448804c0c16040c4c0740704040d807003101c0400801040764103000f400e0100c1480304040c0d44240e00801619131500b003480b0000c6d4103000c074034005280360352402c1038004c05520130032816004600034540404a15059421200200c000d99180d0b8150243c1c0da01d40c00041c002c540041c4c0c2551164001940301d51100016651300000d807083d600c0c1d01131814062000d440050b8240c3d00641030300e400c0800b840c003410103100000c6a10280d07041c840d04e0040140e400000144c00100350901c03100e40081035 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 620278884 1250 620277634 620277661
    0x1206090507113706020915091005090d170c030307030506040b0613031101140d0204091512020906061209010b27011419080a060f050105060a1808010c0206 68
    0x260020303c4980c000d070740743d03007120604640941500c80b0700c026408610034181a402400780c0400300c0e40c8042c01d00c00c8841000510700182080c01c004a40803c490646001e05503818480e6054240d0030482c1c9881c00713004104540004003010054203002c034605420761869a0450b07008440da04c0c042640c44040c00158180751040764002a4140c48107441c0448003484044035a22901c0001c005250f09040d40c4050392284802080c00c0369002107903a190003070703072014002039001070003070b001d8842c42c0000c040e0441e80d0b20000c81c3d003124501140b0f2151a40380d074081c13103283c040c020321407a005241005010f03000c00204400c9807082c4001d400001e60f045400d410810744c915005803600d100340d840b0b000c0003010036510344142d0440f4a2100c1d06503541102a01143c0001d00194014070007850f40800040c606102054051038284118001c101003c014a200c030110303074003800307041e03040030707041c0191405c00340540c08445110820101c0c004a140d914000381e82528220050300c40107810900a11002c08141c11 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 620280134 1250 620278884 620278903
    0x3120301090f06050105070219050612092104030b0a02070b0f07030c050906041e030206070b0a150614030403030603050106080d080a0c08040215041805090f0f030307120609050711 79
    0x10703002c0c8283c0d850000000d0040c058803002900c242c0b6070010320703030804500321040b41c002d29001d41011b80741c0040c0518034024201c100d40c01140c0b8000d8850701003c20b0440300100b0307906904c000c036107414942540c5944003807040c0100707454107941c2d00300402d02c0868000d1040314411000280260070b5031602031070050a442c1c482c1100d0342885030500241407a80d035200243e40a07500020040c0c600500c102407a860141950381c00030350803002c006214414414407141c001d1144451000c248401c40d0318161421a152492050400040513101000c064003c143e0085802901a140100e25a070700c0b03449890846001364445040c60340403141d2554038540002c1041d5005d2080300040026180300d12000c0d2014100410082c420480f08240c14070301c29010003510090507182c1d0160020300149581d8000803d01650442031502c5904003160f000400015003140f120161400b542c110b40342c0305001e890034000240c5c1018201d48551003c1158820ba10401d480340700c441da55850181e18001d001410243c049 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 620281384 1250 620280134 620280161
    0x60b0a0302090613110f130626091c03050621070603021606020c07031e03021b0a03060e160e040c051c0506070e0907050c101a0312030109 61
    0x2000c10260b40c4502e51180d00c8901a00d1846450360340b14032610081c00d4000300e00c1d0700c0c190301280c180041684071029180c0b000051a12000c103641300c030002d40b16801300c0202c203c850181e0300c40341c43c50807400c11081504941280d0407142a2a80d03601c40c1c00c1000c0e407088011001030390710401c000c4c261a15021001041c032050340403103020f8116514280e1039800a010305800c0c1500080c4040040162956031000141c02040454880005122198651029100540e981c80d02010402032906e0000c0c4401c5819602d60020729913090b042081c103001e44015a07229602511068000020481c580030f10300404000002070254000b00c0299841b002180c0e4001140e182c841004000000c0c51a00e22030080e107204441c0c000c1076440102042c1001080c16100500e14041c0d80e050002040c0c004a2100d050082206e040000d542d81c01c0044500d030149c0c184c440b008e94021170444400340310650201d4915014095840440d11a56000c42d00d89008074140f40510380001004000c145030520903c032000814 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 620282634 1250 620281384 620281399
    0x50109050a0302150403021f03050c030903121005100201140a0b0d1e02100e03010507050307170402030708010212100906050a03150b0a08150f16080705121003060b 72
    0x400d800310382169140d01000340202040300c0740c81c55612014066a000310340c0204203148100e0302c0c400c0880e207500d02469403000301c1d04140204081d01091805d481c81408900c00540c1090350540c20206904409448120b2207a04400007003039503180c0c6d003d42c0740358108540011904c01043d80340c000c80520003c00c0c88048030f251503114440c0d5038403032007090002c54000f0007041d0045085a9021011071000314000e501000140103101140d40000628800501c210020019581c0309201a07640780710480d8001c00003805401400f00c1901c0a00c40d00d600180040d04885080d6158108942246d04c416404140800780c5000c200082103440342d400003500e62024107226079407410b008900401e907640001040000901140e034581c0005600250b1107034401408410b0166485c0b0145890b01c81000300e00c503d080360320f030010f001d1440c90020580039014020702014448140c1c10b003101c1044000d031241080040c100441395541220b103e000c0c1c0507210b0002c01a14071455441e1407001c680c1400482ea001d60300 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 620283884 1250 620282634 620282639
    0x806060d0201022e020403030909051e06010f0c051504120306030c05060708090901030605070315140d140a1b08010b031002160c03110a060c2001030b0306130c050109 73
    0x82c007043c010204c0c49000c0d60f651034149080c000e0b50000a881c2204030006101007000422300d43c1c40b02c00441101c4040904000584541c01030802c003e0815199068645d50280422001e500c20707085485465501e14002040801e0b40e5607003418240400b201c52048000709042c44248070340515450348440729400c0801c40989540d88a401c103010500c212445294081450401c4c0034a0100702e41c01081d00906121750303980c5070b1509034000c090a82c1c40000207850203500b0010070020401000545d001e1803803280d0402c0c00301e010440040e1404a00b1034220606a11030300001c4410007070403614512901d0000582c9210801c0c3d03404044040d403001019a0414284803ca03440c08611000c0000100001503619100b1000404400c551600004d00e8041295000418001d000c0385138042c01c44202d80d100c0806941d180121071040790034101502004854203034401a103001e00300c038041c008041c100071031103010010000b810b00c0000c94002c21680e07008900b04003046955030511019000c01d092008041e030 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 620285134 1250 620283884 620283887
    0xc03031418010c110306041212090309032303040605030403030f02161b080f1e0c030601120c030b0f100522050c0f04030f030215061f030b0312040806060d0201 70
    0x1075950082814058441c00c62001d01c00444c3c141c0c482148058126007841c202494200300392905c6800134000954100c852482905040c016036410360f801d951402c80d01c60440e11010a1542401510b080003410046088508002400540300900c02a00d5242d180e03d41400c01809130b60301d50103800526403040102c034108001d825030042945c0e80100c2e480003980304ca0013802145c030b501500b100005104840480c0c00c429000540010b884031603007201c410085903908100e03070f902d542e0348010f075040d00f1075801804800041c0e5100300c0c3c600d004030001030050741e4070b44031030010100c2941d2070803424072440c5c1006100300300d0a20f114010401070310700d80c858202000c6446080103611401c04c82c07241e02c3d200410009460542a220070410b0802e0f0140e64a0341c1c2e10b40702005d0301840004030054000d003080000d00d880101000d900c039807809041c0c2004012202068813101840100301004e040c3d0303031001190962010854000080b21040090340d4560500880a203460381c01480140320700c00400503140180d = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 620286384 1250 620285134 620285167
    0xc08040803190906062711160f020402030a0605090907080715030e1605101e0f020f060f01080f0f0c0d051f050f06010e330301030c030314 61
    0xb01c0d1850030504140100c2440549002c00303000d010241024404125900c6445850000080301c0031210318114002d480c03081914420030841c3c500c0c02c42031096490102e085604184100e101e564000d29040c0f080e40002c040360400d0340c1c260b40d11a0348407024480f40c10b0591060b07420091400c003d0020910f4255072036501c0b50940103c402c5241000b030f640ac00340d4000d402402c4c0c00e207960700c281c40d9500443c078610b910000f42131080354401d0200600c0e030344110b4000c015000c405411610307110040c04208006031042c84000102c10214891072580c401440000c2c04081e010350394034204d10308035524280d000352074481c8600c0e803403400e03070800900b40403805030002d69a00c1091040d60600e84c4403415080040c10040c0c2c40c03545590b10080c2000300070034000a42c1c07005101c0d10104041405507180d5200440b0a080d41800c666004000c580c0c04100120b8405070400d0b01c10404160a000c48041a4204880d50000e0384110b843d070210740004e0042542014501c015142106600ea0802100b1640c00198 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 620287634 1250 620286384 620286391
    0x90703020d0b04061404050c0a140708040314010b0423010509040f0f060504030206010608041e15060f05040605061317031207050d05150d0305030c1612030c08040803 73
    0x28164001031660280101d50408405040d000380104440c590320b4210301c0002183e000340c0d070721403403500700000c80c9148140c0554800001f55900d01c003072614900103454540c0e00c10700041e90260300c14040080001d0341e03880100c070304079141800422540603500c103100c16170700140d05a1821100001c0459046c3d034122160b40d04590b4204c88a4113151624142301c4008004500d004d0701440c02c6207194020300030360790010383c000c2d4402c0c0e08990340751380c0c1c508049404000541d0020518203807000300c0303518207001c0450341150740c0c0034039011845e08041220590880346c0d6503110280c1c0c8200c4480400861416201e001300810041d103041c3c1c46d1118189001420303000074002c1081a0304541286240982d0070000c0d50388100c03100c1d9040d1018204010040c0c015000784081100060400c0300080c00e44c0c9034038581c1801041c01074010721020b001a81c05481c190001852100040805c0c40b403014140c418a5041417400c1c0190003002240141603c001c080da00e01644540901a4080500000500500807243d0 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 620288884 1250 620287634 620287637
    0x32010150806041a060d0c030b0402400b0a061823120f19050c100906020f0303060109052701030501051005041503030e010504080102040e07120b0907 66
    0x403860500a80204980201e0700110580d10a40c0304102c00c001d1007000403c00b240001180a0f0300e903844608202c0365002540b030041000c0d403ca44200001500b40d10240c0d00035100400d201d11229400030800a041080b152090108501c960003078200c900c125407194102102c600e003440415030380d8000c2000055148240740c2003141e40c041441a4002c9111424050a00b180340140144401070b13071054559405c186280c4201d6550301e158090620005a040001c08040f000c1c00040c2c07058103d50700c404a000c0341c01d80d910302440055080303503a25071070382282c041c40b03e8844518250500c00c00929004c401201034019a20801c14014541c3e000300309903007155000c480700c4180c5010044441150300d00e2840d0a6800f100810000c010402c064000c04d109510300000c07100e500b80d4400c00c000c250707013031144e258101d40300c06403091000c40d10170480c40c0d8a08406041c1180343c9136845402908a0340140c0c0200f42440302d20060084c055031299803d17040b031514800030700c162940070002030006c8001620440 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 620290134 1250 620288884 620288891
    0xf060e130807060608012003160e040b0a090e0c100c06050711030a02010b09060a0302150309030f07030c0303150e07080a0e25090e060403110114040f032010 69
    0x1041010150031103000682c400004d019031551440d0b414080c003401d1404214003500e2030b01c2c0590185045042e40c0c0308110b00001d66604041006064560100d003c1d98190416101c03103186020b03444250b0000c00429900d840003c0704180460150700704107102100b01d00c1050401800d140090b4420344541009800180004003502d41000c1a9541d10015850351128000810100d203042d8042d03100c580241e42c00e507a500400c3c0e562000b00400700300e6a003c02903001c2c10074040e203100c80e81941e0295500002c004201c0e40380041440001d482900107203002ca001580708071800302055414007400c0e00465007030b1050010b160424120020094004003140100054100000c000a420303421010309145841c003907440480d400c10301000404400002c0e084450408c144c00a1080503520a0301c04076245040500216107669600b245d80c0041c2007200d2100e9904c4409140304010300e0301002e40243e1041d11112030444040c94042c100d40300701d0640c41c0c40d849051a06c0d07041801d01103030001d4040210346000 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 620291384 1250 620290134 620290171
    0xa0503060418081207080c04061d0406120507060c080d090c030c06030213080d0203040e09120d09030807080907151b0303020324030309040903050d0c05030105040f060e 74
    0x100203084180160b00c81005400049050090450050040025101c0c2203191a903504a00360f079034000541b24a40c40b00020841041782611a080604480c90048291140b040e26800010103031005500300405803407403100d02404200342008654002c0c042401c2c04e00c01001c079074551900c6801101c082c1200710391a401014200590728510364003560b84a00e1110740c3c981c035210018000d4001e65501c1900e01210303400450480400901c0312040005030b40118649414503107170401c0251701401c105c0c01e922800c0c1844001030200300c0500011070004000295071011030800900d17441000d0507840912814006002d606c49012480c81c0540b052058001000e40594200300c0b840402c4150742c1d403056525603840c4c010103605800841c0220701c000481c00c60325001c010000c5400d140f4074900f50349a03000300142d6860781400c1e0130444540780079051a40c1050008440314040d0f030004281040054130010041c0500d15051081614a000300b4204008041c1810100c107410359001c1c1844645030a1414071 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 620292634 1250 620291384 620291389
    0xd080f0408180a09020d0c0c050703141006060e090f0403080c1804021306030b0901121727040f09081213021915110d030b04020423090a0b060a050306 66
    0x200300b07503541d0180c2401c0d46030344c1c0c5101020080d04134a0207030005a091030b0041d00311510403001c40e00e5058111001d840500e10396a40e1082d4141c071030001038064010103a19200d802001c0c07084070700810158503100000e1440e041002404000284205d020594003400d00c808298000c0d03010354002c40401e84140da855900044141e820700d80408030342c0c442e0000514070341e40804240c0c9041250002d80f0240b124400320b004111480ea07007409034003144c0004a1004021a4500d41c00c8038109007003c0c0311920301440160001015002c601e020582d44200442510f00c0c0d00b080d110345050201007010401001c40a542c03a440c13140304000207440641d8403100450f0b80c90003029040180075078020002c188041158814180400c941c0c441c00c801c000006140415103400341e94182c0d07101a02c0030150a0007540b1441c2580200f0001c0f107510b400c180c1c280400715555510510007002182c000d400c81c0030f0540045c04002c204800200300500131030402805104a031680d000f0744c1e1152041e818425202c0e84c0c2c0501 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 620293884 1250 620292634 620292667
    0x60e15040b07080c070e010302060d05060a0e0112030807020c0a0603240e010f06080606070303090c17030d0b0303040509070c14060a02040306050a0c140705070f14030d080f0408 78
    0x400411840d00080c682c04211402c0000e0035104d4030041031715482560360440c601501c4091002a40041e0100b0140203c5406540425403011000385500b06160300c0b5010519400f800b60030401341d900d00b0140d401e090507042464207078441060300c010420b110381d110216108040754071542c000e03d0340350840c41c8581010701803541740c1400b40740ba414060b5681e41c0c8180c40040f20a228052000c0541c004c080f5000c2e20501c0d109200790005010320345041160741c0e044004100c550000c5d20070801d100c0b00400c40310381c4400c101c4005d804800040d034655070040b13002030481d000d04610038460f9201f04006c10540d140c2c40c003049d40c405003504120514526a00342502501c00b43e00c016145409844108a0751101c0c0c2e5001e8415a401040200001d5407141c442c070381140e016800040100b680c000346c0300c200299403401407262030b11a0003034540c0183c2c0c0b0a051216291207403c152080103405c000d20342542000c01c141c840701c590030f1030015114200030841003281c8501502c01b400500b400102030810900f003c0 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 620295134 1250 620293884 620293889
    0x16150210271502070303020703110106050a0e0a0e1b0a1202091503100f090b0109051308250b0105010206091c08070903120201050601090f030503090904060603020a03140d030501060e1504 82
    0xb0415942d520007854010002e5100700c2c0704a01041840c0025002c05c20705118000c1a02e1014003010b00300f9060400c24904080e004040000007501e68507031850300384040c40000815515003060b40c0240b01014104402c40d18283c000002e0b00b81448030f030718050303a505c61015030043d20118207001071100d000b0210341480400b5100a12441c188581481d103450560302190440d802006080e2940c0d80310114201542d800b66580b1981400c5408400d02090208008040c07446c040807800f481c455240d580118814400030b403d036804420a00100007950b01030001550040240300030b4030104000c40d07a040420811381e0310000403c50b2000004804a0094150501443e084400c80c1d100385400400203000c0c0404460450018004120004105003204074207410f6950040c06141001d036101c00740044400018030660f5080c1d2152000005030320f81002d0784003c2d5014002208020300180c40e5a89807803807615446c0105450103004101e500e44c400c110742c0404a0448000c00202080c8114012600854 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 620296384 1250 620295134 620295173
    0xc01021b031c08040c0b0307020a060c02030d0f050108010b0f030a0311030f040e07030b03162d0b03011e15050702030f0115140d0803010608091615021027 68
    0x11110034032140c002e42e0013440f542c4140740c46903401d03882da04094030034001980c07003c0c05a84141c1d19000020300d035810a814104c4c5505c1160f0400c0e801d00701107029a841c07120b02c010f1082d55440117100904081c0956504081c0075a01d0308414041100480d0340c4052214025082000d00a11140c21317140910446801c0050055a03d4455485803607084242c1c2d402d0342c1e191b0200c1d10f88214a00103050101d0b450f07039085201329207402461f1900700c00c03c90440f1900400480c007a80a04031000c95181d002090020f000b07482010741c0c4030b42c10109041080101e80c24120003220341008104034284030a03000d040510b400745441d03030f00e8280d80d202092a085001480c40600e5003000d8085003082c1d0340d143e440c000c49e0744201c02c614560342c10609000030205411300280c1070071010001444a0382c011004580c01c11258401c4440c50291041070420300000c0d030700010022200d00e0819407400b541001404100c00d00c40c1c80800000b031a010400c403000662042c07094482c45050311007400d01c101c0c0540c0343c5c03285040 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 620297634 1250 620296384 620296423
    0x270c0d20030a2d020102120a020c04020a0206160504030213021605070905160302030f06010309150f0f0b06090d1202031b030c0d18050411040302031014090c01021b03 73
    0x2d610701003c0d5101418510b00040c1c1d6986000420729002d038880b04120381e010380141041001042d400380d042c5d801800b01c02c1c10741c40380c004e6001c241d843d20320051592071200d6000d00100c0c1402e5202c65451500440f2280412500f800700340301690383e8250f00c1c00700004c18800181d03070b035204c542490b1040105050150190103100300010b07a02c6290341015214016000c0000921440e04400380d0072404207072002c2c40005038000028107154001d601110700d040c0a4012070640300e220b01502ca050b43e080c0041e509042d511241150000c0c901409000307090582102d03807070f04000e82c0c400410520740240b8030262030b100c034011002104900920403501c0903c0f42104000c000215094680d56950064043c88ca0f07a209101c110140c1a200702c10340c0400f2910004c0f0708214030324020410010300f600c0110f0f200320031810000007005030b50401092101610742880407a400301103e03903400c05034500600c180d00d29040392103d0040c0303030703808076001106504108064940007541400302c3e01d0304480b0240b00801c20350 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 620298884 1250 620297634 620297653
    0x130905090a0506060102030f1e280323043c11010305040c0e07090f060210060906050310090f08070b090d020d0e120114270c0d2003 58
    0x800709100e814280114220398413074072001c00490382c070310400c241c81001c0d0205008141c021001c40c454103c0b031420b5100d5540c1010301002c000400b10a1024040402e441ea1010002c3c01603050f000303d4046114a0044002583e400e4011090404000704002d108155080030303000340d4040003074444d0648101c8030210700440c505d0340b2003446c001d903d800c00381c945003480d0070640002d42c4280200c0b4400d030780c4402c2c1030050714038158805c5100400a03192105005100e0404505182c0c4040048000d0000764000c215144a4818103812a0415007026041b20b081980520044c0c41c0092440440c106c0c07071800041c003030260700342600c0081c006030f4020080784000038072900740001e1100041c003810700703401654050501004140e0707032034010b51780d0800802c0d080403011810f41313040c19030221030000c0f80300041483c01380d0040e114544042200c0c0b600d4203031096010590300f4000002c299440c041e440d0014150300d81e0307050002e8a035070300c010f0006240342c007281440c0c5d01c0c120780502d9600b09088041c003120780500 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 620300134 1250 620298884 620298901
    0x70b0a030608060604020f0406050c01180b0609090607050901120204120303020a11010603030215040602090a0b0c0d021531081806190e0307030c0320030706020d05130905 75
    0x194072a50340b10380f150f1800714555181a00c2100c050b401c41013a021700d02450240c040d1040e400c00c00400c400b95603a20030441005020a6406c14064890303c04ca001906c0d040c1c08120744040c0261a14109902c2441080101c64000d4101c482d0f000090070b000380001140c000c0540a03116a40018106c1e00d014489074013090f825070040d200208481d02c5103072011050410040c00c881843c071001d00168412944038a907100d10050807604280141030151410003c840403550041c0b650340245000d000c009441545030006102590902400307101038000c1d181da60a81c1b00401001a242131440c1880d03a02800c2428400050324420700d114150038201c004060520b244550400c0014401000b00b540c964000f500d000021100016680d1201840c02c03015600200d80880c44654025094454194080041000e0503200001188030340580c04100c1c1d16035000240c14503510032007a0181d88051004d11516401203107407070141345545440c58951083d11401d075100c54031544039005003827610b81402542c1 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 620301384 1250 620300134 620300141
    0x10215090c18072006160e1002070303020c0109060801050603130b0c070c06030501050d1403211006080c0d0f200a030b03030a1d040b030102030c030f15061902070b0a03 74
    0x1206180c80310401d558140c041d5030809a1130340103510780703038000781c002401c007040e010303400c04422080740760191501c114040818905100c2400c20005680062010400c2550401c411282e1013000e2030300b41895460032102400045060041901c180780210000e402ca0046483d112403e9410014070074440c1451640b5565a52000000799101c0c1e02c414004240c1e10f0181c00307054100c0d50060498019180582c443d0140c401400302400802c0c002000600c610f1040c081254411018007100704040341401c800c13840340c020079a4400c030103000b00e10080100c0201c40c0030035038100300c06a40c400b00e500e120325036030b05009000d03040c11441e0304031140c03c40c002101c00740c3c4041e04919003a40c0301049184003420401d03580740605080d160028150384150003004010707000b560084a405440444d4064080c07000a081e41c00c1103d80c401c0c3c251001c002c00019040d002445500080884224012401c41d040801c4640c0b081c1881c1208001d1100d0040802500c00c2041400600c1c04844c21a120301d20b81d180100507 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 620302634 1250 620301384 620301391
    0x7030c0b0604020708031627061116050613030209011502010c020c13020d110304030e09010f080c09090c090106021605040b060403020906060d1a10050702010215090c18 74
    0x32a945203000070458205842180c01d095049100710341940c0d102d46c6031305140c1c0120320302c2c6005c025050880207407202a10144944030f501c0385c2c4d08512071508040c0c00130000b113050030341040c55034040c031210061382041c910f00c2d4040c0c500554a40799107034200d80d0107021020a940c002500013004800004405080c903281113210040c9a00134020100b80c3d4138104e07662040d1408050780000d0340040c0820003a900d5008140e000b020350804075050450010311003c41e00119026000304400da440105203240c07090384c0e94013401021400b11001e605200e0115519021344111601480c00d000109622303900c00c11011044100040551100c0e41e141c240007510345106102000700c400f0482d030045810b14090080342d40c0d80c413025003054140b80c69a002c1080300c1c0c0e005004143c10101c200180014800c240c050200007031400f1041051020f00842404200c450034411001000f40600410b1b00603a400700d030540822943c0c4d00020419166000c02034145070620340e07041d9000e15483c01c072001583d03c40315014170 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 620303884 1250 620302634 620302643
    0x408100c0e06070b010501051606050114121203010e060a030f1101080a0b180411030a240504081204030201020d020d0b030606010e0a0b250305091302131202120307030c 74
    0x16101207110611006010f4030707500802036103074a401844594411400340440d00ca03407051105a44001c1c0d103441c0c04451081e0448040c102c0007107a031903403d09100405400c006e41400007040620007a001005442c0010b0182519034621000030a20301e580f40c110340000b85410a00f2600c0103c2d0500d044d8002d070300c3d5aa00b15011902c1074000801401040c400c002c0050801703040c041c0c043e804299049140b200c000c004880c4013500c1c281088090704c04101021344188a40c4d842440c4521403009400c500c080c3c4400810540d042004103c0020780242c140d4269401c1d80016034460707201d910301a03000e40a490004042c05101042115179801e09405c690600c032400d4050b01c4007a00c07002d0044035800c0740c40752900d420084c844010484035032040300801c415544545207411040314240e94901e600c4404500b41d00041c4041440c444030300c1c140c4058404807010360f1046180520b0030030071200c03070995480f40740d4004548401840664544490620441c1c4400017541c1d500c2c007a07440c010f0901c1c02a190140ca = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 620305134 1250 620303884 620303897
    0x1030209060c03031b04060203040618170a06060b16081b0d05040f0f2105070f03140d0c05192a0612050609011a1c0c1b02091b0408100c 60
    0x404178440c03003110107840245c1c0c00f0307501e81820948181d171904240340b8614a00c2003c0c1c103001a806c144098100340042c2d2030400f50094141c3c03800d02009aa440b90010690340400b002100300c00c1c240003d0380c040d12588040000d0b01c82001c7c104910540381c051a10f2003103805050a02c140440c0d02500600a41d0f103c5054444032980b2801c13048024000c0e401000c00c0c10039121206ea03550748541d0400c0700001d101d10121101e140d00d51508503804000d507072044504403a00700d9081800c003001c2c003500589898911304140ea1080c191503170f0341e0342e81c42010000240400d259080d814014408009242c0c66004000c0c203031811070947c6d131501c55122901ca5440015a02141010000310383c1c0115030107420002e00310b2607642d08202c69450700d1480408204070b0b01c042002214201e000c0694900003210440c0e90020745100c4c0180e01a0113400441c042071810700708a070380c50300141e0b1460b409981241680780401520402000e212500d807140e5009555180700720000302d104404903400c4102c0a05680e039402 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 620306384 1250 620305134 620305171
    0xe10050a0e06040210181701090b0a1e0509071a0c01050702070609052e020609010c0c08180303040b0705070519050904020f041113030c12031b0201030209060c0303 72
    0x3a0b25a68192002907020084051100700380388074204495031081140d01c114001996070034a55085032004d80e100c08280d46441c0840c00f0f20004603180c0e5440010b800080c80803c3c0100000000e0141034038071020810b940d50b000c12500f000401400307010742503070704650303c0e2421040781e80318294100241021107507003003100049043d48045282005c0390141c0e104c041c0c0301e606007810407440380340200c40f0074048034001c210300726020140024021109055006404142040646c4500390350384186418281b000d021101000130311448110f031445002e0207002000741441c23000282c118812588400017120b00882d6240500401103002000c640040703510061007481c450951240000d80d02c02c0c9544001e0b298002005810840301c960640c090007040080d01d41000880602d258019521008003285004d40034401c01c41e00b01c044801410170407107003440c604515540148100340580c2d008810b0494180c2580459000b6010745100c4100204070589841c44038208955a03001100e0001040c01e031b61440 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 620307634 1250 620306384 620306411
    0x3181707031209152312040507080f032502031e010b0406050117090a140d0e09090703020d050c0a06031a0a140f01140705070519060e0d060e10050a 65
    0x40c001104c240c0e0076120321042c00102c0c150384c1007601d0000c00b03c1c03540401c030442041c101c0c020001c248104030031414030714604041c101286803035002d800940c510307800281d20501d282e1000041d5442c104030512105084200182240b801c9884850300075018441c003c0300d039140190003c10203045611840c020860480e403001040141d8107607124980c0400c08025081603e411482200381c1d000e024001215110381050b0f0b20345030164001441004142c105410a155a9a0007a84840c4040d0122512403040c10101100358035015075110003880707181400405400c0001c28012500c00c0b58000300b000c09100d550700ca014008e0541c42032007030148442242d40885610701107042000741d403405901400d500307a0250a021402030140c08080c10b003d000440010301c810754000902400e482075004d854880e103002c042c0840950010f02c820791488031074400784115540420705074003524044a070080000407504001c4001d00100e103001c3d0a030b00803140c805181c5400c41d0003450040c0b449040820410282005 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 620308884 1250 620307634 620307647
    0x801020c03070515100b2508041a030408041203210510080d0c060f020c01060f050411210411270612030d0b0109081006090b041107031817070312 64
    0x1001c3e00031755668401803040c1c9403110054135800b4091000844880c1143d4440c0408503491842100d0707000c03002406020350f0389890b1a40c021800718000c1e85055060a0703a44c04018000e602031440f039180b002c000305e420715209400c1c10b00d518250f4009000c044002580e004003400c400c44c0d0400380740b40f00ca440011550000a00701400000c00e5440240f00e141b6a55140050710303a070004110410b400b441003c00d441d400784110f000425451319804151071820040c4425103c0708004051580700c00d1080301c603002140c2d18000b03051090030602c0c441a50340d82c07802003c02160b034040f254001e510316101050149940142081030100e100c817110076591040c0802c1900d007402c8802410365002031101e09680815078114143c2240141000350071251104076161900c4030b02800300751581d440324000c100040a0303201d2040f144800b91014410544080c20103c400e200317032035004040004001c100c144125402801c0f8025112a0300e0403140c2200703035521640d17144440c0c00255903e0b055a9441840780d1b00951 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 620310134 1250 620308884 620308891
    0x905060f0f04050601030b10091a040609180f060305060612011803111509100e01060e010e041109070908120c0a1401060f090218041109060c070801020c03070515 71
    0x40c407009072108064184000340001030003880c18951038140408007075075603810301c040046860752810030440c5401060424005c2081103449044000c02061203521f51002c040c0017601e4241d031350508800c2c203240c075a40045c40e00c0129440d03003c0c9045004401c0102c007061150040004942c41202c0d03002000c00c050895240ca5100c84a0440c5840041c0020b4000e0040c03120300308091003030310804110003141f5047d64600321121001b07500584c0080d000c1d2185407003501c040540c0800200304481c06d1264140b10110103010300700c461003220001404002900108100010b0040c107804241e0078211009040d0300b045016101c2140101d00c0402e03110801e072000e90310710031454401894107a0090321480890010483c5040d899500c503c404a00c02c211a4004070092140b0741340169100300051a1030f4101c10344c41c58062150742054100e0600131202d01c20b4617014401101c805a4034034140c101c1e103283c11442d5000c400c1650000c01e81190381400400a440c01c80c3c00780041d1440009604403611442a085 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 620311384 1250 620310134 620310139
    0x90f0603290619080105071808060106051804020d0e01020c0717030a03050618040f03080702150f131a01050111030a0203070602030703141303140c1b1906090905060f 73
    0x40001401464040f00d048141501c412066040302e84404a15095580844030720f004102c040c24541c2152000d0050000140356860203004554100307040200203104c0c1c1001d910301c402100f0b620800a96941e8100c0329120722058013004440c0c803c98186010b50407240040303074903028650000516400e81882008001d00d60700c05545024880c003426401482c003d0318090b000320161544111224510f189140594042d1605003c21030f041d1400070304000c8003c07c4001150086d000c0f012a04820300c2c2065088400c00c40508615503d43c0c6a251030184281c1010301601c54850107924040b11501c0050306032082a80e80408072144003002a070380b44100d5102500681c4200441c5020a035140d02464020078603140128001031501c3d44010070703c0040e01da042c0740b443c8074103c0004141d008410400070103044e074001c0303040400c0c9164103515041c4280c4a02d990001e5044c1d032a00300e03500c015010020078103045450007015241c203002412200c2074041c088a013468107001c42c1252401845000001800 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 620312634 1250 620311384 620311463
    0xf020f030909070201060b07150f0c0c0b0c0c0304030311072408070c0804030b06092a070602040b0307180e04080a20030c0c0117060303070813090f0603 67
    0x7058144010480000d01140440d583c911020404141401c01441c1540c040e040c9002914030202c6030008468002035000880b07450b1425890110340c000e014000c035160071084090480c0c0e01c8001c01461442a00212400381c080003a01004040d000740409421010358012600300c99220301c49000001d0321a07901c14a01c0d00005d400c0710740580f007944c00359403040081c5882c100c92011a60740c01c0441e08aa0421030703c2038179040401220741003a404c1168001c216034002085881086030034503840300b2000a442c6101d500103068000d02c2210340480e0001c1c072200004503600d180402008050481908121010000c034035000162603641243e103500484e04040d01602d40311500b1400d80d00802c6402040d003a2803241d645069007c1402c1c8040e04640c1d03041009085052114000184060010072100303111030054018000c641d00d0020036a00130a41c00303001590784004d00141000d81e1003142d84003403046410190007542d404404c0c0c101c64100c0744182c10300200807c914501000040c096120403106000 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 620313884 1250 620312634 620312647
    0x8011406091506160c1e170f16152309061201080a05150f010b070f12050301090605090108060402010503062e0f11060c13030b0a051f03080f210906070f020f03 70
    0x1c8001505281040c2e80e13040342c4070505008503c5081c0303403034404408540408503100700042043c03e404143d05540f189030240410042c40342c1c203a210b10100505c64207180d0301154040307060711070104643b00040300141200c81980d40c1c847d8584d4a4402c000c00300e41c2030040d50050184201c021602501401410b286007542e40c3c01c0540c5004035030001e84090340c0c2498803070310900102c0d2448413500840031890343c40903520341c103000314001903560341c0d40258052090840100441c01c0c1c0410002c1e04940c0c2440c00c1a0ba0740c0750b02001480c1540306400300b800b2a41100010103048224000204c01c1c0720b029190542040d00c0c4442c1518000d0f00e8459041352a000f2000145e40070954400038015240c4000c91202c1503512508d5891404034111580c0e400b5503500d1051110301008040340e1909001c0d0005484a01030441d540d0100e2802002002c000c002c01c08a070700c0001d48080841104622201110b509492424036042c9640c0c1c00b003501d400300810707c0d46001010343c6201003448100c48000b0001940740a0 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 620315134 1250 620313884 620313899
    0xc17071e11010c080d142707050607021f03020a03150305060402220c020303100e1003060e011e0903030b011119060b0604120501050108011406091506160c1e 69
    0x4081c50f0865030002c0801c01444407040a10510042d084000b00b645c00c113140800c080400f5410380310136440c00c4220041e0f1951a400300044e0710b4240c400c103403401600c9140c0c0b0310115250a0740d0042c0d1031030445d20905802c180c66450f40c058070f40c29101d550140100b03c400701807041e201310540006422074000400250240c20594140c145d070220b400020590f004842d0501e07001c4982d1100c080c0d005070000401d00241c054041104d0000e000008a85000c4d030600700c0e41004000d48601c40103103000d03114070030240100c00a51101a224600e052600300c94001144050300401e16040102d0120340b600b0700b81c0c81395510600181144140c09002001d03888054407036415042e50703140d821108180c6034640d05c0300980b1208042d000402510054100040b454a8130341d00b55007058100d0861685004801c89803c4143d03000150411410740b06d010311602c070200c0b001482c082d81050a6000380740050b061441d40303100000341e00c0d010b00440350000803030740351981c0703080c1e4001e4215809031074840c0103424006038 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 620316384 1250 620315134 620315147
    0x60f0306050603100203180708060709380306180405030d0209040204050a2403020c07030f030c02333f13060b0f1f0c17071e1101 57
    0x80b1000b0100c94800205440358001e0380d0049990000758028042d01d0030307988200700000c0b000360990001170001883c01d154028000d000601c90f01c0c2c0403030703903a840c1c0b02d2184000340308031912051100010341c2c100c0e5245911008030392042c2c0303100b400b40704070350241503a41c1c0075403c0380d07800356030b1040141d071902c2c80007009100a90409034600741d00650820001900b6541e4504142c0100403c88001e1079a040351624030710b409aa0580e20418140104400150060003003048020303641d00a0460041c0841400c2c04c44080c02c54000084d089042410700407900300101e1003070074000c8106e54580c0045002021103484074050100700e102282041c00c101c40d007400c00544600c00042071411044400c00c0c0c803882400d50038078240d0b0019180c9801c86078110900000b4083c4008a100640703031003691984120200e114820007001c104441c81c0360000144486224086240c11103410507541900403100c103404e5071240d0b101450407644203540509540c40500201300c40220f03c2c0d040801551400b100c0401035400 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 620317634 1250 620316384 620316391
    0x3c0601180c020d0f0311030f0402010f0912080f0c01020a030e07051c330b0a0e010501121e2301090504170306130905060f060306131b17030d0b04060f030605 69
    0x1451b1316070001507026071441001e0341c0325502029601c0c0d0300e814640005080507610300812001c01c0240d82003808074009429420301569400f50940e40c3d03ca4030f44601e0083c0703000740142101c0079400080c00d45501a455040440440d12140a0b02c900ca0396074000c1124694001c281c220181c00c981180d03401040e51b00c0c600d41500c0c181c000300054900d40380241d00002e001c400c0d0709950007070354860b0f103a01c01e41080356140e00a8503080e150901c1c15410800043c00441100c5110f10840351200601c803e2501b010100c1640303682020400d1110703024040601e44104600380c001c5071403c1c0c0707040001800e00c0080c050701e8051030b00704408103a25020340034586007991000b088107410001620082d038122000f807050342c082c240181f000d0f08050401d0000101d18410140480d4802d03885034003480020260000419809903011410070410454480d070114140780950201e070030302d41c0c110403c00c0220f1001c002400103516817036041002c1c2c0c148008000840701303d27018003504054044d8040c4005003955002c0350b003 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 620318884 1250 620317634 620317637
    0xf090e0a0203030408030403110603010302010c0209090a060e0312090309060304120c1209230f040f06170304211203020901180906090b0103020c3c0601180c020d0f 72
    0x5410050703401203441d590255000071510f900004041050003c8003c2000c08482c088070810b1865141d43c000a003011414074010f84200f0122b80483c0a0b4501008102c400590141c41841590035040740e031034894000d040c0c204452a440c0d00000d68040e13000c01201e6624a002f410070703043d82c403185c40d060150300010451070144462860004003061803003001d10300d6030039982d840d000101e084c0b81e00000081d040c00c905502c41c032a011049540d0742e59482921311595025034002039000e0400358000301801d000d91003840f010b003c001c0c040c41610780100c010b1040d110301100c90701c01c60380000241802e080b00c00d103014056013108503440d40e03154441e4008280c030a07414540000c3c9400081340d2100761211b964442040c0565585040045a00320700407551701e080242404c5003041041a415915444040026071280400913050501d10b00c55585420349400d90244503d0000c000a81e15076485600707000303281c41c1c004164001500d0900900036510103507119030181a603403014910079220204250001070 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 620320134 1250 620318884 620318893
    0x1a0c070e0901060302120d0c080f16050303060102060912040e04030504180920060316092408180d1d121b01170c1821070f0f090e 57
    0x8252062031039840c06900c001d030002611520310310421001043d000744803000c2d5003106018282c856042000c010405401c50b40613a07950030f0b00ca05544551140e85840300b001034248400348140400000954410442030b0220f5126032a61488290f55080108604c400f00c0401c00050200e440c00710309054106120b41861400c0c00e40301e410384000c80400001800f041540c0d00084024804800410060360b0346082d02d00c6042e0f6040400700c0c0302844002d02c05407102441c1c400e408502440307440f102008080c82c21034103101c2500f0100d02c0c0c46c00303402d01d402680010094008541030890040540f0f01d1911000000c151004030700c0c60039103040c1c42036880520303242280c0024400c0303611082007010300344640d040030b0180080340102620b03074100c1041b021810400302212020610030100012a04512443c02040d02c0704421a514104a0104044945c000944003403001d1154943c1106546074070380f0320240c404131034898161404044e0f40d440b49201c3d45404090411001c02e265021042c003c450b4030a96 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 620321384 1250 620320134 620320139
    0xa093207120b2101200d110706060e150a12030c0c05090705040305011401080718021615230a0b0604030203011a0907020a050c06030601180303030e010c091a0c07 71
    0x80020050343d03001c0c0c4070101c48444a1600040c05e10840703134400d0030070080400c0185601e90060940c01900700d080142642c0d42c0009540844507819640903561004d418080303991684c4c0b6a864035502a6070b580d02d400250f09900c02da07880c0c40504001581c010001d103000260399902d0440d9942d00046060302d01c0b545440003c68661956000c503446070402d5180e0300d90700c610b1403a241d402c581d5011080942c2d846280018041240041100310132200000500d403400031690340448000d10804c8140040d03031040a81d188208000b101464490310802c060800280c03413041c2c8590390184940141c140035405407400140c44030403075030041c01ba200c03018144506041d209c0e4042802c40e007480e840201e6504d910180204103240c21041c2d50740c0b18015201919002d03619540e55580c0341c41840455100340c00120008549034072801b581080100c1d0358a0202d2000d969040203402820005058101035007044010148203000c4c07414441141c01c1201340e4402c40f134400702c1032050354220760480c00b114001d15500 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 620322634 1250 620321384 620321389
    0x1801060b090f0301090c092403150c0c020d02061308010203090328050f09040b04020a0804030801060c0506060913020d031805120c01110106050a093207120b 69
    0x810028103821403000741d40d11000000c006000c02c1031803006220ba81800081380008400c1010a0220760200d100070070020044242c60311090b0000b00300000c180042c01d0000300780202d20384400c1350305800300d008200207407518504961408000704041e4000d0300c00303c40319005051410081c807141e05e03020b0700c242c10151100f603480d099900582c1e4040c03840e8404200d49590050400582c02515a4905401012942034502612901500d40b0440342010041146030541d100c90300081664040104215607540d07260102400c158007c0d0b4054001405e1040081405806084440a1a034200d00140b009541e100e003080501ca8006069403065030700103201e080140c40e90311640e09502e10035280c01180303c803400c90702d138500825070780220300c14401b031068034001100105861082c144280307051201500d000e5034490241207a50311040c0c010301804000200701c2210783c00042d0300c810850a4550003270034a0985842c41c0c0d0180d080303001c152070030404125001d0044290072204803c0b44400b05000e4440c800 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 620323741 1107 620322634 620322641
    0x3010f14040605062b0b1803180d0b0c030f0a090b01050f01020f1f05060402070b1317042c10170708060108010e0d0e0d0b1801 56
    0x4c54a00c0e144c21035480c03012280300302c00e85001c0115400d000708032201c440c0300351404440c0c40c000c1032078980d414600301c3c00d481d240c01c010760074046c40208129220704078150040e808012210950002424090544c0c032483c405580a07440349080c608000c4880c00044c5029103052410721050f0016080718600c1c0d064842c2656049056100400143e10300b2601d5525028148580d400f07c0301070803641c0500000c40740489100b400745407151800d1009034029540d00800200c0c0780000110b010060140300300c0b0040c000c3e041e081c601d084455040f19203a11640140c4d100700c0720301c41240250b089d4520140342060560201010500d8040d6207458039400d80d024010943d0b0311a070f05c40396200000c1000d03c0250101105940d4907503035408a86000300164260441c0d02d014100c20801c14601440e0650b1201102510102e145001543d911803100c07802401084030101054120381504000d20 = true := by decide +kernel

theorem cover : BRFrame.Cov 620143884 620323741 := by
  have h0 := BRFrame.cov_init 620143884
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 620143884 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 620143884 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 620143884 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 620143884 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 620143884 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 620143884 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 620143884 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 620143884 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 620143884 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 620143884 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 620143884 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 620143884 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 620143884 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 620143884 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 620143884 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 620143884 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 620143884 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 620143884 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 620143884 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 620143884 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 620143884 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 620143884 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 620143884 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 620143884 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 620143884 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 620143884 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 620143884 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 620143884 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 620143884 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 620143884 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 620143884 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 620143884 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 620143884 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 620143884 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 620143884 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 620143884 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 620143884 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 620143884 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 620143884 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 620143884 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 620143884 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 620143884 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 620143884 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 620143884 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 620143884 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 620143884 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 620143884 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 620143884 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 620143884 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 620143884 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 620143884 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 620143884 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 620143884 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 620143884 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 620143884 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 620143884 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 620143884 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 620143884 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 620143884 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 620143884 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 620143884 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 620143884 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 620143884 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 620143884 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 620143884 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 620143884 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 620143884 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 620143884 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 620143884 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 620143884 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 620143884 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 620143884 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 620143884 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 620143884 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 620143884 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 620143884 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 620143884 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 620143884 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 620143884 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 620143884 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 620143884 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 620143884 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 620143884 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 620143884 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 620143884 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 620143884 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 620143884 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 620143884 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 620143884 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 620143884 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 620143884 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 620143884 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 620143884 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 620143884 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 620143884 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 620143884 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 620143884 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 620143884 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 620143884 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 620143884 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 620143884 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 620143884 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 620143884 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 620143884 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 620143884 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 620143884 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 620143884 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 620143884 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 620143884 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 620143884 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 620143884 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 620143884 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 620143884 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 620143884 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 620143884 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 620143884 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 620143884 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 620143884 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 620143884 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 620143884 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 620143884 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 620143884 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 620143884 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 620143884 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 620143884 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 620143884 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 620143884 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 620143884 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 620143884 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 620143884 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 620143884 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 620143884 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 620143884 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 620143884 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 620143884 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 620143884 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 620143884 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 620143884 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 620143884 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 620143884 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 620143884 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 620143884 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 620143884 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 620143884 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 620143884 ≤ n) (h2 : n < 620323741) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
