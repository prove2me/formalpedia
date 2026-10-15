-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_5459
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T15:55:57.078767+00:00
-- url     : https://prove2.me/submissions/1e190c21-711f-4e71-b99d-5269f31b623b

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 981654676 ≤ n < 981834532 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 981655926 1250 981654676 981654679
    0x210d080c03061e03070503160801052a0a02120d06031218090c0c0206031f0b0c100b1815010906110a060506120f07061b02090615220302 60
    0x9644800e805100e05210507030703400368402900f040d030000715920040390501400c0010308862825960b14003190074540724881000003031b5038103001000203071820700400ea4001000e0064103412603c06000d5503140c91902c900301d1407c2d0000c1b880c41d400078000c002c030024500360035407000e03100c0c10100740c800d0103080c20b8042100c00303030310001039401414081c070380d0043c0020000a184101e28103241030300008104d000103e800300b06002c0050000f60b22072000441c0941c00881b0480484042403610403542c402070790140e221028204007800b031500d008201411000b24050000c510b03005c0800010f40003c400c0d030302815240c56190180000c04810064103881d40c60280c86071444a0780e100415203c40c0b0400c41d159249401c0701c03c20100154071607000d154082d000614540785255200d000510382850042e407040e20f2750201400b400501d41001e1540e5400170f5880c0c1c602608041c0b90b01041160301c0c068030b00c5008150b1484003034000c4141406541481e09580c09044c6600c1c802103420004084901c0140d = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 981657176 1250 981655926 981655937
    0x70f0b0408070c120f0b1b030901020a090b12010b0a030905030a0c02040606020703020904060b0a1d060112060b3709030b0106080f070503090c04020304150e010623210d 74
    0x4088118800c4d03685030703035000305404e902000c80380c903900c4560301d00500c446a400c5c140041c1409072542d540285000c0c83c0325000041e20350744480e00c05855050b46d508010450030060180400300080c07a101035043d0741c0715910f207130f4642c0d240b1340066020f0249280c000b40940408034503882e120360b00841c1600014000c0f94184900e81e80d0301d0301680c403000d807404040d41090030b03e800503020400c1500448c401c01406404402c603203079108181b04400da031000c59a000d00c03c00c84c0a00020307607801920b54819071850003003080079900e81200d0140ca44104072000d0a9988030781c00088512980ca00809654000c000c141201c10001410042403000c26000440e03c003500e400c00440d84910821405204100408180300d0070f494260b01510150402040000d0703c0c81010384541c895226800614051840307821074440e42e107441c04181e0700703072581e582628810340c1c90090704005000c0504071417020210f43c0c5241d0018444d004011806ca85494403103080743c207145414251485800040141000c1c1c240e0b86c0c0e1 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 981658426 1250 981657176 981657179
    0x12091a0d050609072f0d08090c0306064c12050c0a0c1b0b0a030c0e0f040b041404050d11011406150706150501091415070f0b0408070c 59
    0x30009510010340700c8078002000560300110042202c10072458443e4179440211102602c00d0106152008507880d0f1070000c0c48520034080d01c0507080243c40510141203000d003a5030315104000c200f0702c0c0464810790500b03815081c58060384500607488400c42078201022428050344010b094540c518940e20180001441c9000d400000c18861240700e001d0300009041501e0205299003c4582e038804141c1030f101d4410312500c9040f082e2012010100400c0ba458150b5140e01c86a40060100e4a1303600d86442841000e010b100701d01d03a104103568141d200c041764001080e20b40040818020480340030b8803000710315220144014008000f40e140c02400c0c0e07035503039a0b00c1200419042c03420f031000e00b0003003a882014980480c1076442c0a10307203403079080c50300d21b101070400c0c1c81d944828040c0d07074001900d003400c14010711090141c0c4d6403040d5648050003010f02e401c1a00392525000c2000041c541240124019000c1000c40030000c40d144914a5903070011402c103003134241410060b01c290320000e4200d4024554850 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 981659676 1250 981658426 981658429
    0x31a270d0f05090d0623090d090608070207060807030e030705060f071809020918070f08010f0b0d0207020307050a03060f1404034815020c030712091a0d0506 69
    0x2150071141c0d02070482c0341000144d07510700015150042007105c0403c0806c0450f0300013a80300b01598441c00855006025008048030007030440100ca80105040024001c1001049030b000108001100d5540c5400401c40e81c0300e100803402040c40d902c081099000008400c0e06020f4001130180c01000f070b4041040145d1a1a41c00307450100c1c810b001007001502581c070400100f641d9901421038440003522600c0030b0510442100b444d40c404803100c0c808900340d028030081440d40201ca513409086d030851716052071414407604200c2400f4081d4071a4a140c1c0014a45045407420f222040c000c10b00548000038a903200c1c54660050196000449003091a19030028010f508814220340200d4140e100e403000005c203007401e0300072a80e0036603920f002c80d0704102c403a0301d0315441c1c100b41c401e01c4d007103d200159102005240503c0345c2090003900282c41c43c014030034800707011008011680c100358081c0000c6074400c00000180c8185000b03600828403848416210540e075003c45d400ac1a0301c07108818100030030f40d110030 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 981660926 1250 981659676 981659687
    0x6020a03090e04050c09010806092505150c010204081f090305030c031e0109020a1413121a0a02030105040f200c12070f1b031a270d0f 59
    0x16405000250380390401c201c00c00030500140e4001d80203c0c140c5810702e1081c008a040c481082e402000c80e0b6004008110348000240003e003040007495485080380112005c4002c050441070103000c2c85100d000b802e104820260b00b04840c1d6085000c4000d6413510f50342c0034070644030560303500702c210ba0f080a0071300d60100c01690f10446035280d6054403114215159194403030501e42005101c0f070020120040a912181990302145008000c01400540e40e075580030b800920607140e0304100310001005106950b075a001c0304420009568000154040f0260701342000003c01c049040211040d00800c1d05001c1d0308031a40d00258140c03003040d9014040862220000700c00c5030244c0b032403200c0c803070482c05904000703170381c0382d80140411001041100c035620060300c1880030503840028100c501d030421001c00301c1001105030b0000c518001e54269604250700d5910781da010101e02c0000e4554021100000a6511a9100240c1003e42415841c0e10011410013030840d0b03070b0410000c103800410384041051055900c100c = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 981662176 1250 981660926 981660943
    0x90c081c020a32030301092405010309080d1506140a1d0d0c0e060108010806010b0a031e09051e01020c0a081819031506031a071b03090f0602 62
    0x981c0240b50200503511500380419800072800034000c08400da45829110b032070968440d06040c074019650740d51408a60030111003141051030383c013404c440411003840e500107482c041107400a007004a64103280340b4102c841031040d0706080c01c80c1031038142c00c0c218404840c0c0544050b186561141c141c0380d00e280c0c641c82013038046d01442c0800603406080345100801d9a42c03020303105880142501c140405207070340e200302d0071b0201d070080303003c071074a2800f000055a0320103d03450040c20501d0141c2480d504041010b0200d20424040c071040c1074031030805002170b200b650042c02c0d82ca2801001002890f4080c41d00c00d440310f0b5405040200406814110030301c8034011310850b482c0c0903103c002000044096900c030f920f56001502e00d81d107030300c44072848454135440303940040c03040c80006520200820b08510b004100c490404194018080c80e0810600004000c1b45180c04149108815100b80b6a5403000449211002c0c2068114200ba06200e900c1050b410440110a440210880d511144e898a00407079980c80034 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 981663426 1250 981662176 981662233
    0x70c0b0c2116030e0f0301020c030d0c0e0d080703180b0d05090303091513061104090609061511010f06060e01091502030301061116031a0a0b1f090801090c08 69
    0x302e2a0b8180000d014201c0e1001d56000546040728810a4000082c220381103e00c41d0a80c5400028840b8418561881a111001c200d41005031071124a0301c00b048407014a50001403c42500088d0350003414040c50f054050340c0d40d010b0580d41226110b46512007183c015858401c7c4903420500812280c410120580c0d204085200003010b030301c2850030f182400141c0140031003800341c90500200c2c01080790340c02030018800d100101d069403680b800d00c05d1021105150300104d00c0c1460100140303e0003040c540320015565851801204180d0030360b2600c2c0c01059680c03e50f0b41080c1c0b4180c80040e00e00c1c0c01080c28104032400340c881c81c9809649442c441c0750320742e2031841980180c00030001030040c0c1c3d016002c600302600c174001c129501c1d03103402ca0200141040a40085d51001d1480101e4051407040212941d40041c10b000207222410790704011a020141d0003040407001403954030014503c903c01c01030b034401400450020f00a2018609241c0001d0146010722000780c01610000b4107a1501c0e0603815400500 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 981664676 1250 981663426 981663457
    0x40b0708362101061403211c182d0503030627040b0609090d090b1b0133030803060f1513061e14070c0b0c21 48
    0x20700c1000294541c20040341615100c654000b000e45100748030b0750018148802d0203043d500040380405140c15682224004000d140d00901034111901500340c0300800102848198000b4100d41413002a1280440702c4110303004045814003170102040d0360544502c01c01864118940c1c0701d0300c000c410304407090000b402c5580100302050890401032541d90411115528600c0d41100e02d40040511076410b0714203070740b448030240a2010300c0c0f4004206503080304d07843c00100743e00d4085803009040a801842051990100401c01d20b03428090021000d14101c03d80c402040429401c0b00400c4a2050700c5000c040080e811818003060400245101402e036900018500c0c21651402c0030814601001ca00d141d810400014082d4000340c00c06d0046d100c4100c19840c20640c1d2424120010b045011041d0090310220001400c800f200b9044200c2e21100071440c02c280d69191400d09020010321010344c4a848007000c0007a12003102c5401258088280c0b44251521030040c444103108605800760b10320b07241c2040b0 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 981665926 1250 981664676 981664777
    0x190c0e010813060b090c0a02010b0607021f02010e12071703012306090916081005180a0615020a0c090606120507020a12030c0e0a0b03040b0c040b0708 66
    0x1110ba440200403a40715600118105016001150413201c1c00d0f181c108103040049003100c41e898080c00380b241d0100095a2443c10100c55800003a0100c0600c0d001607403016010b1049001d41c0d00c00c1d0001880700428901321110907801e5440b4403110740c030100d02510340b8880ca043c13206680b484842268100c403074800e08800c2014040c10703100348100c00988582d901c14010003924441d030300c82e00c24041c0301703568059412900c6c4040c490040c240d054020f240340541203520409010540e9592580d034000c25100c0c50070001d076034603c440b01c0c0040c00300da08050f00401480c09001c0b521a40010489400d42c80741200e000207070b558440f0034046d512030780610404100c240c01c8100c100743c0e43c6d52005900c90141e00c1165466131041d04c4000045c04564441d40010b5112445000d0040d001401c1203603400c0700740c0300f042415240007481c0c107642c0806400141503611900126040303034101000c1da0007900d80d10b404281c0d220001d1404025a40c01101d83c01861800300125900c035a007502e003080d521241103000442c008 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 981667176 1250 981665926 981665941
    0xc06180c1502030a1101090501290d020915060702030a0b06100e0307060c0822080f0601051804050a050f0102030f0109020c0c0103020903010f1b09050303190e0a0e190c0e0108 77
    0x9202c0281e803045e20340d82c689006000c524240142a0758107c4416000800e41204415100440508901c0c50083c91480703260b00041c2c9507089560760220f810009260100520000101d143c85464006135052141c481441c060200d0040c1c0c04c1c3c06050304a852a0803400c2c002c80c150782c2c403058603040c031358107801c090030402601d03000d140c101000e5403140c101d0a241c204141c18115214074488038511340d00c0d40f584c00174440740600304406000d00f0361040c0281030310342c9010001a4500700748501c42c44181c1c3c44202050800400300f165415095000c82030342e500e240341030340030381c000e42044540517000b1032120000102e44c070043c4201c0d51900c00140c0035108800510f00154041d5108a1140b40c040d944c07408a080310000030302c0ba8088089042141c1c1e0b01450030504014080c103c02c0d00850320a800c20000310b000c01489071f000d003e11b42d01c141000410754480c00005400990325a02c04409454680c080041d2000580b04000c44840c00c4c2400308a983d008100c21201d030004402154046051840424082c = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 981668426 1250 981667176 981667187
    0x105091006140f1b0d02010f1107110316031a010608010b2d040f0e07031811041107121e05040e25050d110f030103020f010c06180c1502030a 62
    0xa4030f0800311100e00e07003e01e03d81e0884041030079201200494005000d107560503030f4280103c4291519814041c4407901419802e98528482ea507001046000c02541c0000191824000c543e004581c0d011410710b040c2d074a041c140384058022070300410741c0960200220b4541c0c022806d0030b06030b95607400c62030300f41070040b0700300c0018108100c0b6030707000c0c00a820b1a80c800c80300c416000304080c0256507141a00580791101c1c414268001170300e19020f0500b04400542c11461580c80400416044080f610039000c2000104004240803c22000c130183c00060b03040902a5900410181c0701c410796411700982618030233400982c0031062101e00003202040200211171038804141d40114214803a016140c07103050f41d880c1d0360081046444013080000c42d00c115161020b11074000741001c4504494603210482c810b08506100500000703106800c0290440b000f0391281081503c03050703000a041115001c2d4007801b640d450924078044580300d25643c0c01140301c10a0740360310b488184c032913001541002d1109400341c44 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 981669676 1250 981668426 981668437
    0x50a0c091707050901081011120615091905031506031207020a08060112140a050d0305070c0f050102090a0b070b0604051b0703030203010e07020102070b0406180506010e010509100614 80
    0x501c142c00002ca020780d00c0000742402000240018000c141d001c00c6501c05903014140801c416400502441e102c2d061000201a03000d10200c035807a030403400040e202c29060080a0b902ca4000c4003289800700301690700403202c02078505c1141241c0310000702c80c0000081d180115011905a0841c46100010301e10f0140940b403000d2000f840781d0b43c06501c3e10f944901d8880c00340c0c05100808030307d020140501191085003180c68030154064aa91550364603820340d0b540f5113409105c00c26079983d00040c08144600540850a64805603d2541c0c441c0303400d2070350103500140300c494403514807504000f43c5554040c1c11200e8980d400540c1400566a040c10000180320090070001c00d0720070071116410001441c0020000c861294500581329410003001c1c0c0f04900e001040320065a204128420100b03503c010201d40c4158020300106e5030f0700450205510740c240342400100988103003000840c0c9a0f1040040301e06843d01034680e00d40c65554460815240641741c400c0c640400c11041c0c401c081c442c5903200400 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 981670926 1250 981669676 981669719
    0x6120a0302120f1c0506010306050a1d070e060714100b1c020303120406141302031b0f1801031505040812041e0b040201021e030a120f110409050a0c09 66
    0x207042015143e20200c4c50344980e100201c18980d11342c2080310560305480f90402404083c3e81c2c1d251a00e0030501c003400d20802210b080310b0800c4060000908aa1044200001d0748001405031501c504881c5001c182d1106900c0c03400c40c2074011101455a00780d12480f4440c40c14400504500083c10f0420075440d00c8641d4502c1643c05000400001c20400e284180b4240564840d8400040504c40048404d03a10f0001400c1612034451001c20807015980c00a46407942104c0258400300408958002400c45d002004095400544880b10740c0c00c05511401481e0484e8001e08140c4803a16150b03511074100c401c100c40080c09144103000e02044200c0351490340c2d80c03092044506c41c0e02c8203807500300b511098030413283c2120000340f100100300c11942d0600c14003030b0205a800c80d100c0b01581a0204179207a005544545007044010340c034002030459140c01071100e0f06d45058080100c80108180d00744168810b001e4242d0090400c2d0100760340558030321985140c40555625442040d00b000716200208200483c0c01 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 981672176 1250 981670926 981670957
    0x20f0304033008011e0b0a2d02010e0f0708070b130f030f051504260702060a020c1005040602060f04020d0b1518010e0411180f06120a030212 62
    0x760014410038101409507641c07165801585491101d81c81000803150162202c20303a080c042200d02d03880b8050311f92058035400e02c942003030260032a007501803441d1a00c1000800c240621000d4958040d0300c00360302840440140e401103064620040d81d0303550180701d07016082e8030200042108512030000351080808801c51850300941c2c80302e0318003600c0303881d40040c0c0746020718103e00410480d080282141c1c030840404a500145444c0d2541e00d14900030108621410010b0301c0f0340ba00076485001212030280e8001d046c9501c80d1217401c0c00079030710f04002a0543c050300c80646040c002e00c2c0100140c90844a0590040442c0c0d5145001014041005841282c2140c414000180000e11401220384521220040340710015401001c2142640d018040d0904944440d4018070607a1241940141c5c4540c01c2000300074081c581001107050002d0350900003019421030014055011079244015001d0340c0103c0703401d280c0c0304070207852a40ba94560080100503a1042c0d5100500d580d121014100d108000800c0 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 981673426 1250 981672176 981672233
    0x2121911030a0201020405090619031401141812030c0304150207120e19030c05040507110a0507032918011b03020405180105150f19020d030c020f030403 67
    0x40c0e52030354001070542000760b500400d043c00715040a000725540454100c0301e80e1b40000348681203243e001d0705401b001d81600c0c0c4034003885041e007100750807281800070341d100e0824051400241c408058261112182214095910b0003500840d456050300d0007846440941c0b481c0d0f4440d6510740415039001e240d6507813600e400303000280100320211110001e058654681e02190a600000c004480c007101181a08009603004184040742c2c1884d800070a843e41039038002201e880328402516007202030741301b0041038860f86440000304140400c040084a03c9003104000c4154240c11b140d54110a00c1084c0714841942030000e0030741c0a9002001d59503c682000010f0303400031a0b46030300e107910b510018960200c1d0b00040d0070419421b108081d0128240c91103100c6509504005c0000c145003030205c14410710020104820b40085008030869000c00040c1c0000d0640e2181000d000e521400c0f0280068041391900c008400d07404d0000c81c3e4149009400302c0510b150605540e60003904840d03a900c4065412700b41c494 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 981674676 1250 981673426 981673457
    0x304052a0d0b0f0604020f0403080f070221070902090603070f12020307020309090112020105070f03090f0e0a051003030e3007170a03050307030905030712050d0c021219 74
    0x5807842842d0160401400070f19021042498140c0301520b43c03030240d441007111403010300012040c0c40660b648100034070f5a40b100d1640d1800755008a1001a600148030b02419100720891100403010300c7c0c004d4190703030780b00760b650301c0200c201e01494680c96002801000040c504520070015070312040843d080c03188a1038a9564110226002120000007580c00000d4038002c91505d03082c3c2d42d006282e042000840503540e43d0008116007c0d56000070b29408448040f401054080c140f07060141c00c512180c02c0009544084d102c0f100c0c1002e6030380008940c03070600450072001d07140036071000f5079405840c1c40c580c0780310001c203000c605026444030041d204040610b800e003124030000d00d501080003402c020400c0f1410080d0300880065071400219465010a40440009801009486d030048281c200001e92640078180300e800c52003266001080003500c112000f0307105030400c0180c4a51411076208225092244005030780d9158800407000c1241400e01c41c80360072440c80b817000c90200007980b0700f4801c03240c0c1d09030307 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 981675926 1250 981674676 981674689
    0x1a090a230c070f050606040b090c07170d09060c030b060921010b0415080c01110601060305062107030b0a0c021509010608060f191107060c09051e13020304052a 70
    0x4404607401e1700280144881ea01e498003402006140c00c590440c80c80c10903401c0c050940c0308d10240100414103401503202c29441782c5040c1d814840c8080018098410305241100043ca81d07151010f010a1800f4040d541e642000d00c10b0300c651042c09089200080400003400d551a070f01210054415902c03454041e010340c49038040d00040d8140b0180c15840c070703810490158140021080081d0410001c2d444200508030005002811903055082c00209034131183c0100c1e203826042c5e070041e00d100380c4100c6504030064001400c00100c038090802c540c5039449540300c131803d07503808008400c010380c80780c10b6002821190548903900604400000500c4075a0307140a030741440d0003110180f104407021f0302040004800240180f1451000e210208001c03204010400d08a000e549009080c2903550720038070001c0c03400303600880e0207400010a800d0809402c490703441c402c038225008090050000c0d08160341920751078000d803401554080041c2c003004194440c2103180154030201110000642007c5443c240c40b4070703 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 981677176 1250 981675926 981675953
    0x2703142724040905010e1014031606120e0706210902180118020306180402030f0613061805030a14040e070305180703030818030c011a090a230c07 64
    0x10780903454a140c01d043c01c080b2031059003c1e0f005014400c00704800c403100c040c4440c0039182203109190841e244940424500b5070a40700d40041108040000319120360000302070702445a07542c0080c4503d51511501940f1288144a000042494940300f001d4440b5161030080140706103d43c002242e0311141c00041040759200c4110701451840f500501440b00172000803c0c2c02e50204005520f5806c2200c04101d0b403c1d2007030103000e240c1e015900440c04545d03007405404814002c24048030b005080c04042c10000720140340d02200c0281c90003414000c0d0030511046000010380040185080410891041c1d0b02401180c10350014030310308100100b40003180c0d210642c020000795400140d14a001100300c0b119141e855410104d0340d07c0704100700b0010354449a00ea900861aa040e201354101030103105145004648040840b5402c2c020388080860004c8984401c90400321403003042525203003607000071510440c1e1000a0170b201e5414000441d40d0300704000350000c490303640d2245001401d459581826000 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 981678426 1250 981677176 981677239
    0x2100903030204050a0f0b04060e031006031b0923060105071401050106030e0a050d030c05040512060405161421061513140a0f27031427 60
    0x1143c24051400c28801d081c0251810f241c581900600f801c1c00d9515a0007a0b01c116000c00500354072220803500c05112480031b1702102c01c800e100054403480c0070000602400341d840721030b45006500181403c91030046004015000c032201c040710740031254041c00290f00510075810720030208030210008407400540b40482d0560f4000069950400400805503030700300d109514564004482c1c14041580071464bc0c51081050a000940c04641a41501c441c0120380c403650b48030081c0da00400c1c11850103e4190b00c2103201d50240d400b146000840d00c802d0303010b10b00030355148a00080e8051020304004d00180c0001041400c01a03030b1950722050079142c1442280e10403554240500c1c0000d05c1e04007100549980d0940400510500c00d05602d0f80b600d02000500c0c0d540d1040e100c0e070780c030780404074550302800c140f121440845001254941c0107510012201c0403c600054240c200010300d0a5100c0503195504030324902d0f810303043c0740015910401c022801c880b56109aa5443d40d0503100d19000c0d241003641c3c80d = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 981679676 1250 981678426 981678431
    0x20409050307081c180b060f040621060c0201050f0f090a0b16030c110a11210303090705030109080d2d0c110705092811090913021f0210090303 63
    0xc0203601c4100341ca03421300000c80313540c240320300417400910351021281d03104a0036540c1071000e4000d100000c0180c034441d4014071a0000440e03200d0344814081414040c4180501c00a01c00e081c0b0202c0c04a003200c4d4220b0700104044440070124030003014948900d500610448201c0b5006411034a40f0143c6900c1580c480c007100c0415001003509541501400c0c15004050504030501c0ea01240704540f10a542c03800280107e031101c0c01542607903107420402100381907005100d2011400c0c0c0f12007507900d0f8800c0d20b401c2d940d071141100014651405014110f64160b114080500b40b130940c1090030042d058034401e445054107000200c03111100c11000107040d41032404000710f01c900f200c25028200358000780707024640d50042101445191501c1c0305050300400c20446540074038948a0b181030a1805881c8601c400c0e40c103158a1103d0101040003600700140201d0b010b1050741c4036010900c2c110208520000e412104911155280342402d03002c000800c00e0f24010b5a020070202048001100e070302d40c2d0100c010a9 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 981680926 1250 981679676 981679717
    0x60905060909032703150f06040c020705132004031403090609040203150301050916080f03030c07020118120b160f05030a1e060918110f0a091b021c0c02040905030708 73
    0x29400040d48c0107002500e0030440e000381c40c20b00135100d900078001c0a025049030040c01001201d90b80c0300541031020f29410300c42001009103031040a5007d48015101d43c506d01248160200001c41110743c400d600421480c94511610184030194200411115140c8485944400c044e00c0c02c0c09418410284071024100540141da004000440b007600328582503400302d51888200c61000003103030f8000644001090f200c01a51004a83c00b44802c10110022000f085000540000580004070081c1c840d0488a0b160f5482283c0c41501c40c0c442c05180000804541105400314040e0000b16000100443c0c040392415980b040755002d4440a103550038020342d00c100400ca000110701c2010341501200c46126500100c544600030200c01d0b058a951180f1200c40300d151081d612452048014150250240f202400c8841d014a81c4514000350304058000c1c02ca02d603a80d41c0f03420340944182d0229480d840c0d4240341c0e980900005000072202200d0070300c000c01542001c16451381c050615642d41602c4000040c = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 981682176 1250 981680926 981680941
    0x80402210f150a0e062e150f032705010f140f01050301060f0b0a032c1c30020f0a0215060d060515040f06090506090903270315 56
    0x10b4002001d4800491502a18101100002c90010341004d00482c41580c111140000c0b4200d00c0c840d14801306a0038005500080d00600714544800078a03420340b101c0405600247d0180c040d40c24101c0c1c1c204103560b058050343c07501c1c040103062007a000e0091000084000c0303010503138012140003d08090300e888000040000280300c02d20b04602415041e0000d01c01035190402d440e1162000d801758500042002c03580c1c1c580707280303e07510030540c1c0181118035214241c0d403d0300c040030b80c10129261020901803480c80c160003800f1842e4090301070f60207940d04c00f520410051114800e56000c0b00b044011480e40d40f007204041554000f403c9242c1e680c4200d2607031128403d0020340b401543c1a02010381082e0501040001d5079801072900095800102c00b01e025990720014080c060203001c5d00c01c0d40700e45050505041d401c000d03407046d01074078075145e41081140c482d54104a100001280c60050f180d0003040350040034400300e0f4a1111040d045440624981107140029017002c8510651418585542c030400151 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 981683426 1250 981682176 981682213
    0xa0e0906012403020c15151e010c031b0210050304030216180c1b08030115080903180f0310060602010b0108101205030f040b030a050610020d03051b07060b0f10080402210f 75
    0xc0ca1441041040751230a400020340f000b61700007005003e010502d915800780d440f039080d014904680c010940c101c00f10176501c0280040d0400c1e2820703001449950907203aa031003403039510f00c01030310105a0703600c401c2d81b140c1120030041c00904000c07d040220f42c801d802c141c0c211510803410031603c0364071187e440703605203115091031490743c050100400c40e1a0090100b6500048200d80030780003542c51002c45c24003498040380ca052900c50340241c05100e40070200f0f20b42e803201ea0248054500030b40c028404c1803c140c004603144041500d004005140f1074104000d042210700121701401e11640907641420741e0f84c01c2842c2030b03800035800400500000010003142203490b204460b4400c7c81118080d00c03440c0a010300a50310500441004141039403140402d042c1442c2d0000c0300510031480480b90341c0d41d5220301e03005000d010f642246ca40160000e0800300024a0804031031507641007241d131054600d5403641c01300021100007040d01002d803014240100411402400943c031044014002080131203000541c1150 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 981684676 1250 981683426 981683449
    0x7261801230a11070f0611041d1041090a20040e040209190c03090c0602060c0a0311040f0305012003090d0c020f0a0e0906012403020c1515 61
    0xc6100307081108100060703110f04010817040e044280001c001050369110b205510864001142d6402c880c1c0c43c2c840b0424441d40345d203108503480c00a1003207880d560305407100c1502081ca1622200c2658072200c080c0e1480c02800804401084000751003003001c018041020a034050343c00c503d14a0302d40d61211150080c0020a500b05001144401c1c41e003480c00c0b4115114a2001d00001d02c03910140000c14114040d001241003444044030f4104440c1c4031244019004009208089800490407403001861500100301144186403404100d40b0b02056048c00300c000b00403040801d032007503400740400324140c0020340307501000c1c0d0f100f000001000244103050700c4010340140728111351040300300200580c031500891604403211850800d504003018030300c0000c0b8115010700030a40c00220000c000030b11600000c0482e07014aa580c41654203590300c0d0f003115100c0792920600f012140112504946080b88a035000b4442c00c0d00c03101c2a54245000f0001d0103440700015548401400702408403982c0d20b180200c601c50 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 981685926 1250 981684676 981684701
    0x1080d0801030201110c061c11040e0610020109050d08090f010c05090607052803080f150d110901170d1706040c110105090607261801230a 61
    0x8190200210042021005000090400c09000d48025080c0d4003040091001240107001d10f845000b2421040b0700301003402d08820107141481d10070401e030203d4004a40c1a00c85c2050242000e94905052100c0b041100b01050304642d0b80d0090f500200380144007482c440c8042e603680108504008c08401d10b441c02014280c50580d25100c1610b030000e4000d8100d84a0140a50300c041e120700f61400e00301e00703010b150074202d02e0060710080d01400c0c03048001184494640309071100035081c3c482d1203125410ac68100d40d0300b1001840d000c000340b018030b0700c1000211000e209003c4800641458000f15903000420391010b09241d48259981c04020818851072284840070701d085010b00c0b1290100ca00d1501300a000c0c02d0046540d6126803416611840d03801e408000450024822414441c1c0c03241d40c1d54404035408c0d4009a0b60041c0350129121207040d44da60170303c86108070099a19010403920051441080400daa596110b160a00c0000c009188510a40031440d041155103007250458082c0e9205007881c0 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 981687176 1250 981685926 981685933
    0x408030708010e19051e090a0b07020a030c060f020702030307031d063c0417060a02160605071101061d0f0403021009150608030d0b0301020c100b04090b01030c0e0108 73
    0x72080a80e0510b0050040074001340100b295202c01428001c01c400085030961140320030420441d8007080001c0b500e68a03440760046448555a480040340c95a40c4008010000b410080180b000b0901039001291031240d011401442c06040f64000ec0c03842d841040701300c0100381508207410b00c15444100d40842254140d610071700e0300428524185c9030010b0a01004a912030f994141c5421700f0a03070b214004d0b0608459211a030710f58803124021940384214108004034810000003440380d402e107000b039401c01010340007420184941da0340c2c0c800c080c0200801c4503003005003000c840c0180c0d03d4240201401400e1686102c4010031038094030034650b2030010300d0940e100651806000000c0c1e400074614541e10790040c0002a5a04603291424000da801c403072300c04215082090200301c0d40300200051a141101d028100034914041b000c2c14240e0007083d4060109400107807025a960169810540780180010000100b4440f940d594109028080e042a0f800a042c2d1000780918502c071000b90b405480000d008 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 981688426 1250 981687176 981687181
    0xe1017031213061406210106270b010c0c0b0a210e1213150c050615040c09030c050103110c0304080304080607230c0a0507060305070e2205060a0e0408030708010e 71
    0x1080802000407000801202e00c00b80c0d1052641c403e51200c1c01a05150324001007100c0e8011012700c44480301e0000d102c0b01d0303181800c001d04542c0203d5420a500d58880e005903c564901300140069411808010b0140b02e035400c14001c21401c0710139254a240ba44090005002044200540c6000410307822150400407c000703000e802c1005015190031500e40060070100c0c0c030a80003089131313058000c0000034083d2181c0b005005003d03c8100c4150f1001c0000c0c0c81c10007140111f01804c032040c000078400540180100700003840194802c0d0803283d541185175114520700385e000303581e4600d0355120f588004690781001c60107002030481448010f4100d0307d03030b01d0159885410001038031b43d18040300c0d0084c20001c1c800100d610b081002400010000354001d002c4c0c6040550740d88015014000482d0305000158100c0071000d114684081c80140d0b2450f59603030002d0301e40c0984801401040e018219551005401d44001340c02d05415916611862149101e00d0b200d040029000d03004c0300040c0c000d1410300314203c04 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 981689676 1250 981688426 981688429
    0x11150a0e07060e0603180a0b161e0c030e12100501030506071412040611071a0c270d0506040609021e06070b04062309070e1017031213061406 62
    0xd0301e801440b89440001b41e10303681e4031068500500345800800f0305003080200902c42c0d00c84d04205002c01786a86a40142c9640340c0108440300c0301c82c2c0719444c0458500b865041c0800e12800044c22201c01c00740c640140c0340640014a481d10040041c25400e02e900d42c401482000030600415400000c41d081140000f072421030001a00e004089401038210061000101400820340040013034042100d0304c80c0d541d8140b8103141d84400066421a0102030100c00451862020001102c0c011510300c4203030307912040f111a01038003052041102580c00503c030310442010510611175030340110710070000011072040d1031050004100204404401d030030301c000e54842a9856020484000d03d51000900c10a682c66241c020010103e00e503034000b00e81030780c07000c0d6410341c02060b2070f0b14050f216400840b0103807a640c59540e0010402258148c8850501190030080a0000181e108801880c6000d5a00701000041001007109088824000c100300c690b40341c1d0140030a038803c620032480020500c0c03a0a140090 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 981690926 1250 981689676 981689689
    0x13091a010c11060706021c0b03240408090312040627060305070c06021b120306100f030219050702040c03151e17010b031b1011150a0e07060e 62
    0x1c00645107801c1880d64014564802d022030300056841039046444400394041e500410300c0c10809a81e140d0700e000b84800315480c00103140001e074000d4808a90b5007411344c00801034035480103441200e150105120068035641c040c000c07091003c0c0c7d41492a600d880c0f40101c0200201441e101000c5100c3c6020b40c0d0f24003040d911280007080d11050304002c0356640390b442d004c50700c00102c1034000e01110320112714200304020b40300b917456120000d003040b1030202080c00c20407480d6110030f07510b656020300082e14030030000d07020360341505c6620401d0400500f441c201b1310207812079101d001011400560002119802c43c5031610501d031440003a45800c0041003031032062101e20080600450b900c024020b640142100d01104841018040d034007001804042d00e500b038640a0310104000d5071003402001c403c0040c00700026484407015000402c0480020040082034a03200504c220b00b850502a100c1c010341d104031992031702c46c090717110000c00017220240c4141117800e00e17400b038102c102004810196604980c0c3c0d1072 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 981692176 1250 981690926 981690947
    0x303091606021c0e0a0803130e01080d0e0d0606030f0b1317090f0612041707050604020409110405040507030c0911090f04090510091a07020a060903030e0313091a01 72
    0xf0221030203503020100042d900c2c00e000d00d081e07030781c864190100800c41d644e0100c0588940d40341c1001089a00c6e46070a15212151024081c00c94181c2c0690812828a0302c01c1c040c3c0e858095014180817402c024a4a0340003c0e200306410581d200c40e402c0310100104240d0325003096000100c00806190a02141d540042103170001079524001000860316000703070354070000e0322414000f0003080940c3ea041c2140c8a5941d1403011642601c51380a029103070516518403c04441e031882d0302001404c3c080e07403164208030080c0310854007502d04c503100340807100300c9072a03500c80c4600641c0a10002c00700e00e4590315054010b0000b0360004001d15007010b9070400c41080030010742e4180501111000b0007a900000814020282418050034510500302001c2c83c40b034041d4814091103001d80c8525113246110501034021b5101550031030010382c000d58000303010681590003141c1d024070a16000c6a41202c8903500c51854002c81484004007003004806c1000070407511410700c0003d16100c0300344118522000191040101 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 981693426 1250 981692176 981692203
    0xf090412080f04200316060206060f03010c050307141603020307120e0109050d14010c1d010306050a030204021305090a020c160b030408071b0902070605060a03020906041a0d05030309160602 83
    0x550154029a45c18000c2e0000305c003c0b00c01c0203c5069a03568002c0d41da140070340355180074100d8070001e20f1884c181800707020b9600201e41c50f42d51940d00d803010112060040c112000b030142c0c20500400d484500c1505d59200c005009034021a258645410318039000c0c1241100842404500b07500e5242d141d800518102c1140c0f811203004611b210681810404091065a5807a03d94a08540054503e03003110090340315501041101c24100054401541200d041c0d0262507400340070140d0810051421781c000b03041c060101c03902c02c04180d903a8004243c98001c140e031001c280e2500852001168a002c20501c2100c090015821401c50f16100d4803041e9031101070005020f030440007800105108440c0e807840c0f9803c8911000305082541c452840713009410008040761118203140114500d442c01c6403030042aa900144100c1460f100c50b030400008105a0505c000c10601d001340700c03a42990303908804010103014001031540d0749040328100d17060030500e900c072480c140c41c450000d21045a001a610300060340 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 981694676 1250 981693426 981693473
    0xa080601060f020a0f21020a0b0c1c06030b22020f01030c0504080a1505070810090f0b040f020408070e01060e0616020d260c0312060f090412080f04 65
    0x30902c104c0c103046003110b01038801c211001009040117005260303004500b8036200e6031084150140340890700c03540c911002400404451300424441101c1d070004002d010a10100450000002c0c0801d0080c8c2e84281e00503210b43c044503003003001c0042400a8101241c030b900031804c0d0030220660005083c00e05140c05181010781d6000102c0050f070041c02101c01a0800404443c0030200615210551000c0c12078040086030070040420512401291418069929030141e42221402d00f20322000400c1050350301418242c450418400d60b07165072058000800f1140805a901c0b824800d03014944140c0342c0c02104080c0840004001041e030044840d02568070494100340c3e55807082c9a031741244074501c40003943c0807141c24500020003290805d8be203100f40011003403013600e00000c096254980209031100d8620b0704100314855445100000c0300303920603401003030206001d0304580450042c500c1102c084400c0c0ca003114102c01d20941000000e54003010392940351241d86880e503520848040240c500b038000c107a = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 981695926 1250 981694676 981694697
    0x40509151012080a0314131101050c060f09010f060b0c07060903030818120d0b0a170304030f14030a090303030506091512010f110a0809060c07080a0e13020405030c0a08060106 77
    0x1482a0404000c00c1480c0307001c000c141c200000100b641411000003140c20710075023030030340449502580590711094075081c040e000039510301848040741c0100410303a400c0c5558901001c0200d1a41d80701d06c00244c41e0407002a0340700d02a22150a1404810b50843e82c14814031250803c0000c0d0f2002da11a800102070540c50000350741618841c1c68503424150a100f48000440c03448203010180d48000301c0c0e02000c0741d20081d003690302c14450020503500b165502c50741e0020001800440d65040c202c400f028450000b03003900b100d06150301b60450f0444452100000c0448100304203141c1d141c05580c0d04038a040301d043c585401c026072030302c042c4a08407481038001c0742d40c9080c440304803c003944611010350042006100211481041201c10341c440a00c6202145050001c0740c240238000410034070444141980901d0078105845051194000303502560403c290090000c469407038100c916640d00c0e80700345001d611b40d41000101421300c40b0b40d038250703801120402800c0100403000200c050440d041c1e41031980340301 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 981697176 1250 981695926 981695947
    0x501030b0619091a010e0d0b0109420812091002012019170f0912041e1202030a080d0605120303060a080a0803010e1504050915101208 59
    0x4030034a41c0310f0319a031071400c10000207041c88464078100640e000da80c2c3c405120180f01c200520307501050009004101040010303c07031880d07036a01034880c0700d210800c012031011000207040c90494545001c66001c550010b00c9a030b0302d11408584001400c0501c024108524149100c48014081c1103910751081d4600000081d426000303501c4040c3c2a2202480e402d44513003c40c5e80407500740c0c0100e2103801c000c080c0f940c0482c2514441c4050003420f10058070310803081d841d2500054400c180c0642001228082e005940320440002c0c00204001c1c00d6808400441c044000e54038690204d10341c4c801c0000c030040d2880d100c0140c2e8085071000307241d507004400c5920382c490b09503420700802560b044690440b1380d848214082d45000000f031841503904541040c041034481c102c80340c58410101006206510070300050180e43c400c4400c09511071444180c50460100210000e01030303070020303588a2040c0d0814048841000101c40c031441c1e1043d04491000c081c02e241045500700001c800e440030313141318001309144118 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 981698426 1250 981697176 981697219
    0xf0c0519020a080d0324080303010b0904140717010e0c0717090312090301060812040e040203030f1209010e0f100b031e030a090522020309010f0c1706040501030b06 72
    0x28040d20350446040c282c5a0601030010b082000300d00032100000b400c0203800c0c03050100248147d890b8040558116440c2078040a000e8010340700355944551541d460030070b100c8401c403075288201c040399600211680004d40c004060001a0000c8600d20490f1003081030a074000003c4584066001c0031150079440115166280c038007032410125458010800300c03000100d1004060542d8075001c0300200071103507841100e10b40d1f841080341c00f20142d4000748000c00c000d80701401d5107944680090240c900e403480184407510f40d6407264041a0455030f42d5030a0081c40e8400b40304405154800c500140080640c62881a0303446e282d9842591090340c482500b00e00e140c03820300c58582c0c1c45c030110208003000640c200700030352039810684007200050640c2c0340c001801d15021403650034155a500d4114201c3c0c411825440c0650300c014608031284d901c035014190840114403c142c2c410901c1d50350008c0c0300034040704034518503401030703c003621030b0b41040014000314856074052500040201e0b00780c840914902c0c00e0480 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 981699676 1250 981698426 981698429
    0x30106050903010e1903170105010903202d01020106060e190803032a1603030b061303050c0a0b07200a030501060e01090509030c0a1b12060603030f0c0519020a 70
    0x2010f004100c040c0c000f041a400d030006140b0f2198071004c2c100c1f4031001c04800b02800074032683c1d001658208040011540740641d10040d1400034540c0351801500c0d101180200c901d008030f042c0003409410b2043c05403228503d81d5828201c4c2440240003141c50010b00030504008034401314440c11040184524428002554100401c240030659442e842c208400e0070350980c810850201002d4841c06116600d140c4008a6509040a0628042d4095107480450080401403002500000e0400001480b0101801e0b410000e42c896002011008103080500c00d0103e1070741d02c090000f61040c401e031000210300401c401d051120007440c44408000740b4000a401904690002c2c126500e44100860700c0c0c414034060714140c03a01804140101d444501599640703109541c0444440e42014001c00009403c4901c04e100c5c0d45800e0551003402d64503085090036180e0080801c46035a642c40c07408100b0982c00ca24101c224070000d050840c013091141e140d25445407490820010615a101c2500086680d001d20290 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 981700926 1250 981699676 981699701
    0x1e1c0b0613031b05150301260f0d03111c0908190806030106050d051e010609020c010603020a0909051903050f07060519061d06060c010e1f0b0603010605090301 70
    0x1099540c0d0b41401d04014450b01e01c1e5400c0001d142c03d01080b03d081485c0c11802165081489501d541e04c3c1100086c08507d11400c852036610410740040c200120401c450710041c242240604590548120060219155850306144030003042c00071100283c509414101009006035010516a0f01ba281905440c0f00b4031342c501c15454907039604040d9050340188051b10407501074008000c102c0e12041080361013250528000c1a0313501c00f40c1caa0803031784501c1840e05448402c907000030409a444a246038140d8224030a4031903140c2d59003d042042d072400041503001407413684c00401c40a0b01da501c0d060f8880c1310401030742000d020000314038010148694102c581da1040c141c2a603848030745900e0441c02400084d074014080c00e130442c0349070754542094411081142c50100703028008401035014400d0000004000b5a817161051000c035444850a029200203440840040c00c403600308500503c0c0340c2407080f040b400c031443c41c1c0315107215152601ca08070b070306450a608119032504003d00029024102c01580e08 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 981702176 1250 981700926 981700957
    0x2708120f010311030613020103180b010b07051b01021c0c020d15050a0b0a1202130c0e0307060e060403080702061b0d0e180f04261e1c0b06 61
    0x1180300d540303400045060b83e02c01e085241016010b081055541c0c0c034140d6448002039103e0154000660180d07018000744071610740a18588041c1d078840c40281ca4090740014904040004c1100070424184000d000a000410301411105840c1d00000c2d80c072500b20744032110025020b01e0706001103010b09c0303087d92840c1d4020481c0c0308401c00752814022601900008180380f07401c1101052148445002e6022440e002500d540c40c03403841c181c0c0040c00c44654000503030308004113054203240d44e1418090080804c0080e1206001ca49840043c1858802c1b940d00a0040024030306102c6501d640764800c94040301d03001500951608041c1c0001409480b0b02464020701010811108080314070125010014801549910f02440052410301407400070240b00c64044004420000e196404482c04940d003081c01010405084448040d404a50504040e1034000702100400c43c242c295049604540c8a403902c1c07a50241001800c45441c82841741c0d28240d1510305850303081c200c20740c3d1260410340b000e00754010390742d = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 981703426 1250 981702176 981702181
    0x50307120507030b040c05090d02091305060a0902090117060103080912030c0706022a060c030f13050a0501090305100509280c08060601080103080a170705030702060a270812 76
    0x40e0051044d100618082c9091214405129000d10b05643d01448080d00d9540500056070030444400341c002c24a1426a1031460040080f402c1040303824490725030f00800040110050041203400c80d4140c2c01088000703990a900f00c0220700c0429114112580400e4458441c2c41030000100c1c0c10200480041d411300c008150f41c0c80070a0300103550000c40d8400c0e02a40c45004090411502a143c00c06240d800e84000d50602001410402c00502d031120462090782e00f800403520503a580b9a101c50407115400038006828051032410850a00040c90242852801540395684040e01c8030310740c0b007041e401c45a4800c0011200d0300103116407031340340e40e00e603541c600348040740700032401203c141d450180c821248a600114101c80c00080707550180710142c40351005a80b9590305d0000300c1d070020301140c00304010701b00e12400d13402c001d40e8140e0042c0d0703040e1507240d141c0c07808180007460003c2c014487d4001500704a0b640384408140c06402942184017407040805641a041404181c410440403403845100c1c1401c = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 981704676 1250 981703426 981703441
    0x302130203040303110a1d0613061803020a080a060501050306041109040c0509010602010c080c040303080c18090705041e060f20030307020705010f020721050a0609080c0106170d0503071205 83
    0x3107000d4003507e04e58070100304001005109950245840001c2002d1040b03400740802e0b80204c019034402d1000703403100502c40d600c80d4042401c40b2007640c03201001d64090000001005040d02a05014000581c0100690314054a40c01c2c0b03d00c1c81c000142d801540c00703402207003d02504060308400f60001a1070704206583d01c4000030700070521403d40340e000400381c40200e502c104e60941280c080340d03090f50303900fa82502c0307401d1080e04035444420f1004c2c9801d41c100e01c03001c0315241d81041078855100c544070300e901c4515000010321480f40710412004441c0819405100458200300b8a468400c0180b80240030202c82604152119040558200b41740c4008010001c03615400111182560001c0e030301c10340701c2000d560060380c3c0d03801d95000301c40208101500f2580003c00c40340382000c89500400440b40d5802a540b01c000889000f41c2058416040008100496200074002c10004084411406400d050414501900c44003544180001c100001002c2001c0034461038111512001590081025007001300 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 981705926 1250 981704676 981704687
    0x80a09032d0215010e04061e0905010c0f03020903070603020906091c114207032a0201080402190503070f08070b0405130902220617070302130203040303110a 69
    0x4070500c0c0144039407980d03240c00560a09606040f81d4031181540074544951742c580024081c2c03e000405117907000700090045c1c003203900840e10b0080c0190000901411034a5006125601c10991601410b00412800d5000e440c00100041111420b213001a01d880e05000003958521641e804240e105103285c8044440000c40b0503040012842442101c010014860520140c1520810030ba505030402c86080e502039220460140f00302c08407060300f41880e210320041800150800e440a03000500d00320421000b5002c400e548901352200e200b6480f05103403807580020128580100300030f0242d40034410050441c040c1c1d000e040d01401c00201a5003006d03403621016043c03604c4600c5400781500c229075000403010410001c0f241a104054400605131031001a240080c1905000880e00900ca0000d6048000469040c190510074125000b203006854a0b0700e09002c440580700c0703030469800403c0e0820040c0d4401c03c081c041801400005a1203070f4a81c10107074001c0c101c060001d00b8080c40011084d00003980b11 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 981707176 1250 981705926 981706007
    0x31d03030604201806071217070905151e040303051c0501140621150103110c03121306020315040e01050712110408011112070c03080a0903 61
    0xb51400c0101003061481500045036000e140e00600c8020807504680503d102d0805400d0600a0565031400c0b0190750f4031075150382100c0f0440d0000c0c04c1c8045051b5030240100307100d42c0004a518260b00b4160400303000595a041d049015014140001006000c8030b41803030f10000142c0050018540340c3c7d03540d06000e400f0780d100d06c036804005d030008900c1c08a400e6251044a05951071400142285404802801950745c84020b2080f10103036801d000c0f1040c0040d00b100d5034454203200752041c9a03140b2900026043e21060240c44002113401e2150041c0307810008103640d0550400040e1510326103451380004851049040042c00481c0000b0030022591000764400303c0000b0150b80170403003500340e03441803800c0718002e0b50003070b000035229402c1c034180c01d82a80041d40c40040354400c0d10f107032a903543c003040c2c00c5603103103002e01c0d5404402260a0030706000d20201c00b0f40c0040f2500f400e040c001c8540c1c2d0010b100c801c006045020041d541e815203400c1c588180c1d00c040071010140dc50740308200580c0d0310104105c0e0003 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 981708426 1250 981707176 981707179
    0x4020a03060303021e19110901090c0e180f0408040b0a0302070c12110f01020f07290c0c2e0809010612031706010c05030f0310091a10031d030306 64
    0x3515000300d4940300d60b002521803002040e0117031030110441d40040141c40d880c010280d60324185100c0c011f00075900c001c0303001c1c024032001200058211903000d019040290001400c1e101e940105004226a0b800300740c6180e011039120702c101d140c2d55030382c0780c480918011a01b00502c2c01c0c0340841c0016010780c145d8014405c441c0500c028005041e83c03030803250b650380c00040008060300440d40203509203041c0a41008401c0c02c050041e10306682c2090607052524946030305c9928641e05003e01c41c5c040910b60345400e800500400001d07890003e100603d51799030320250b00c0313403070246a105e00500c50006004556640140c18040c220620480300c100060130602c099a00386810b520b0013400007002a4000800b0717a40d180c0c0740e11003001d40088a9010b0580c800001c0c200c40c1480000c03507002340041c0c01800103096254400c01600d86904240c143d40c5c01241c2d80c2d07080810818580940c2c00340c041d02500b0300900480f070803215000e044c441070380c003100a04400400d03591002c42e201e444101032603004c00078500c940f10 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 981709676 1250 981708426 981708433
    0x31c05070b0415060b04060f18080111030f0606040e1b07080c0f1002040828020402070302100e070b1603140c0703060e0312060d080408030d05010302030d020a05030a050903010b04020a0306030302 86
    0x2c840071310350846d100d070b48100800710b1481c200009000e40a82d00003081d0b04854080c24095a540750031103030a4442c2c0344941d00d01e1810000800c4448014130a0700c1e2341264041d10103a0425040103804034403810080c20429210035803501d042400c0700f020b011180d10301e6001c40c44d55200ca07082940a0b41e1f811a00d90229940d000f101501061440c5501c00d40f806c03a0043c000418800e0341c075051109200740369402d1012030010700e000700700141e11640020b10459200358000d0025200000c0c4000851b0b4103181515040c2c4c210310820000c1750f051400340c410a66125000c800f003050a807805540562050303040303801e060404221840700d0781000c100c6d01d003102d0203004140000803070032101c2512440f82c49242541080c040b8080b40311400e011030154001e134800d00d0423034a450f48132001185103401c11200381c514152110018421405c050201d224a1109070005107083e0380c4560301e05491740600ca4807181007200200320100c46a50940140440070806042190b480840c040020043d20041c00180c01522 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 981710926 1250 981709676 981709679
    0xc0c0712051c0912030201020f0f090a0902030103020d020103050603010f110c2401032d0807060e030306010c06020901170a020d06060206070203040513060b0c0d09090209031c05070b041506 83
    0x40e0611030203002c0c00d2255120280c65040c91982c0b0655800500240c003107660901c42c540c800c402500041024620702171242c2d4a40c0c680804200091002d41c00140019005000410060700da030300c00e14000c6942404c020030b660382c80c10080790062181d120505c1c419810590050502c1d0071600003000d404024100f62441c0817400d400f00c50000d01511100d684039100c0a0042002c90307815019541c482c641d404480c80004e00d011840030f5050707020340040d2120340300000c0d40c10801005104a00340070b00c034040036504514250001038910100c1c0000580701503000190200203a100e0000603030342e0026100d01030034600300004504004d4100381c80f09007402d0714041000c2841c900005040d40b0178102e9030b006516140c1030009000030321109045010b0202c3d00c41c035010440140035005880ca840355200146600d12580100510414040c1d001e928954810800d40745251400304d9070445003081000000c200c540c0f0100c1c22261886941c8000d8081230245040c481000000301c44030400142ca50001c0c446d05 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 981712176 1250 981710926 981710953
    0x4420b0109080a150213060504150e211e01090b060d0b011e050607060c030b01090b0f030910090c1e05130b03120f040f1d06090c0c071205 61
    0xc280740d0184a499500004005001600b00640d214020407501d1000d0300304011070341d842140c0246a08610302048020a0620003204140180d840c2c0c0d82040c5041062f050000002c14480118500201080c8801c404400c2c4016801c0118004081d00c0617004028504000c3c14940240352856040303c582c0034000124200c0e1600416030803201e500000201140d0b482e100380001c5200b03101c072046650001550300040c0760343d100c02c0174059940c02940082074686400030000c1c1110388466070141070194000c01030202e091504260780703140700c2003034040e6aa1388403800c2d154603166001002005075424075000004008102c04104102d420001c0081810a42e0351703042d030070381c011900607144c101c0d0b242d41d8070a4000c101c5400c010201381c4007409030341c201c17000881a40303416404851070710742d41c540010701001081c008801210081090f50607003e20a140c0c0307403800c050100043d2500340b0404c00800420341c3c56a00c2c0045400812006003260402591401504001064020159118010407184003640c = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 981713426 1250 981712176 981712187
    0x60d09050715080c0f03070807031538041a190c120201061508130b0406200304050703171b0d0f020303061f0203130e01050406060c03050304420b01 65
    0x101d41d071400170a0451f55030540440f030100c40201800d0405880301e00220307180c07080d1000c040240c0341020800c42e001041e00d042e1500046401d02d240d140c10b410030700e000c031301c40c0313004041c2e400b03452140d032402c412154036020959090103800c2141c052015800090b8a015400080c16007100d0301c43d0040702c00c21b01c5500c0042e400c031103440c0b048026011521440701c00142c072030000b41d648110040c0302c4c0302d04040e20b51114443c1e1a021502111090303956500e9110f402990204075030205407020165103940341654440d40c942400c2d1000030079880300c540c0c02d0040302490030240c038a02c1071202d0041e001d190400c640f0a0340c03010340018180204044c04130590b2403e01c04011203200c0c40c00a0034000c40b03c0307480b503c1c3e50300a0760000005401c5001c00d01201c060305290200700c10041031030242c4008554104010041201c0d455400541031025820300c10b0002900141030383e5200ea000400503040301c801401c9040d5040780188100c0710f1491124021a40d14041c0954017032020f1020400c124900550006594 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 981714676 1250 981713426 981713437
    0xf080120070c1829030f01090c0909080f0304030e090f04030813020616050606040c021603030e04060f08030d0606083603070b150109060e060d09050715080c 69
    0x152030000c100500c00c520462101e83c0d603900641c0c1002659080c0ba02801e0452030803e8501200c465503800c442c1c90b246010000050301016060007003007210035640d10010718600610a009003140c6612441084c049510305136000007280c1e00801e03a0b28a4540f50003840c07910b400c00e04038481d44245c404110021030301e2101600c40d950541b44d10301961204103040d00c4108010a00702d13802030080140c603c80d0000a00340c1100b03948207400924003804d0240421050300c5c5403070080e003715440350543c4021514510311170700440390181040f900f200c01400104000d402e40c2c0e0080503541c10310440000303010704000001c000548030380b0300412044c1d0304c0c1d400884000509540103080203498015a2480703d9040b101004a66080515240038081c0135080d24295004000e0503101d25290004100070315898001c10341e520780c400d1030700002140c01c0c440c004d40340c03c907000b00d824054140480c20903404031a40d402400d045410100f200c1c00746036070342d41d40d01d9030030a59071500d00021031003004a22002c121400360ba0 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 981715926 1250 981714676 981714683
    0x305060a020a0f051c061d060409020102120714070b03070e01020703111e040e01020c0724030507020f10020307020d03060807030813091406181e0c040f08012007 71
    0x3d00000c48084222401c3d0419440b1050140e030658112044c3c1000d4805c6600400f510040195200d681020360b943e10f01d001040c0030301860900f400200140e902058201c050091f6001d80740e159800303400c10a5814a02c110342000d0b038440c1c0b41010500900e0749014501c10320065440b9000070f800300c0c00480e101d88880c80002c2c880e0140100100c0549055409800c000e25001803a498184000c3c1c0020141c480c2c100002c0d80d2654000b40d501c006400500c810740103007040011075070b901e4101c41e0444210000030b6106c00101542c030b02c04106060b100b0b0101402030000e20007121165840084c480001f0350087d00d641c0050321804034010502c0c1e00038000e29089520f500064010780345075444461a90380014600401c00b000320703401107486c014505c68550400503050360f4860b00d00d4010280902003010304006460208010201321249494508900c5030205041c403c00c00d98546860000581c001c54110b0032401101a10101d08800150700c0703620000c2400160302085400a000c1c2d04503881030b4100038 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 981717176 1250 981715926 981715937
    0x10f1b021c081f1410080f0a05150405040b06040c020a0c231f030501090b0d030c140318030d0c12050c030904091104060504020412140a0203060702070305060a020a 72
    0xd103400d0b8000d0b00309642c4582030044240a0451010342490652107a802c4080201e410381599862410099504504110181000105401c10318041080200010300c0007000d43c1d100c1d40081c5401590b218480015080540284514100b518001811030800c86440d40610b18040001d400203100040610f65107400400210046041000c2c00c0440044040e07200e02100e51610103541585504000031010490b12110020301c000000740103003522010b034807001c1300c14280002c03418103645012012808a1b81800d10301c0f40d0340647d181040200c00041001d00c061701000c47c4141240112800300c02c105141202a9882080c0001c400c0d103022122050160860014018189080e40224000e000780403c850850341091400c50024050320311010080b113960170b0503801da5815003820b0280c4409401d04460039403c05082011032094441140c102402030190a030404c01145010701c00b4401e016005130540300c461502140180d952451480200c502d07208140006003101694400d450700e00c034165540 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 981718426 1250 981717176 981717223
    0x1706070f0f030902030c06070b01060801091517012a1b0b0601081003080a171315110706060f05030f0304050906280e10050607021c14010f1b02 63
    0x8800910310f101c001c80c0c0600c25140340700d566951300400f0380030075441203181505540c10b002d0000c0c6030b1101130f403201940a0600d020300c0c803896025120740d4190707400b11408540c110400003899014110400d090010f4161102c440b05640317104140ca4101c01900d07450b800354030401c40b51900300801e094031024183d9408074003c81c5032036100f480165044401c010b01c140109072242c680305c2041d4046040707200030070780b62040c1c100e00711116200300303911240840c40f40350080704603144c1504014220494400d81a07848822a1203030200005680403a07070040400c1200f55240e0030034440b1181c242c0a520310a01c940300e44001016400000c480582d240905043c405880b030314107021114550718000c1c0d452032980d1603190301030489030380f02000400783e41d010482641411800702c8422a5030360001406040d040240002580317404011041c42448104e03c900c000c03030582407400507851141d41c4002c1c5542846072403080c01c4203c2d040724403210240000100c400e690300710180e980d540f22030114284407640001 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 981719676 1250 981718426 981718457
    0x615140d0507020f060f0f070203280309050106031538012c0f0d0b01171e07320904052d060106020708250f1706070f 52
    0x1089030002d41c1801110700c0301c040078952505002040b07418403010782d1031030b04119100f0304900c4555001150342c00958a4070fa80c54043c2842c20441d00c44103d500074920600262a81c0b003a4080c118150f0410001c0004585919281442c0d403040118104041c1c24400a00d5400061000880f003118140003001c0f0920061081da0304803c2480c0061814041c2e9000310046c0c0d00b28822042800072078130301e61607800c11400000c2140141c8054a0741d40503055221051001030070b4040614199000148001060211481603511303219841d041c154028208000301052401c00041400035150b40140005402c4d51080c11600ca4010540300d0610003202c602310a841410201c00302c64101d80100c0981d160200780c050548240343c070402d4a18050f0101000114a5003030130310845000d02014030140c4221490701c440c0300e40c0d0b070b24201c401c59030012054061245800040e4404001007608035a4030080580c0c8012000c0c4024015918a081e4012000020a801d10490740d03071036445c0040e241c0c0082e0802091 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 981720926 1250 981719676 981719681
    0x10207030b0406020d06120c08011a010c050a0f0812071b0803070e040204081506030a1218090501090903022104120204110c0c1206130303051f090615140d 68
    0xc02c1503415941c20403e8018040302801014050500220100c0102c2d02c9072400c00c0c01c0704140e620154030799141480480480c8a0f03044800959242460400600106800c00c40d0a0000d81039000b44415468070310718040100f42c2001e40203849a00050340c0c1c0d10380d180ca1055405501103800e003840c3c5c50100035241c2c00140e00b04040c54102005103003c1149a0f14000072030308a0b8007035003028140b0791081180506030a58100346542c03124081d4003502000d14244e5841282c84400103084c014440903a400710020642490104010200d070a02031055581d100f5450004000b2600190014060301c503081886058040d5102445408207030500d151601d812540c004040504804036031013615524144041c2c4a1103001e401c60800c80c00c0602000c5840303404008542914059070b91181c3c106da0304201002840f5150f02490640505001c1030558920070b400e403502c845154000d250faa0816404a002503007a07010b10240e0f41c030a01e081001c0031550000f03803040d9410100045000d402081055035900c03054 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 981722176 1250 981720926 981720931
    0x280c0e01180e0f01060b0315040b0a06051c0203040f0c1d010612022107080105030a030e0603040f06231f29032a040303020c210f0f1506010207030b 65
    0x6415540c14203000c4a80b0f6095500070b51108800b4003011003800040716043c228030454a40440d01003090744814000700d285040c02c3e115800c180800400d029195032007000d20b48104425103181150780b850701c2c0ca060810307401e81d440c0541d0217030500d1401084c10f1846284042d1103128080700c9041c240c0c40c004c000ca40c4d8038006461f0f507410325001d00c00a400d82103000016181e05c07001d098000c24600d04460010140c200c1640038074440c0c2e205010a00c04250098000c045062050351110341d60398071420091000007941e80c2c014a030f20719015081a954407000e102d100440351542d9032080d1600d451a500000248001001e64030a0320f0900400200d018208c0c040f24480d419071540c604e80901065010070b0390002c6901b04075000180c41030606c80501d824079004a9120301c80b100c1d00b45421510020741e40c51040780503e000d0301698002d0301c1c120655600c09002210590b08031500c62090102c4540c40c0c031250071403814035204007442c281044406076031140c42801c0c10785c0184481490f40e207540000c800003 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 981723426 1250 981722176 981722201
    0x50105120307230d02010605031209060409020307092102010f03150b07170f03040515010b070605092b03050f1302010503070e0a0b0901020c030703020a090e280c0e0118 74
    0x50f481120b41100144802d91032144540c000050040c60442458140700c0d84040d0f07000d6503079040003100c01c26038400b829a400d441e510640140c480d52400e605903401d540a4102c01b1000d12107a10948001c039400b51180c40340d900c02e07a950445401d8400c02a8282e528401c20780c1108294140c0c00c1c8a0250139202401c01d09000b242c8148a0300d02c4c00c041000540c1c000c8104038941d400000400090050420a003180d1140104c1406010762410740004254000c0b00d10043c441500e95020420000c0d0800c0791144d0003801c013040309040d010000e0500119218030000344042401c10300001c0e4a600d821100307500c60a010030b900e01d01e00d2001d5004644035840180810144010317103c0542c242e4803035100304005481461685665038403580006490700d2103800c1034500c0303030380000d800380010307210301440d003040307408181002c600c800c001d10310365041105a816060000500342212013115005244141809025540c6030101c01d40703900201c50900000d00800004018116061320221100d03441050b0b00780c003 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 981724676 1250 981723426 981723473
    0xf120601120e0c0d061404030f0f0809061308130e070e0f0f1c0f030c060621140c04150f2112031119020115061704030306031a0a050105120307 63
    0x1e060060306c0d0008013a00c06500148011020340c006035000108a440703080c943c1400191032400d104110364465000344404c1051182006620401541c0c00c00c1ea250450151030b070715402a11401c00d101044411100140060a04e40c0050640c1c14600304500039800081c1c402c1220207480b0083c0113450940850520844c103960800201288121284590a80c840c1c2c0d07800b45005018108602030301e6441c1c020100b25901c0603ca42805210441300c005a60b034464040f02090040710303001401e2203240841c444d0001c0c10319507000c00d03650042c00601c054400040a949440361190045c200340300092100400c620302c005018408504003900000460180c2d00e03011400400c0120105c50540203040b081a4140d8101800192290203000b405144550080c0d2001c85914044c401008510308180e15402400d40d00c4c082424140b0940140340a9900410110200ea01c440d020648020302220668901483c0400201c1c0f9464483d5104421108c420000c40c20b00030036072a83d6450040100079500d9001 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 981725926 1250 981724676 981724691
    0x170403050307030c02030105240d03050408011103011505090102030406050f09040609020d0b1017091908120108070b030103150b030f0102120c030601230f120601120e0c0d06 76
    0x12810030003000118443d913074600c9000010302c1070609451010b08411004050581c0c1e990502010a0001d071b440041151106540000b908007074519205a4202c8244c95081c040d400c104281d014009604843d1002c04407404021296001c40e261302074a199103005170001c10080100700d225001429001e103840050501e0030001c40c000a045400701e41c0301018440d00400d031a4801d040c64400c460b20040140c440174554601c000d8020300c2c051041c810500450f1012000c1200c0c0c80081100355610201c10306480705070322903410b20004070b8003e1070140700108941800072130360030700c0030a0000898402c800b2140c01c590a583c1e48000c2c0d22040014041c2941d6258040071080ea41080b001144850780400160340d404068014100c407000146603400c10807080061040756640320b003407460325003569031044004a150903100d00340f5108a211030811198081600707069010003141c0b440c0141c5007600c4400203025030300760780703801d50300314003c8041e46421140e1400d80340c3c00c000318000400c0b4414540003d555 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 981727176 1250 981725926 981725933
    0x923070e10120f0b0f040b0306070516061d100209030304030f0807120e0a092c0a0f03050d0b041503080c070f030f0201263c06040614060304170403 65
    0xc0b43c00204200c0d8140e164040c0010b9401c15200b0700345882c1040e00c0a01550600c08040395656001400c03420030030200203881b054170303100718541c0305c0c416500190078846907401c1d8001911301807112100f07014502440000840c04155842181d902c0c460140155050603e552a91005034051000c241c82c0d00300c081080c4000100680ca146210350410f8a030b03506048a400d080c07113504541a001010220f19284100039007060300003101002150710034807508600c3c07403d422507003004015407000b040345180035150001c064200001d46920741c1160420081c00500504100c1520304440c40610604c80301c0c241400407405600083c401109500c045509182e030780e40050852104580c026074007024000050300856034000c3c5090f11031902d10a00f03a60313222000030003010041c00a003050b00d261041c0f4650b081e103075541d82d903549800003010704249071440e5091484d410b40403080b60700512075480d005020904859454000180c1e130300241100d0f0541e559542c03800c00020300c8051082c0311103030502002000 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 981728426 1250 981727176 981727181
    0xa020d020409121e020a0b1302030c180703230615090a032402071a070903120c052b03110c030c030703030b220221010923070e1012 58
    0x20407566946010a040600c41484040442c4c103800702c0854009813101c0001c25402400c0e1a000b5140309160f584410851000034907005a1400c1150840d41d407145440420801002491080220303440c244126429055102252500704a00c0300700000e0031000b00e903c1d03040000390092091310400c0b142d80b424609000003500304210341c0c001c41e80b4614214220791120310301c41c4041c04100728010203500b8020b03942d80303400c00401c0c0807030f0107101000418002411980718020f40c000039500070048001d030301444203000b061521490005c1d80d05105200814030703038041c05450000094500d020341021041501c2048002e8000b0340e942c40346142090051011811040c001410400b00540040da941d4005181c007a06a440812446208115003001003441400481a90041c03030408640107a84810015580e4203000c80898146000320010300041a07041c4186e00c00a040802d41c0030306020890300c032410a980b05012104400001c0e2400c001c00380900300700507030a1000c00682403d41c0c0c020080c1010804 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 981729676 1250 981728426 981728453
    0x180806061804033f2d060918020f010c030516030e0a0b030906091b01050f1b010f0e19020f0d06090c2310050a0c08040305030301030b0c0301080a020d020409 69
    0x19120780c03441207140031204060010b00c1340e001407005011103420045005101d4411481c004032402ea003a140c00a8400141d10240c0905980e00080040d564038003110034103a020b60804a014141c2070311540143d602840201040962507660341d45030100c0c00d91070001d44010754608a00b07204105d99800031903521203141e0703005081c0203207810341c4910305202d40700d1801001030140a4a50065003001a0402320484143c1040c4001c0c20701036640c2c0d00348003c1c4180c500c01c000d01c03050900419400c9480181c01074002e0411706203001e40600c041d180c030449003500ea40340000d07043c02d058070920300c15005080c603032000220018002c0200d051440d140e00c640c4180c40c51038070220362800300c204080c40300c0307070151180b40b82101c4422501c907000c540c200086610b440c5034280090610030041900c0c1c019a208400c0c15405a600c8440d103900d4650343c0c900789a49420078082100c00100c44000109810b043e20b0030b9074101c8071403500810715190141c09028a5090b210000d0760440d0f1581c2003400861020f605824 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 981730926 1250 981729676 981729737
    0x170111040b031e041e0c050607031707021515061c0b03160501080714090a1205010f0504170903030d05070c030906050c120d14010618080606180403 65
    0x40d6a03162640c01c9440146100f00400c805512400a000100c0c1809040c114070215860300d04046000780d0a0000758895258480c50340200001005d8080603405211485060403c0b20032a200d6100d410b41a61240282030b0f1b1141c8003291100091990044010716009000c1d000e00050700e0305070341005402e046610302c082c181285449000c18011401c00f004002507026194881582d800d080c1b60009024282c081c2c0311307004100c122030070380941c0000325040720351100300200960600ca50b00ea2110b100142c540d00252903170b500c0c16017203d410b550180940c03403046500c5103503c0c41401d2818409082c903082104107941601c000d0200401100280c80b41a001342e000e91036100d0301d0203c1c0d1400900c0300300359800c6042081402d000307141c0f1800340003c80011424102000c0e07034a80800a08420007849002d021144081e00c0000005d1210b4001d40700c0001248210b0214003440d40b1080500c1d510001912115000540ca248203000c90003c500c4540d00710344039141050038012840003d64201e40c1d50107500 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 981732176 1250 981730926 981730949
    0x8030108060c190503100806190612050c10090b071a09150a09080f0a0503011a090f010503070c12020c100e150a140d0504021008060a17011104 63
    0x40c01040d40030444076038807001c520141440c0c0390320038203040103400d00d0000841c140480440418520f81d042c00c01c0034003400c01c460842d045444d00c41070344141d60102183c403841d4585002d00210b4111405003500a446410034010720910f6480e4003070200003140c550010040211540c800300e40c80c1110401800183e015900103003542c0c140c081062041c1e0409480000180d01c10030300041a0400820840c0d030004035024000f600c9002400c080c040ca2007503a4041c40114000100c640516810002540c142d070703a80400303601c80e20380e91007428065128551009030305c03189c5da84c5180b0302c03036104000840d80034903d45015800ca001ca43d69415244050035034120268000134100103c60801c81c0c2c00b0043c080361480d11005902c60316001c143e0207048400d80d1317841303181c000510743e14040c01200d158007400da1304201250345000202c42003000300420b40301240700f140088680005544501500d41c0200c00081c40140b00da850b0444c0d00c00c66a42c80b03003011301295210750410007001c031701c01c010b0402085102c060 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 981733426 1250 981732176 981732179
    0x801110d06080a030c020f030a1e0c0e040c091d0f010b01080604020f04170c1905131e1a06070c141206070e011206260d020a08070c030f080301 63
    0x3031a0a0780c031203410180e12980040796403030110342d006000602860301501d025503100c42c0040131a007411400000646101500211003440414408902602134020010007650340d03240d000c408aa0502580c0c00f408180c0004014000101240d00c0614000d41c01d51040c120585920a02400c0c5031901c00540d9403655035150701f01c0030b540c009000c158050f100301e408514098801a00100a025030302800500c50401c0c440c0c00d03854242049503492070000207100c09841040d14100d80c507584060f000b418058840d29480505500e850700600388280c4202d1034401c240210000c0381c0300145580d895070301859440302103030020f0b61580320062030701340e0103107a22686040c109041003081e4401d509040740034602182c405003003804085495504030041d482d001440391407440c0100d030030b0b03a080304140400324030702500000c070680c264418218140050044c2c20b4603100d0300c001103840311491700182c00541c0208608600180c4180d0040c10007030f106100d904c00d01c945a86480e580d1454042007140c0d1414000700 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 981734676 1250 981733426 981733447
    0x41401021e0d06050d21090f060c051203010b0705121201030308060310050a0204080708120a1409030d0306090b03210f04181509050603030405090a180b0a0f091703070504080111 78
    0x4845001e070a1414547d000170300d040d42c0061451968400d110400c80c60103624020824103004a40c2e124003000c074003030307201d503110080500b50b030740b150104540324403540280f8000ca845c480180c80d1b111714a00c003282100d82c44c42d20280e66006e80280308036450700134000e5180090019214072409803402850050300e4a00309802d051400003107410100c0c01d68480504007041111210484180b0005443d1080749011215a9042c45001e0004c09550500403110310b00c00c410b6150b4400000c07244450320038002e00045000703040d06c8007100c610220310b00d14403008a025001c14000140381103200c42100d1440c06959280720071804154100c203150644c1c4541c0a00d0241402d417040360302502c41c21000308254180440001d0303491046100d407070f0050503d0381c00201e49243c40d510505071906410744402c01142140f81a41042c00708682c1900300901c1e180c40146100b01c140700d0304088903070254541d4100340b416642c2524603003009180c041003010820011035904020302034400200b0f020b02c032150310f8010140707 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 981735926 1250 981734676 981734723
    0x90f0d09080a1101020a120c060f02120402101205010305012f12040321091b0f0902072f040609050f0a09050106150503041401021e0d06050d 62
    0xa1540080001042080c0712496000c2000308416500c404002420703500040142d003406000e04000d8401150000d071906900e41014049051038030450080001c032411020040c00c0340240309081d980038150800081c0142403006084000c1030241c00c140e40b4030400b11803c641950b00c00d030412682a5111b034410b80000e01e00d05c1c226114006082070403421041580748602141c0109507607480d00080c800082402c4c140142e8600d01d90440729002840900d5404039070707101514850508560680740e4a800031380040c0d40101001c02c0d01c007160340050303605203041c004501942050805486c011400112165008106d1b4282d4030185034440310f0120310b41070034007000100c4400fa800f01f950181044100031001c8040e8100c2640181040340c00a5200e41d5070034a14010140742d00840d2400b41e8000d8400310700c0f070304030000e988a28442c0e0120b80d031110080440d20700380d0280481c01456003c0b4800000059603007000a49104040c4100000d003495a4000042c280001c0c1203050310071507611420b43d8000d06022 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 981737176 1250 981735926 981735943
    0x160906050a0e07022a1018080d1b1b030b04030305130f030c0f0c06020109061104030f030503090a24050709030b06041a040606030624050405060a02010f05090f 70
    0x4496000a02d40f01d00040e440e00c0714641082220403810042c84074014500c10060a0110040d01d44080c0000b00c00c0c014004000685c207004405030f4213030380003036543d000243c100b0194000342c0d1111108034001c3c488510700707441c3c1d010882d20009110b250008140100c039500c001103014001c0582030707040c01e081c00341c02c503000035110365400c10300740d008440800d00880441c8041c541c14948040e611045080117990205003510090200740c030b40000140c03595054000c0c00c0791500420080200d801e44441c00400f81c45a8400100007010155401020130b001d0f402444d0b000b01000151107200d0780e01d5a0784c0c041080071310082421820164481050801d0512501e0b50003201030912140e403508544903a03604800040010344102d440341d012510b8050040020701e0a100044d205204140c0c0b80c9034084c004d024203000d51940040009019018007501d45460004401c0540720340d03181a0a00d0140190380e8003003115401599210610f88203982610300c1468440c005c6240a400750702c5030a21035a0a05840 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 981738426 1250 981737176 981737189
    0xc0f030f090a060c320f0c2d010c0c0815100b0a0801090b060c0616140f09040c0c0203031803010507140f0918040b071205190b0102160906050a 63
    0x40f80300400175580032000340c2c3c007a03103018070501413140c6188104038985582203c45100c1c05103c0b00640030b524002402003d01c201110030440294001002640343e6000480d0105920034499124074654050100003003041d000d002c0000303c69480303406081c0340624074440005804095070030403044000070b800c1701001d000503070481d614008010ba00103041c100c041c080c20591a60700e14613842c2070354491046030203041d00d030004e81d900c42c07500419150903401006070b00408500701010441050101c02e00f00c40d0b0203070300e029025003010303040c00c1440000d003050808841408100814000581e070200003800c0c2c4000c06440c01c1845082d03000506080d00c502400030360900420105141000202c0800e071a00e0180200d60076403070b5601c1c40000780e03030083c64840080b6010394031003d103c00e001e510300101b8130030100e07a11030400606440c0f010000b00d400c12141c0e0440340d07894946144021500741c000f0a9044030520441d8240d402012040c581d06020364003468506540d80310812a50030140310780d0005246 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 981739676 1250 981738426 981738437
    0x30f150f03101d240f131506030b0c130603020306210a0206220e060f0d1a011205010b090408120c04081c1b030f03020c0f030f090a06 59
    0xa0600100b50380c0c28040380140c814945030424002d0119408900225658141d41107800645145108001080c111030007900900c00400000c1c00c4a040c100c0018020502c0d10084000c0d92950b40f26101c81c00460841440c5031500e4030f000002044d11168020300851015101d036a40b02c6840481140780c406d15070092090500501c1080481d90790000004041a42003030010600a1104000e904160305088020b40c40341c401310382402d580c0e68148801070011801501010000e41341d10313020075490000c464041d44581195124560f60400755400b17940b50b40b00c2c5401280c14910000180b0607204242c002d405a0014018524288030090040140e1410180c81c0c005250400340c49448042c45030080388404150f484000c0386800d070600301100d00038003098090320070003818044a00e44070003c076041040010401d40c501903603003501c05a4902000c1e41a254500d48182101c000d50181d04504030409550003082c01106514400b8030080c20307600741402040341c1e01c0780e42c0e104024403106150130081c20400d = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 981740926 1250 981739676 981739699
    0x3231b030606150306120a050318091807150e0a03030e0a0e1005100c080307050403150b1e03120d0603050f060405030702010e21060a0515010504051e06030f15 70
    0x30041c00c1185d0300a08280c400490400320300c803c07070f464910b00e6500104140f20015816181c25010818034068400c1254020f445482e04881b9131009140300e408041c0d550850789040103540400c42908000445038140714001c010020005094450140e00540c08507440c0301384801d185c81c26595000141100b95480b40e410704080024071003000050144902524a1001c455403140c0180a02d01c00d00354413030075541d41ca28081c0f600a12035001440100d5030044031242114040d40c16029106000c3d201800c802c10340c102c03074140060b408810300c156623050b0080005582c40940c40710001c0c80e255400d030380701085041c0342d440d1251410b41d695440000940085091000144e0048129100d158091a0a032100c282042c0025070312810303201d80d541010110844c003806074001203091486a440400d0800169907602141c403203004050340c40038001501000b0500040c40c10380580b6844024041d0602d0400380440c0115034194015211641110a003008100034405605922a0b4548054a08000c0007 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 981742176 1250 981740926 981740959
    0x30a05190227120726160302011b030c1502041d041202010c1e03060f170601091e0e010204080a140f03040e0711010f021303030e0a08060103231b030606 67
    0x210154050010503540e600c409100034141e2041c0e905c10b140f810710945101050000d82e858410310b592100328042850801e244200d00d02003804a213180d0b40540307421585403010740d5202008505440302500c60707a824030010500c3e2280c1c1d40c800450828214240c09907040c07a0a0205140c01204030500442e070525801c101030702d52003c0b640d0980540740c1070442c0450ba1508056000d0409a0007420a121050100140001d0011152291150500b007940c80d566201c041541c00d40740100c9880319102c0303070f400c00f4051035140b540c0311003c080504400182016114019a0b0174012400407d03039100101c008445402c0800b800f0803007810704040003c1d031811b071400304070a000700c40040055040c48400101030705940420b4010055072840b10408555445107021900c080c0410f501003070b0002000380c9a04c180c0c9003000e42c4198142c0b0003080080149a04c1d41d42e8005413900030459000d0503203111207204245180812000642c2e05011075024540155502414074014000381210700c10000111007a009 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 981743426 1250 981742176 981742183
    0x3060513050a0311031e221a0d091209180608060c071e0804090b060f041703041706070f020606090f06120307140c0a060203030a0519022712 62
    0x1072690504004c0300d041503455201d81035000e5448110120740c10300b0101c61401094000410380403c1405010000103c0c1c08070025010103039029240c200314102605a800180d4900030f09152508004040340000746540d580c00d00c0c00c0040c0c1003402103102c81c482400000c92202495a0100c8012010403070707549840b0b00541e480e40e02070000087d18200040d007005006020307409404040d080c003c40c825864551400c0585988103100f28591586803030841c0f200da00d03001c0100c40c0072501d151101410b00f03007031800b4481c41940d0001a003103140b00420000401008200701001501010f001510071440c1c807900c00303010100c43d200c0c00707411500840e04014840d9a503184440d000413003280200c4c000d03940c840c041440c40c0511000350b01144008200c40f001c020050102e0107000400300181d920404c4607006200000742c8034011000940c2040c400115440b040c2e0348413a0f4007101024184407004170300c040e03400c2203034491800d031800c0b180305111025008200c50603400010806480b5080380c00301d00a02d0a44 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 981744676 1250 981743426 981743443
    0x303090b03100317190c0308150d080a0e09010909021e01120b0109180204080705060301032d0c06030e06062d04090c060c050c0a0312270605040306051305 68
    0x710300e49800041407180b0715045e0344140046040403804610380e071034060013a66081d0707030440026854100060140c041d84034065280e11029082d0520b44645555a200b1904850914410400003000b400641c0d40c44042c140e0017081030100c0095002c2241c0180002502030100000c452801e8158000140c4d92205610202c40350450000136000d10100040f1040456688102ea60349606c518080790840d0030340c0113200301c4020320220744020380e0702c90900140d40024400074201125107662810f040c00002e1a1150701c80c011040d81c0e25410442d0b0740c24850a1254100c0700000b5170b1220b612119840070401150418811103120882000120038407080f6400c00d030026800700248031205120351241d03040740a0140c1d1040f400380655442d190004d00ca228584025112449050070030903641c00c0100d0090252600885400e10307600751140f082c1c80c40c8400c40c0080e640d4602440d850510600d403135010b440680380b10340d50f555483c0e1950030404159407000d0020001e840c0544901c0d00001e400040e00355 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 981745926 1250 981744676 981744683
    0xb0a0f02030a09051c02030d05090301150b1204050a0f0803070e0a050f010c020102010b090a1e0c051602010216090501080c03150708190e07091805060403080a110c070303090b031003 80
    0x14171001c042c645a0940405000c009404d840386804416016401201900113020b0031340007000f01d500e941100c030700404603510a08041c042c080041c451040302020140e030b4007900078011070361101c45503034a411401a0388070050382c482801000f0f1190301c541c00288114004000c954000700e15050100043e291174070142031905204c40703400c40208590003074100501200c0001e09a947c107181030301c00e5001401d010b08064001c02c0040d8445482045507125082a0f110a0390f18142013844640c0f13980e5042114103020b90541c4180030880d085202020580e402030000c0d40c0340450903501d0008424540f0009503041e84c400d4100c00d2612982d9442110b005500900c14034001a40b91603150030a0821005408101c1d0451300f400000300d006070000a0b82e20442d642c4880804c16007102c4145040c8502044a000301607400001c0441c003c00d20032419280c12642c0060001039000e410444059a98801c141c9002d4603046030030304005240e00403107820010039682e20303401e145140200414088450600004 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 981747176 1250 981745926 981745939
    0x3011505041d10020403110d03050904050402130203090703060b0d0f08030711070b03100f080c4609090c12080915090405150303310b0a0f02030a0905 66
    0x2280c0d280d0414180716114020b44291459100021240e8010358400e00040d544184a201c3c034a915003410b51f03109440682580e078840c1082c101c8070420010f01400345c02641d00c990311210700c0b5404036a91008601580040008029462545c90902c054507440c44031544105541c0c8020800b048001801d004000d80c015103182d601d66134034205540a20401148103007034803641c1e80104030b8854450045010340e400300c0c003810b0003035914a0011a101418012454141c106005400030750a000740030000703680c070402c1d80480d8520300b040140388180c0340c03240e80140b0000c040c1c924110181d184000002415140c9814003644405843c0c24924998601ca074503030035011b0b4202d0905004420050741d01340040280242940c40d5030140300307401d6400c0042d00b1f80c825403902c00440c4451900c20b4000051820242c051410003203170720460080400004054882900c600419100172400c40c4094005409150004d5444806a11000304441c007081c0100c403d5620820030310b0101394000d0001801c450044a04 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 981748426 1250 981747176 981747191
    0x603090a110316080d020f0106061e0c0209100326160c050423100303020d1d040f0507271202181006170c0a11031b010510050301150504 60
    0x4030f4a0042e4800d0a84554081d04002181e09a0042248400f000f516400c640403049010b40e411300f01c9007580305040105902a01b64024541f0b11202620540c0300c03401c000a1040381354020440c4000304842d44035107050303210024010072103030140c0c4103607800009800302450590303100c1014491207440c100c40c0b01038050310403001c03c0180c5d5254510150201030001d00440a204a180e08250b004007224000c1100036000180c407801d000014500702d0382c15500500c1c0c64503040500340e40780360009503001c143c5080c0c00f000303425985450040d02c560b03001443d0300085030315022400409400b40440b600400140040e8480c0e21110a00c40000564403610090740c6c1e129080c0c400a0f14903080c0c10141d039003119040b004c01100b0320000030101c0444082e5222105400782d070602c1d640040c481102c107004124000e002241c0003600c41c81c0078a203d810303044d045a29015004407500414171b8001140340c9140e464004000b065000d102e141802018140d000380b200c81010a04601c0b402c4407405418060b07070f5285403 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 981749676 1250 981748426 981748429
    0x813061e0207120209270309010306062615031504061104181112040f0201020601060c03051204081b2407050d1a19030b0f0603070612061508150603090a11 68
    0x406d40b103000000b00c05640d41c02c1017501c6180c1ca9400c8007088c41e000c0ba10b07002002031440c0c0900d030010040741e030701124111040404185030301c0a10014020012424400312965001c0d201040710040001d402100c200c90341c501458450151090070103c0c0c40082c00c02c4c0700401c86024900d44043e0442e041c00c02c049007242980b10481124010426000b156000000c1844140403ca0b04491600350003a802e5a195a0b04c400d8261903e0b90362400040004100300201d0114452210b00c00380c00a10034951a0300d0121540007450350300a0070b04c0f0042498200103081c49000003c40e119a40d14100c1090708030042c6400c546c09043d900986c2e51a8642a40350b424040b8249810f01442c808120f0007885030000c1068800450b4010100740000c0f905402c4010220f400380c0086200c151080d42d00a00800985080002c1190504640c01d40003408035112400070801c603080c00c0c00c1d03505881d183d984003070540c500381803a9040039007045561030049c0010024082c000c4e20204040c80d82d690040301c183ca000c20000b0 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 981750926 1250 981749676 981749701
    0xc060c10180f1202010917120105030d0c02040504051033030c0603050a09020402030a0e160e04080c100501141e01090504020714070b090901090c0c020d0813061e0207120209 76
    0x442c020551187c400c0c81100202100028000d0600f915182c52074a0380c0750018140d40e85101c140b0710001c140454445001803526421041c3c0c468070900568100840125641e02030ba4141c0e00c1d802c40612808040d21a408101400b111085072011044445241366442d0000c08501074000c40c405c240d16100014200103031900045440c69001c2c00441d60b078601130b0f07003010003007840b180420110f0242c2c10000201400202c2814240c0b508900c08074078580310343c0d950b80426070010302281c1041c020505c1c0006202450b1003203500802804120500b61103100e000c0142c04040d000e200d4036190f003190f41c0007a690364400c6844095845c161001640c60781e5904140c4854540381880900510074028003060080303410002c2d02035410203070780315031160340c80e09400002d40ea41d0f41d5410380003c038030568180241c60300448000402d8040c4420314070300110390340c0c80050082207411070000b003400c980f20300b900c41c00e085a49120911180c4050b101003070502c4511030f410803124001a00c901001c1c0d0100c1c81140006 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 981752176 1250 981750926 981750941
    0x702070e18010914010b0415080c0f0114040609050a0b1306030c030605031b0111030c1908040503010c080106020d09080a020d050309031b150c1903020c060c10180f120201 75
    0xa07466460b801c61341500756002c2c1c0080c5091074000d9040041103102840c003031030701006403208880680f50084002007070280d0080c07000051410080c07108151410844982e0090000c0c29445d40c0300f00400e0b040c0414400c01100300e62102d400e003d402c20488180e092000a0320301a220746180108103c4a840b0307049001d00019000b00e17a160140c205204003051b001e0800400180c02038961036504101c110030107840b03010b01415403142d500200b444071281e80d81030020703101c20381c4200070441c01c040c0c0341e80c00b01e07085901b001a40004035240c00b00501c040380d0100100155582a4035061401c0303030524075441c0e10390540c510004d00071a42807004000300a0f0a00c00d0f908001c20190880c5e510142d00041d4000e00510000124056041041c0d000901c01046013120047ca1004000703015846c405010013100141e9910194210700508040010550742c5100600301038200200410a0741c2242c05180f0071501c01400c89030703030050b180310980b00007175106000e800400c0d0041036201200c600c4420603409408003 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 981753426 1250 981752176 981752183
    0x100f0f05030d0c1509020f28060915050d0609020403050102030417090a26060c0a0908030304020108270601081005010906060c02060a14042c15041e0f020c060702070e180109 76
    0x610580c8c21900130848201091b0192098400c0105548550a40d100341250198462034008914901c1e0349501901c01400c0c0e01140d081c000690954404109049030415041260941d4002003030006004603003034401658680700108900d088105000514074211a2003114510980d1801181507802c041c0f07014000150b4200c04d9480300c0c07504070b004400d550700c4940d1003400f19440301c50120f0560740000c1903a10859044e1a034030034986030358030850300540504e000a004800103030300000c2c0c3d0b031409100c0c0c28000c15512000340344030031010180c0001c0c0c1d101600301b402e15031700d0b1036002c002d01035010510051594064540c690b881c0302c04141180e8401c8030f1404051590300004000500b41905c0808101c48880030304c50303c21602032043c002da00b028043d2020001ca05104480407101d117400e5210451403c04403440d00f00c1509405c506a06698100c0b0024107840d90209a10301600810322441d50701170940e1000c2c00501b41000b050300001240640100c46c1d4002400f40380403044000d600ca0b0704090341 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 981754676 1250 981753426 981753439
    0xf030a02150c070b15040209030a150e01020310090b21030714031e09041503140d1e081003050a050610092003100f0f05030d0c1509020f 60
    0x6429a02035035440c09441078a51040500d0002410060514152002c0980c0041100702c5900d0384507804200c2080c084c2540d50183e07080000d800c3e19a420003800003801e22400800440c4001891001d0407a010411070350440c2c0d00420812601000d803545107802e583c8100e000242c4401060003040a25064a003080c4200c8414000302d50702500000c0500394081c4156401d114a803014803186480c0c0c0500c41040c04d00d130103564592050042c000b8043c01150320081e0001800010141c10042501050f03801580c40c03d00403a05180309070300510030010850458144140c041000e599112040da82e82c00710507040202e0304001c540b03480c0001844030011500201228000343d05420b10175121801501c01405251044d0760018665101d03003d01154101a104054091b0b400a1042500c0da400101a41c018031589140403608018031908000940754980040c1c0e8040c0c189400c4c989004010041c01c400c0c01200342c600e10008108504060003072850b00da0102e250000c82c800b08003410010404154481f0 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 981755926 1250 981754676 981754687
    0x80316030320033103082806051804080a030b0402070f03021e0705011202030408130f06020d02120306040b0102010b090a09111f14040f35060114030f03 67
    0x482d04000d1806050f90407091080200c0030340000411200346900c008800c507100f40040d011034010a582980403075042000c2d15041e040101c00c2030b078512455800c00038290f440c9824040c17400e1000695030000d403032003c0d01842c0e06094071061003500a9240c603500f0151074001c02e088a4031680c0568a1043d44140b07000442d00043c50065140c19030021441c040f10081c82d8101c0c00340000166880c101c5106071507290759140e51004d00700c06580005c0003a290014200f099120710700c0384038030002c000d025840944010600300752000303040100b40382e0700000310b501c242d4034021000b9603041100d40000781101e00054008800005030b016040c044003060348480c0a00030000035006542000c40190301c40c425400c10100650100b00104c405081c189a04d1842680c010ba541d5024403030a01c08442d0501d0105e0411b0b0b0707550450460480c2c5904413041594030314984803c44003400c2045040c40b07036101190304555010030401c079a50481441509a00e032a00212100e44d520203021844100e0714000c04c0e25640c8 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 981757176 1250 981755926 981755981
    0xe1005120103030c020f090c09060f040807030c06170f1303020f06190c0516020d0c030b090a1401050613050705070204061e0e090a1b181506090803160303 68
    0x154113014099000c0d840f00c81e0070500313a24080300024454403c001406081010034400d01c0329075009a00150b115140402c004601c0140c104070000041d0722605050090504140d00113284141d501401611101c484080c0400800303110419a071100360810800500801418100e02d08101044250800d0040d2000c0c00310807030780d90000401d51603890f20300340140c0b103456a084809101d11200c41d1107400c0013040c11701c01450b00403090448940103508050707000780c0301e03201d640322204140e4a021256000111032000c00104170715504c00d40340050001c0080345000c00104519009159041c46010b69881c005036003240500b0035222019005030080080d183c4620610385107001781200b91304a9a00000001103820000201611078415080540704a0a150b50b9102c0400b500c44040282d0303101003d80440d908811481e5600f0000034501701003680494104400c0c0f0100003074201c1000c02002a01c00e02c69110000100c0f90042104101c0f8500695070741400c400800082d000340d19801010340c40001c41 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 981758426 1250 981757176 981757187
    0x907051c0c090f0303170c13060203070b060d0b04032a05150a02030c0412080403141e1908030c041208301504090c06020a0309150e100512010303 64
    0x5440c0151201c685081d19120000b00341246440010002804032003031440d2a40c90301b40094010b514080c0050800345131401e4001201c000303030420b000580c40803e110090000c040d4009402100540b41440c0881141d1076034944808004c00c0a02485040701c1c10b0b81401c942d620360100d4145850705001c009600342c2ca0300e076482c0e015805d01d0040019001c0301282024080d032003224000c2c1d030b48605042c03a06143c105200c40c0c3c41c40d01c03041036403891801c0c40000080b40c07450031003540030244407025210351a1401441e101c185002e50a5514952110780720a48a440036584c901c1c055400041c00c64480d43c50240400640c13140f40c000412041070300301c081d410010f03108041c0c010840203010118420f1801416112004103a6103811144000040071514041d0252992090304c0c6010f880814031002c6600c550030303164001d80c00b103070040c0d00485607103040c1640581d2600181400c40046030044a003640014000314100c2e10061003188241c3d125030030a4003410071114030f8508039100d984550307500d00f0050b20 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 981759676 1250 981758426 981758441
    0x50c07090515090f01050a0302270c040806100302060a18080a03030203040c080610030f0218181b060a030507050c0d02150a020705100c05130b1b03030103050c0907051c 74
    0x1030507880004ca0040d110f2850010f0503594080c0012144502d50740070484004c0c0145140400e8001d1000380301e805020508445105203d2100e540e41c0c0c4030b240884031403401c88000c210441072100d041e02800140c2c0d0301022201c403600d40d40f411004d048801c0e481d9008603441c80c1d20580b06446a448440101500f503006144102c1c01402840c904d076558a07071090701d5103411500c4900454403140c0500c0045e61501c1d00c501a0350001c0d00401d080d40501040320b41d2458107840900e4511043d4001c2c20440000f00500800d0241283c00d8804400c241c8020800d0303402600d050b842490f4846001502443c440c0b0151800302c4848012101d220821150280d00c503050104282000310744003000450315102402240c203440d0380000141000c40d030400c607020060038500c5c4840b00300401000b002044044000f181e1000d0500490341d00c3e41c6100300d0044506024520503840c003103410520040001c9600840c4100c48601c1c1503c18001c2030792035142c11075407441081c4110031604410080c0c0d02c1c8040180e0310011 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 981760926 1250 981759676 981759679
    0x82e1a040e040f02120f060112060f05100f0f21060207080307050a18050315100902040e060406060c0206070b040314030703150501021c1101020c030301080a11040507050901050c07090515 82
    0x100034032217501e5079501e448181016071200c2d07011a00410000390899500709455000d140c0c00201c016281c19003005661050f140100c02030700c100014018442c020440c00018105400065032a0303260180c081c0744c030b403000d4103841d505031340c1d0100780030078080c403a0112100c0d01e03408a0300540d2403921034405001c3c1e401140e80343c0e000a41000c8900151124141d070703003082d91001401003044215105c855480d40500510074044e00c0c1e01035100084443d0940007900c050704d2044100c41039490b02900388400c03120168004020014803400d400091789505048844480c3c000702c06810f0755449040c151402e1400040150030750500004000542d54103502454041005c000d81250ac65074603c012680ea283c4c54119950300206a82540c030098002c070b80d83d4022000450000d41010040c0b5403903411500242d002c140981c21402c0d841d0304011111003005419002104c1c100300c642083c0c1f00050050003400c81850600c54000380c2011910003c0003903100504000c40203101610303010001c00d4100801a0700e05 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 981762176 1250 981760926 981760939
    0x11803030e0a271d0a0c090b040606050d0b04140106020d110d0c02060a0c0803010f030302061b0415090816061101020a0203040b1c0c02030c0c0108040b0c210106082e1a040e040f02 79
    0x403243c5440c1c06541c003141d58523580e4604001c0c00c03441c490018803b034040b00d5030046e0351700002000f290285008500030a00da8024200c0003c3d0004042c0c081820b118003030245400c907c1c02188c005800c81141c420300d0750117842543c0c54030a40c440a40d261460444003401040011000141e4101c0e001e030b0600c1039910a50a542c074a0312004d44007111014100c8854441007002e00c07003400001b51401d00421060b8581c03070700303040d010349c0c1d50303480d60800001002c014403000001605100c0260080440c0c1035104656000b1407400e20042070003902c90145000c0c0c600c0310903000445074807100c1c518070100303c409a8042c0401c00a031192a001e50b0340c2c1d1000745140554012520b8040b019800741c1c00e60b51003607800c40003041e10382c0d80350315208040b58485400307c0420f012210340750007000303400341c195070192100d40c968826905002c01c03000ca40032480e4103440341c1c08420018030300c0c5813900c2100341021540c0c88241c00140107007100c0440c20750300540d08038000144225041005201c1d03561039034580b4a000781c404 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 981763426 1250 981762176 981762191
    0x1b0824031504150510090b06090f091b160204140c04090f2301060207060302040b070f0503070515040215040b12060301060510050d06080105012102011803030e0a271d0a0c09 76
    0xd1080f2400384040207135004980312b14003401410041d00f007540c40000b202c9401492200c40503440c2d2203400440c120000440c0bd80c0d250421405c0511440b0305181a60080040e5483c250382981001c0c8074601400c010390b52a4003004248045581101d152020100c0c500d80d005000c4031006075441700c0074440d420041c800e50000051250081c4219025a0031250301c0f02e1a100884d15020f425007102181256284020042080428410b012501d6200c00311101401c0c1814540100500080803c505000d5140f0810080011114142c200e0701d48001c6022200301980e5008002401006160302558100b000c0c203c000a0791580003009250351020000308206070380d11940b040d801c842007401040302c009002d00a803500241860441a080c81c8145442011107841998594120981d580121301183c2e040ca0200c0c02841c0600460700903103078a501e5000f489043c1d4181030000c147c1c00b082c608140366200445201c0d01c0c0007800301d500410009048a081160300d00e0b0090f0016200d224124003586401e19 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 981764676 1250 981763426 981763429
    0xf1509050a1118040e151810050f181e0106050406120f03080a18140f0a200d0b0c090a06020307050318041b0824031504150510090b 58
    0x151000160741c402000100400c002c04d00004001c1c103200c8450300c1c860003400c1031071040148542c61084c00f21002d0b000803070440811007841c142d60030960b0501c650400c400c022013200704000c5640d10040c0000519044405000d0240c01d04104000410460b0240e4925651008054020a040b50411350b000c004e00d0303a8866100b04002c4a0304c1c030003040b6040000000c0042071140320301e150403e196000000710714405c10b140001101c0d00420443d618144c2c1c0c552450200d070300b4071180c2d404500c0c40d40503000c400750960f00e4842120040b440141103101d1461203010a8865800c007035481c5512040d000c0c9142800c00038014140c2004062505c103092091001c074480d40302100380e03180c0c10352020055061659403041605040c02c1001155007007a0348014240b5082c0d1201c10380140b440e5180ca035450703281032041450b02c405164868600035907480300c0782d10303049450001d6228000303800f4015a40c10f03a182c0f40741c0030302da00c6508546600898144000d2000c0700c049150b0750011540284020020340301c0c2c150 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 981765926 1250 981764676 981764711
    0xc051008040f0b10180917090d0605090f010624021f0b0d0f06050711070b07020d052103100e0106020a061109030106180e01020f030a0f1509050a 64
    0x1c41c001d002c2c0704040c181e0000540070080300340e0840c101c02901d1400c1520b8142da44800b00b042913a40146a494141c0c3e0070620840810007048100010181031402590802050064615201c001d1079140c0e02c40000d82c003100d051080903011101c240003400b4250ba10303040c1048800756100d00b513030b100c1c900700c401d01856400005c0d0341c0744e0202e840030f8a06603030b5801d00342c40008024413240d59030080407081d8040c00050301d101146d850607200d5000000d00c0d0800f11801850a02d0801c4400300c0b55200490510841c544041620f990950440d0741034405255450700c2d0b0b0810203048081c01d2181c1c82c000a0390b4440c4022030155104504c3ca1401701e0101d40d40300c0700320360000701c20b10862015801280c4c03424041000e903003021001c3d9110081007071825001c4c80109003111159400b2450164034282c107410050414002e20756407010040c000e6080c134002e1001340c601ca200140882d01441c0d6100492100b089441c0c1000c420001c586001c02a080c1d910921a80609800c9513066462451301d03040d09485400790 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 981767176 1250 981765926 981765931
    0x150f0503070503010519270503130f230406082406180619080d0504170102071101180819030f09080316080c010606050c152418040c051008 61
    0x144003d01c00c022101b0b04c100400c1d1001e905042d808001100b07a80000302e00306c00380c1000f0300c582c00540d0340e6240200b11004420868014a02e9008503035401c001c01e5201c02400f1000440301c851003510650200006401080f00384d00030500da000c1c0300d86001c243e460203403080c9512034000c02d00d070415540714803c00218400541920903410000c0010503c1418141382c071800300c100700d81d1511100307038643c01c680d8034001028003c0130000c0d4001400b070010900640301005c10328030f07480007035042c0003044d80c0c0c054410421600c464100000e50486c83c0303541441100c1d1800510a800a6441c0e1425410b1071500d104804001074011a0000b1004808a03228406801c11030300128040e509024880d4500080d030103544009969250007400f84802c80d02083c4a1b020041c069510341a980b203d04060060610420180039400719010404220f602c542600546090300700070000042100005d200040d0480340104101d008440740070700301700070000600420001d9541c00c9a075010020b44444041302c0660b0704 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 981768426 1250 981767176 981767191
    0x3031202070b0406050901021c060609170c060c03040b0a0930120c020a17061f06053006090a1109060705070305030c01020d050f040305120406150f05030705030105 72
    0xb400c001000326803545c4c0300a8214250030000361401c0d48020720803a1904005a601d41429596942041515040520000140794001900c50060310018485460b0320407010101e00a13203001030340b403007a01d10500880300a403000340b68050b12958040d40003803020f0010302035010300d007202c2106140c0100e071030050301010000045401565086568500768140b0005004800703000381e40c03a0b03c60050b503031941400044d10041c0c420b106140c010441d42c6145c6200901140500b4000b2813408000100380c0da01102918928180f440d6203203018980034a51001d07451402c607e2299500c42080e0711600c544900740270300c604466106003074071000200c1080307554041062000c00b02c2004150403c1c00d10788050900c150003101640c43d5260b0f130340c0350390303003950310036614002640d50002d41441030000d03511400341c00070039450010f0101c0c0b40a95001d0310070721500420446011400d8005000c00000da000303201c0c01d2600141c0d40301e0050303035064510078404c04c40c01514030902a5020120b4542814814144121072 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 981769676 1250 981768426 981768443
    0x103110421020f030703151a03120903070f06050306030f07050d06110c070e040c0608160c061d03090a08010209010e09090c150304030f09181113030803010303120207 73
    0x840ca540c86042520200c2243c101c1c20626642080e607505004c101d0003103010750b100800c4010b00710312a01c2240c00c0b05000b203102d0f12041200401a8400141418000a0400056035a2500d00000030318041c050ba00ca0110403152503008a941c0c2d41c030801030340c01080160202d80207449450004d86e1103481a01074150441c0810005c0004108690405911665081002441c01c00c9850406081c81c0e00c40e0040300254003c5010702c4100a2441005d40080003540b400d8004c5082c0740c040c841804400540160410252808038801d02619a00441d485c40383c520000d1042a0103442d01c0d42c8a40013440003922800402d480020300701c0042c002c4900140d0165210002120010304000301d2042c00340070b0700e0301482000c9205240d5210080c075807891404000c0440d840e0b2601d89401807422640545242c00c0003018801041881314080c44d0311030b4956200c40100d40800720041e07858490282544041c5503c21a201c00002c0c408804000c6068900980c2c6454040000c01800da040e40300304000242a881c = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 981770926 1250 981769676 981769709
    0x21e030a061a04112a060f0402011404030b191d07060f0504150f021f051909171608040e0103171c0902010e040f060f090b0306061e03060a0b01031104 66
    0x42d03103400480d60803001d00143e40e4050300c9170300c20f20740382c10011100112034884800903c000d5603000055940c00c15a03098455140505590750001c0480300a40300200d20403022003400c0000c3c803641c20441c1807540520f0700c010440da0744490160b80740503038450360000c100d1040040c00c85601c120115002c2c0c80b07400c804404090500c0c0c4007140d203003c05460100460151440e0381d0090300040d081910249201003001c0f4407410820303100900d030031000700c40710391361031038940010002a1090707500e185032080131817400e8440703007140d00159040240d188002d20744600003d01103440c10811500c00d050740c0c010090456601c060580f680750760b00c1209040b0528001c0100071000314400c1d50459040d42e441850602e0b40c0162210104040d5000c00086581d2141c50301c400384000c086000c0c19000401188005000400c0c002001c01d448060161070340b80a084002022141307460040e204030103050000c4c04036951490100c5a2900030511a001140004d013003104909110001c40141c40940c0c00d41c005095044 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 981772176 1250 981770926 981770947
    0xd0918062402031c0504030f030911090a060b12090706030c02120a031503031d01020d0c08030402040209030d09080607090e010b1315020c041116021e030a061a0411 72
    0x1008850784038118481000307442d2401c13407400f9032074003a001c0200001c50075007024600500381005407a0b08034109468284800007040c1c0310f415110b03490509a03144400780e00c64180c42c101800c2242c110480d221000070b04242c41030a0b0020704c910440000701925101c985075402101a204c40c1c00314080140d101d0700c0900c060191140017807000301d0303090030005854510b400074030b0180301680e170050f40414903200080a0100126107511210b40c403d2000c0c004a40210300301401011011b100074200d01000b000140841d15290304884010400808843c40c54814044c010084180da001d0003440b80a0280460000c81c041d0903c01c0681342c4d01300c4c070404580e08000c000d4081e50030020300050b120f5000540010780c6444655014024041903014140200c804804e0000369112036500041c0310a04000d0105415402164900034942c122441603400400c02012480303544501c040507454010020300704100001907000c0806d002d0750b03a4000440c0e500340b4007080215201d001204130b041d03008100713003400c6 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 981773426 1250 981772176 981772229
    0xa0b0403020f100504050d080a030c0e130b0307031e120f0e060309010b280506091e03030f1c060e070e0103180506010e0109050c16060f0e0d091806 65
    0x400c141d04d4040d04040d0741c1c00c00207a1042d401c200c2651a4400010707958290341d80b501580314650841c2c10032a08190260001c42c0443d09042c50396820555030391030200c0f040e0b0341886890000c1d504440d401e440c0380254a407a112900a155044403e004428802103840c1d0094007007110b941c0d659180c00e42e80b03442503014080341d9800102070070b243c1c0d543c560500d050341e9920740c0c000d8290110b01c4a8401065039070040621020003e4101c98415601401104150341c1c41315201705030505d94800c082c085001980c080f9145008610822403015408201c0a062008001600700351402109003400000d5440e00420030b20442a03900400251030070f03901c100154029080303542c1e00c810314685401000b52640b52941410b800fa0040c0c004006240c004005001503400398907000464012140d00c0d04a03101b508440701c00f2400e00c02401c5584400781c4000c0c1d13421035849281415103280645070441c0801e18004c1c0b05c2180e6020394070b558085800c944143c0d000301c0c4070b41829540c00c03101c401c46110184030900c08 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 981774676 1250 981773426 981773449
    0x6100801140d171b10090b0402060d060e04060c0207060305010b120919141b0d120504050d11090f1005061e0a0c21050318010b120a020a0b0403020f 65
    0x8525603003c407018110305a50300103101c2c20001101e0000d075080030110060412840d070300c00020702c5013021603842c0441d01005600340c01c43d90458030a66151200c0825901608569119040c03525110040006024035500007015200c425820b49422503107403042501218028003c419007040f041c0201425024201c3c60290040c020340c04482c09400e004202c0c004000d240380007290009110f20200c041c03140100300700c14802e01303210004215400f203030002c1030003c44d0494010340407540850380703008118029411a0050030001d0901c160105860600c58030083e503032100617000700440400166813140c0c0a120a010f010700400340d035401b501c0c0c01d0800020b0740010704140c100c41414102c0040000302c500c0200100c1d44280c40ba0307124150700e800c0a080e2449000440707070110920358007281c00f007940903084983c81900c9086000c041c0034002d130b4141c0100b580c1c8c0701c1c05401c1022440c5401c0ca1400020348680514800c407400c03da6a134a40c41d081d4020b001700c2c40000d401031101c0314205243c6c504054a00c9 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 981775926 1250 981774676 981774683
    0xe0103200903010608010c050a05031f06031b0806010f05070503040b0409150b090607031115010b030105030c040b0d0231020d0c050c120318060c0306100801140d 71
    0x18099000d64250000c080ca429110040d1003002580101600b020f010b040000c1001c44020018907582980181c914440e8032007402c00c1181c0000000c3c56200d070304030a050120b01e05c402c0b40701156210f02c009401080705400e0400044030307000303040c2a030034850380006200b14010780d241c010358116440c050b25140c01524080700d480c0424400800c4540c0c0d0000900001d2403040c20104511510001c100c116601c250001656000b0410040c07500e0703110b16084400f02585803400c40d852450403041e05041c911540c054600741d101da6400040c441d05048040c60585208070306460740200b1107404c0008495101400503004049100c0e00070142c1b074100a1032440c291800000742c0c0740c0c030461541d241410f48101d80090b60a5020a04003406402440381c21480c003420308000386000c68a0084a80d1600c0b64603401070704200000004407550910401280c0c400030700c07412074009041c07061703004000b50030817251300d0302613030003040d005080310710503030045040b24488015903034406128030134000d0801340c141d8240d = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 981777176 1250 981775926 981775931
    0x2010e13061725031e08070501020c0106050f180103111207030515060402251e2003010627060506040b03060a0512150402130c020601060210110306010e0103 69
    0x1402a0700c1c1070b260000b003a02e02d000b0703010050700c19001d00e4070050483c0b80c0c403004000308102480080e92080181030314080c02c03810000140300314a04000548110300b4020581d500100d5400365004054002c20f003550700880790300e1400705c6e5680c2030200b0720b9100c0c049815120ba0000c0100007040003c6101818280c002c2d01c0071400f40e14442c202440c03d10503074000c45280c0d201079041c6944801c3c114881d0f402c0802141d00b5480d120382c41d01900300038511b021004079401c8100c0d8680f820048034070441d403941308000c60038031042219800c0c1403aa200b814065459030402e0a00408039034a0f062041d030003500d007004039481d0790818120070000380e83c22066000008507596800442e2a60f2284060f0001300203405200c1d90340d141903424000050001e903c45270080c0740071500326440300f202280102400506c01091401a81c460001a901140c204810910985008885051641d011410b1810f039015a004ca0740203044940030714040311100d590440401070244040758056204451b0048020b10500d0301 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 981778426 1250 981777176 981777179
    0x20a020105130503060708010801150b12060f2701080102030f01120311031201180902091605090d0c15050903150604090501061401140c03031f0e09030d051302010e1306 74
    0x1085c500182912480c000c01e40301b500401100f5001d00a40315000c0100c0ea11311701241c5441010340c0d060041c0040041006014000551a40c841043c03410503900d0040038034120159098005180d030300d034005280c8006100c7c5001198480050080741d00683c2d02211641c41c0d6803814090b10010507244504901b0041211183d4401000402c094000c1001e8000e0417105545409000010117a04440c00100d40d0b00344a0a0800f40e6100c0c941c1640c0034100c100c41510091040c4401c81d80d0784100042d0f0f07903000d50300780540381c1805404004101a19110030340000101100c0c0b80940b90381c0103020885d03605500c801e5103000712420a00010743c101901400c08250f515103907036800d083d1055504107031180d4540310000c02ca10342c2d119040d14110000842c40340e1600b20713142600c2d070b201d110060108070841d020b056100140090300100d10005d000e010041186414020b440584aa0004110100c1c80341401c020690003e5601500307141154140c481001c01e507600824082480010390084c0005561180e0 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 981779676 1250 981778426 981778429
    0x2040515090a030b0c1b010c03050f041a06030c0d21050c03070f030c0b131104021c090c03020612010321050d0506120f0a20310237020a0201051305 65
    0xc070030280c3d4000c000411890300d41040241114401001220b0115441e000e01c404900403c241070500d40300100e00d20700c00ced0707035110200c0e1401d003000c41c0075500880004400e01c240000c00980080c501a0b04200220000a07035004455a000d08024000c0b9034108010090000383c0b41c0704103c9001e0310a062007603020b2440c2d15588030f9014100d540d0b0485a003000c0c80031040101c1e0040800e0560b0b011501141061002060307604611404e183c0c0140c2159a00415070034011444400002154010052580c542c0034207d54061103074280f0085401c1521218411001c0d8408407035002e443d45155070302800d20f81b219619a000d024050200f80c0c01c46000da070301d40411081030142e1216116001c0c02403035120441e141403030440121600242110390101d421080c2035032400c0d40400c1c403081501042c00c64440501076a81c00c00d544c408544191032002074070412864121240e030000c0c07071401007491240ea0a116990080440340d90001005030880380c198030040d8010009001041440c21003404c1c0395441c2d40 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 981780926 1250 981779676 981779707
    0x50706030e07260d0203160320060412030b010309020d020d062a020c0f090c030a1b0c060b0904050c04020f25020307150f1d09010902040515090a030b0c 67
    0x8590f8030003c1c1c048040c0e50008006140b00000d0900c000c51900e400c3c404449400071a00400400f0418814080380280010030322608001074081e06444440c10645407108200400c1c400075008030b81421100d02c0c40790b00904c99080e445030040c000004281003542000241e8101c5841140c4650f9136030143c4a00d10700b1b60241510403008406518100c8006180c0a454001185002446207407110310b40c620589820058581100c0122820b940300d455040c8000701401e2074060420000554140101015501c1010001010300401003082003088003000d01075a41822100a40a0340c03060083c070186041c2039004052444804045a043c003450641703800044440100c1d45580b50340d4042c0d0350003949800d126800040140c1d00402110101450700039003403d11802802d010b03c0701c2408100044018040710b11800840100420441c1d81c40d610060000d4100e07020795800b9542c0301c028100b002c1e20b2041241d640b504000c0901a50b03501c0e55960307120104000b4a050300b041e009024580c01ea50114 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 981782176 1250 981780926 981780959
    0x1b07080321010b04060507031403040605071407030806011803021810080d090e0601030f05181006050f12010204080a0b090105060609060702040b03120430050706030e07 74
    0x45015555070000003030400111009040030344803519100004000d103d01c0b0030101d8084540b90b042094541e013490034151103d02c1a071204015034075000040008000451348140d200d003181e074480042102003201031004c80d00640400901150003100802e00944c090041705010040004a2541141c1c032940810b449042000f20440c8003040a818480e03449481d000d10809442403000424940e0782c080002000720380c007880740583c2d003c01c40012030707456446600184120841c9200a00a03400c2c1904410b02c0705020000042d040d018101e030300c5441c06040d0292504070741004001d81740f020040402c200624004805618a56500b084001100030050000c0102140948441c0b066440d1084055081d100f0042800b41700d20000c00ca41002a900d400543d00c0854040d64002108480f0300046843c01d40d0132040001c41400105000075004108103607030b0722100c1801d070b050300700c0000f8601d03e842264030018010030b99003004405004240c4a584120310320004c070002c40c0d050658a044800159900 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 981783426 1250 981782176 981782189
    0xc390306050a0606020f10091502030411040b06180108090a1a07030c0903080301090902180c0901020f19151e020901030c1809020a09090f020c0601120305070303021b07 74
    0x1114100403910001c0e200d410004c003a240042c0100c5101d0441054031024030039880c0c021242e49180e013105104070b4120100100744001c104642d2804d050038072101c01425100c0080c0b085003000d201c8052400c0441c10380d0607070111400b051100e80428030041d0742420700149600031900c0b40301c64003030102c0c50840740414035003044851a840350900d2140101915802041c01c2d051005007141000041c14400840707044036000c1d0780010748040c030707403002a0301c100e4107a5200855146071001d0000c4040c4400042446c50005d030211143c00070b200b2541c41d01c6100900b0508100c580010700800428141e4040342140070f030401d40018040c400e00c00f4030001e40c11030007c01c0c9201e40d002c0742014540d6058818401c81184508003010318501e480c0c0c91030007500c41030040c05610741e00400d85a104500034014000a00b200060901c511545004010020f400280030307200540301d4000002203008404501c423207041d800d5601c05260240341d0700c2c250065031000d4242e00481070251030461000300140800000303801e4 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 981784676 1250 981783426 981783431
    0x4200301030b160804120311120106031d0c1804020d050f030304030f0e0d03180f090b09070906021507091e03060f0b1f0207051c02010f0c390306 64
    0x1044000503030301e15140780150050000c0413061001268091300f8040c0156541c0c5404200d503601e07041c1600031401100703c1c004403000d0002c00402c44d2134054011000061400384540010324502e4001c956440140000390342000c521103420101c94070400303c1d02e601c10b0001e0640d00c840b103d80e0365110725140d0081803280b0709800100030321081580c040d55040700c074200c13442e107030003403040007000103050a0301420000c0c14801008090300e021011a502c10300100b0640301600d080c90ba4411008002d003503140d81f9540b0806015000805084c003d000741004d550280e4000d10350541c03400d2900c84178a0380902221306201082d00b0020380301e00d411503e409040c0051000301001403031440c001c0140c640301404a040b803824038900e1911502d81402e140c1103131078403101c00030791140486020b90070448607030007281d0460004003040d801c0c081f05d0644070808500c00c2c1e903582002600c6400440340030300045002071200c0c4180c50405407490004a41c0c451b401d210401680c401c0c0040104c10001100341d40c4125000340c0c = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 981785926 1250 981784676 981784681
    0x15020c0601030305190c1223040905011d040b0c070204020403060e0c011e0219110306040311100203330603090708070f0509011e0f030f20090604200301030b 69
    0x80c0c101c200b1010145d450030140c101c00f100b0703038502000d9001c00d0f407071400308105101e1907200d40111139900c424166071010034942d202d441c0c001e5280a44803d000c0e1a280d4030342d401240f09580b94000b001c40c801c50700401141c0050710b40310740040d51503016100580c0c3c41602403002101090080c810b00459940d094002e0000465410016081d21025400c20f040d210080c001414070703030340100c1d03c903141201c4c01d0101d0490000c5450645842c0000905054051003450200410140c03c41840010000007904407a03031000700000c48026031008459003604007450015203207200340048800304074600c91b00d0004501d5008a0003040300c981084584031020762103071104102c1e0340360038000440030b021818a50343c011030400c1d020849048040c41144800d1b0640460702c801401d40039013040107030951022a040c00343e035038107142c1c105589280003502d1410910004961218616a41811009003d0b1600c01c21344d0344c038400c00000704078115030701c055000401240f1170f102101e88011806148140702003803c90 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 981787176 1250 981785926 981785947
    0x319020a121d0318010306080a03020a0b1006091406160b0613140408091c12080609070c080a09050d0b0106020105130c142d1e0a0315020c0601030305 66
    0xd504500003602d45200c42c0b003440102e82c0c40070044900b1107400310f40281c1d134004202c1c0120000c0415a0101c985c42c0900800d4a08040c0d0210306010080e002d1880f007680d6450390701c180c20105059101d0980130403612903042120812102c00e40c500004024030381c1d070902d850b0341d480180603c0c4487c8100c40203540340301004428601240302a1010445a008000d01c12203068200801d45024201410868003c14540e40c0741d40d9a051021000c0180051280890980d103004040000b801014001003100000010003d08100805038452134a07591042145039654540c00c402e580810414010040080008142900c90758901a1524070a090241d0503600d841002400c44078044e190661580404160001180e4080800d205030348011003490f040380c2c1e0900004103100207050ba070320a00714103603943e0045840d000c415610100700c01c0e50b80308040c02e407000c080c000d840b020350340c07042c0d1003200c00c038090001c16010602640c070300c04400c50043c40c0c03801c00d071402032030f24200368012070010780d001550003c40c = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 981788426 1250 981787176 981787181
    0x1242040e030909040807080f18040615050307030c030605060a0518060a080f09030714060912190e0609120d02010b090609040b040f080a09081c090b0319020a12 70
    0x30840035405142848215400600c0c03410003c0e1000e8044400426824148041102210030694036195030344d51301e42245800000c10407079a4080780c4100d1900ca000611020007849060303c1008694a81d480c41e40c8860090340144442c0880004240c1d5411002c149510b8a01c01000303510450b440305515858005408036507000391060040c0a00350600003800e40507000307154542c110050803411203640d611020b40500d18018400c0142c0520a00b02c1c8040e0000300200744180219000c2c0b003a901c001021090151551140c03060aa5804100c00ca4506100784103d02e180d441c500010940e0b03190131410b4000503031007418840c004e0020340080000c41901074092060412039242a904040300d490031400041c0c40e000d00038000b4040c001500000740800a184e0060902d60307602060507601d03910301040c02400e0404e1801280b03918424040a05600080b668010f0ba500000e07644512207141080d41040d0395410241061440c147c00c1c0c203085d16071501a001400060ba01d40d0394003483d040ca2204e04005 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 981789676 1250 981788426 981788441
    0xf080304030c081c050d090602390309040902041506172202060a0c02040e0c01020d0503060a14031006060513170601030b0606090312030a0b0303124204 67
    0x40f154080a114070880d000d006034825035601c82d0030041c1d10303020848000c80c05000741c00300003880705100182800f03000d1071140524403141078000c2d0b0601c04106412082d040902c00c03861030001540103000080b42450681c200843c040d1001c0c001140b42101945540300e1150710781c100502140f090320141c26a000e040d611030368403800c0f42c0d411841d051000084503003010b1910b00081c0c0186000200d000443d402141300100f901d90103001084119200c42c3d03011340301c0080c4202140103001340003004048520600a40340140320082c460340e606c4c0d1510103c855040740c600c50b0107030140035000807030b503450380180b06901c010404ca0721400d5441c0c1140903400c0d6406095008214080e03401045400782000008100d410340760b1201d81c000780c4d038584400142d020b00842940d2645072151a4101c055909080c0145004038200002400081c06140c109912401843c0381d00d42c03242c0201c1c000842c45d118041a0780105808200c040c010f01849815036803008292110a03080d05031640e5404600b41414403034400d = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 981790926 1250 981789676 981789689
    0x8030c0a12180603020f0c0d0c03080c07021507020a12050705090606120a0c44010e070311071e030210051005150903010903090e0a0b0603010905100f080304030c 71
    0x20050300180b0100e0708250390041d0010540c0c08a10078040c944400c04403110b1030012800c0b114802d801000081010f498820100d0000c2e40b442e0101d0030340c0c0e48a1068450056005004d140900426080709050f600324000507030713001c400b180000522400301072100744498044c201502e000741c02c0a05101e41300b007015015500894041001903484001d031003226030400d1a1100101c4e0780f0392a40c10482c0c0460b003610300f070700b0450b42c0b0f1940c2c58200b48030401c00001c1c1d00040790281d112f4810f132a24800a07500c091142110210802002554041c46a404540c08441c00b04100e070901403240c4604803071804200ca1041c51034051a045801e06804021240c2264a101424000f80c501221080c00140c000d00c00c0501908103540440a4240384c2e1007030391013015010300200002241c42c02c000388a94598400d00d01d0064440b00462095000d50080010808004c0c006c14516482c00400d04006d0600522092070b01f0840d1401080309080682107030010000d0100550301c1d1811414001c815801039403015 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 981792176 1250 981790926 981790937
    0x10e010305011808090409030c0c12030e0901060c0f06060f140916020d0e010e060336060105210105040c080d11070308030c0403080c030a030f020913050a0608030c0a12 74
    0x10000113002e0021034800080a4401060701c42e25460103448040d0000001046d0442d000c0c00812028800d503d0051110300035aa400160b84018060214000080c000c01000441051052020800c00c2e01d5450289116034000910542d43d1605c1d1180000b03d50480460140051070840451503c2420075800000320348840c0340c1101d016101954034000c02038484180070120082c13030312982c080e003000c036480f480c050003e5070b40b8a0091242c1c101d02088083c8200301c0545604803800d400303030540720759110281e440d0050100d43d007410100704403141d803600a201c09400f400c030f0b91582e0510030f00030140114881c0c01400d900394103002956007003118a442000400134600308034070040000107000030440b42c01201c265580d44901116a07120f11494002a2401000003024181d2210020003400300303000039542048801046000703801a0300c01c013100554000f40010410203081c0d40d40c3d015680182c0900c07c0052260350394a0003905540286ca5000d159801c4151410240b0218925a103190701d46407816 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 981793426 1250 981792176 981792221
    0x11040b0f0f030106120602070507120b0a02030a0f020a0801180e0316050a0b0711150106020615210705130b01020a0f0521030412030204050a050402090d060203010e01030501 76
    0x224410040d220105031145035840440c11981c0c07004e50264000d040c185100d56043c6841c0d091100c0658030901d01200d0620403402d0000d42003503250501400030fa4000548003407500c80c011440040d400c041c1c11a4406907942048044405951005040207000c544034188158544031700c0b412030802594166010a05141800e000701c00c000c0215646660080c0e02408116414100b641c03508041100c010700511811041c40071454000c00c07905040c915074800c9400d40000c0f032800c40311031364080c42003802581c01079010401c442c0e90f407d0121290340019029000d05121204005402c0c16135010900d002e400c844014400f03420601d42545046aa004041c4400080c0400003907542c1505800505034804e11421181046424401030300c074000c164425004460070f0074181c80c01a44242c07003ca40c0d0074541d10304c21030317041c9c003034020380f0122100100900b04052811080c48043d40c44141c600c0d5201000f02003100c000381c19072000d103020b0000460105015030542c5091401c494200c200200709050341c0c0d11 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 981794676 1250 981793426 981793429
    0x80108010e12031b0c1011090d060504050a0204060b040f09020a020a0f1110090501030e16050d0203030d0204080f1203130f0245040804030f05210711040b 68
    0x6206401d440000d050559a645103050114100140e0702004006613002a41c1c00210340300294400c0041c102e01000c0010307040c403208000301c0f803149803152a00b11034580c00207004252113500456000e40600142c1e08200220380c002811903646800c005140c4c0030125060202c3c55840c2c0500005d040210b904604e413000e0f803d80a035544048880041034080c103240540c1c02c001d102951407203514009400c6e1400e164400002074140c04040c060240024941901c02000b084009080107009142000e070482d03003400d1009100c4003911520b016a0940302c00c01c80e149200025100501c01420781c0405420000c00c40301515040c524403503a11380801c0d2060084c03102c02d14410020703501090344200d00307909084541c07000c51082d0102c89400e036540c140901200b43c42101020a010756941e00100c002d241d20054110b544410304240e8004e0300c2c1c2c0c801488203100160103450f190108602580031981d0000e1a0450300b0101000301103048200100405c4000c00c200c14000c0207074000001300c40c1804194606030 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 981795926 1250 981794676 981794683
    0x130c1407050a1b080a0623040c210b040b0906060108010608070507030c050114040c0807061407060213060207082b0f030e0a06021804021204300f080108010e 69
    0x380b024001c401650000d620080b00c441014000742240801d4035143c11503400d2140040aa4401603030708039200c0300d001502e151090083e030344031f01c0d409140b07070041e03d040a1098015101d59401c0c980000c0c46c21440350007050804140c41c0c4103a1040d410400d1500e07141c00e091741414000350450303060200b031100500201d0b0f0084802503221089103805030300c940540c1801c030b60140c201c400c064601d51a01c00d000740c0203944600c11602c55401140d04803440d0f50344480c182d690364001d01c102c0740000c082c1805440c6200802e0020000e050090300d0250504101c45040401c810644d4001d201583c44803e0070441e0840c1070000030500d400701c90b46041403c1c0e41c48a981240c40e11548181e017004800d40b034098040d400b90b40f186200580d8201269103011080c40c1c00402035102d0b12546008869218a8001e00c2c034040c02151184000d0f0f080c21800c0b501c9654801c0004100640c00d45182e4907038100003442030400c040343c3c00850501e81d0316012003100c4441c02404a40c01030300015680e9040007d640201c41001 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 981797176 1250 981795926 981795943
    0x80903190c0e090c0d0602220b040519030804080f0d03020a0c140f030a1d100c0b0405070b030c03160315170f06011401020609210a0e130c140705 64
    0x34512410503640d0422140c4c00d19048040d07241c0c1c032003000300d44502444840d5020b002c0c101001c2420103181411603004d0703c0a0340007442420b841c0403080000348914140800e1081d00e44140d00140901a0303184e83c1c95035060740240e04a5081c0c1d900640000440e031500304001c512021003401c04615101800c1c900030304c0b4401201d0050941e00c1204401c1d03802e50000c0010301c3c1680030300701c03d8940f59641000018030f4020494649170780c02640c0b41d00520203281181140342452455143c241807014159903035070080800078001c0c0e50501810400041d1140300d0310096216545a44040d41c3d00e01c2c1044034020f10f801c104002e0400c04d03141820011039140801c54110954503040403947c10001511544d61800608000d003044034080d440000410785002c058401c0910426001e43d0080d5a6a9003603d99400018000c0000d0326400e26407480c0400b20500141100700e0070780742c100d694000303075401308980d10415a000c107519540c48017603092139940000d80190503034080036401c0c5410340644401d039961122 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 981798426 1250 981797176 981797189
    0x241c2105040513050705090306011403070501031e05040302031605010902011407050606060f090d0b0a05010e15060a120507171321022803080c091c1b03080903190c 72
    0x4c44000c030f50715602800039101e4155000382191695030f19401940000d00407001d103139000384035030302d004565580170740510010010209202c00030440002001405840082c005a0940c002008110368000c01c2d086004016409200003044214492000602d400312000c40220800e805001500000e070000c04c6e1036411040c1220344a450701c03c0130300850740d9803148241d01ca03800000d18a0300b60401c401c00385854400c2120107802c0080741e0744e5401c044811101154694010818840e285200e441e046000c3c0c1100a1640b4002050210600e100e008440301a034110011684c0721048040ca201c2c1410f100ba402082c00b4240100c03400150388407440b41141031021190004503190b040c80441c401c11443e20000f00449a21000150030758004a42d010306110642c000f40319000018a22003004d011280070f0b00025100c03031a0381800030809940032016060484052144242c2801c0c88003d901030400650f01034000190380d0440c06080602e04203402218841c900c3d000f07558072001c07514016035041210203 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 981799676 1250 981798426 981798431
    0x1201090e150a0b060408012301050109030f06110a120c1e0516060204060f1d0108040f142410030201050913022505010b09241c2105040513 61
    0x350080d42c2c1c400791203600505600700c1c4000c01c002600582c150050400d1110201d036003201c601c03032908101010b410900071170740850341600d0f00700005031581b05400341880c0200c40c0000c0c940745040c800f003040d510079910040015004414000745d0403c41c8507505400d09076007032031588000254000e1090008124030712052141c0071601081023103c0008001003079a00000c11552143ca07600d015044000d0030240c000010780400c481c02081002c2080b2802d00c9005031140c1ca4107513265914600007010f004001c407111010040e00f81d10003202044540554000301490214062501c01c0f8420204401024207000c0c00348280300700b02603600070048402c0d400c416120720b503002c1040303204103000e8410a103071605248030071030b002d40110342c0680d00030502c0740c032503402031164194101c20020150005d03100c00e040c070500d0b117009084120320035919000105000e46450050340f81d00994400054054106549100021a000c00120300315003030900c1007403803420721a0a003400c100201e00c90304035000071142c9081c1d = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 981800926 1250 981799676 981799681
    0x1061a0d090203010912080906010e040209070507060c0e040e060606040b0c0703120e09010b0c0d03050612030313050d0903080a050a030209060c070311060a050910050f0c031201090e15 81
    0x5032250001201150080d00a1000d40307001e25010296110f0b4105240c00101080c01050f05001c1c00f0031390a048845013044610316484035001c000008102900030030500008110f0070000604074012401405041e84643c420111024103100030b131819003003840402d0304232a0402185642c0c2605071410388008203012501c40e00c8070f2120514000d82030300090030101d010011840e110b5440310450301e4a46094a00405c6079130303121701e0505c60303000b48445650190800261100007900ca83e0115a020030001e1042c0c0554082003002411940150b07807404640d03140c0c09d084018418200540c0d400106685031492042e460741e110540e05009081c03188007040000143e03207005074480d0301641c10f030b00d000403c1d282d66403403003800f51550b802c040c1c8012100035154842844140c0b42010581d141d01d60951a024134000801080081e508424410b035070501c04103108080078042210040d00021048500455550b543d08441a500c550145e01c550146801c2c26181c0c101440c01041000d1420549040e030b28454 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 981802176 1250 981800926 981800947
    0x1b0201020615032e0605040608030a0e0406120809030c010e010210090309150c0b090d0903060207050f06040803010305010608031e0306030715030906060f0e06010804030c0b04061d01061a 82
    0x80e001c1e130a54440d04c90580203225950350100c0700c03684280701c030003010002c072a40c500034031003a2600b6208600d00ca400600000c4402400380c000d0030000140208001115034690010000880380b400c010f4aa806d0046180205401c0030010101a5842400c000d5019003580340000e507107824010584081d80d40740d2111004050041c1210340151041c03801c442136000b282e8030020103071440300c4d0081e188000c01102040d000040485d41042151042c0d40342000c29043d070700c036000694401c0904036214031500102a803020820b000003802548191042583c079455404e10a09581c45500040c01c25003003001728083c0800c2403100c150341c0c4403420845941f01d5a035070002905003d0031764011241c40805840b4009803da060740316506651061707100700030141c0c80d0081100d80b1100750082410070b405010200d003c46d0701402125500510914040348152130b03503640d841c142071040d00c0c215442c90b2200c0e8011030683d00b09107030500c41e0b81c0d248020040c103880c140542d6808040000501d800d44000112480c0d003 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 981803426 1250 981802176 981802183
    0x5130e0613060917120f0601020c0d030c050a0b04053a0e030a030816260405070b07050d1707080a05060604050d0831060e010306030b0f071b020102061503 68
    0x3c0ba4104d80ea4080742104003031503005a5003c0d00020310311300b150100084102800145203801404180e0052480705c415005001071101d0101c0243c040c400c41001002c001794041002d19403003481000c81c002075007007074a00365190481c02e1095440540d070900f001090070a0345c42654460300705100c0601500178401000366030f40302c40c00c0135854050140d544002c0a254224403164050072802071700400f0320741d00c1034003107a1000a004d00461a40040c460900340d1190902a10360014000d10540da042030380c840031100542d11040c0c0840c0c45802c08600b46207815000b01c591030020040a0100e10f4902d004d0000400100004200b60540c0d0303601c00201721551900020754015100250407000d07802c82c14205000c503034001c0900301038910742120f0384101c0d040c0c0c6840e00d040b0340341c00030a032030b10050704068003907403003040c071440050400d03a036076800101207480b05088601501d0020040583e5042c0100300a12510306000ca4000b6116422040c40060742d00092982d4010b0983c04005003505401e00041e04 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 981804676 1250 981803426 981803441
    0x15040206070506070206060f0a06140c12070515070314041b150e1918020d020d0204091401090e0d050904020f0a090e0901050c040611120c010605130e061306 69
    0x40c5105003800c010044ea00000c915000321412a048580781d000c0d0400c0000e1045540540c41c000b5100303682d42c01d040c04290000e4115000d03c5403e03100c044900c07910001d22030f00030b070038141e40750b034080340050f44c130390301c0c00b0a080750412418503040c031500c000000712414050020f08000c100f902000d945080100103100040040c0c103928000f42019071101d88010100d0a085c62024843c801180f45103c017508095503140440d040c8200e00c1a0020340d041948000350050303000106029001c0010040e082035501c002d10207407140b18000070781ca14002807800010041604600c0030f1074a000c2c1410207030000001c809030020414601a0340c2e80380d50380007041c0680114104c8445501d03010840686003078010b0303004002d85404400d141515a82c2101560903924141d07080d14100200f0042440014800c0189000d00c60880b4102c07034805005001c101d005a00868054207142d5542c0d50502051900304109020301075030300424007454100000050301c1d0000500324a08010b29030680e4000c0100e141c02040 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 981805926 1250 981804676 981804683
    0x2704020a03091e0b0f1302150703030c0c08250c14010f140a0c020303120a0f0e03130509060d1704183c0f0207020a050604081504020607 60
    0x54540c0c66446015014140c00d22084980c5049861111502c031444414412200c0e001802c00320191289050700402e0702d000341107100c0c0202e0000320040540c0b07071070301c00f00751945240c0492a5124a00d040c0281215003007240f130307400c2010340d00c014004945034106480041da0900f04030700316000d501845401c00000c3c0300c401011400d07454000120601d0080c0d400c4010b510a80750102009030180c0304031445c030402102c40308101c07400c0c025003845038420000c490350300784040c04880c43c2c9507803104d0040c0c42e03490480301c00c2983c1741c03500c0980072010b030035028101c043d510000007941050340f203c06400c140c03206801128090b64000300015169500c00c8008140705400030318080100140c0400404d91b41c0c000e008446243c9124034040300002070340d00c654848208080d60500108800081e40b04031080d14079415044007002441c0300c007c03550f10b44601180120103450041c3c3e0b80005106100760161aa440365115200601042011810204030a0540f4154000310b003c2d56507144001041030140d4400507 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 981807176 1250 981805926 981805931
    0x4140c1513051503010e13020d05072402073308063a03120e1c020d020607030f060b0a050703140406120504020307171614062704 57
    0xc00c04103000c40c010010007881068060034952a0002d00418400301605805003103004c0004005540e90a0744442d04108070348118203080440b071300019009480c05d6810742d4980c109403020001c0a09001544c0d504a042140364403030000314100c045c1d00d5010f544901030301030000c041383d0380b400b00c1c5e00e242d49a9811880c0504111071008424010b00301002100c0303550150f00c4074820303600d007120031149107031800a50b408030001030b4200e010780345440b40d50329000b10144042c03442d00b510a00b60f40e0041d032400310f4001004110802c0d8010400390326480a135010415500726005040c203240d8003040ca1a404080da003008a030000400007400c0c018403107030f4046206168046a40003410746c2c868003d06e01d042c026a101013040034100e9168410b031080c2d12410001c95208407902c0c50503d42500505d80c0580001c01380c811442d42c5904040417400f13150b40300c852681120982800c01c128101107403016185c24100001d1031104040403640e14030a46540f10003121102c84205003481c084100c10110b0b46025109 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 981808426 1250 981807176 981807199
    0x151e090c120e07240314040f060e01140a0e21070308190c030203060102160e070e0d0203060c070b0f090c1210140610020f0a1b0306020c0312060f010804140c 69
    0x600c0078580e614004d0000003814410780c01d10400260344c0e040c0c0036076080700c0c8146820f180e659500c001400c480c000030704036549170700d50040e0f8101c10501441c810301daa4140402c0c802e203e08412030400300e10140d612008000d4058608001a00d001504c4440303a040c2801035554495103c961402040c00c0111000b03103040c000c0c00640c0f161300d60044c60051100380c080301c10710407059000300c0b41844240207c82c0319102400c0010462803040c202c09046040190481281e4042500030a0400204070f03080042c40c140014418100000140f800364040400014045241410b204180c3c035000c481000d1403242c0b008032585142d1038014010407644046091040182c425141c0d44000d2001040364442e01c1802c0b80c0440c004210300226002e408000204003a205030441035462030100f4a401500c550321051100303020001444030320050081060031001191250702c07200b2075180480c0014000c500070440030380c2d4860b541e6000003c1e16000390740b01c0c0c402142c064548010310b02c1e16010519482e0311403000c0d81c1 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 981809676 1250 981808426 981808469
    0x1203070807060c02030c060a0b0105090a120b0105011805040c0e032506090b09040e011803020114011a0703200703110307080f030409090204151e090c120e07 69
    0x8000c0a0b01c030305014000c81c0000041030380c40c2c0c011040c2c4059280c01c2100010002c0c8207561146410040505009007001c02ca440810f40c44e030900d8101c0d4035070095443e24a002c0c0060424001c2c0144400d00e800c2e41002449590141401c80921a81d4040c0d80c551940038007983c040c19404800540c040c0c102c64900d903010140e00b041d0b80c4a041540c070a80300311440402c0d01c0e881250444180c1d400c0b00d8003e407428101e10709000040c403903001c0b005110b544e908051071900440301200280d1134041c4d400840d0303201c102c0503551050351040e03002c098004c07501002d080c0040110700c10382d0651600740c00e00034000749001c4402e120281d480c01000449029042d004400c12540c500303041c4240d001581110402034a9200c0f155903903510b002c20040d10703401403004001c150a40c2d0030a114081c4040e00100d5005a054941c9010142d690807480c6a10100e8440351845882e00e202d000041c14588400d100759642003001030180a480d44191b17095075114001c00c103c840c0200000001050145081d64a04101d083d = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 981810926 1250 981809676 981809693
    0x110424020a0f080306130b01020a020d0c08030f031506040f050d060e010609060608090c0a030f0c08070e0402010e04060b0331111206070e0607051614030c030a0f020609120307 77
    0x1c502da80300c3d02e004031b8101c05030560b40c8104210800d041e00201080704164003008917a100501d0103c500c010078060100313100800b400a8044030708000c000584030b0a0195919580290980381a8020785041c0400c201d81014186140e08992099813a602000c0d443e0904001900c2c00310b50f400719a60a0400001e0360380e03150307844001264a103656115580c4c6680d4503071503e4a869500d4698081404403040c1701141c4104141000a4480e425055200c0d603600011810f140c3d140c2d01020150304003004203c150350b006a59800305801c101d6080128600300b41c8400c0742e5000141c241d84501e2444841000b040c520400340c003c0ec600900c0031220320404d80d103002c1d00b00d20041d00b0030600800861403090741c0104c002650320f0003031015480f8130300d1030601001444441d400000f403e80d0a071040042c07100c202c021650780203019100141076215501c03820310074540717041c2e000e481440c02503001c003d120020400c03500d4900307400b95040310701d41d0f03560110754005198000452400041404005002c0d004c208041 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 981812176 1250 981810926 981810931
    0xe010c05070f05010e0d200319050a0b060102150115050705060906151f030f0f0903020c040c1b12020f190b0610051204171b01110424020a0f0803 64
    0x36a903405ea28031110302404000750000c0d80044c038542201d080c81c0d1a160f41705181c000203240150860f0070386181a01030424191891405407807070303044200000180540c41c15801c0d030001b028002003d20f1041c240342d10001d49014410344c9003444903d507910307011521840885100680101c1281c2a5090004200b80c41d100d051300c0c03003960020100c007040590f0804980c003a0300540703888451000d8404a420a901504002c00c81d50b007543d07a81c07072003040003040c2c07881070350100c5d4080da0040c07114007401e10600c42140d03c011509400d00640e03140729014101a80317040e0200d039a000a4016900141e0304090780380006840107000780380900d8080000344401110071040c80342c01021242060b48500041c01403801c40c2c10b400342c000613400c010a0340340300f800e80071581e00306210f184504021754120f50035440b40d801611206000121901210300680424040c5805444a003171030340c1c2c64289000342150400340a0340406040d04101c4540b00c0480340280f0031040c0c0c054015200c0030b42c040080c07034032007802e9104 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 981813426 1250 981812176 981812179
    0x91103060a09200306040914031801030204050d1707171c020306060711150f0d051f12080f04061e18180209060a020106031218060e010c05070f05 64
    0xa244002200003060058220b00f000d040b2070004504602c0b46400007552008040540068403250756000150142c0000914014180061600c0f5494405600a0030040b141d0540c101801404244001e42e200c078400b06da865032160400700088056860501c9500034080040c00c40da0000781c800c40081e41d070000410410600070088507100001c82000800c07804141c410b6500404184051000680004076560190800902c0b42c000b80e10070340480030641e80130710200e103191000401c050500e00389034050560850300308801c00b403900044400c10558155076100b1007000c498100f1652080c4001c003001c03501601d0a1000080d034603a180d00014001e40c07000440f000c0101c265180d14001c4900c207400408503840301c558400c2e6001d02d402400348051158100c400f110030780c00c0248403603d40d2550020a14142150000314106146007000381071503500140420038840038158038401a007248110f0000d4a80d641000c0401201000048490444680004195214803030001c80c0500e0503c0d0f1a0003103480 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 981814676 1250 981813426 981813439
    0x1050a0602010629160809011704020d060902060c07061701060f080c1308070e0603070807060f2a1406090f100902011404030605060301060b0a052209110306 69
    0x156100e04a00f2604148200b080c2c0205110f200c1210300300d107401d544005240c10780840e042040600c0c10b64201c2c8030b0018200e5480000003000700701540c0084c65123200d01b1f15038a034014680703095000b0840d120704580c03000b0302c065555007a580443d520340c1c050711925140c0e20122007803244c0b2504007410f2030580c8102c0054540c0d50000003d1000c0c881c45202203507a4003a85d80f400303c1c2e103880c104900c181d042441051001a5075600c0421090010842d42c0014000c8640312046401e1060134035040c00c04603009601180c00019040c404950007000007000c291942c40c00329940e0b035040100c10540d0141d640a11001d401c40300319201448a416500380102d410101550b0b0561140000c2a07a00c00008803a0400c9411180d100f0380304000b56440244070034010704250007840075046420700c0740c0d4801c0d00220b52907965407090240740c4c1424490803010303203441e4400c6498107030441d20180007400360040c01011141c0c07030ba140440208800a22000624a2060030701c40980318410445542e0003c4484500642 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 981815926 1250 981814676 981814679
    0x12060a020313200301050c0c0c19150302090a050103020a09170c0409050616090f030f051005011701050906040309090b0102100c09060314071e09051003020a02010b0a150c060f0e0601050a 82
    0x1c1c01f0000c8038a070304400070087c03030862840b10034490b2400002120508007001400c000071302a001c40724200081e4000d550050751342e0713402020080070013004d0f0402030406106001d4081c0003034104002d50141c0352014052124004058000340c0f401c581964030700e4005007011203d004003e40020241c0c0200e1281c8512009084010002c40e0706c4030861084c20009103100400300045402100c1540b0284c3c0544192541030014481c1c030701c01d9440c2a440201e20760598030b03810035099028401c0c142c1100d04040541300c28109604c0c01020b070b18150241000240d60380003801c441d03070300030041e90100c0f148010051207982c9959001600025440c400d013004a410700d44645142094501400d210b4141c98507a004044203800f8000c2d5941c0d129041c00c1d0070711000c40340219941d5140d441031591046c1941c0c000d85ea172016481c00909407031002d522180544031500040c028424030080e160b00b2641c841ca040400c01031b141c01c5c1403001d8901d00c40607800d50703441d00918854404021643c5410384606035060410107 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 981817176 1250 981815926 981815941
    0x1e04060608070e030c064302031507050904180c030c17030304020d0609050f070b0301060915020c090c0f0706020d27060b0d0b1005090612060a02031320030105 70
    0x884400140c50b178003000800400c000c146080300002e02401f1f14000710840e030144610010503401040315103c1054403884810340c1149010131051043c4400a11100c5a6040440000d0000e009040a5504c12501c681704080c0034410800d1050845801c020031829455032070601007040002d03400b43c511610300d1203018420300c0c400001280c2c0140d50140c00c6001941d41921004000c0c040420b08a4081c00349010141c00c211082000d0b0011305290300703c00e541c80d40341090142c2402c1c000e500c03c0c02621035140c900c403020b5030046102c03e1041e400355844840796a8501d024025803260010181c1490b50109481d03082c041540d016140040b4280410803101b43d01038a81c00d280545071440342445100c0f00c0c2d800c00099215040360402e404042c10f00101d01045a45001c0e10324011901d0044040b1000c408120318030f0062496900145c069440020b001107182c2c0c0070303440350710003009001c40680000104402c4200f1840880c40790f03420040170317403100c40202d0007000c0080400c02541d11039070030840444c030031 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 981818426 1250 981817176 981817183
    0x7120c0e01140a020a060b0a0e0415060f0509071404120c03021c021c03030f110306040507110a08090d060627060e070f0309050f0a051e0c1e04060608070e03 69
    0x10f5504c0e0020050880c680e0b8805020b007030440c03003894100200c50800140701d1a00140b81d401a4070403e05c1805030400d0400810031101e0903402003042e0114603408100503105d0840041d007140d1203280c800301c804604045131070544a03d0b030181c044405810710140c20b00041c60341c04010b591007168031601a100760728220942c0c041654020b540845203002c0040410744910007414598441c2c2408130700c0185600c2c80f80212250380021000c94030000040007483c0c038040c45001c0d405411800c0150341901c203160060764030a800b40c0c008040c00c100052403100d42da02c20400903a501d520083c00d008582d2502801610f0b40c038000e100f0356202c1201c646004000e02640070707180941d0708581201d40c3d15a188082103034070303603a800d20100a0613501e400310400f01c6d2040c0044440c441741744008102020071840d04610382485009035204904042c250078401d1940410740802c4910116005180d080c1c5030908064a1801d454070144e00030310700800040d045801000d9680b2906d8580c46122200f0b6a0209142d02c = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 981819676 1250 981818426 981818437
    0x308270c031234021e090a2c28031418040504020402130f050a0618030b180a06050a2d022521020a1a07120c0e0114 51
    0x40f0520b24900700242140c10f00c15a2045016040c0341d1400704002d402240d2000800c00300307542c10040c800300c0f2074010305041d840e983e00104200010400142140204503005803d0606e0141c510343d40c11a5240e03000c800c1200c2e40910481411502003451a81303855405042040e07412408580d0307104c0e00301214882903007629171211040001ca002d865042c03007040001c1800034800c0380d00660038408003440c0c124000007403000d4000c1440100106080c04c0403c1030080c03945d40508108000314038410301020541e846001181d0b8040d00c044034544459600d0514401400030181e034501c00c22001c1ca0a20a86400180c040d5414060402100b00c03024500d170060050901c1d1050300184030814104180141d900a1002c00000e003d202200c26003055605100418200169001300d03405400500085220003821340c1d03400307940000e14806100383e413003400b607101c604400014031007203000103000f850050b600c0303d90180c985c1d4410481100a284060302d40c914610041c0d0008101c0e44a00301d40c480020201c0300c = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 981820926 1250 981819676 981819697
    0x91302030c010804151104090f1e1505150702030f030702040c05031e180304030503040302040501090204150507021504060f1709030d0b030c09040b010608090a080301030308270c0312 80
    0xc0100305842c0801c00b174458010840d11651b400c0000240c24103851107050000160850042014805003510014044600b03d0758440071f490980003440d54035501d03c9400466a060b100107208001c0c038450820180144a806034160080c102d81d007507040c0002c0018040c6500c200c8040040c500c02a104991601044400441c00d0010406405207104180d50441d402078480f1074000345507040c04285030554100ba4400c49441e80089001e01c21407402d405894050400b4140850605241c40c072011200504108040144040000d41d4000d548403520004000801c0e00325507a80c8a81d40d40d1b006240d080c0c4004031100160020301c43d8a060024103200703e02404004000710b0a010904070b49c24001c05448801070b5051180048150898841e41e021134411070041040c0c0059601d051005041d44a0007400d4200f260060707005400042c40f017406a0303054030380510302184035584030a4031403a41c404084607100307200c190100c42c0301c0309800050700c1c1003801030580995030326282400d00136140e401900b0161 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 981822176 1250 981820926 981820943
    0x2060a1101050903191107050a06051209030f090d082101060206090a0b01141207030b07120b03070306020a110106081c09080606010f0c0605010e07090e071d0a05091302030c010804 79
    0x5c0d50864815040d00d85c04983c1c001c2502e40465580300000c46a00081c4d020f280850700101c2d69600c42c41300b01014030307030260500010f185404200056901c0903c2071a028920444030b0210031401d0062900699014800d8004205031240340003c82004045007440b03010014440c5000090340310a0201d035454010b0750000c4005d006909000d008820520700d08640782c0c10480101560070036450410a40e4020750142e4032040c010708107400d008180001c03901150850364200030f5500e0342ca031000141d0b01d0489030082d80c01606c0300c000d400212007200600720300792800e6082c5000403411210100f10a861031203042c02d00e92034106841c90030345604c034952042c09402d800003800240c555001d0302c14a84105000d19121100004607640d07401125000c0e0040600304481004100c0045c1c0c1090000b00601800c441440091614810007040402e1032001c000c1001c1001c42c1c0e000c9161141c1d200300780a03000080521400e803802c018680007210702403405912a1041801c1883c295002d003008600803034004800 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 981823426 1250 981822176 981822217
    0x6060302040e031c020f251b0609030605180d090f050117040f11090412081311010c02120d120516080a0504030203090d05030a1d0d03180302060a1101050903 69
    0x244c0000d4100f40340070002010300b00116551130b5400008800110604100144e1040d56814540c0d0484134012190a0400d11844144001d07900640c4200880780c0c08900031400d5521201c0c000940380b070f8900c07a0403840c4900080500c446810420310300c00e480e8040c04681000396501e00450715045901246010301c03003d01c021502040e00503402041c0b0300e005002440100c4175182c082946224101c80c2a90305c101e80320707010050254000070700c98102443c0c40c040500081143c55908100341c8102105042c0001250010215115a90800e00314110141626203201180a01500d5080510b180150a0b4605400030350038041440724210b04050640d40d6150661342c0c2d0b41c00741c00500340500300f074080d480184544400d65440a9054075800c0c132403000b540d100c0034401e41c0a00340d00807091046003500c0b44a803184045031a901ca810040035007605d0400c824050070403010310200f903140c1000e034220500080f80c0c245544c11070500c04a44840304020401540c400002c1030b00e0b03029040c100310003010b00e50003 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 981824676 1250 981823426 981823477
    0xf1e041a090706094b0803031519080d020c0102010b0a0305030f0f0702090c0403060e0609120f0d0f02041707030b1801021902160603090206040323030706060302040e03 74
    0x4103524805948041500315404040826543c0b9003c501c81d00742e18176a0030100b60004042c2c04e0b601c00406115008609500f00941580c000307900c03503401e041c002c01008038041c50761441030099800a10100043c2c465001a86c48000d403200c1c0c02141d82800b540c2001540b03452400e00c0640f000440390850055820110740b10050203080d88540310190038404148071140250351038503a4036001e42000c4100030303503c8e0300d14600a400c0c1d0304102d55850042d08140100f0010280115a8810f40520082501d40e06c0940c548a0a80c9000c0e21825100280c6090210700c14002150300810a07150318000c004140e03803078005142e555914030b000041201050038003044c0c002000e651020b1070204104009802e052844405002d446190000c690046c3e00c030002d40c1000c0c1c25148160409002c16203000e11060341c6136008101140308500c4000c203002048110131110410500086428002100580e992240c6c076040210142c0841e00042e8426440c0c441c01d050000b000004840d5540021103d01d407501f6003814 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 981825926 1250 981824676 981824699
    0x3010b0703030c120f021c0203090706030b220b0102060c040602070509040627020a052403060303070b0403050a0815010c060b04060801060e100e06010203030f1e041a09070609 77
    0x444005024900c00c8500c813a00c06405818422043c101c401600c94114000c45801d170340030000400c1546204100b880071404010803a47d060f56028100031581d0800400410702c0e0220980003414034610141820b0b000b8175540d040400d10320026801c8400b0f0b51114481070056200f00c3c812000941d20030b00040056041c080240b95216000b0000000c10300d0076960000300030207900244103800c031402040502180f4141c1e06c01d40c0900000c0d1403600c40550041b12024102e554019014604440413000481d070303980400c100e502541d4481c054410794203080c034005d4243d030803403080480802d1000000400e6a94091480200c0440c141d42d03503a100161030300c07410010b0000d0014030b0741043d00c40f000411007240034043c0000502d20610f031440103107020303040002c24100795008a10752014607000e02c901030380d0000c141e035080040441c89010645490a4000c1000c00c1e440303284e4a1825403904000601c00c0c022445466054486103004c1c0a40c1e80c03200860b20b4080fa07011f441c1c085400003006000460390341 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 981827176 1250 981825926 981825941
    0x121a070215070905060d0203070329010309020d0813030b1e010e060307031b0303090819150b0a0e090606010c050d051c09060b1f09210f0605180303010b070303 70
    0x141800540c2079140e201217400d03035200f02c0051a21503000428081000d0b072600c5206440d1800702e1402c06000180f0709011403200011a0580c109900e4040c1d01055507101c05204c02642e50000c10156076040e0440c0480124241e0b1000b907941d00b80c0c0d00c0000d41e2468203c15903100c142d40409034482136a0a0107144035081c28080d110340d815100b440000320016091041307410b0f1118841508100785461440d0061003040250045c81c42c42d04201c074007042855403215601c907115440319254200e801070000308002441c60102e803c1d4400e0b130559000038030741584000c840c0070f4544041503d40c90b56030031006454400302040c00030200c0c2c0c018070f18164914400e40191003425a103280d10044c0f00042d0f07881000761241070100307079480b0741d49940400d043d00e840345a0301001e8840b8008031413241c100780300c080c120f04454802c190980f901c4265040790600702462080300c5c0e5070b110f10408001c00003410b00d40300801c4200c4040001e6441201204c1061500101f5281200c28591006207000c0d07070350f03038110050000d0 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 981828426 1250 981827176 981827191
    0x305040807020306040303050105030d230a020a0507091a1c11010509040509030307030c0f4404050106060309080708090a380403150c18121a070215 65
    0xa020401c0141d609000c0d082c021400707950041440d5040c84109800c1c4856030220505000084046003011911404c0d4040040300305c07004c06d0b464000003481a82040100b1400400e039000d51540416141d04a0384401003000301500d08600e19444441840700d484202c01010104e8213182c04680c00180400040306c0d00100d042c9000c034241190b9401140a440301034804a02e90b0b0004820070440d95414410300c18051002d1801d500c1301403000e80054800c00c5c58031880c0746050f1035401002610300d98595a2441008444403890006a51100d200051502658102e50035401c2142c00215607219018141041d6004109140b82070b00b940c0e140701c25580700c404440e401440350400020a030941e4410600c05285c6502034400000d07a07480e03126030f4010f181c1a02e241c0c51200707010600116800c460310302d91000824078006108803d0440948400042440c2c0084402008002083e02c0382c01002e6901c603188035000c81170125500d03601c00d6011407400c6600300f0059004481411884000810b619001030700d = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 981829676 1250 981828426 981828443
    0x120a09080c070b0405040f0204030b041e1e0c0f0815060a0e041406070912150f0f020705060606071a13060c1e0903020303190e030a03022d030a030504 66
    0x400040040c2031010342da1140f801c406020500300f00604050041e10901e6111000442c5414110741d200c216820002d4000303010344800c003109010f619060220a10b008ae08101d104100c010407450050880108140071a0524150074000401030300d00d450344000d4901d0354024040c2500c40700004101d140c401058a036120034140b5001a204142c55013081c0070b02d000d100b002d07001040382c290407450003030003921480800503121010820b1081d4802502c42d40e503407099204040200900c2c00c3d60107411304500c0d034002c0c3c5140c0350f0f80358000e645550041c0b9045106600760f41e041d40d6030078100182806001e001500000401200c02d0610b03003402c0c10264020150b8040c05514041c54407044d0803102c803004044042070709140c1c0c4074502d040880004011a40d10701d000707440582541d01194407409400043e181604241d2240c0e000c980c090400f0001c0604080c0071118040007504000390b642001610101991961a02c0150301d0050581810b40c00a600b0004601e040c10300d413401c5000b40001030050b071310845e = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 981830926 1250 981829676 981829687
    0x1002030d15090f140c040810050c1b07090c0302090303031b0d020a0e1224070c0803042019060f0e04021c0612020a09090c0803070302030d11120a0908 66
    0x15000d1043c244240389540000522114501c49a0a0030601405a10134018180f0082104040004400103030107801140801c15032030f00201504107002d03840801401c002c1b02525088401c2000580724211245540c00340300980050070240c0c22481441d5049405070400c00c0000d000341700c8040c04c1231a0f84114603400e45015180780110003241c100c0001c040000f00e44103000c1e1400d00e01442d64089000303291025040140fa0740e248505d03606240d40d40040681031080020b8402405045103055103a0000400366483c50140303032814a4032104940c0301c1034078000d115901054208030341051040c24804000e4a181402c20809a490410000d80d00c020881a0104c041c011b845a001511650030750500c5440000700c4444088155440b82e004125084685500e000259840000780e40c00c842030200d000850610ba410401e2a101594015109602c40028481d080560020041c0108001c42008001c00030342107120003070b02d200d50039030020721000d02e070046200540c2c280c2c0410142841041c0f002d1608 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 981832176 1250 981830926 981830939
    0xc2012160b0a09060b012a061509020c0f0f030a080a0f020c0c04240311040b1c030201140f0a0531051203060916050c030414010e1002030d15 62
    0x21000b00c4110649a44500414080110500924201e03210900b05841d0600c0f00c0c4901c074078911401c00e408000301c4041000d10050108562083d030004401c2a010849139403a0b141d400040d50190f21551040d10511a40303c1e40310750042540c072a000020b20156207450308541003110072030005011490a90764408240c0c07003181c19413008054108010700030b032101d4110182044102c03080e030701140201c0c1c000380012651030130100002c1c0080c0c0342c0c45981301802011240120f4000d0400e00080c94021000482c000700f05030b1841123440505229600900c41c044440300d00b03000408059540c1c6402803031490218140d091035030400396001d111140160404081403a1442c0d08825040f64244d079508645a19001c1c0041800070a212500b00740440340303541807800128021f001c00401d032880b00100c0345110401103104504a030701480b10f000460b81c07140d0f26080c3c0d08400700a2241e543d80030460462100d41c0d02d080809600303501c0d0209402541c10260400c100001a045134a41940780182200c80030480 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 981833426 1250 981832176 981832193
    0x2040b1b07272901050d1803031d0a02060d05072615010503220f06060807060305090609060a0e100e0105100503030c06010603020a140d0c201216 64
    0x5042800d50000c2c200c091064014040310405040c152402c42030050004900d114401885070340310085ca0f00507500e070588070b88280200349454003001c11524140881d030615525400601400442c1da4802074040707180e44416945109105009400600a1107860340c0c100061340025404482d504000144d0352400c2d400c3c50001c80b159103015080010302040c4441070b141000140b00380d580c04c1c2421455410100501c1d169440c5040c10201c4004c0502d881e030302082200680c0b0040a076200e1814401e19480310116911a4440d01840b40000e14180004014900001d8214014034005002d400c032502d500c420040644400108981c2505c01d000c01c408101800e07205030340d032105d044000007510f4241f89080441c44500342e808103100f58000d010050f000003020035a2070464829003401030fa01ca03080341c81a01c05808604c80c22442d000c02142c419407900c046d820400c0c4483e0070782c0e6000d07002050040300400b10356844101c0c626540c03100c106068119104002071461600d00e003040e030400307281035840400 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 981834532 1106 981833426 981833459
    0x501050415031b270b041406040c032702090c030c0301171204030809090a02030123030c0d051501050d0b0703050703140703021c02040b1b07 62
    0xb254000c00100b00042c4081d062402c07091080c148034080041c0044e403141100c60030300800c4d40786803070b00c2d108400d07944010b0941900c03907840f940e003400700a2100714803003024036a9540c0b1903042405541c0203408050003042c0d203c1c0d00c002081c41400250700c4090070200c444041030050000c952042020340703040d5041c00d00b40c540c0c3c40e201c0080091a12083c0c0740012030109000401006000c440401030100c0c403029555080582c560b4000101244000d02c60030f8100001009014148103d031084020404002022240d031441e22400249859815010888e4143c3c01030000c00c910003101c07103040c0d00400b01101c2d215a401003584440000d942c00402c030108040d555000600701a000e54081020490300e110115a18903042d1800340080d48208502400801c483ca80f804020340d80e40202c0e4162040c0c42030081c20505926200c1c289400d64074180440707801206d90114401104801820 = true := by decide +kernel

theorem cover : BRFrame.Cov 981654676 981834532 := by
  have h0 := BRFrame.cov_init 981654676
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 981654676 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 981654676 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 981654676 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 981654676 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 981654676 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 981654676 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 981654676 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 981654676 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 981654676 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 981654676 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 981654676 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 981654676 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 981654676 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 981654676 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 981654676 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 981654676 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 981654676 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 981654676 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 981654676 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 981654676 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 981654676 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 981654676 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 981654676 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 981654676 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 981654676 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 981654676 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 981654676 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 981654676 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 981654676 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 981654676 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 981654676 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 981654676 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 981654676 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 981654676 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 981654676 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 981654676 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 981654676 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 981654676 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 981654676 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 981654676 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 981654676 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 981654676 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 981654676 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 981654676 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 981654676 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 981654676 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 981654676 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 981654676 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 981654676 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 981654676 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 981654676 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 981654676 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 981654676 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 981654676 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 981654676 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 981654676 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 981654676 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 981654676 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 981654676 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 981654676 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 981654676 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 981654676 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 981654676 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 981654676 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 981654676 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 981654676 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 981654676 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 981654676 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 981654676 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 981654676 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 981654676 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 981654676 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 981654676 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 981654676 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 981654676 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 981654676 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 981654676 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 981654676 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 981654676 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 981654676 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 981654676 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 981654676 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 981654676 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 981654676 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 981654676 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 981654676 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 981654676 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 981654676 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 981654676 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 981654676 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 981654676 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 981654676 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 981654676 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 981654676 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 981654676 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 981654676 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 981654676 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 981654676 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 981654676 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 981654676 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 981654676 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 981654676 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 981654676 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 981654676 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 981654676 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 981654676 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 981654676 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 981654676 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 981654676 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 981654676 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 981654676 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 981654676 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 981654676 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 981654676 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 981654676 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 981654676 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 981654676 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 981654676 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 981654676 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 981654676 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 981654676 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 981654676 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 981654676 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 981654676 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 981654676 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 981654676 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 981654676 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 981654676 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 981654676 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 981654676 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 981654676 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 981654676 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 981654676 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 981654676 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 981654676 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 981654676 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 981654676 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 981654676 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 981654676 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 981654676 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 981654676 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 981654676 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 981654676 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 981654676 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 981654676 ≤ n) (h2 : n < 981834532) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
