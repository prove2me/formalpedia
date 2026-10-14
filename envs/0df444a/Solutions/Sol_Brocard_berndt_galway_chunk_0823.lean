-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_0823
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-13T22:59:58.116188+00:00
-- url     : https://prove2.me/submissions/7cbf00c8-d0ed-410c-a0e1-1eda8b8d127b

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 147841726 ≤ n < 148021582 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 147842976 1250 147841726 147841763
    0x30a05070305061b1c150b1815070f05120304030306060e0d02150706060e010e06010909090807060b0613060f0207050d12050307050d06060806040506060702010e010503060d 76
    0x90000d4041103415008000c04602d406141e450b031203071102403d00000f800c282c02c2200d01c1c0d041843c00380c080303440c0640b05c1020641181c0840c803801e004d004005541961b80b106603a1002c03200c0b031090180d038000c60000c000c034404002d01c00f0943d046d043e8010b00c0140c0903403107420024071b401c0300600c00901c0c0b0f00d130000a210415070158882c030110781e85a151521403c2074a4200014801040c001940002c1d0150315810418801801841d0681c4140c80c00a4100d0321403911002e01d2000b40c2004141d60840c0d01401559078002c0b6200f0000d140c08102485004515561440140150a401442e29845145014880d9112001d681e0414040200e0044196a5820090111244c80c0003031025018020000c101414000d03010108542c00001e00d41220b404814104c03610350004141c64200001131090440c40d10480c016000248059076400845040c1780c1c0c100400c499005c2c012501c0f40034100101c50050760450030f040b6404900b401d00c5901ca03503450000c80c0c081000c01400130844540c08000c2c4e00c070b0 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 147844226 1250 147842976 147842983
    0xc09031f0c03050a05060907120e060c072d23010f0f0c020d140a030e03040f080601050a03241d01050f090d1409010c1401021b1216080405030a05 64
    0x8001c0958040c020707503c40e0740d0040300b10b40058500c15045518040003c00700d40c0251581c14402c400c0040004080d03a410800382c1c1004d800381e032400302403580000d943d014401c00c1c2088810781011601c1030f00a1401d00010700002c900e20a0008000940d11b000c03078010110b4000480440c0b610f01c0000f030100c030403054802d4000f086e00010542d10603242481603444507100103010301103440305840342c2c9000d80030b01c7c00601c01c41d04043d80740800c06449011400c86036000340040c00040800010320540340e03040070505424014141c0040d40204265602003010403c0841203810343c4900407440601c0d5200e1803042c401400300d51440640303e16111724a0602d06005502c014400c408841140701c4a032111049191074510000c0c0160024120300743d041e1051108200901001d40d05041001c1c2c85c283c281d0b20382403a90501500301c4000d95000c908601d201111044494041c5590b0b0090840900d10380c01c5072505009920030b02d503201c11000c0783d42d420000e0340350403240902801411a8007004c200e1818658 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 147845476 1250 147844226 147844241
    0x120213050c1b03180103050901060312110f030a050406030c090302120a050616020706080c130b0d05071403010b0f0f12090f060603070605160611030604060506030f0c09031f 76
    0x9030b8000c03000c0c0a60740500040141c0f000300c8200440701d40a000325000440c09098003401504d09556103d0740000060f501c94950b08480d009500c61002020684030040d092107034900321401c45410400501c04060707444400c803800d0f00c0340b070f00300091140326601e412104c260003074100170340200303036003103208612440041c01c2d0321490320034000c4400695405070400c3d01c0f500a40c42c14030250340078047c03d0000034060381e1110b60081c504488641010310300703e10000700070000d03803000c40340443c00201448401d800e801407030781c49400c07410300001c11b00c40040700e160148414030510800c140d01140d0300e04181500f2040b94242c9200c612106d442d4045240d6202c100d1000350b031844000e02c42c00b80c4100300300c5070101344030b4425240103020b0701c2440d1030310805880d10f5002c15030011a007145600300a0008025100b0980c40c10600e420050b142d2400700d06100c1222050307000244100307800e02c104080404880c03039051744010801501e075218004800880d2415210154079411020340d0070040ea02003174654032404 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 147846726 1250 147845476 147845497
    0x6083a0329130e0a1a01050f0111071502031b07080105061206070302090105120702060402010806010320070201020312040f0209060d03020c090903041d01030b0c030f01120213050c 79
    0x115045070005424050034101d000e240c0c0c00168034401205030070325941c04040d8007866201603d072030501030358036850701d0210349400300900d0f4507400c011700240c1001030362070004901c01e090114030000f0500c00c1a554081510840854910b11410b42902c24400e01c00e981c0d112205152100082c06801140c5445001c80c0c010001d9a610300400515145001c10140780c1c09000c01c03000d41380c5519548000c0f00a540b028650906014042100700384588510a006104840030707805081d090425200050241c10007a01c2d49041605205000424140070841d44602d4503040622030b58480391440141e04502503a8080800e00e64404108024021071184501c0c03818821074141c00035603146020880001050070010740142c0c0181c01441480c1010348215401003950310480e81465642c000000200604014203185001380100400822802e41c90507600020445102c6045142c404940c942c02d02c1d051152040e4040000b10040941d100d105854100844800d0240400c0c6420a60100b41c1d500000540 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 147847976 1250 147846726 147846761
    0x609010506100c0303050402060f030901020a030608010c0e010c02030c030a05160801060f21060606050a0201111e030a11042c060303031b0d0504060b100306083a03 72
    0x644520b00540081030411581d2181d081c40c42440d00c0031001071400820498104108000b034502c81c10540d40514424605840056910030394440020241c84455101401c143e040a414050441e00050f85104c418400e107480e105920386030001030720b801d6050702c0403600340c01030030140b0050003004141c0703c03514140000c2c4065015030340d6003031600f26000d9104003240202030840034046143d41451100d0713000d4000c640030390b110380765885801c2215110f900140c0807402c0000d08200050f02030042106640d0440d8209041142440103800d406082d4004180d500c04000b00155000d03c055014991a20701c0c0001c1d01d454945903001280c2c10b4200710741000c0340c68107100300b0300c031a5450304101e18407407507024002c0c50964aa0928a01c41410200403000c00c00a0a00105442c90502d2055511688c041c200210340902c1e41c005010201a0740c0036444100360424900b4003a05800180000910881c4c00c0c00101c0f03c0c410010082c00000c00c68203d819000c400070601c1c1109078180c003d40006810700024 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 147849226 1250 147847976 147847981
    0x4060506150a080415091403030907050a0e0103030f0507060e0703020109090203091e0f010e0106051215010303050f12040f0c060207050310270311060a05040803150109150206090105 80
    0x600040e030107400302840c0064a0440002c4c001a070715140d0130541c05100c00d01160021040c0c0d40d0385030400e004c00394a5a075500102c10400f24502c10455603004240035a800d080385800c002d10300861110501015051102c00d410496503284184220340341c09420075810460000d01101c45610788000303220a900040700e19070041404c2e0813510849002d905858000c0003200c03200e0380f03120294600080300c1030250060260003205054280140b0384000c981200004100e402c2c01c0c02c0040e0600540c2c00c0d0909981700301203c040451414522905490309401c009446101a104401d6103115507600010100c02420900c01044844103c070110f0900c650180762175680c0780d0400b269030f00150700c143c69056120b0300c0422609030703a95210002d010081c646085080c2d0381000c1d80e031032080820a04500242e0b0405001703d41c41002d0242581002000c1010300c92810f10fa221a001800058055080040d06000d000856170140c0c140b20020202906101642c40d0396041c065100c1c0800c42d44807280e0b500300b000 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 147850476 1250 147849226 147849259
    0x9030c121101031a041d070b04080714031b0406090207050c01110102031b07020303040b0310150509100e031518060a09030c030c0501020f16111005220e04060506 71
    0x14a1040513800110100b01c45a00801c00c805460740080c1c94092040155030320000780024403950025252143d007940c0d81c0c81c03800103803914040c074551040305801c03001d0701082c156542c00b10b03540f0035071326880c840816440c00c40c03c00503000340900e6201c0341003940b0000d840c0c41000300c00f06121055441c240c940c2c113584016020050300341e100c1101c031840360514104816500900708405880c525001a0031242040e03158041d0603039540c01950b40c6411025400d20400100703c0d50000000e07050000c1c0360143c1003522000204144007542c003402814003140710218a441e45080103004403500d12601900c0f000d08046e05000f690704007036051001e45001c1c07080007a0f22154540141c5248660558900202c2a0b450320101c5154018445c200d807655000c010112545905601504603413494000207407000075285041c00310000800c00341c5004841101c0a450a1034015040d10b129032203003501c281a0807070030849201004c400380c22100c4c0c440b00b041c050105006a80c6d1245120740d60540e19031500e46030851 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 147851726 1250 147850476 147850481
    0x27030209060607060b04091407091509020904140735071107030b0106050a080906060102070b09040603050615030c010801180911030f060f060411070b0709030c12110103 74
    0x65080960100801c0103030506030010002d0b5805020009540000c4800140603070307007032a0f0282c0324002e204407074080348001030001c600100703102d000400001c41e0500c4c21010450951264800b040c0e8041602c40e02e540300c3d900802d03030710b40065403007280501c1d140b50013a2403105020080b404507541c034030348440e03003e19000319030350040019403c0502a558a2001311003401c181c10312580e5038040c1c0f480c0000000c8441c540140031b03003a00c0d201c050315031042100040001d5001801e1070001d40c421001d000541c0d8000c21504151021001d101d031380c500c0c2a00110f0003a0131141d10040862041004200701c88800d6581d022041e0002c8041c0c480300a00000119800002802240025414489410100e441c00d03030040030303000c0c4030300a1a01021090740010f8208080e240190040360400e408000d074041f404003584d03921400855041184080d401c46114060150500040000c05c0d84401b003a1200d0254841e00700850b409580e04d440181c440c1b1008054045801c01116208402003030b0707100c690b01a0 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 147852976 1250 147851726 147851729
    0xe130507020d0c031e030213030b0103020906060406080f4203030301050a120204060306090602070203010b01020708100203091501080f100603152c01090309080c03031218030a27 78
    0x50b84d40c290102c83c0203100c107817000e44003502c441c20305508010b541c480d407139030003034000056005074152001585180180101014010304c8140300384010001032102903000f90f24a60802004513040f401b50703540591801400000c441c84a05040d5011895050008409281810444160103d031004a40501803503500d00080c002c869101644150501c001c005c560401c203081400280003142103230342c0307446404c219100c000041c0c80e102c1c0c00090b08030a44c2424040c4d032017512801e00c014064030380340010141d1a11180c110320b40d82207800001003160f60500300003800342480001a001c010b9690b40e403040340c0d111480e00030401a4040e004420460120921881d01200e4100d41c81881c000e1040c0e41c004000c01c104140007488030340c0741506c0c4140f04510308800280701000000081c803120981000350008409902942042e403129181440a860200541c0c240c009000da04a550b0344503500c0c0164284113045181b000c9202c04110f0001c2c942d4803903e50100a12400e030300910410340200b050492550310f = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 147854226 1250 147852976 147852983
    0xe03010c021e10090809011107030503030601051303050609070f06090b090f0303122404181101090b0a0215010b13031e021305040203010c02030a08070309030e130507020d0c 76
    0x2030a1508284000d8a15200038001110240c079000c1d007503c000310b801c442d4440ca090303070b40090100b400d40140d600502d469889814403030040000720300e1961030f140d40380f00007004a410400b0106809001602490003a4080d40d800401d0700c0c1c0501d00001ca45540d964284030307065002d0076081000034460b001c0c40612040d5201903a100d03142018640502481c030b84580981a0184020403060b03c0780700707515005500075150748030310400c030116107480782114900c00080c2600c0340e8907004c030906805051142c0603d245030702c003180e10034a407260030060f200054141d10a48203200000f50303049002d9408038059400812110301c110150b41c03640c2c0c0d20341d21405814900b04000703620301c00502c02304403e500d08005281d42c800f89003000040c2c650104107401c003075035441031a90340c94000740000c501e002e000740b0000400f20f200442c10103040c0180102210070181030f0005166494060005043c49511800d1042c000038044200070bc2c0002d54074001030004450803001030048003d0b00d8405072290740903d2220780c0 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 147855476 1250 147854226 147854233
    0xb031510020714010c050613020109060216030b090a050706020c030712050c0904050c060d0204050a08030a080412020109140a020a050603010503120f0408070e09010614090106030504030e0603100302010e03010c02 93
    0x14a4803c284642508010714140101c1c8000c410004034200303d4948070b202402c1e0191203a01003440094050300568200034250741080ca00c0511020800c040e40d000c0b00d8100103c1d07066510f0b0240c034682401c03d820f00c0600107010310b42000c40d0454001403a001c2c9141e0036070440e1000303552604800d20784503000fa8000e285070071450030000e6034600402e0b1160014000c60039a0702c101c800100160300c0f03600c42e00610074011340100e810015468094000f900a0290102462404000050040a8a400070700c0201100010800b10f681e940c801d40c814008203074000007166000d03000104180c0d0340c0104031001c0344a800b480c100440c00381070003819241200d0b0054003d0450919001000740c50750418010340d403004c03405000c0056140030030400320b0000c0c0051190b5210038140000c80d01d081d40e105030072640000ba11002000d04a803600a040741c112099454005070700d444600d803c4071600c404106280d0300500120902103810400e48045089034402d0b25244900800001498281c4001030b81e6039001d41c1 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 147856726 1250 147855476 147855479
    0x150905060a0c0803151f030e010209031f0b040603080c061302030d0e0111150106090e01030c03020d050c0d0503030106030f090c03020d031b03020105220b0406240b0315100207 77
    0x801c100007558011898101e05d181e03850800d000b050f50a10180d00340740c1c008a000d0580080d0903094840d40c1100003220000307614101010300425a80c10031521070040405120301c507211411a6607000d101303403250081041c44541c0e620304000c001070f0820f000c80c000c58010400410382018020300034150700e0368084c2c0501350114074100c0a0380c1c0d14054121503414810507480c8418029024804901c40c4c0282141950940d410086c000b040181a40c21205550f0742c080014000b1520042070101200e904646544400d0068981282004030306031090b600200ca9690721010030401101440c141c841d15a0204000c9282d101042e0503030b0400200901417004841701800035050042100560b14003d00300602142d00400e40081c00c54241401540140d54800a024030000c1c9101520502e91400515032907140b881d41340c01000c2503014000030840d81d941c1c086c0c0034030100751059880010300260301c81d13051556620800606c662084644c0c00000b074800081d20303464500b11049180103d160703401090355a = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 147857976 1250 147856726 147856733
    0xe030a03170c040f03080d0c08010810230a0b09070201060e0109020f09031501030b0c07020627030d050405040b0901080d0f0e04020304030225080d030908040f150905060a0c 76
    0x2441c060300600303003040c0400c4041030301d4420001c0c8000541c40355218982e200d100c549804111080704402d6810003094600411550700c0020720161f80d1002160001140422440324200c51080303029884d0311044000d00b00b00349540c0561042035244d01c04e640c86142a9035810b03080b0b080315900d000303504401034401d0052140401c0c07903010300040801041841e260100c80c80000e0300e403888142302c0060b41d0f0b034610b00620401ca10121000d0304143c2c00840d45040c03036200d900240c61802a0b101c001d000c1510b02d0a004d41c03015440b40c1444428070042d0907074007001080300d002000360380300c1d001d4180501c2c10120303030480380d081010381c190489442d10064960103012403000c5034084402c900000030400325011044041e660b40c401580210701c40d070000c0203921000d0031090710114803860b141c50f420074030a004100059020908800c0e00500d4500020112203614200c40710b8040d03034011072883d00c5081804201400100e880409400450f03c0d510041c941c1d800801c030355440390000400001c0c01061401000 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 147859226 1250 147857976 147858017
    0x11010210110a0c020607081b0c012f12040f060e0f031c0509041406040b04151703070c0f0f14030309060a030b030d08061801050312091801090204060e030a03 69
    0x105100400e81032500030140c547c91100e030040460790303001200406031030300907010030005c81102a4081c2400c0f08610702030801e08600ca61103c40c40b510460342c0000c0c0841c5001c05100d0001e80a54014080f600c4030746500c0803104034400ca0146001007031403003100c0390b000e1825a106c2c0e00b200340f00400820340e0084400160b14075078181c4050348240074051203000c171a65502d020702407003642c14440b510800d103410b40c108400d803441484a10b00513032500d83c40c0c7c0100a01c415840c0291294249007010104006a00901e035208811024045008a004c04548540e4450700602141e18984040c4c0c2e1480e01c500c811212194401500b0340d0641c01080f181d0403e050540280940000500340055020032010200f420000380e942c0c0302000130100d5013001681d00d411426200070b0124070400d84095070412300805e03541c205080c1c4030b489000b40858031084c1e41d80c502020400a00c0002000320b503959481454101179000360040301c0100c1c6802c0282d000314180040c50702d042c00d4059031801d11000e20700490604 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 147860476 1250 147859226 147859247
    0x602010b130c052b06090203070c080310180501090e070f06031d01090302010b040c0e0a0b0906090a03030c051212180102040506040821070b0a15050405010311010210110a 75
    0xa00c0410300c81030624203c101c02d0b038514411a90308200130030350003036a18005c0b10a2034014a04092041c01403000c0d213603000072000c0e10f060f8010752a42d500d803190040201d489206078408522030200c100c03032000640c00da41119048a0035048140580d0881c14045601c40130035005804031030615060030040c140c842e40044690440fa41e1a03020101c1200b8055820f40d4000d076030950240c0e448540c20052400c03d0300c00e0360301d08005464003c800c00280c20010301c5855a9200d070703224803040401c8405003640d03224101c030780c0d404000f413499447c3d0b552843d001d00305801c42d11040d0b40e40d005548500e00360115040845800201401e42214241d84280428907645140301104101d59803d01000c11240c07603410003070010b0180c1d50001c1c035000ca003144825100c0d15070035004040e200002c1c0070903400610000c4034650480303000013000c00c1c040140caa003903001841380c1c4e01050f481402c3c0700000040c041562035958000c0020b03800d844502c1c40720506081613a200c1c0c00c0c94001203000304180074138203209244002 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 147861726 1250 147860476 147860501
    0x405150a0c0f0f030e01050913090501180b010e01050607120f11030f13051503040305070f080f0304030f0c030206070f11030f0a0f030905070902030405010209030a14070602010b13 79
    0x314000c80d4640011421030030004540581c3c078540940203154205061108565092a045140418100c00304004280e4403010740c8440d07441e00d8007070042110a41284054808040748105801582d0402d840d4010083c0308203080d005480c400414181003104c2140c4445401507a840e44100400c00100c0c1c000c100d10719404100110001c2d41001e0300414001841800460000b4580b1651003a21840c03e00542c2c0d03010b10b21547c40340b111035160541c0303401a00d903c50b4040c01c080791113400c41d0900340c1c2208442600100303049400034400f0b2048038458080c5020383c0c044da403000d003d5089000255968802c10f240600960300c4000054002e603ca42c198800065103132a2202e100389462000e0b40c6144c004450910600101207035195903142e001c0354a85940c065840d01b800380d2891922240d44881d202d00940070415000800181401402d404807040282d01504940c04100385003421004d6015860b069000f03070007a0380f000915a441402003880c0d50800525218110311140e8580b0010000880c029 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 147862976 1250 147861726 147861737
    0x12030e091e011719030306140f09010e130807030201050103030e01030911040e01020f03090a1b0e01090f111809101a092e022802100201060801061e050102030405150a 73
    0x203200f1205040c4c582c0901a209840204090b0f007440710310400c030b14007121158000e0314440c4410403550703034942050381114803280d072055042e00c0d15280b0601d246801400540824800a0020105a070546c001c0d13041300c1c020380d40c90303900c0d2001100441c15500d100301c000d41420180701a110080c642603010084101e0326400062502611440c2c019868004481d410307a180c014070801c40504c140e008410704003002a042d07000c0d150b0700785482001910320601480c1030301e947c1c0d01000c1907903015a40c040480d007480b462010340c6031a0003c50346600d0f545d6030050309000b184c14101161003802c1c28482d22050300c48a280c081c1c0c5403030040d940404182c0001ea10b0603480300001025200030480501d1410302000040341504005001e4500a49450340304802644c50510504005203c081d580302e51605407641203d0300c1042c9604410204d000d032070380340c00c00f0840394a042000607036110390129a194058500d04490011a600c100580c0c81e401a8070a5135009a0400603410102c00420010120300b50a410710 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 147864226 1250 147862976 147862993
    0x50604022106010918020d05090105071e02030f07060b0f150403030305060609040504080409050f15061308010e0a0c08030703080c0d0e100e06160912050712030e091e0117 75
    0x2081d026845d426124045c1940c0010340004440c400d0203400e600030241c5000707001e5824490720041518143d04504244148011070103903442c0c1c42402201d84030014904101e072156414142107004104052945102e055510b6080141c0c3c2094100100885a9060801d00705803451303d058014140040550b50310003801c01c403800003030b5a58407400e070040e401600c8094840b41072500e41012500040c100069029400c020007200306405018401030540c203891042e04c0e48070080340c201001c0c6d60380d0411840c55003003094541100b6800200d52107814026400e01403000c0e600c402c60341d160320038400c3c0070f00060200c00c006030215450302c0c020304000e00072b0b0341c0014160020b1800541042c401e03480a00c8a251030f5645842091800c0251603000107801c81018518803614001416200c0c0c84d114010181c40300030f8032841804401d01079200241901c09101980040358600203003102c04c9102c240d481401d071200498040d200c42e04001804aa542240c004c560b401e0420301854101c906001003124421408c0 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 147865476 1250 147864226 147864239
    0x280807030201020a02060106170402040f0f06140109050118060302070c12080711041e0c05120c03040210171324061401020f15041103060f0405010506040221060109 72
    0x1489054025400140c0701c0e440c000d8004d08203035043e44485c0030030081551080d40002d41d40c26151300140d04071400100c21546008020241c40031110f0001014078203440058000b2001e401e13919281c0090380d0b4811510385500054030700100c007041c401140b0708040402e104481c040d500030200580600800e200b4196500c0c2c42980440c0b5504080720542d101207601d4040043d217982c1c440b40c4803404c40b020300981a1031624401c2c0c07109444121144c1e162034400f2500001d00034004c45444180b080c41c5241d0301d1600101e80213a0b60700580e01280a000c802d0988801d441c4a60b048510714404042c54669503245d012224200041ca10029140c009540d00c4062900c0004419041c00b0030420344082103080c503021440c0c05814040d00181e05542042082518008000c51148400240b40000414031b484904010004031542c490041e01445485d0500c6010503071903c01710f106d04d100f00000d020940c8d500d000e03c070513402590b048075001410600e41d00c2c0c0c0d55951101c2264401011300d407500760300da034454 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 147866726 1250 147865476 147865493
    0x11040509190b040212070f0609060c03081f0f03030c17030603061b0f120613060b0a080a06090207031d0a030b010b030702010b0307090b030106051014160b0f010602011d28 75
    0x92010001031000e26040084540002700080280843c0c00d00000309046528007806060001f0000040d500c61040000601c2c400c7d244003001a004e80000300441d01e8a900c0d000e030910307130030950603104489455017070081d412100e03040381e10400c4054050143c9072101001148800000303d06982110002d0107012a0f640c90a009019074007049549081e2a003810b00910084210b0200d000c60103d09014081c0440b801910417105010070320300e00318407150b588000c42402031205400000c04240006400e06c1070540c01100e060a0f001014243c052908900301003003130b90062844018050210540104060b9800c000170310f501101b580000318580b00031400090801c0d07401d801003281150f9914100d16182003d01c00d0318080c0606039900004400d690b04045e20901c280000030310017581c000b40080810300c00c121040d601c10707401000110f0500b800c5181c05102d00d424024400150300e000d04000804441d901141c40d0400c41c60094440d15002c42380d0368140c1011010700703580c07940c59200c180d0006a0040c = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 147867976 1250 147866726 147866729
    0xd0c031e1e02160501180801020a031d0c0109061d1807020f030c0c150c0111030f161709151807231c02060711040509190b04021207 58
    0x641c0e640749880480110810502801d001100440d0712956100d5000504600c6107015640242410281c07025152042c503440c0c082600480101c0d4008100e100680f074241d0032260104821001c10083c500c4024046650340780c84000150000b07102d8030042000301c0c003e04400f1a80041008800c000d0f40e00741011412002c5650600300480705030a0030010b14507418070150380c01401c5440990300d0b0400c0d1140055035503c0e07480f2621710401007170348010143e00318401200c5a1110303030300082c80141b10100c51140c064004548610309c400440c00060000702211100c0c0d8040003054a8100b00502d14040c2070454410082010b000340c41295440b07084c00481044c441c0c89080161000c001001035684130310304040d0f4660250300b480200242804550b1034456400c80411381c02d51b0014100070b070b45141c0c2403058009510294000d80000784950a2140c0501d1910f0300079005d6806000340d032a01d241e0550745000c00d280c03141d421403401401c840000c0001c07050b580c100f070005103220300d800400100a410000035 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 147869226 1250 147867976 147868037
    0x30b010e060a080702120a140a11120a0306050f090f0c0d06080a11042d0b040c0509090c2106040b03150414030a0c120c172104050d0c03 60
    0x2120420404075810401c01e02420701b0348580a00b007201c001c902600342145954102c03078000e00803c11414152080308096211404842100c60300c81c400c4201036456404134541c81e001909107040407805061091409049410140000c0e61603640c00c2000d071114100038082c0419170004000d5100a541140944405801104e002d40106049894108421842d07480c0103806603050a0084049881d0b61546201158034071100c141e00c1220320f0120300040207603c10340d039403007881c0028580000f6400b1002e8000c1070800d541903032854484e05103010f102d00880c1a05c1c0c0c20003001008e549007001d11046402e400c044050b101240442801c0e0009003400040380c070703c80240100302d04210610000102850040200002562511142400003001b504862602030f103a03210300c60700149a184031b00700106c02547c21069515907030070310411030030095000d0b444100d00f64a200c42d11000003400289a0750041c3e510800603c06240c40c110b05441c0503240b03d00a80620103d410310010380304202c084070480550 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 147870476 1250 147869226 147869237
    0xa090203060a020a0810140d0c150807030f1a0d0305120a1e06060f111507031a030f03041403030708041203081f0306110d0908030f070c0b0106030b010e060a 69
    0x40700031300180341580c020021503030740756250030070003030070f5190798503404440307001c0d220024071141900b810080c004090340b001c907884034681c030040d202030791004015008013520380e030501c504600b49035090195240c07540079000000c42c410400d0028070f0a107010102084c824244203042c03203d80107030124048401c640c01d00c0c280d504c403841030800b42d0220300c2c086589114488104001428000c0051108903074007601e9052244903850403650f0042000079a0141c1c41d40e641821803483c0041e0002c01900265000c40c1004028290f40b507428034021888082e01a003980096092526242107803505040703000b2070542601081007103101180e4500010005001c111200501d0040b5601d0028000b4000034000c600700c0302d403030383c10110704840c003a80782e42141e400c5980440e1042c6214001c04061041c100040505803030440101c1c00c215509010750f05c02d01410411640d00d6907904c1c410703501440040001001980e85070f0041c0032140c060743c426100c4810626000c507846d064800807138000c1c0d2180c40000003095 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 147871726 1250 147870476 147870487
    0x1e06020712080306011202040302061b01180b06060304060b0a0308070506060f180402040e0f0a020901050f010c0818040911040510080a0f02030312011d010803041802030a090203060a02 81
    0xa404104410050903038500c594003189494aa200c001e010140200b8100300c0030303c0041c0b01c075941c0f640551700510380050890390740390141d964450320040e9184c103000710342d424081d403032036204a400070113107000340c000c0c079a0140c580d2010b04224071903200800884409544484034400c58039201c2461024510840000ea9219502e0501e80e1500354002c1c48248a40c1a80c41c2100050702c500b4000012a9101c0e84c8800c2503407118030016001d0300322041e5600c018070404200e0200b0030400074a81d80514000d07150f1040703503603d5005100000801c0751002d804100c1a0f00a5800240c2181c000d10304140d0a05004030030a12460008003a1184280240c0d030340d4802940d80d8080703141c030344601908801580c141005852800e121a40c481b51000009002e180100700114155202841219045290000c01404030b46e154072480d52200e803a1016102d1f0030140d40004246100d0020403181542d0040d11030000c001d002380340c403a01941c4010404802203850340700303240050310308001d454000c0c18035240158440c1d = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 147872976 1250 147871726 147871739
    0x15060d1404030c170901091202030a050d090905180303040206070f080f0c160609120c0509040c080d0507080d05040f0203060c040612020403110607021206040b01090f0209030c060a091e 81
    0x9591003000310b42c0103801080401e04130380e00047e400c0111002920303440e252100d03900000e81400074060300949580540e14083c41e65640c44010130303003541d8484504115a884144102c4081181004500001d510400100f00540752a60180404920a5a001513112107941e100101ca8100f014442c00e03481300400c40d10f110520601c0344c01e204404145c0314200e010720b050b500034100410f0340304003660100080d80d000180a030070f8612002a001c040c02000c501d081514200034901118850207031503000c0c00340c00e111014442c0301102d480c80c1d00403842074140807801940c54000c0101070000c075007040c64440d001006807410b1100b070303100d5802e00742081d0b1282d00c4c0c11406031500404089942400344100402e10029604925103141c0c00e1040d100300b0389400803440842c500c0740122400c03003042c0c81040304000411400110403410381d03440220600080100d108403005900846074610b505070800b00c2c0c62420341c100b14001e02003070202d0749010211103039a02640c50034102840c2c05901c1140d622241070020 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 147874226 1250 147872976 147872993
    0x318070915060c050d05180d05030901140a05030105090a1b030902030c0613090c18080105011e0522020d02310e01090507140c0a0c0e15060d1404030c 66
    0xb0710711810050124059551101d03115408140365030706102003c541e114207041e8400c900b04c81c0d82400341209104190906000383d60390000c4403001d000803a000c901c0c4010b16000345c190b0b40000d0458a526046d64200400c014128400030f040c0070301982da5001880c0e0b080c0300d441d552903070b41c0001d4030009040683c074010b0508005e90107042d030f8011542042001d0350030202d00d80c0c001c1220203048000450b808207282c12214101581003030900a07850400c040b5003d081948002d048400510900303411200d0300d449529a18242d00c50268030400a1101035640900c0aa0398031040106d103034010b10b0150074041c481c0880e081400381c04005026020490300740144040d06000f100035500034403144500c0c04080f00441001401034001054960b0003140d000b600802041d00e1302495040c000380c6403440000e080ea610140444151000c2e400b000001810600f035021883c000c003504070380c1c40500070741c1105010307941e0302401d515140603035a0207041080022004182d40658800e5070f50040781006800c05030b45 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 147875476 1250 147874226 147874229
    0x609020405091f0b040b0a0e090d081005040906090b10030b13020303092101020721030c02060703090305160c051002031810030e100509070b0f0901050318070915 71
    0x1c42e54015107080341c0b0350180c100703411401c084644001c90f401a086001c140602000ea842d1313a08016184004135080c2c94128040e0711032040e03041100d24003076404904440c1101c050302e010141d940b05136824003650401e600090420b5000c3c04011034208915a142034950500b12486441c00c0b601102c01d008000d010541260086440200706080c0800c41d0002a143d108018a062280802c03078920f00b2000003c81390850300310404002103481e0b140743c0c02d05200f8800c40f542034408050310920b400c42064003a20550407803159550007091199107850050740103184928043d024401e06216491010711003841c0c02c0a4140700c0c0300b04004203441d0034103215075000e0b02500641075400620103000d41141880092040d030400311410325103003e0002c02034000b0880d010b0701030014050100c0c69030020405410460041940030102ea0301903580721110388140c00b451113218114403040081d0280b81d0b20800180d17800c00d6190307800c961074024901c010b6207040001d134070150003140c035025040e20042c200c140600 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 147876726 1250 147875476 147875491
    0x5090315010e0c03070207180204050414090a110402040506040b0a020105071e0c0311030c0d080105030d080109091e0506040309050607020603190b120f0f01290301020f070609020405 80
    0x14035541090401e80030031200a01411200801000250389a4401c010000050414810040d141015400ba02010350701a005d040d009a042003440c41c01d900b4118a8644114001c002404101946960344813a170f240b040300855005400340301c04501039482000500082c00725070405643c4480c44080a03080d1100100300100b40315000c031792041540159100e081007080d02d49410100b031002440c00350343c964000303c503030101c41c800414070490321103000402044050051702c440701640e07614400c140c2c1d00c200203100e8400242c5100c0040102180d6a081400310a00c9201d82e0310340c90000b180c0500f0b480d0481d100c2501d56502c2581404103254020141e074000c1d20043d40c042c2c0c41c0010301d13000b01c1d026100207484002440d134401d00b0908043e03800d0380040c0301000014020000d02d140d0306c80165962116002c01900d0340550007402120704414032502904000e50030f00300100065042c6030080c007a03101c40e000e0380c00d550204200720240d900c56000b40402c80c812440060000ba06005100480c0c0b0b0050040 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 147877976 1250 147876726 147876763
    0x9070603020f0403080729040203010522020405151f0305090a030c02010503060a08070603020a030e0f0703030f05040312030911090705161104052809150c021606050903 74
    0x20340c04100b2840c00c540541c1d8015050369a101c2151401007018180e11880403d4400d030346410b20807100300030718250f0080340200c001340031648620a5080760300900030101a0395a5911013490010306054001961040105031000160030b4400d01062420a5244040c4100a030088100803240d40600c10315810814803c010141c80340d03036035009800000700c604080e05204d07021001600c0c2c0d03aa4500170401510490040d222119590b00e0040e0103504075120b4a00464146865121656070000d00380c5ea83e0000d10b00188000340c95a2004d9950b8250035501d142000001c0001002280200c222424520b41983d8001034034281070600c0701c4180858600280b00d070200c2014451036a91143c15541342301416201c16018024600e0034800360000c074003000d0340280c107180401510303c10340030552006241c2c5126020b001c2e1009241d80c0f0858848000080a002e840040c108480f0b800f07520080c03804c012401140ca581d400b0689034200c511059001000151000a01910030f05041c01300003941003800c43e14 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 147879226 1250 147877976 147877987
    0x10050306060304080c0307050111091503040804030201110a1b061103070308010e060f0315010303031103011a0d14040c1502070e0114150d050a0605010c080d0f060b0d050907060302 79
    0x7080ca1101403c0070b05280b002154002213084180100c50300c044d032084c000c000c41e521254482080d9000b003214148181070081050008814580c100c91090b54015803146c5818216401507950448020200903d4450102484001b8201001e00b500040e103442110ac03450703140c004010091408812000150342003400b601001036004102a4191002a0360641d04d5070340328070101e441e0344001d19249034940b20b003011400e40555640c80c910306a134000c0d5014403500c05101e0010f082c6100c00c0c4580200604408500d41c41c0046010141003921901c0c00d010484010301c3c0022450404140c405030703009004100c04114600348150f500360080e1482c006062202d00d42118020221014412107541e407000440305e00e482e50322601c0c030210700c40b9021055506c42a0001040e030046c982219141d94880c41c1200c08503044d03000d00d944501c0607511555580c0781185c5c0c1d2440c500a00600030030031b40c200f904c5000208003900c80d14041c3c01200c201c9000003800d0701d48851000d01d00300711a031260003410b204004 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 147880476 1250 147879226 147879229
    0x11030d030207111002030d0f06080706020f0a03031e050f0a050a0605030d270e0106091d0103020613030501060825141009050a14030d031401051203040510080610050306 74
    0x1103c3e861240f00315441c2424014046040e4103611451448000391741c6403000d400070107840f9912080c02d81d4205001c450090b0b4907410183d0340d0b0001c1e420303488403903403190380e0840c0082e1094001c000001003000310407038589200400d5034107446003a00c14522840ba01d02c10404500e160f84a80e541c884115041440024601b0380401d45813400c0e00d50f01030400c1030300d821360761240352400c211014000096820b90000c070766a100c580292842030241030001008984002410402403a5041c42e0b4a20345080c54200e91a66007000050750022002900c0d4980041c000808100284600c034010031080020341800100a18804405480461495602110300030148854280101204140c8005803841d03400c000740404242e0f2841d5859005030750042050a01007402c81356105070303501103001542140c4207124080001c0d4240c50210300000c0320b10085000411041c60700d0307400711b929a09080d0540b4641500c400106240d401d103001040c0220f190101402801e0804100d06c1040c0715107440c100d1b095050010 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 147881726 1250 147880476 147880493
    0xd031d04050420060c0a0c031509051f14040503030a060b07110607021206070521151003090501090821070c031815080103061b0e04050a09080711030d030207 69
    0x8000e00d040c400c41e181401c04a44968048505060705c0c2c404803940e1400a01d8428102402c0340801c46100602c100c000140001c03034040c13645000d6104000d000d000c59050085044c40c2d80407106044c00d15100c0010203006210326080d2230285010300060765987c0b8148c0c90101c151001640302034994a8200a01404105c20303454100340c620049800c140d60342039500024000c00001c0070100c12900408052001640d080801864054a1010905010781c0c0d4541c4600805070107c604581d042d0080000f880740d807034507440c6220a0049420001502101901c6403070841e80c03001170480c0c80c000009000301c200f201c000612035000300303010301c5602113140c1340c10020980020020020f00780710504600c0841c40d0107603d0b180c0d0140c40e1008503202c2c203680c1e00d903000300480c4080c0300c03e840c0b00d4681094010381c802c0e060301581051801c2c0e00c6158403140040c05010003464010043d8003119964a200c4000030402c20090105a00074840b10315a00360322020035080170416840ca1b0141481084014002000340 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 147882976 1250 147881726 147881753
    0x9050102031e03041407080312070e030d0806041116060b060a050406030e070b0c0307030f020f0717070e0c12131502092101020706060506030c0417010b0d031d040504 73
    0x102d0754498866150850b0324070b21300c00d0405c0c0580903034180441c0b162000805440c2c004041c581c2141951100901911540c0b1201810398068000303281c00300380c0d24000c0c12207541102003e000016100218400d0203443e800c00c080b0103400b910191041c2c010710001d40141d08446800301c900915001da260400303030140c450b0f80720350018140c40c0c490601e419071003804a00028416241115503582d98003039456160f510142c001c4000c502c624410b26a001e10018601c8801d03112080100001070400340034803504400200c0101c5284030342440440d06640041c1020f02418240f041d03a5150b14084a00000021000b06012000c1c01d100c100c40c8085248041602031400d400700c0c1c0180e90b103542d040810043d61148402c3c080f010102c140384e0300c0000c030541c01008001d01411080281644078401c100b0248025221441c5a071030901003880101c2c44118014020308401c0300004030041d001d8041210010540c0044c1d001c24640c03141428139221003004846420000c403020001890169034030410785100 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 147884226 1250 147882976 147883027
    0x1110715180e0a05040b0a090c050f0406090911030706020114040201030c05090a171203010b0706180b010e0f07020102091008091006120c0509041109040f210905010203 74
    0x104521501c0c1d5000d51841201070808005203616501c1d100c91100301410064070300f1075007032603501e00142041c0c90340d1081040312980002c0b44019545884c0c00c006450b100540b07929403040e0354400005014101d4420076040e07510036a0014142080031007094107020301540100c041d6414aa024040314281e42c02d1140e0043d0309081c0014510b241c50411a40340c0202c081d0203400680380500032441c406030310b0303018084001c010200c0da00140c040e040d003201400300703125404c1100720034000c00c0c0004070a508452000c4014854040c2c111050317454011410700c081c2c1c0050002104081032200e81003070541c0c0b80b13a00002d140000d528041e203500104050380041c841d440308000080d0086425080c0a10080351040e10341c4030240542e6484038504a070703030020304500311a2021054000101810320000403403017590000001202815507000b0700010600040c000c036000604003034400f0000b892003020b4085251071140d02006004c0c40000646401050341220f0f041d54414044503001800c41042028803414 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 147885476 1250 147884226 147884237
    0x40516090303050d1112011712180d02060a0e040605040507021905250504050601260402010c080c0a030801080c060f0c03090d030f03060605120a181b0501110715 71
    0xf03154113000a1075100110755040b4000183d01007501400d50200f0b060340d40181c40e4000803507115100369610b454526044800290902c00701418080c110b0350034000300e00181041940f0030482c0c1c00034100317138019907052000c00c50384581c86c10681010f103e010041c0005807003c101d40e051184001e0b5903503940f9143e001c29400c00301c2d05502003140502890310b03107451242d5410720302c61140210041405850068900841c0b801c00080c400d58858001d03c41405043e1040329a42c01c04848546c2034448024010303414407504404510000300140002e125511a207005403070421150b240c0141010410f81c800d41c169400380180c8030150360b43e4422980c640d06640d107003e80d641c1880f03040b24114004c2007005548211640f101009040c0c00095182030702c101a9010400d0b075881e030900f41c2d12401030404030200c50b24010005440d81403580e1115800321106510a039240025980744410401e11800506050248941c2041556001150031a2003103000024198450911900400c0c040324200c10004000 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 147886726 1250 147885476 147885487
    0x702011d0d060e0706272102090f04020301051008030306060d060e0c0a08010905090307060b01050912070f0506030f161e0320090a0902030c04180b04051609030305 72
    0x141e46121150071954003a200b03201481c414038645498804620074140801c00c0c2003103884081411a10025140c051440250309190418a82c425190040c0f00d82c0c0300c1c481c2c10b45000c107000d45c1c1e40141d4184600c40c100038514071450b140c410b040c00d454000e001000c813000d4009040c00f002c2808019250300203000e40d8140d49a80c40d01e09034402a0070310b0b0b80800405c01a050a010106180b20000c016440c800c0d21030b0481e5036038817041d00c000c0b074508940094550304184613410004029070000000ca510524000d41418001000101d902c00303222101c0015500002c810400701035401d00c03040082c04100d919600b980b0701524421302c00000200424410b202c4076181e11141806541511000c0c20895541c0610644203038000c0c00424000301240f40d007102c042c055908850004085030702e5014080d04001c1881d18080d8004c1c0a90009011121045e000388000f19014a00220b0380b620307c2d00000000c00c101d80e90b4401d000c1214409860720800c240602522441c003508000d00d40e04682d8540b40c40c55448 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 147887976 1250 147886726 147886729
    0x150307091703040f0b07020418030207030f0c0e090708071409010b0307230901090f030210030b0102030d181a040f030e060d09030807120501150810030203010207050a06110702011d 79
    0x10b11807a0130444078404d4042000c50704c00c00c2500581103241c803e490030800c58450700724200903e003070660001c0060340311140501c0000c8200ba05004582c0c4201000ca546580f19a03c0301004d43c411190003800d6480321408100301041040604001c00521659044210080b408100d60038014000c00b034828100102040555125910a0070414402950a0004501c2072091811540b112003400d00041c6c00700b602144010b12038008201301c0c1d81c010f01a0720a01e014100a03000f07401400c100c281075010500400301c8111f881c2c05021400c1131910b0400079104403900d802000043c82d90352032411148540308003c0050b868100319000141c041c10326005485c400b6000440d01d100ea50056201c89007000e51006c01c1540024646020b903080703444828101c1e14000c83c000c02c070385003403084400410003019070000083c010340300e0036000380002c40c441c0741c0c41d80c580d000301e030a80e40700d080215000d07844902c800003480010300c40d01d5084021400200d240400e03580000700238810880056580302c42485903440c19 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 147889226 1250 147887976 147887983
    0x3040603150510050715020a08040f06060e07090815160503090106030c0308040602010f090201200c040207030e0316030201020604112719060e0103030804141b1503070917 75
    0x1020024640d00343c42801490052040e0002201103809066070301311141e16142c14000d5401c0005166160801503a8a448003800034940000691ba000d90700e40c0b001c0340220086044521609075503c60168091801818074074068203005c1f2080d4072a4403005000d01070461024882111003a49442e0351a41c482d00c1c10321f0300518803540020614045088004200700300780003e0700843c0c1454008100c400d200c109042c054a6517000024002030151000d100b00b025003444a01000c41e80c01c0448003808012004101260b02894042e00401c0340c60345114000e01c0c0c104944500c1c10045005441507901d1540040d5460801400007401c400d55a13006c0c3c540d5860300090100210304042400a1519000b14800300e07200c416030f00310340c000022030004410090f16000b480c0c2299606155916140e01c0c503281200c0e030101c081c2044403d40e90f01c038910310300c035181080070403210301c00c8000a048030808542004010311407445001082101801080929900a98404104d5040c40310030100841a070048509 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 147890476 1250 147889226 147889229
    0x50708030a030b04110717031503030315030c150307050d02160b07030c2d050c10061e08030a0e0103020903070806150d120c0c0302040c02060406060b0306030304060315 74
    0x81500c80401d25194107940340d04500700042c010f480801100c210380b1404606445005005088040a6040304d4142540c05005661180c1c1500c0d01485180030b500c00282140d00594210381180700c4035504110518040c8145d2080c1c0b2000c45500500c910211400c0f40640001490641445070104d46c09200c00b515404442e04240c85444204207500640b801340100c01e016104000001d00e0705490b500d03118003900c0d00c03180959a181c014030034451280c1d907500b1003090420885003040418031400d414107904000101c4c0701e080c0124085001401e0141c0d0300342003900f0300608108403c0b0301d10208180d41c004022160560401d1420780482103042005802a00c070300c1e03101540600c90307140002a012408941240030701100642e40c41c0308080c0a081095803041c4c2c2d080a0541c450112400751024000c2c81d500f100c2d20320401098038050364070740006003283d103c801c49001581015007040100106441940042c081440100d0300b907003041c0740404c0d641c0c055405070100341a6034080c01c0d104080583c11400 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 147891726 1250 147890476 147890489
    0x80c091b0d0902060a0216060f0207140a05120d02060702010b010e0904230c040f020406141b01110a080a051005061605010507090305070b030106050304230109050c1014070f0507 78
    0x180d0742e0021700307402552121007100c428221543c2c81004100244186005180c06043d64014592541061544410720f10820340e00742d0f1054001c40000b40315110b500405c0800005039029010041c01658040d0800000900c0035046914140d4090226031700400045c00100043d03070707118007954581c0f800d502d4400107640c142c0541005039518a2a65000040107816403400b51070602c21484c11026480903801a030040c10b0104031320004855040125501514403105031040c0c48403d542180c00407402c44000702a159800c0c040043c16058040d0000710264000c034120b04c1c1001907280c240301c06001c49070749016280c441c40d0b00080003211001013209400016070400e0007004103060890003d0810815440125684c1c0075003807000401d42d24000680f41200e03525141c1618682e900d5449000300c511a0b1405d801650b84080e40031140582440b5155103a44110014600d850300e030010081c510350a00444420041005600051048a10f040c4c61451740c0c000c40c2425950301500e0150b05007101ca82240 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 147892976 1250 147891726 147891739
    0x50901090b180d170f0c040b0c1501290a020c03030d0b03071e0501050304080c0a060b01180b0d0504050705030a0b0109050130110316080c091b0d0902 66
    0x1003606034610b040e150110111100b01c0d00d09201d08202500c200d07030200e0a012403030075140c0005003402d04840046602280b100c2070245850f49070080302c017541c0c2010303c403814a0303844044e083c51230000340f40301c103405048030307114000d46500c9042401c00400d0700180d42c5241d1140100345115268000c000c0c505602d00c004080d280c440e400403900d6002001d403a101c0a1280c8a11070002400c0c2002400c0208194041c551142c02a8100780064403150300140c01200d0703800c4100310040c1c0044080c04042ca010307100d0709011685080c424001000c0100d02003900f8000e2800b036800b08100e04a1100705d405030b81005001040ca559182002414100e941c1d000d19058015000100c00b04104401d805040c5e42040300108900d1341c85404180701e0928208030154088a0b21190503101309100800c0b0b0145442241688800341c1c1000110342000b206806210131070901c10401d0020760018450004820070a45801c00b0916040419110100078035a403114000382c00144280c1c10302098112014554000c0d02c00d = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 147894226 1250 147892976 147892981
    0x9020c0c040906112b0c02060f06010e040204060e0108070f1d04060e0f011a0306010e0105030a1116050c06090102280515070f0903020a09020d02090312040602070801060b0d050901090b 81
    0x208040707104500014060034034504016040c401c1c1d06d114000040ea0140e0040006580d03e46261102000181030b26050052040030429903940e580002d101806d51542c5100b14103590303100243c038a03200a81700303605201c1c14030740d0b0307961040e40407500c0c268803511310705070807224985400800c00400d00340d0003001840407400100f01440441d174120394100c0e41244540c008120f896140b01505000c15142140012820702c00c044d11588620003a6810004010000803051250450f60800383e00a104090070680701e00316204c1848070070311442203680800d940c03086ca0301e424800000c0d280c141d640780084c40304500c112801250080005085211039110341241c0140e02c0100c14441418011100000011442c5925210881c490149001103030380c050500704800c1c0c03c00c030303117040a50070104450440541c2400000c90540d01001a03490784084075031a15903c60600c20000d0422445410900304caa05100003007128004020488cd85013200c004000f52540300c807008503016101048015010504101c103 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 147895476 1250 147894226 147894247
    0x31c3c030b0a090507090f030c05060a020c030109030305060f0303250c0801090803041401020901090b0d020d090c050301051015030b130f0b0a090b0906090702120301030602040e0109020c0c04090611 87
    0x50745c09082c032616482421a6142407130400782c0791900001f000346005150410407811f111001d010010000d0065a1440c0d070b4620200c1d0840d031100f102503001235128001c1c09a01c2c02c108080d00c03400d21054015601d0942e002c1c0c0c07281241c84005025052603032071406414240680122000d01818608000b8415401c1c607040c64400c6410a5806a40004c3c00d19084e10311404140700715820400181c5a6012407458002552440c0e0029041180284e4080200c00d4042c4003d2080c90760a502c1810100283c7e410b200515007183c00003031100c410044401400e010701040310300c504004440c54500820395451480110303640c01d4025600c000340c90304045c0114000c4d80c0d9600454900c120179111221001d580396280e0064404103041e140d001400032000c5004e90030b00c12041079000c01d590044907020300c0407085020066209034026510340d41d0208c0d00340400058107030100d006000c150015070408590032243c40c0c40700400b8003603e00c250354a903a80380401c00544c00c0741140c1d00007a401c19072034015925 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 147896726 1250 147895476 147895481
    0x4031211010605010309051903140c0102030a0c020705150f0f04140102010c030c050f070203241023130b0907030605030708010c0504180b031c3c030b0a09 68
    0x40c0d40300001c0d400e00a000c074695200340f0031102c44075048130051040c2480c010b4100143c030341c5484183c080000300c059008100b41202c009050380c0444a000603543d21780541c1c008111098581c2000854100d64010442a61514160358001d200031001c507644480b500c01e2040c491081c1c110301483d003039020400065060000d402000b44031400e8000340881080250b0850494228070036000c086102885411110800103000d000440e02c05000c440901040682080e040d2200f9403245145a80f03440030002c66000540d80c07440100400b181215900b80414400d0011144048490b805400c800182501518158000e890400070181100410b41000c0c2d1f8010003814441c0901c0c1c0c028807500d02c000a031000305106800c0950810f642d031604003410040e1400440310040c1b40358640c280c903000b2007409a40d0a00000b0251400c050000d0000300d50007101070714281090b080e50f0034200314a148940118804925813034955007a01c104030110000e1031080e0001d02c10f00c1c90340c03600710000110200b10051281e = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 147897976 1250 147896726 147896747
    0x5010306061e030b130203010b0a2709050c0603060301090c0e0a0e070b18190609030c05060a08060108091603050a03021c0c02040b0f130b090a02070206031b040312 72
    0x9004004060400101102038542d6101c020880c3d54001c00142101c1c58a20b42c0c3c0345054401400030508400c140c00184a40405402a100350303c4c80041040310854000711409911000100a008841c031a0b240c46403544455810303d4010900000041c505030380a600c82c00105134400d541070a0603031194050f484101e0226031644d10281790180100c400d074400200304040f01c0382205190300d4100c200074503080da0240204803070740000c01c1d0281000040c8404e00c000d4081c003065511201e6407455070401690480c06540400e000f52001c0101d0764801d40d00405a507842042800d01b03000da51070f11500390703141c16030715804929200b6003003001008000d408160501040d001c1e50031501c5000e0329404548525640d4045000403440358807034000141400d8020000c074413002444c218464001c1c5c2d000c1071080c208900c10700f4a42e030b039520b0744a03407914100111700c2d0000e00e809002c5050240581c08a0641e03c07001e00030b44004034014030030707004075401c81d0203c0e030180da0720140001d161a0394910251150410 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 147899226 1250 147897976 147897989
    0x26010f05060f0109030209060f03030f03010602010b03070506090612060307080f0318030d050a0c050c130f0c023004051203070302010b0f090a0203070201060f0618050d230109060501030606 83
    0x10079070b0703a100c0e40c4225250340c00d49400804510498407207804115a10100186454041c007003030001c0c20314100000080c6000340015000804c4451100081505010301500007a200e26801e0200541035200c1d6810b56820100f030803030140080e202c10300003a203010710a50181c010341c400d03841c0002201d48044098500032092200c642d001c0d115410402d0b80b100820201140019424400108034078898564403040a000d40c0c2030f03646464040300800c0d0a050074806582111b61203505a0600640602c2020151511440900520300c00100c100d580d50408a88200c501d00042c00702000030b40544044500501c00140051602404201d0703158881e0020801940503518111151300c2900b09001c00c00e40e1014000c0a11269035270b0031010900a41010b810101150740c0c1d1400424654a4801d040300030342400d460b0450f00180c0d651600310620072a030485401000c0760050580042c0103221a00c21007616901c5071001001c02d81c07242c1d40140003061002c3c20b02410a0000410b012281d031210003510103 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 147900476 1250 147899226 147899239
    0x1306030b09040b040f06090501050106050408060901051009150803071406010902091309060e070305210c0a03081b1c05010b0901080109051005153126010f0506 70
    0x1000c01080750001045901411030162480000d00044003000b415030101e208600008141c140380d10342c6402c4030001d802450200c3d800003030070f0150a01c1000050b501c100f00d0402440989018403104d40401c0d510b00c101d0521584035690150390300c00804050001c1e10001c001c07640c80e8500c5082200010304900e2150b020780c043c69002040e050514000c91b200b5000c0a014080f0520446881c40002c1c4003034002596216a500d50b6a40d0070201441443c00840c001c1e80100360102c054a00d04044050b065058808040200003503a008507012904224240d00b6040920003903031006520a90314180303004040e005000000e0705c02140c0f001072451040c00403205802c108907070301c600140314240b14000ba0540401c07400303001004400015001168410044071110421558400200d101b40c2c40000f10f0124a600100c1c7e200b003601c14204280009800350118010300b004810000d25030a041400b0348841c50303260091049444016082e95000814014020448500d50210080c000e0005864403480b801 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 147901726 1250 147900476 147900491
    0x3090703080c0102031f03111509060d050a051810050c041215060b03010e060f130903020a02040c08011d06010903080a03090515060a05090a0e01020a0c030f030c050313020a030503130603 82
    0x100e060309400c7e00d40c09030b003050b50700703a070300c410005841c140750342507607200304108401c80964981c0400307440042160300000c0342e17a00709100f002064441c014540007035415808d076401c405030000110003040c10068140083c450312250f030202c09610461b0004c04c42000d0b801d624404110308101c066298101402c010010f00d03450301c41c40c030200c0c4000c0c0320f03c5884e0232085c004141c1c83e02d02152602401200148180d03020300522548200303590162a040d0056000444000154103140c00741160204841c60031103810340c10924510544000040081b0700d403200100000c40c0c2e64000d11265024503084803000b5201c958402c03000703000e80040d80713084a0602030145804100c510205d034441c09540d000f03058400c0ca0f0708040a1000c0c4c0e80f402090f40214588625200300d80da0400e10003064001d0b1160b442c0313840b500e801c4c2009031030105968081030070585002c0e050704078147d010058a401000c2c0c05c0c1c20001c580a80e000040d00c058040c0c102408900001464032841c5010b6514402140d0260303c0621406 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 147902976 1250 147901726 147901771
    0x60d020306121e060903030c0403030e0a090c0504050901050901030b040f0f08030c03011d0c0f07030306050604120212032505030702090a0506010e030a02030307020108042d0b06100e0603090703080c010203 90
    0x1e00003030b6040d08c62040148824000a401084a181400707005421903035810350b0b4000400c107403007800031410085400004e082c0300b02e09021810501620055640d080154074503943c80b841d072100104085c12800c0c05405450411600d00380f00442150881c0c0300b1500c0381818160200240d000b0300c101c2503885000985844c040000c46039003131141105100d10350408a270200007507842d41c88510128100350761840046030603641c00d400ba1018200d40040d0891110051050190841c58494190381a51080c85001034001080902207101103641c1d80c000b075022800d1130007a14600400b8002940702590f44204512604554042031050b0801da956425511515060540350101c00e0f6019405801c01c0000c1e2016502903621140c00c00d201e50032041a00001e183e0b101569820790007010f5420a0181c00d00d4140410711030080c0d0001c500f02d5541001c50070b400070150070081140222405810040005a91706170203015030345c0250740054800c1d43da42d8990000318003e620403500c007003400c002124001c485 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 147904226 1250 147902976 147902983
    0x30f0e01020a050d03020a0e030102030405030d2003060f180703050f010b07031d1f090302010210050114040903030b0607060e0f0102041811070c06030f060e06060d020306121e0609 79
    0x8040c3c002d00644250b10b8407000884c0030350300100e40c1c401404665020003041d92002d100461050380144099a2035001013080a010340d4400c0e0804007843c0460501d84008941030021280c129030101c620000c0d40b83c2034004100081d03007a07040c1a9215160508000d00c03117401d50803640c031928080358190b100343c1e01c071041070210f0b0003106c00240005118111078080f1a001400c401615440208083e079100909212403a60b50140c0d640c1000160900c0400c00455804114144404008500922071581842c1041d0300094075205024811900e440c0b900b800d041c000e50240843c0d14000d0a00c65442d80d00d402c00b00007924001d0003550b0640300708054102c00b0341d018030903142a0307040042040021400390350f1440113820018580c00054400300414800030307448070403110041225880100310303411040240720444001d03501515503c09a007003041015641c0d04100c81c4c0ca0b2250312001622902e0341c4000c00d1450102c46440083d900c9003201218043c000d4000c803110740000741003160714640c0c41e0441c20340c8 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 147905476 1250 147904226 147904243
    0x110a02090117010f1802010302030a0603080408150f01050105090405040201090504061418070e010c030e0303071a0a0605060910030908030c1902010b0a030b04080c1605010908150606030405031303030f0e0102 91
    0x511701c40245108006621a070021a00305001c0000402c00ca920ba4841100380c0d84294028a640c3e40b01c00d10f00000401c91600c2c0c1513001010803125a030301d615040002e8202e01c01e40c0f00040c03046584c1d80c00a001c6a005034541c0c1c000d814040d104001305610360502ca001450b03180c2720703a403003074a20503084107034264404043c0740b0500300c0b13076075000d00741c1082001552003071300c3d08408509000d4083c20799110780d1001c101030002c0303c0c0200c0a14000300c0c2c140c08801080c481c05000090010704100c000d1117117850365402c075030361102e05462181c1c1c0c0a00b0030038100e000b80a500030081074604000103002038240300c074000d8103080e404400c1c00395089004060a03400c07030704004034150700808403800c100041a09000100e6102c2d000c0c0645074a440402035210b0300303120042c50310340d541000d4500700b4040c41d42e04c0b110b10800b40224000804030212108419240404014080340c0300c1d80c4000001800c008043c41601c40c4d201d138001d070036540f00c1c0d2a80b4002d02400900d81000340002d64015201c5010741c40085c8105 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 147906726 1250 147905476 147905501
    0xf06040c050d03140f030105150702010f1d1509010305070801150e010302070503160c2304020a0c0c09022104031b21020a170316110a02090117010f 65
    0x1160910380000d02c20100d60b8200c0a0301408408030070104110b80000c020540305007001c110303603038940c100400c008a030550720102083c1500c041c40000c0050340c0020488002c08024104840300700800c00c00740e8001012900040d411044c41110441c20000300f0015080d000001d0720140820750b00c0c090102c400b1142445109030403c0c41c04c0b00c00c1d07415800b45580c04000203061402524015043c0c4669283d607000441000307102170744003107090500c85200c400304060501d0880200d085c44c440114210b180e100b03110007902c88c550015a2940c0c03035000340c1d10410007550100500f410280c0c0c4c0e41603c2c0007900b1024914000750082e820b5100841c031043c8081e44540c1d80b54641110403a0b510b9075182400c0c0c00e00c50100c40d039051032140d070105042c416522500a620300d500802c4030061742e28154401c042003400540a0407818414460640718540124040d08158074281075084a81031800e440c1007103035a8040c0d0480044070021458855002c15213241c0ea449000070b2007010034040b00f0500300c40f803141005 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 147907976 1250 147906726 147906743
    0x105010305010b03010516050c100501080a02040b010201020c1b0d020a0e16030213140109080102040b07030e0604030507051002030403171b1204120206090909030714070b040b07320f0604 82
    0x1950301030b002d00049c011101030304c400ca03500034420800e420b040710005c6e00722055550101030514214a05801030119141080c0b0096040c10000b14080341d8415440e00800010410710301d86483c45d8480381d00b650501e9800800e80e0120f04c1d610310300d16403c8502a111100d880035454252480343c0d00078021a00c0c40c500100c4000305152800c24440c1c14004203403085030401c01030190003c0c1404007400a040030784074a800c1950389025919000c1d00024818103424007404c0d09000400201d103000ca00380c0c04803501500e83e52013412060360228254803894200804022160f2004e500d950324030005010014100c200e1581e90040000c0161340d10003600702d0030714914408000a00058800550280020f803029020034100303038812000400045080360003410b40da0001c100401442135807900c4250306030242003c2c06c000750405001d03198502c202c0c09101c0d0840b00006443c4104204e046840c4074001d0241481e01d865048903c0c008001e0f00c0c030036040301e005d2103003551200200c58003180f601d01950b8041d081 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 147909226 1250 147907976 147908011
    0x2030703030506061306091e0e18150f010e0703051506090604031a1f0b0304110105090d0b01050310020406091203020a1e0209010b090d060911030d020105010305010b030105 76
    0x301c000d024010000358200005003e00c10a107214085100094226511005601402c0c546058680110641d0f0048490032408007040150000340809411410b00c205510292603a810480d00c0d10f8080300c00c280d03203032103480b04002e040345078180100d06070f42c1e02410001598550000403400c0c0c070009d5030764540390002d40d81e0101003403506c84010311003c0000b0308070031709069a0362610070142100c030400a202e61034110070000d80c01c0240e14840307d007404080b00e103142c0908000c40030b402030100800041022101080183c0c00342e0044081e1103000000501080c201980c600e0030b0701c4506030a10882d402441901c003c0c05074003000740281e5056541c4c035555441120700c7c1c08459080701280210039001e40c058280311a000c00da04840342e4101180540c085550380328140f0620003940c8059002c903420340401d10905d28990340c0d6100380010b607500514085968543d42c01c18820061072484420f40c1446400d0a0006064040d0400f40c12a03020310003c20032041c059041c50700b680c0c01101c0b80031840659000 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 147910476 1250 147909226 147909233
    0x40b090a0e160e01260304060302030a1b120b0f0d02300a050706020313030809041103090a0203010605041b0f020c1009050f030106060e221b080f07020307 68
    0xe455030072045021610045206500c000312100700760408010b100c01c180040c0701e80481036007040d40c00c00d1030ba21381110203041c41d003081c0d0300ea001d00e0080c0b10030150000080ba24007030080e04131040e1001690200c00c0700c010041000f030400d03e905e10f420548241802d21040c0380e072504c07121450440401800800c64054030350b08000f990b20080c00400c0901305007600380f81103480000309106071042d28400810100e02d1a080075450410158858001c5602c1085040a280c01c140000030480c1d03031003040c2640312282c900000d4082c000f01c58812454005c044200305401d10000b400d071070f03014020780c000c0007065101d400384425280c00302306583c2103000001205810070b1140c0c8006004400e14410b64800120001c001340b001681c3c0504070300024140c90003401149807010035007074013650881c003c0200b00c1c41d00d4400b03441104000500c0748201e80d088a80f0411101d2660780740e29005800c101080700c0303507120341d801803107650755040107000520300030010b507902032100752150042515800440c1408210ba4 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 147911726 1250 147910476 147910481
    0x60306071805102d12090302070605030c07021f140f180307030506090d0305011d0402010f0201020904020f070c120f0605060f061b10090206040e090c060309030a0e040b090a 76
    0x4040d020031690080d85903590b002080c0d03100d803130440d82c650700fa1060035015000308005ca0817404c00201c43c1c030740040800001c1e0000f489400302c40190030a00c0e101d40d5104d80e04840f902404001a4119001c0a030005074584101c2c5840290b80d42c1d51184068940980d00d4012103004440741540205410400d1301e06082c04000c141c180744200a003254402a02c81c0d480c00e06200381034407005420b9100075400c1818503014040c0c1030151144480c5500f2a03400c1d003150401c1c0c4400640301070305200d003030000404458400c1d0105c405c00e19004d8002c0d036880361040315a0300198072800c400d542002c8a444045802c009840f8400308030b03604910035035001c9006440f42e100912010f40041e51200104000b0080c5840d840054856901403081456440402884190a081c070281000506034680b00440300160354190981d41075601c01403001c00aa601e00850f14130b881d0255001c0b50380100007204100d140803002004010b5514540d40302c0c212710040406200a60700300c00140c40e4070106000020b10340400c140d = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 147912976 1250 147911726 147911749
    0x50d03020c15270a080f0109030e01030b0f0108040203160b090f0d0b010b0f040f0e09060907050310090c0b040f0f05010305040c03060207031205070e01020f060421091d060306071805 80
    0x28080b140c490382d01c0318403902d802a044400c1c6e0041e51a030310608185900480c04445090080c20148a0b01d038140d0b0020342c00c4980d020800303043c00070003400305083d500c082240e821607011041d0050740710380c2c842101100642001c0c0606202d103c40300803d8800d0b0400c28450001c45900c0300c403003c40350f403d20503940e500760484400404c0400041c07000003128810022140c000344000c2000000609108803001d0404900808015055001c00410800b5071400140c00000e04103041002942c0701300d0340f070848142c40084e800142900d501050100700000d03a60140400c49022658074440c603582e84c4015000d541c01101d000c1e1110300704400c1040842e40c01e80040000a101c0c1c580194800c80c44005841256415102e510000700e1802030340c0d0565804011501612500c0001058039141c9591804110401d4401d04a00100d1080116080c0e601410307201d0003428000004141000c00709680c1101040c3c2100c0182c440c0c0300e0080810062405140070b03503081140359030300b444c81c24105000d118168490 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 147914226 1250 147912976 147912979
    0x204030503120a0f060b04030b06040b031207110d050f0d0f05070311030d0c09050406080c0303070303020c15190c050c0705060c100509012a050403020409020a050d03020c1527 77
    0x121480307140d40510303134480c5c0c0000d00300c449501a25036007903040000310031000400040c0128036190341d1010940d000141d40c4c9c0c1c0b24031b00e940f0719554ac154a181040c503184240b200141c0000303071144002d041000c082104050150610111742d00c4c1c4000c64000c44580c50180390b20303c045241041120003003441740c0e9400841082c401d00300c1e860a0742c621040350840e841d009010001996080f801e115510b01802410001d28070440200901020341001a0301c0744030f1080300909250340000c0d0142da000080c0030f0514203a401c440c00146c1491f2000403542c4901c40e103c0c0c0c0094892800f52001420f42c022001c0c3c60480c8242402020076a003020144004c0d540510030100c07161260144140402555000c0c45125418800c0041070024103c0b111200801000080c421560360040050003100c0d441015601140c2c0c0450b4042114081030000c10901c220f2504060303003284c9010100030505400260110b0503040681d019410a40d07540c2d00d08006000b00301c415019074040300c840c0341c01140c2000c0900001030f030 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 147915476 1250 147914226 147914231
    0xd020703170901110f1606020102040b040909060e120a0e0405010b031b0d0c02070509070305040206070807150f0903090b04081f231603050f040b1b0a0908060a0204030503120a 77
    0x3143c6088130700c0c011484480c008031780d005051b0812013020010a600040049000a42c2007a0421480590900035030042c40300c1b03103603900c0080e011b1041c03035007004005002a4040d1111100c0102715040994410159071001c00ca0b412082c0125040c18440d0354101d840c80f001c21030554440074212012282d15200c840e51501d01400000f650300700620556000941e25001411294034200c140840c6400051040341818075081c10030015803210b00449001b01e078050000e5070760351030b585080d4802c102c508102190941c54410b1489101d40e81d82e00200c4d07607a00949030842c90740e0759103d422449100ea4011805a40c20410000101c5200c08082643c6030600e0500469042503000d06004008059580251078801410a0040c0c58100140c5c5148200d035a103400c2c0058503104000b0f91030303a0000b800003000c91682c000003810021148101d056981c0a1070541550f40d54500e000402429841c000c0018038003900001c00c5029040c0d208035000c69501c07001460501c020602c62809844000b491420f84a4 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 147916726 1250 147915476 147915497
    0x20d0302070911040609080106240504030501110c060a051b160b0c07030801080304151412010305070f0e0f060120010f020301090501060e0102100c0c0b04060c020d020703170901 78
    0x244140103c20341c030140500c8080d1942d1a01790014400d0f26150b04c00c40c1d061740360070814805820300c1e8880d00007400c461892a051503c043c2d82c1100c0c90b125683c009400c84d40f800e181603014940c00001030045074840411900c1540f40c09000208807501a910030085041c10342d0388101041c0848040c0c800c03040e02c179401d900d10b00d0b41611382407a807004c122500100901e0004005c41010303004224031f805804c40e03400540c246802c100c685041014500d0310402440300c0121141501719040c000c840c1011079200d048041b550b0340e403030081c0c0d50301c00d940250596080c5908022440c00c4039403002070700c1007803043c0008800e505e0300d07001560400c0e40d9070030f42100d040007008100c0901009020f15001c001c010800141c0c3c1703614010499080b10410382041040003510080501c3d240c1c0d00081520640c03000600004090b01040c1c419511322034005c90041611140004120510040c0d501180b44001203800399100015241c5041b0f8079110b803408024560000241c030000c614001a02074a186003044c1414450384 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 147917976 1250 147916726 147916739
    0xc0e0306070804020909031e0703090e010b09240a170105040216080a020a02090f091b030a030e010207050409060207050712021806040b040204030f1a150904022e031103070804020d030207 82
    0x8d5070712841000c512400a0307840704260384040e8000c014528002000c0c200d504100c0d02001c41c1c4100c1d0407a500c1003414410710007000d25505030020f40c00d001d42c680d03130740d64500e8102c004c4c140c1c0d032107c891105803803800c4000140b2401c29000310340030010113410b00813001d9440c1c0e03a05095a0070002e859002c600c81c4031784010041e22075000280c0a096a180401601e01d04100a03a18090245003025048000c043d5001060385000a0f448060b69050038880541d030315800c0100d00d4400582e1100e540303c2e0a0140d89010b000341540200b200501034815520b1850325074000e00340312192203170002e40003440e440ca0200050070104145030071034030080003c2034040402d0000f6041c4c3e0425041903c1582002c00d8610402c40254229140b040c500c0203d00582e00d0014040b0a413000600c80704d500510411000030210343e21590741404c010701c02942d000040783e01ca0390700b0145a00442c05040880e140030084054241c80c4001c0c0c070302c69107842c1d607010311982e52135081c0318501d51450360032400d504c6500f5010074407 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 147919226 1250 147917976 147918007
    0x705060706140705121014060a030b03030f0c0f0703051906020f040b04090c0c02060301060309051c0206180a020310090303021b0105060f0103090b0103080a0c0804090c0e030607080402090903 84
    0x202030503503130075898000c000140c00c0c4d24503000d0945107052026007010801c480390540d0729030302280d086400c00d80f2540101c0c001d40140100400c6207500d40400105244076502a2001d0941443d0340406c48075080c8004131010b984141a00025017254003006810704121544c01105050520442026052051080c7d1a0000c1c0d0400e411000c041c5802040510100f000d500c14040c3c071124610b040c206040da00d4021403550305c8180a68810143c5a4101c417007848401c03c18000390415420381c9134a0107040b0880203413a440300383c2e00a075120a244102020560b80090403804654009000d081c69944602000c002070100306011011f040d02030040e480003a403480c00985030141c510300080782a15181c000c01120b000380c2d81400b818145410f14400c04100060100c0d815213500440441da20514041e09603400941650000c0c0007017800240880c0100d21130b040b0904035501230f2603051110142404050302d40200312950720000300c03804009070161500b00075080c0c01c142c00400303492600301ca403100281d0 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 147920476 1250 147919226 147919231
    0x71209061406090f01090203090102041206060302040e0a050706081302040c080402030c1903060207061d0a11060a020d0305071103070804050a0f0305031204020a0f080606030105070302090102070506070614 90
    0x901a95035034407015684004503000380e002030100c40344120703882e140c400100e04500c18003811100645c040001171100d00c0960444000e0100c1030111004c2180d83c3c5006400390007940400c0780039508140004983c00b030006030400110f40d005d009800c00d9810000c0441e80b0000007041302c900c80e2525207010340580c4891103215401803465480055174900b0f4014146081380170b0b00030901501d449110020348000c090320318802e0b00ea0094005d60307110710300c0c1440340c081d10106410910005011424605c0c109000548081491144c100c07401048500d404000300c40c003440710a9400b42e0880c22140000c14803a50000e82e01004908040c40401c1c4500f01c0c0780c1c6990000c000071141c12200040034022032400f1910480101401c1031341e515801d05580e40e09803a401b510591482803034501d00440d0441d55030200c200702411117512003407100395807000d44540e141c4007501d80714000d51819010a2105110b402200d1a45c00c040e002040342c0341ca003a05005140d03100345001e840241c0e031152102003800606c210300f030 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 147921726 1250 147920476 147920483
    0x215010909060522021e04050f01061d0d020d0f060509010212100f03030f0903050303070914040c0212070501060806161209050d0c060f050405060a061715071209 71
    0x180c0d1104502c0c0a008407003025082e103820a40760314404200070040c000c1440c0c0160306840803800a9000e211203080001d50418040d131103404c0a0401084801c9451000d040314141e5448091700000c235081c04440c49000d49216422440480049025040469503001d00d10300c0b40214449541d0f0340d4407240e003120010f41e1100f081e81d4000130030090f01102c120460b84c00c6050045140b4106242100311280100300388402003d20046841c41c0d48201d01035501040150341140a607035803403402c1e810003440b48585020360324010318040d445107100e0420381315408083e4141c0c0c0083c0b100a404228165032504107440880d0b46640301c150104112800f0702c080342c0900f503110ba28406900f51910040c003420140c2d03c01c004254038081d0a4800b0803000522a6641040c41c24500d4250103141070541c0600b40c000d078110380d150f003000148000c002000691034441c0e1a070310420000d0584031203003060580d8060740c0d03003666a4003603d000b0307106c00041c00666030042691705080790400c10781201d86055824214065 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 147922976 1250 147921726 147921731
    0x111010f15060e0307061103130602030a080109090c140f0a09050f060d03050f03100b0c07030606081204050603091501060206060301060f061209020102070515030a0f0c0507080a02150109 82
    0x10001180719a480c070001d481c5030304140d4800540388000c03075615429032003444d0404c0074000a1504d081400d0048544003002002004071701d58940030080d59070760240c0c90200021b03401100020341d8030315900c01d1a00c0d082d880520069420702d00313500d20318410040b861040e4400d1200600400d640d450718070701c500a1212040111f01c0b450602c0b003890204c1d00c000c00b01f90141095005c0e140c00a540042110002c95400d100a5241d8880c0c8409503e150301c1c81c1c1206443e42e0002420304600100080d0761700c00c1700d10504062140e2034035074180320340300e6822503981c5510760010700c0140030502d48140519484401101125040c89440444000c011421b900090258020703400740441410203005501c040c1001c450244030403850404014140381214881c1c0c034040f81d4030781d0114110b82c403c0c00070b080189002440184211508544045260b200781c0d421418140b0b85254414005402c3c06240c2c040b00c20340d1103440c01c14400d41c80f079803120381c800b10250003140034200300d1a140201c6031107694040c0c40b580000 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 147924226 1250 147922976 147922991
    0x4050d060608010606020f100c050f0a02030913020a050a050708160308010303030b040c2f07060306170705030c010809150f04021e030d030f060f031119180504020111010f 75
    0x46421644c00b81c100c41c0071500200e051010007130000540d80c110765031082000403120b02440b81103907140680d6000c010726140000310051801e6002001d400c061008450300140c032282c1503c000c0032441811640000700c3d20a1140ca01454001c0018000303480c01035001c10301c0d1070205000d0b032000d203403989811400f040401d0014000e050741446845030740441a50304100b201d00c60f40c0c0c050080c20405902805805610104500004c0250300c281038081560701180da50948a200281c0542264003580406021001898002d01070003c1c1c3c00040396000b8002c0d1000c081c80000464412100401c100f41c10307c1014484000d0f060150811481091440f0750301e00d050030a44108000c841c40300010f075030b00b210181f0f80c011042d580851054611701c1c0d80e0900240150744652090080e08250b4090b030401c203103084000084c40820038100a400030111040782009444c00100340c5220082d000700180324041124141400000340c0c0510780041c014100130041d800c0081c0403600391401d1120040c0503a448080 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 147925476 1250 147924226 147924239
    0x30605071205010e0a090f05060a1b051c0b01020f060f04140c0901091802150a030c170705210411100507021302030718270509101104050d0606 63
    0x145900c000380700000500540d45803644034000c2c14000f40c401c1e028036549005c40010850310f08109601c40d940103040c0c7d03c4510342400703d807004040100840c41c11407500011202403900c108201c40c40d807074103030300c48074075a602c803140c0b41004000716100d140c15131080c80c2740000040b000b0000383c0e10454001c244000a49003e2508030501c040c4000e07116080d0303025240f00c41042d52040310b0309064510705800080c5c3d1044030741c10000035024190b0041e4001c5070000748148004d8180d00140741c0e118180e2018800540541400c0303540c800c45591115040120101040207648035400030484181c0e0342c110351080410840340c4511499041d1001c68403441000610440d5052001c1c40710f05c000010f0403c01d082060a0300842e2441e401102c0c7c8421850340003000920207406110300d00c881411800b04012400e4841c114010814201c410048030001c7e01c0d01407001c1c245040c06024071581104c0050110050a01746000c0502048880c210580000340004a55500e40508043c41140200c078045801440d000 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 147926726 1250 147925476 147925487
    0x20a1215080a05070527040210032009090606030618040c0b0307030209100201020405030307020d021203120414071409100e07091d0403090b0a0203190e03010b09010303121e020403060507 82
    0x10391180c061041b205508076604801289103a01c1501075803511030b0341c02c0c0034100320010b001c2c10031104000004451282103c0180702c010700980c00d07003681c040140341c0350442044a1030001b201c00d158407840c0c00700c12440103079004010756000f41c401c40030090034540b250080d0309107030012100b50b40001c2d03021550f415a40340206040c01c1541c110700086142030706000c0070a8807840780c910b02900423448101d6034411902d8078200a0703942107040c02a82c1e1158003e042c1040c23484030641c0e00380e0700e4006400401e00c2000000c900d900031640c0110554907d0700100c01400207540000300400720002d1105400038403c01e0845900703101e2001540c456846034285450783c0300c030703040030321100138051814020080003942100c0c0190540303240c0311303507640c41c0e80030785600701d103188148000007404441034200c5500c805e8100800c0190740344114001e00c25683c51b10f05002101d402448054001685080100d94010460b40100704c00710f41505819100a24a50300c03409980c010f81c0201c0e902036070392040025403a0b004 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 147927976 1250 147926726 147926749
    0x150504020c190813140916020c0103020c0f01060312110303150f0f120f01150e131e0807060e0d021002090f0a080f16030f020105090d0204140405070603020a1215080a050705 76
    0x501f02400d0482c2c0c000710083d520a80380c10803c0c1495400601b240c0e09000811800082c2c0002e0380003400360540301d00c1c04c104640d500e1301643c2c004c2903403403e144802c020040252071107003140300c5001c1c440c0b0190300b080000c1d0303e030407000160b04a09802d032150307480d8451105a5031030b4080b400003130003c0d08601103020708594495594500d8410010405e1000581022055400070781d045d18059010f481401c050414000c81410701240171a101c02c0c0e1020450700340050b06a0b680500b01c00c001956104402549528003e4540340050700a0421100c0300411580174203440701d400740c040d88203081c412000c03a07040c1050303401c15106a4804800d800b0050420440ca81141c45003080e1484540e1451355071120351905604003d06100740031810503505c0c0c50300c64610b0341903074000300184201c07045104400003202c0c003902c05580c0e502070400046420b034064000c44040010360395417001b94500f0034280200038000b40500d070b418141e20f8800050340450400415102d180203d001d008502e10300820000d880c10750 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 147929226 1250 147927976 147927991
    0x609041a07090305062a070606180b040c0914190b0a050d060609030210030c051e0c0106082802040e16060f080f011503060503030409150504020c1908131409 69
    0x200c03008506c0d0048110645204c041241c031685031212004c0c0b40c00320140c421604900b400c14082c0300c20310b14241d6190403d07045c050f02600c04200f44050907400300c1d00400d01d4003c800d2080900c1c40301c40658100100600003003c0d880b88100d0354180ca4131400c2005510040507640003d1010404041c8550350340314a1009003410306003e4400c0380f55a02007059402100901c005043e9100e607040b00b0760f8019811585010305044410700c06510904507103140341c00c0f0784c1c190f145a40c68140042004040040c011942e0002c841044010720382ca0126502400c445603001c030780141c0c48120411451008024281405e080280700a2042c1d05200005041210350306400c000c0000030828000880d8201c544d050644440e078866201200f0600c4044d000350072568069034040c0f20018000590303041950024a92130f0815072440005d6a45400b00802c0c0d01400010501940001d460b5941d6016103c46c07141c0958460390009042601c0c125203014240030a51081403401c0b0035a2003880e030b81c50076503240b6610020 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 147930476 1250 147929226 147929251
    0x6030f0c02060c0a0c0b01030f030206091501050d0206040b030705041809120302092808010606110309061c0e06060a06020105091b010512190c05120609041a0709030506 74
    0x6a080000b951860007400743c1e10040e8001540c82c601178410b0100b0300900740c10400d42445941d60b4580f10006200782e10054006004410104032186804104400c0c1c80702400c246c10003030f900b804200300d40c4920f1800301700d80c080306c200400105000010040e6100c7c00403602d40ca901c1d94070702840548141c640e0440c0181d100d281041305130000341e048400303113007542c4c482c5001600c1303070b500320003095040c25041149156589802d0060039940c102c1c0141e081602c0d1800002d20541d5910002541d03803039510b40300141590802c0c440700007141032180c080c02d01d041c0c40250701c03c1d500d807c1d01212411103410141801c0181c00070810402103041c0b0044242c02407039588001c00491030182c5070540c5030070052058500c49080501e07510120380c451f00940d04400000a00e80f5030030b0424940203a1400d0000003940045400d004655480600038030581d40c040c0c5001401c40703900d548a4040002141000b4001c0f15619441e41803100d84090ad40c031424403403075658490074103141c2142040d514011009110212181 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 147931726 1250 147930476 147930491
    0x5061002030f0426060411120c150705031308010204150f120b130c110c0d0201050409020a0203070c0e040b0c1303020111151608060603010609061d06040f06030f 71
    0xc0c0c01000f120101c4100c4d50b071803102c0c0d210350062a0031190f85000400360b144211414007091208814624100c8501264003501511400b0700058a070841e85404aa000e41f1146d821414252800001c00041d841041540d00c0c100c592001001100b60f01e410248a40e0341c0450280148070300d40c8000c114202050030300011010004800038000020404035010309519040c0c14403440c0c85018505402c0c00350814148081d20072306000404600d00407210200d80d00c02c1040c048d00ca030410020220140741c041e5542442e1905018000780603520203d04042148010450800407494182d0b48002074503c154518105081500f0400510000584402c039107100400c900a01401c141842c0c4040365420b081c074801e90500d0412107418081d43c1b541c02180d0005940c2007141c0240d00c1c12805021803202c0d00c0e10f0581c0d807200070610030580001d0048801151806605006c1d2a0050550340c0a0034040740700214003440c00750110708103411640c4010800c0413103500901c00140c043c081c03410302400800f41000680c = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 147932976 1250 147931726 147931747
    0x40e0a0308071404050f10110105130203150708040f1704180507030b0f040f02070c0e0108150405190f060f02030603010c0507020904061e11040e0a140c0c070f090506100203 76
    0x500082c11b80c24402c5c40b6018030801001e00038004403501841c0307480200326a1804000e807130003803000b01500b2071003402604c80f007083d00d034001025a40550040d69910070f0a071781d990741d822098907016005503403e0f596031798040841d0301854000e00c00340c18007510018408000b084114242c80002e00743c4070505080245201d0035840781c0700c3d0070300705600c00c42d0045081d201244058000b40318540000e07010b0303207400d2408140b201e050000ba5049031182000c446030a0409165048800f1040e075005255400850400b2083d001010507840b42c41e02900d00203010504c99903c4000710f40100c3d030301e24040364002c0201310301441e080c440d4254000450400c103143c0704441d0b001642d000d200a000611840e9207038901d04140b80018a00d801c4141030100c208154291106003c0300da80240c81051085103030000003c40c5142d0710f002d100f03000c000c84010a000c60720b40010004080e080000c2400107481020000580c40242c000020001d0544460000303540c146101403182142020441c0340540d4000c1105540300c = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 147934226 1250 147932976 147932989
    0x6010804050604021e09090d18140603191b02070f0803030c0c0a14070503060a0207020315071806030e10090c0e040201020a240e120403080702040e0a030807140405 72
    0x282d0440d1038005d205c8008007503012100b9852a00c0d904001d0722000c00c00c0d071440c0065002c85048481d22081140b00f03024030001c07003074030752030151800c5070303200401d0090181010006990846c50301d00706032002e05101401081124400151400d06051000c0c41d00c0c81300f5014003a48000c0c0c40c86500d940c0405090180c010390300d2201401d2902c4401c0c00150846001005201140700d16074000390740e105496043e049941d40300414000c1c2d51003800f405000c0354440741c46208071303200700e64042d0140c140746010080c030012518000b000354003030000c4103500070101a150035040300944050b40300040c454032400300c1c031442d00230140789042c50340d4035045944000c903640d940c400046a6100851186035031352480102c1c00d185140c2d10041000d030b10100b40007005218442d0f104880c0000c1d00e070810810070381440503903561000922040311300c20f0421046c008185240d000f4010316002a00114010000d0200d161130107200398001c0d000079101105104a256001c40001e2400d06460002030500e0b04140001d00c2 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 147935476 1250 147934226 147934231
    0x23010b070f050a0507030c06020c011805040b03010b040618110f070f0302030f030408030105030d021b041a060a020f060f010311010c0f0c0803130605070b2d07030207020405060108040506 82
    0x181c40107554104200002004901031050744842901d80c0795942c1d16108080741c8642c081d00d0050300403112901340f194070844800b520300e09a05090031596107080184001060030031500c03901552070320040b01040d15207010341c20040035141070158040c003503200c181040720310004600351049020000011046003000a84101d1a0007042c000d200c1031162170140e00d584144d080300c4030400f40120420090185039406541201c0059050384c213071200000f0200d80354034075189003090300e080e6402000e640f400c080e80003500c542005520200c4aa2040300004c03036503086105c000300160706c003429111803114244440f50300071005414103221941075540d6010044108641e4604218411000c58103000c5803540340e0280c1038106040c00000c40c0c40300c0d01030340c5941c41000000030039070300f4910009000f4402c5044411158010f02a400360792640c811210020551030489844400d2103006c00103d182080d02107405622552001680c03801644180300a880005004034140080d400400000c180c1c0400c0d00d55 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 147936726 1250 147935476 147935483
    0x1b1005030c09040b01090905101d100b0c07080a0b09070b0403050d08040f1e02090c070519020d020303030a050708010b0f180406150801030209011403120d020409020d23010b07 77
    0x642e0100c130401250249840d50001000d142840705024041449070100300c140d640f5003010141c140c441c0500b11245900075030300304620320440c4904101440002010340307810800fa00596921641d02c01034986030024052066803c80881c00500c40c459204000d03440040503402c00250400380756854040d21003004600702800c0c8070b480070000c3c04006407140e0303481449501061911826220000d240d50780d0403106403ca02602ea51404102011903400565001176484001032800f1400103140c5d1888004010b07040b41c020801c0c4001e140103960600103580b0800740808001034a107050080106031540c1039210450300e450070404030440710300c84801ca40c00100450341038454000c0b07501c085401001194080c910050441c0e4405141580c0020494100c9000322a9014540d1726032103101407011141240a81c19408242d43d01d0300c40c0c0b0b0420103040c803002c0c030b07290060030b240e5910200f44c00d03030740021800c00407180d488144820000c102c41c4006415211440006034030b605001c6140268072030740e44017a = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 147937976 1250 147936726 147936731
    0x61e060a050a0b0309060c161716030203130603150501050a0c060e0a02180106020a020904210c1b0303080c07050705060a08060120030a0c050f1b1005030c0904 70
    0x504545864406000900e80a4082d0201c00d07500c007000756803900141d60302d100c18010540440d241c440401e042d41c17844650385003e855981e000d40c0c3c3e0181c00b0b48011455441c5040c090201e04020f00ca480c2580c3c5005029030007440d650030000d503418441800a4012307009241c40e2903002c20b801c125003c9008252002820400e076a00e030484425121056000c000611031400c0c0320000039084d0b4003060188101d4400d0700c014440484c40c81c501407240109002c0c90b00183d02c86262900507150200b0505d400038096800c0781c40c2241d03800340c030300e52104110034800c02013110003a00c2c03003c11042c0c105440141580c2280f1841013801e5076801800b050001d001039000f03000100e900801d00100380412002840000d00007540c51241d0080900745800071504c1078003049800c1901c91841c1c108050918644988030701452030f180180e00296101038404400b9120b03031088544910b510720742000704101a0080700b91031040900d90100f0454035064004600080140c2401482504600d15041e01c00e10101128003 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 147939226 1250 147937976 147937981
    0x6100b0a030c0c02100e0a0603110706050c07050312040201080105010309050d081f12020a051c0b0712150306060807080c04020a020312040f021504030f030807110f0f070602061e 78
    0x80b02c0380c040018019500c20030040417109041d070040030f42919240d055503030720f0140340d440c003065040700c0c10800c03800500c4400700209400240194011640b050b41d440200d82400029203a243c91034000e410f0307415805810034180310643d070f085183c0c103004103401d28080c4804980c0342c0e1100c0c2c1f1011413107900c009001380c07000440c026501100d01c500103080110002c000040d41c4000d0312001d014860b40c140d00a5004140c00300741410b140840c6034602101844410711154290b030f5902800400034120800c100140c3c1c012440317110140100050810f5900d0103180080c190f00306141124200c1d80006002d0b03111301e00422030f04001007590540950110350050300d40d000c500083c1d0840c80f940f2100c1a1094200c01048100032030394440c92032841c0203440f006c1140701002108081c600c00c9000242074207542e02000800680701d0780302c3c030303600c80101c5c40c09400581003015601c0c54084004005105a08658038140348424100400d0005000b80e03c0100751500f8442c451180c004842c4408110a10310f8200 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 147940476 1250 147939226 147939251
    0xc09010e0d1103010c08061003180b1513091203020405013507090f080705010c02040b031f02090909010b06040501050f12011706090d120903021011040806100b0a03 72
    0x100c2d8a0980c4003030001d1003c0440d810f1300400701c817400c41d40f40e0320901c00e208182d0310180c030902c00c080c0c604c00c240a0000e1054940e03100c11a40307400080011400282e070a407040899104d10381241000c60707621602082c2e800f224600029118079011428040510603c02005203a03480228000d40810458018410030403000509852440f0300b407020494484142c00c1c082800da03c0180d850031104207600142003203071100103450302c545a51107072900080003c00210054501640040c0c0407401c01011580c0ba05801c2c42c3d1981042d150514400e551036011640b500a811700205082c0c1c02003c0b940200510244100014028007aa0190700d0400c5000b18945484858050072100d0403003900710310042540e541e108403501610484e01034040380c01079002003015400009111b844489840c0c4980c0c00046000a18800400d442e83c41641103109001c00c6000d000290f114010608540b222180e0b40e407420b00c1c40ca18581071018150005100b072410007000741800003800da6000030805d150101c0d100e2680396 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 147941726 1250 147940476 147940493
    0x114041e021201060e10080105090c010f0509090a051509010f060c021309122a030f050d050f06120f0607030f060b0a0c0b1f0302060702010c0f0506060102060c09010e0d 74
    0x14240042c0350310389540824034920020306580300c2d454071022244826242e0402c01e081c2d41041d581070b01258804110031a5a60040039550a04603862500e681400c4090000502c40ca40940d03444c3c0001c0d64071014840b000d03c42414038071540700107542c9050294508801418240020702c650402c04c00400c9114003195260044a5400c00d030200c02031106482906141c040318101c0604003021138011400c070340c4400d4078011401345a1f00d03c0a5240161115600c090320b88200c0c001001082003810080d401007007e441c440c02c2c1c01421043c000204616142c1c090011601050310b51230039031707840035112003103801d800a90b0300d911450710302e004103102d100c07001c0040c06802940c112044036007000c00e00e40c0e452030b44240348614260003269150071725240c008201c100603840482404443c00c0fa514240054284880280b038800d01c18584240108911303198142c0d1028000c100321680d40098042c00708035a410042190810380200d20940741c204908c002801b010b01500403903008040b0310504209028006 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 147942976 1250 147941726 147941749
    0x2090402190b0304200a0509060d081b010902040f0b03060a0908070b0a0f0507110d18080304120507050103050c04090e2509140f07110a080403060c020114041e02 71
    0x1c29525441341820718000c9134189410f07001c50b52035040300d2031003c09890540c920104450000e001c200c0c040d2114400d0003d003806140302a00c2c1504200018401401c40303030100b0203245065400040c000e00c4510402064451480302c0c14822410a840800b05076408945581c0040705188001260b40a601e0280d00f0f500440030080c25100f289410480720100f180c10400c002d103030300142000340b036807001c07419180342602c400c1d104600e60010f641c8640a82c050540c515215000c1004404150b41e20f0015620f150b2050b004003580b02440a5000c0c104070041100e400a08000d080501c01c03450050740402003801284946001c10f5120181240c82ca007052180b584104211030304050050720816140c1285c16a61060141c602d10308480b01b0341c0da412400c80c0c80c0c054000311a00169903198140100d40750021000500c40601804d106100040c5440006000442c8244004280d113040c0e41e0000e0708445100e047c0050006540c401c0000042030719541c02d219221400501544120500102d01d40281c413 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 147944226 1250 147942976 147942989
    0x12030c02060d0609050901060609061107030203070311011d0303070227010311030c060306130c091502060103030807020a020f060d090b040b0406060510020d0c0201110d0f08070c0209040219 83
    0x74802c440c012180e08410300f075820b000300502c016211a8211400c0719814070030480001d107803040602c51030b84981e0103041c250780200c04030340466899400181c100a400d600c100e4001002001038003255810001d40d078800b0030020020301c5040c4125012907200d00c00c00c4002445425004111204200c41402c60104070f500d10004c0c0540c0e607140d28201105007018401c1030320910850a0303a214900d007800c112440313408003500044410150341c102001508140b000ca4090002c45080840e000520480e4020107502e80d03401455103514504014145001c080c010300119048600c29101680b1840310040c41c0c4072058852598540029401400504880b0802400005500240070510030440c8001c4e008901071201001055501c0003000380c6410400c04000240e041850214111401100304041030350060424a02c20301042c031034941440752510041d804201800344407011168400000e6074404001c0c10300d000701000c0c1d0380010384210300060000740b180c0440c642809141200d080300740c000303151 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 147945476 1250 147944226 147944239
    0x9180e060a0506010e030a0215090607050a030203070c0501081510110106060e030d092607120305070308152206090c090303020c010824040905030d141008060112030c02 74
    0x80249030100030308415203203e40007807100c100308546440d020032650182da90041c5502410802d14403400c0107900401c2159610401c14065100880c0c1c083c0300c1d00400074402d034041d43c0c0d140c4070741c5411402001030342c03c560704000c800c0d81008040c0540903298031541c44112502d10181540c200101d40c8410041c03403800e001c1d401c10a0005100d500311200246e22042242500c0d41c0201010044540203220721a0180d0183d415680030300011807030854a4024504c0e0080e222a035413581a030508210720341c0c0d02100021000181c607424035038803000c543d0304030068001e20b0002010010019410034640e45041c40526000e02820b1070401c5141d001d40000c00c4c01c40014400c4410951300940081420f11040c0c015005010300706000d03600c02d0350071522415200a4840808402c1d080d41c0c1e00c0150b120b401180c005035182c004001080040020302060485000301258210b409a0301c4018000e0152903030403840d81000d070603c00c9030004a400e0341910b0041044800c082018201120300303100501020390000c5 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 147946726 1250 147945476 147945481
    0x30809070312030905071703040812090306070c080906070b0f13051e010e07060203071203230c090a080c0f04090203030910051303080d050603160e0a020d020c030408010b0d0309180e06 81
    0x1203022001d00210381640d41581c0341e0f86114121076146102c0d9814469040c1c00ec54006030241e40242c402100076402110307407030708224003203001c203403180d022200980d07410f281a020030886501090281d60b1061208036003505852055a61a40d140347c022480101c184401440a80c407440944c00301080c0c403990422503401c55502c4502035180e600042003503071415001c6890602c42402802946003c2c0707000300404044440c1407444007007002000e441c030981c0701010000249241d40c0c00541001404500c40909840c00d0303048200b00018880703c02490182e4101903100025a4000c803e403075085205880340704a54944c1072040b02e99104602c0d4007010b01840b04030100500c0f010101034403000f800400c1c1082180ca0b0fa604140c1c1e03d00c51000400c0b81080c1441041c0070541e42001c06076040b509100015040070819400710081e038000d40b5251489030310100f410040817009004215030203d00f56844800c0c0300c1692002080c2600d140120080910b209241d00310380c400582c030180011901e4410f541c25070 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 147947976 1250 147946726 147946769
    0x30c03060406051008190212090f100903080609071b0605041a01051e040e0307050a061808191b1b0509070e010809010e03040b0703080907031203090507 67
    0x641080e246140160301e0a0804265428400c0744d0724a03460468070b60350f20a85d200d84203043c0041c0d02d14100003c645d02800301070141c0422a00082c003035800c26014220003003040c3c2c0100d1400c5900000041c0090903e10741801003070300028040d801c40d40503509880740d0360f1509401ea406141a8500b8100c1902c80c400711070a2051581c02140564403031700d000f85c58041c00b00741980c80108203004941c0d10107640411100001070320801c00a02d03207000341001c0740b90300d25200080d06680185800741c6090308500d00d00e40404c0418400c002c049251024080300144035511100300394000c5000c000210030411080c00c1000e400b99210008110380548010040220f030300d8050302c80d9010084c0340781b0030241c00328049064a012004607110707207042e40c1d0f442c010403c2400119006113000c0c0ca428440c0d5603d200d124990f80c0144000c102400110241e10b0380d400f00c0d807038028424000106030010301e800440c010b200290344000341c182c0e498040e240c04160502241090f6040c140349500c014000d241507020b94611 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 147949226 1250 147947976 147948001
    0x50a05070236070206010315021605031b101505092a0715110d0908040312020607020f010216020628081f031101080712050a0203040c1205101802030303 67
    0x154003080980e00c589444010041c5d80c1c50400b800010100d44582c241c100044806a0250035000158902d02d0401036054440342d055901240740480c00890007038080781c0a0b0003c218640005c400d4240810031103214034032078a04404140201d41c418105400403c280c440310f2a50080108642d20902606d190b01c80c01c0300c1c005a002600844151010f0304030328800c00901c1c42502c41807180303058800e01c2c0441c1c1c000e441004240351001200d010710f0034407010011640303100f0b2001c003002d82034000301542c0c10001c0c0d010703161400d01101554183e004006140d080700c2d0488150103074a506841c09515402040000e80c00140001c00484030240c000d18a8032116030300c8640c6900039141440c078030071b0003580c90341d100e486410070f030102600717100003603070f4026076940b00380390160b400881413904205000f4600a4082540ca042e190060640d4001c000e00c401c4c88442125000200700d00c0301406001c0c000b5a030354640f036103007501401c00069a154402407404812040444640c3e50040990380d5074075214112031807 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 147950476 1250 147949226 147949309
    0x610021e03090a0501030c09030204020a020708060c03010609080a050d030b2209060c03060b03060616080406020c01080106050a1e02120d0f05060303090604140307090903080402030d0906050a050702 87
    0x803c1420718400245540070b8891121200d00c41d55581500508580903c006540032140c81c1e011403248a000107040341c1c060042d01d0003030391050b505513074070b5140807801084440203410440039500301d040701400082c0000f403600008103e909010520700709081c0090b290b640040c0003184242014611400060b5095205103e000c1c130580d010005120790103002c41c200e0b8180c0c001d000041508002046841c0b0341880a4504100c0341c0a400b0f5910310180c2c0d0701c91498005500ca9805a482652a1501c0d5a0449481405807c0d140b810038200b0b00010300040400d114004800c074030a411a04455005100707121404040d120380c101140d9501741042c51000a00b005842d00d40004d103440f0105486240c007008464038010010f0403d81060304000c1da4648000380328801540c540701e003400008455500340144c50f01d6900a8407014010720705401450309100204a68004001050380d081c01615003101c2a20907400c21890b04645403161440414820000e003001c0840f600144035400b04200e400005580303 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 147951726 1250 147950476 147950479
    0x1120c170a09150b0a0e1009020f12070c0305070b07020703061a0a080a2a091b030c0206041e0201030213080715030504170309100516020d080105090610021e0309 71
    0x80103d600c1501090441d0202c200c0b0719886190402c04100d082e030144442c0750065050303102d03402c440765240010002ca900c00c400d202401400030440d240d0202b003e081260380840d4909000f1b0850303c040c0d80003022446120b070002c208450070000714117268802c00030320700a1030f403040c0300304811142c01d032011014074044058a885081e00b00fa01044641011800000c1c09a000c1c82d07001240c4a041490b008541c180310110700400c00d807540c001910180d0f8043c0502c044854454640481780d0058002c2c16200c1514940095610000a06c00040c04111460701101204c0020728424107180c80100e019100e00c100e07035141107065047c0450080b801042c600205e44491f014030400c6a4510810f5050794401c442c0540b070000a401644c841e09102401154003104502c1070303884001c00d81c103684e022a24140c2d10f08600c000081c23160310600c0c0d0100107500d92003c040c18108030540c0350100203903031020010100ca00038007221000d104054020007440c444c4030b404d040a02c5085005108032542c1c2c0d044140b445 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 147952976 1250 147951726 147951743
    0x51006090c050c030409020c0f030d0b2d040c03090606030b2d16050403240b040e0705150717070501050708010e130503130e0406051501120c170a09 65
    0x460070900a108444180c110100518181494a0700c52802900a0504c0221134000c2422081115509100503c420181c101e0001880101c00c000e0000307113500011820b1320051249196080c150001441d00c10400b0126000700d040f11000c40e04030050424014014a001c0c00c0180201c1040401d03a240c6105003808007600701c0c1749803000260b0002d030300100784401180c103801020498640d982c00e80240300c5422801c00d40d180c2541c0351340310b00c032490200c0c4d41c5412502402005448111040c020300b40e8040f82283c00b448003112203005c40740c6a81d0700d8460316109208140c00c540c03412400e8000d840c005900044040d2108005598804155101c0354044403154a80800140454002c0c000d6505866020024903882d50b19440100303001c003e17241098950784810b0bc143c00b002d407040751820001c2c004540c989545418a850100c00703695003d440c0341414949024441c4259901001c20205030803c010045075400a4500a580b407507007404c18056020000700400001411a0f0060580700f48101d851 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 147954226 1250 147952976 147952991
    0x40f08010f050c030414070e01090c09090e031606060e09070306050c18010c060f0509031c0b060a2001020403140d021203010b070614160206070503070804021201020705100609 77
    0x1c5a0342101c421000f0182800842e011404d08120000a0648581158600c3c0e450780f80041590000740d002c1100c5507140c0441d85081907100c40c00400911100c002800b041c00c61440340794a0703014425240780145c1958103400c1c18018207801035002002100950f8065080071a000d80d1038101602080c0c0c0e04608220100b05050400c200b00e0b00c40d000394218424801e405800119854164a8401d680154807030540d101d1340e0b031807449214000c1085000956481075501445d0505540180f100081685844d884260f59151402124404502840d09042c00e2440b0050140c411450884144540d071002c01d000c001c1141c0c5038440e40020382440c080b07400305444100100c1e61042e04e0345400d00600c0c02440100300180580f00a08a440d1054501156000300c04440c10b503e4542240e08c8603558500e111400601a01440f43c250404114580907246181c40000580280c030041c000034025031605100c2800000d0070350503079400e25400070a5504d1500112100e101070561800ba9040b21498200d8 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 147955476 1250 147954226 147954251
    0x206040b01210b060102011508061009061a090a0f18060504020702010f080c0d0908040f061403010311040902061c0c110c0d06110c031c020901051b070506040f0801 72
    0x1440b0000100203400c4001c0444a95254165940040c0082c5d0556407200100b11a51083d101c1c071320301520520004040614101100302c001034050790000c0d0b0014980403040c40500c80b000d841814594000401c59500e036201c901040400b600f075400700290001800011400c00b08007a55100f0307080e840c0005101e1261298100401c920440e48006d021580744824001554044c07110a0390140410300c80c203041c400c000c03524005480f40e21740c080780e94100c00a0140009044911202c0280401d4a8801c05810000500080314401800701030151420001a0f080607512a08050465030780580b00c551100303c941000006544e00010480c20300d030410031035041261017900c8201190b40494002d040da029031300140060390807181c1040d61340c82c2d04ca066041029407090020441c01044038011950791030b4407454410380c003508207100300070940100319240f01aa80b042c1507c09424a0b55101d207485104003402a180503c0313540b001da08201d000c20000380340e02070860242e084583c01c000902514000381c1 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 147956726 1250 147955476 147955499
    0x10605010e180a0c050408010903050309060a230402040615020f010e0303060f01080603030c0105040b1f120605181b04060b030c1605070e04060b0103180203121e04060206040b01 78
    0x1c1107450a5549002500002044c2c0000410f40e81c6410041e241c10348034180c0b182900c0d01002c0a50200308004148074080340b00300310701703580501031200c01c1011400a01082c110b00b0300f0305c03007041d41a411103004101035585607130003d002030600d4503900d80ce2900b02c1e00040c0d00c80c410001c4410055207003180301c4281c2d00d408001c41e032041400500d0600c95000301801550f0301e10300070b810039415100900058940240c01d1040c54040c41c0075000c17190103440c01c129669030480d62085280c10395507459400700441c07a44141030f5503006a2058002c507007643c6002a5580484c0400c251580c503120344ca0b10181d00100400031130091081c190740901a0a4540b900307064503210581c0c900c0701c140130400811195461b80a05204c406101d01c00360340c1103036907903c01085250016681551616921010f60596680521443e154401c40c0c034078403c081d19150300000d0300e441308070704502912440043c075040c4003501800070901c031811408159444030b8646900940c2c48000301e078116a00c0034603e0001c9078403810503 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 147957976 1250 147956726 147956749
    0x5010f0c050c0d060f020f03010e1323030909012c1603020901020a1b090b0907020a02040c171f0501020f071a04051e040b040b060d05090c060a02010605010e 69
    0xa110420b50041800300003802001c0988050f075842d285407001c903a00e0700090a030760038008803058480d41050001500c0110240c590480c4512102d201380004001c049200030b41c4014124009a465101c01e595046118005100303500c07020100020030b22080580e1220310f01a06924803d40b400481d0007806050b46e4107a5581440e841c01c464000301d803501c2500102519901031040d6503009200b541e8a44083e203085c1c01041d2040035034001071080c0075a620070501c940300b007105c12a15034180303604040d40b100130144005e80101d03240d07950300c03001601a02e5042c01c40c903129101204241707407076028500100304a02203c0351501d607440c80001d1640c80080c1c0d111424122001a2802c0c51030101e8494840b01d2002141d000385e181808001400da4841090300c00c0310510100d00381200381100104012154062101d51043e0b2400c8070050350381d141c1c0800c0c1c5400b44c030501c00000d0141c89415440d403504018081040d401800013651a1029506401903001c0303034800c2e00d030f11141e0f006800c02c101005152 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 147959226 1250 147957976 147957983
    0x60602010f020a0918020403120e040b0103060312110f0703050a0b28090c09020309030d14101202040e010e03040e011221030b060c032208070312030b031605010f0c 72
    0x54090038880b69040d8421701005d4640040300601d029542d64640c101554100745003008540700e885003003464206030080000000702440c0820801c1d04581d0380d54040141010440104030400038520070001c0b00300800508040b404003281d180e16075a1802a07502d0301d00200864100802d003020484c620b0701c40f44044003c01d201c055108403201c018808000801807400262840315807040c00140000c0d552004500482a0101560391100c202131450280c45418071040226180c1a08000c100103201c03030b80030240c40300310803c071940914034000203018100e04144000d1a500e48a000d83c55010300100801c102c80020b007400e10f003680e0792610006103061041020f0074000341d80c0d10341c020282a814070310721051040d04000412002c42408030340e681e00806200b5404e9800040e070510159042d040e4228070003100603881c0c0005017007403401501d880c6c59200c024140440c0c5442142414080d03080152802005003c40300f50303505c0c06a404030103208600c41c3d503010400042068501a214110020f4000d81 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 147960476 1250 147959226 147959237
    0x6140408120313020a15020609061b0906040306050a09021c0512031e0403030c02070f261009111302090108070e0a0302040609060501080106022a01050d050a060602010f020a 76
    0x102a400e5407040e0b00040404007090012441940142d48501c240c0002c1c000c400d00822007445500c001900e824406424060720303501c2a0104101d401c8407001d41c00c4803070322690b105915030901c040810b0580c01960070003003400e801d05040001080c0258454641507000311a162071450a145074102c0d007076103d1030058440d41004c2e0021180342410401150072440e00709205e500151186128180035209550032400a41c68031380c6a140c0030b0741000030710050802c403003400813014608080040c001c0e00d0642c4448009440c60b031000e5950f1402e000101c0340c1d017440c410510041065141440070403070750b00ca4003489105034401396244c5000e0751003a900407040c1070311504226140e100040d150441c0c203104641e4030924445000c80103172102e0095800400c048103010420324101400504500340507085901158002901100c0f000c2d1580c8407104040c1540d100400310110301401200c01d03100390311581a15a040c04140102403a2a03032107501158520341c0204190140390b0b614030160310032283c85100040 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 147961726 1250 147960476 147960493
    0x108011a03040c0e0f0402040606090f091d030c0a021008060d02130b030114160206040201080a0e030f040b0a141801033209060606070b0c03060a1e06140408 69
    0x28001150854000e14101c500c0c55a100b0010100f400b040f80c03429030f44010002441b0841c1800e02034040504a44d04151809030300b8010003000b01d1401d44a0001c9650701c2c0c2e0b41010030349158070344140160118105880c0e840300441e102c50b03a150801d2600324000c0312a00010781c580e40c869041140100350041802602c4a516000c000c407204144100c004020354400190000f541c092080c08855643c0c00324101f03540c43d000030040e440f40705910043e0150340005081100503a484044580e2000c0008000540080c0c60000303c1d2542c00740d800b403007120348000580030440d00341a10140020554658036803441940c00b02541d400c5004071090b0060000c441008400a076009800c90356034201100c0526403580f08044280c90518004564201214102014082c0d174803820f021a541c00720094a010b07240066940c0e0749010320100601c641c11104002c00821604d070342c0c11020310003c12552040141140c0d81d13406403075540b04240b140d20085240e034068042c0f030f49a408140d808036072422020b485035a = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 147962976 1250 147961726 147961769
    0x11060a15060513050915030c030102030708060d0c050603070309110312040501030c03140a05060108010602060712050702210d0606090513020304080706020c030331020f150c03030403030b010801 85
    0x280c00101050b0010302e20390401007460b40b2074281c99407060b19061445405520300d0407d140c00c00c00e26002540c0264010000c001e1543d40000586800480c2515101400200381c24030861111003a00041d81c000e20000c02d0141072a4150801c002c090701540c1d50000d03009024041640c0c0e658207810b4620080e4091008000325802648810305010a074140400c4160212071550b82241044070004c8109544006015407540d00c48412805045140002c000c3d50400d142c0c00ba0985c04103030104003203180c413240040c080c2e40c424840020214107124041400b44e10b0101c00c2c58980e00072040c1403015078030703100002a01901c2900b50f88101d4101a1500c0d1600308510312050196000a00603200510104007600000383c03144001d0081e1aa400040c544a04105031344001200c00011220f40840c4521042c10448002e100c0c0524415411101c0328400b0303000001085107503002111a1000e604c0200c0c0300c40c85000c01000940c420343c0700ba42c0401c00601c3d2407006440700c031828005d501440c0c1c100340611824 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 147964226 1250 147962976 147962987
    0x30a0213150f150206060306010605030c0306060f0d0e010e0c0901150e10120b0105071101030c1b140f06091c022e0509011a010c0804030c030311060a1506 68
    0x641c44208500d0303103a181c40d0201001c00110981c092280400c0800c40114042c1d41800196004607048002d045a545000001070050101074018401d0103000400706001b966020220740c583d02070034844644540804486000414008541b030119500704092050503000100f23230705010314401001d08210340d00b441d007141803e144100ca02d405105140c00310229030f65900d44d030f6026031000e55840241c0411038084080070744140b840154107120b0b0034041c110009486980400c1c1d4030340b00386400600c0e0a0071200844c0c0c480c0801402d03498810030400803030184400400c60020148000085071101d005003140e0b03da40d91412101181c49410105c503600c80303030040030b0321131001c6816807040b1040200c2c107100e002c1368403600200c0707100c079006603101c03489031100c07240202c9a0124900008020042c143d984020411440d00340c2a810040b181841004000d0000305460107140c00954050034551640f80142a04144a200d42414814240000c000c08140d010f103280621210088031145850008150344 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 147965476 1250 147964226 147964241
    0x180e0d03050c070821040f060b0a0f0e130212030406030b03030306010207050d0c0f0b1801020c010e0409062405090a1a010f020f0d05030117060c030103020904080f0d0c030506030a0213 81
    0x240170ba00050b20b00b500c0b81351100c006000d280a060007c9540c509490028102d400c01c002090003000502010403038400707403031045003c440d09010520803070350b100c198240c4101c0380741d0b01c002d60101d00d02c0f0860701c6814001000d0025100f083c1c808001e0301c0c610004040d41c07404103d403001d0040e4801d50060210b0b042008020b5603651042c102c20090646801130150074142f0340e04490903405010895280c9040d80c1d1600a401020a0001e842d11007035910000700710742a840d041501484e180c80300c140400034198095a01100d8113450560661002c01301021b410b580c1d480317410b201398110710202d000d48241c0d04c5a0865046080e040f11b0201c0015401510642c2c24400003000303500035415403018038141484548008030199035140e070b0b29030400c00c1d0250a0384100c1103401c180e5010700d04001c7c4200f150011203040d81e804a40a00c0203a4032481e21030103d01ca202020a440680400c3c1d59039001b5247c1c000240ca42c0c15a01e0a00c60395540300c09142e51007480240c00707948a11902440660884245d00c00700 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 147966726 1250 147965476 147965497
    0xa0306020c0708030f0d06060809060a240801090614090601030209220b07020706030e060f09010e0313030201230a0e01021e0304030c060f0503071107180e0d03050c0708 74
    0x24115950707004098159040085c406004640025001c140c50710315201c2c80001d4500350030089158100f03120a00d581c0d0100070000241c1d10380e13400300382c8240340540c14002c18210a62048411003600d03900d405002e00035250007221003e082c000740c0f603007071224507c80074071852202009180d50ba10b19000c012408401500e901c101d030f4188000726814040c40e05960448d903002c0c60707075003101c0e0814072030091800e1426445141014a0903542041200c2e011410303a801c404845914462500c5980081d03004011413502d1041c140300020358030012038100000841224001d0b2030303a03002c410383c44038940314410382501840d80c0d9213010858580c0c210b0085000f1517003014103104840426115044084220324491525030080d40007003810002c000b40c3c4841c220181c44103281800c0f0341c034803400c4084d10501010303100d001031114409048802d01401c00244008001000c0004050701800100350014102034941c121903004e00c950b20700c4044c0c06401202c1c011001d0704130300da282c10f1280d2604800c54109040e640c = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 147967976 1250 147966726 147966733
    0x270b060d02030a02090f040b0a03030c1e0c3012090803130504050a0213060507080c060a0207020f030106080c010c02030312090309012d03091b03080405030c0402090a0306020c 77
    0x8403000c00948003861080344408001a13803560680308209280c00e00c81c4015104508250550b02607440c0c0f40c00d0b020449515052400c80e42c1c00c0d40c5400c40070020501c400d207144000d516007000034401c40c0c0b060401114290728100032420b42038490081800c01000e0440807060aa810748800120f81d148801c0e20030340e00d4900120a1394070780a0071401c582c4501102c841c246000315060000e4034241c81000e03000b0020040861800750b02111f0805850118030410b001e12401143d03003800d010984003142d00500070780d41a180c03540b8115805000a4200d10310a078080c00c0102161003403810144110425940c1c1000103120901c60540111960a4003100c202e0301400180114480425442c0c00a40201404030103182c503440480001000030036544241009840204840300801c004c6800000041c0c04c98600400c10103c45c0c1094092024803524000b1030039281712000080c004801c01520607240c04038107840300940e052041100380e000d40041e00760b2102000c1e008000080d41e544c014441d1281c1c1c0011f4 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 147969226 1250 147967976 147967987
    0x2d0312060f040f020a14031b03091501030b1501020609070902030717040b04020418080409020d02040e0403020a02100203040612020a020a02031002092b1218060903050601270b06 78
    0x10806807018a901c3c3d400355a004102a42129003003c0903109584e030100701702d41146000c030480d007250151140251a2018004041010280d06104d84c0000f542d20b03c4102002d540d60b03252559046404441e48480d002040aa00406600c0800c105006181800043c1501410031900078025440030340030605000d46d95540003000c8503940340d21481075020350306103109850180107000549030750720140e0655000d42030100340010750060581b800d89021000040c0c40d1145003031180002c1c851a003181c40d0f807180c00c80401041580c0003030a8041c1c07a00c20388004400a510840980c0d403802580148000305222594241800000d45c2c0540b0300c038219481200c403a525503802080c10201411185d01c5101d400099160807410401203030500460b080b50082c4601100f840c0700c240c0750ba99180300900b840380c0d000f04004041e200b820020901d016841241016541e1024058400f80303803403000300d83d030340100340000850340021a410b1480510b82d4241a20380ca0041c4800001400520f110301d1f0f00080c24010f = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 147970476 1250 147969226 147969229
    0x9030c0703031d040b06040603020d090f120225051c061404050f1203070509041119020105090106270204090c03061707050a05060d02090d052d0312060f 67
    0x4198011400780e1141c03041c51148004500210400071031a81c0510304008170031182e915100119000ca401a140040c2c450202d6200c001c050080904064001c6002c8003000081c450f110880b0310102030302c1d408849034880c441500d42c100310390502c004000f40d02407100801c01400d02c0c121a4009a4404150001d2210b456413044125201481d40c4460841480c0800c420400d00708003e101141014009184038441030307041c000341c0c0c84004c01070b40c00c200d40400c4641d12501c40790841c0d8076500c140107441c1d451301c640b07540038840c018141c4000001982003c01140040d501841f480d8281c4491100c4a44800c02e2a20f0340c9e041c1d12140c0507000d254580c20400060300c0c504c20303c501c000da800c25980c081503603890803100c5150103003071451410154010030010001a0307070b000c0908d82240c0003910000c0d14bc043c42d02c01400240550400560450000301240c0100000410004841400300c950440c03503040000c0101c8200c0c000c0001411561300c2004001c01d10030b821a011644514018120800c1404940 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 147971726 1250 147970476 147970483
    0x110f1e030907030302070b07080316030f090305031009020403050d030b0d17040306060b0a09150e03060114030f03030411090411030312040c05030a170c032206090b07020306040b09030c 81
    0x11600310701500920014010540d0500c88000280b9a00d8240741c00e05010341c0382c1c2c846034480548003101c06005003511410340742c080e4204050184659404108084450501034026401252054000c40d10400042a4544079100307807010740390400000e0405e0384000c041a4010001000825403016a202e007000000c0c51810010504271070070b1024507210780c51481c050301624041e40001c0c072441d4090010b0002c0a03403000340c0c0300440e400d0111200c551412414141c4a0500c55503c050301800b40c00008155038107280b48403041e2131001c0d000c41e0801c02051104a0300c1c0d000030341e030082c4186c400c4082c0d00301901d4041c403038540141c0500e081c000c507403420f003000074a1035021649505081555030200000d01840c10898801001c1c00c1c0d000c0c054060035640d942035007080003180b00300c45080111300244038010400944001188220318050103c115240c11010b11000d8820000010403484000c40c031202e9035000e40b05c0555010f0000c048a440d03d642e50f02c45000010240505488140020030303001c0b8003003 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 147972976 1250 147971726 147971731
    0x10e06030907050f0a080a1b080114160809120309011103040515062202031009062603091503070c050d050a0305010509090d1110020d1a04110f1e03 65
    0x2406190f240c8000d1104106022590038070404200305d0800c1100c00214421003096441b4040c0f10b580f01c003001c40c0d003191102e603400c4800150320308400c41c0303803010707091803000d0149441019082c481e1000d2a01140c0c0c0540440f11074925820800c803c203001850b0704041c68002e60030600105d445807624501042c2c5406c211401d9409900020851341c03005183e51810f13411003000d0f5001c4114045440c08041c0701c205842c03440011550010026020b0340954034281c019101340501800301c5592192003141c0c05244034904480c00003041024065448000225000402c02034080100c01400324202c000503003004002c5000d101011120340d000035820301c0900622802904c595071030f0508244000c088a030160480d90040c0d41003018001300c2030001441c40d5507a4540d2800350040040c1b5803000c3d0410b0840b40e80c12050341d0011608400da4000ba801c40d0031401181b034880703500140e100080005441d02c5c0b81c4900310b14a0104018542d1a0103600140800a00802c10740b480038100580704d001075104 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 147974226 1250 147972976 147972991
    0x15090304120c090e06150d110306161719020d02090d140f0a050a080304210306030b070f09030303020d061806090506062811030a090f120302030711010e0603 69
    0x21840c18421030705544070300c81c0850007810080039240f608a40d203460141d044105a48103641503400c1104000d440b0b41c41080e074900c0a8290391250801d41c0604cbc00c009014448003022440f08407440e01102e41c0c025241e441841c20407442c1c07a21402c3c80c1d1400009521910028200603000c100b01d400c503440d807003004009144076011211011304101c206a0420041070099101a04504281c50120300700007448202d00c2c3e0411403084d030702d41707491030f00d65000290411000446100389460848040c0c15a210310f00b200c0c05002d110060b5618610100ca0141c990130101c408103d00020a2021130312950281000148441000480b181c48401c2003244900c0981c00c0102a43c407401c003072204002038010b0f940c00c20403c0e01c100e405c000c15020f00c071010008141561218090100e400103010b441804040d078540c00d03800940f5910315400c08002c0c4104c0c1c150140381c110307480c10f04000810852111050400ba0b800d80e000d5810915190360304030124007040603031070410072010326100c00344d0794500086004004 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 147975476 1250 147974226 147974243
    0x3100303030e0c010801140612010b0a02011a060a120608011d010b030c060304080c03091c020f0f0a09020d020c030a0909050601031109040513120f0905040603051509030412 76
    0x1662030014191010300c59107402580009010080b182d03003050444d41940c000b0b00103082542031a50110f1003500504d44050782c000c00a8000203140c070348000c028000c0c10460360090010740305040030f6410318000b10387c600c0e8000344208001c1c400e140c07240c42614889040b103640401c90b56511600c1c04d0940e4003942d0642c003080c140c6102c201070410240f0950070000002c4e806000c24102c01c500050a41c0800cc101400507140080c1641c0110410300440b64600d40c0146500782221441e101482e00c0c1a401c00c003240100485103210200380b03400e40c0031000f8000300074030001440b410004d00001a410200101d09090780034010324242c15824400380241102e640c1d82d420603d460200c00000359000036045606041c580395460900402001c1141c0400d030b01920013180d540c503802d01d01100c901410714050a864040f45c0018801a4800f4214050505a51318440829118010041151400d100080171580030202c09841d084910075403992110116040d2801c050b03441403400a1080c48050860b035004 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 147976726 1250 147975476 147975479
    0x9060518060f010803040302010f02010e060c1206010801210303061208030f0703050103020a2d15031a0a1406121f080a02010206010519050d080c1e0c010806010302040306020310 78
    0x40d0812296502401c80440420385501d0000e586403240701d02e02020b410000921980507009000350000020180d1801c201e071107070301d4030b10300040264002da0b070f40c000b60319000b102195503507100d030361100d044c0da1410707064030820140003c0310b01c120100c1aa0490a01da1552030004540307403500f072401d80d100c1c00f0b4042240c4c1e9140464100d650044001c115a06040c076050061000da12101c0002040ea6802c8a1111207045200307100840782c4040008881d0080d031480f0007049c1280c3e4124180042182c0d903c05105080000c803000d0380070140d0170040c0c0e8000003522000c1091031000404200f000d1000f4002600c0e10000407460321402d5011a9035070307042a00c0c0450400c585081790701e208020885040500841c6407181e000075141e03901031103500d10a8030038420101e10100341a409c00c004280041a0b0f482c5541980703021100c50300a03040f190180e01035805040ea02c117a28650004079030b40400c02601401850000542c0c8203280500b4042c10140d007800003100044d5944001d5000e41100c040b0a110035 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 147977976 1250 147976726 147976771
    0x90a05060a0e01030807020405070509041a040e03040608040809180708010806010b07150b0a090c0e09070306031203091110082e0911190c11030d050403020402090301090605 76
    0x80600c1d40100030850b907100040001c101e0703003410b54000c150304130340200342070700d9a100440f0f550189000c06680f0514180c1c0c01c0d03402c40c540c5003410101c1c480586061043c0c0318101d40c8542c880c080d9101e40808074002c03100140000c0d14020003403160180c002d00060340211010300041e59444100d800350b02155805006010f00241000064010142e14280c90f203032180c113556060715540c1d2074244045103500c41c42100007581d03820781e800c0d0150040c0e06040014021541004040b10312658055000d00100000f00b52054424090402500e4000c0d8110181c4544240118018005071009071490200344170001a16501c400d50680381d501e03150380321040c5080c118a801c51503281c2030046851001c40780389000f00c00c50407841c403c080302c030242da00103032200800a45400c030740710b50b580030140a012070a03501e1441790401d90202c0424011500680040c40110605035910100788903100407d109104c2040140303000d030020400e000703000c0c0001c240c0700201c0d40c580302611000c2c0c551400078001e40200000c003 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 147979226 1250 147977976 147977989
    0x30915151a0a0f0c020f150d06151b030201060e010b0a1e0e0d0f050105040503040608091b040506060d0501180c031b081f0e04110105033102090a0506 66
    0x80c0c1d404500c40c0c0c2d2a1100ca0800500f0140c55242058144550394130f44a040d551400c81c060341051002e454800c00202d030b004000b10030391042507400410340c0b40050204169401e90500107000e00151107a80381164000b0300b0101c03c441d05c10084046648455004c42e0086469a11a008107164460191241e403100340181060748402c000c0b0300440c0e41c01401d024019400a0a805c458105481c4080c54450780c0c10403214100e40654003400c80c4d802c03c000e020422030000002c0c000c0340c256075074000094440340b00481e00c40e008030244c15581004d00400c841c032854164031458201400401140c5030101c0d5881309426200260b0040c00d20360001e400d2079441c034585000b118801492031608109146442140e890a08400040074007000b034035400140744522180b1054103030308004050f0303042c15030fa10214203c40010440d4112141d000c0000c0150705940501d003500d0081081050858000c0d211b0201080c4c1e4076603485000c4526012103003204090307103c0c8101980030b5846020f0207e00d5240a80c14040c0 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 147980476 1250 147979226 147979259
    0x4141002040f030c0605120a0e010216050d08100807061d0415140613030602030603120301080f150c031602071205060402090105030d02032715030601030c0206150103091515 76
    0x40c08820002d040c1f000c4038140071164404d4850500060b41180440c845009008010801801801c40401902403081c001200b01003001241d4801c0d026076074400c4440007e904038403995409500000c2d042c0501070042c00074441135999260b481d449039031000c00080035100070107201c0c40803500da48000d110315010039410307101210081c0c8505140c03d0844010300c0350140940b00281140d075010000c5a8541d5051004040c050106805d143d200e503106c4504c2d544136007100030220480c0c41140540110400c1401300c051107403510705041400d40d03071828008106001c00c0304d01c41045000380c010100b4094591b540b083c12241c0546c009160618261051010501c0180c000d0381c8130744d201c2941c8113191030340003084403074144005581600649080d204103a0381c150301c030000360740715aa0002ca0004d41000390041d504c01c55090747e003440416800501662145d00a8039200030032010f12010a04650094000c0b0003020704c96444440030540e411250382c01c40c0c207208161585610740600410141c001c8861111 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 147981726 1250 147980476 147980489
    0x160e01050307050403031202040b12090c0d080a210c0e0f0612160302130b0706051003030f0507080d0f050403121404030309110301090605190605030604141002040f030c 74
    0xc1c0307142008800a8180d020341e2000808110040c580d0021200280d01138070000c21070660160f450f400703400c40b05092000111034040f01d503c0340414030500d0b89085500390800c503410801140c0381580300b4100304d4007884188194080c6250b06240e405a004803889100e071409816510b0701740400400041210000307150315001c0c070800040c01401080d42210780c48a421401001c012100c0b2800c0354030540c080c0c0181d1400c008100c900741030026000800303030300600d5501d10503030041049030b03102003000159400c140809400540c0b9154101d030b4890261000304a01401051150300b0a02e14180c00703003d443c9443c1d10072035010303111014441003540190003d009040c90040a010049281243c012403510042019042580301e485507004d00205500003050392030058000d02c0840c8a80c04c0c41006040c05071081030200100c1c0740c0200d01c41515104d40e00560700005d01900f440e480d15100c01079680c00c0e40f6941c500b1405120500a000130252000740010b1101b140c070527194a18500348608041500e60001 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 147982976 1250 147981726 147981737
    0x606040c09150503070c08040608010e0109140c0c010209030f070f05150d11070203060a05010e0105060a0e09040804051009030510050108030d0f0e07060e0307140d03030902010e09160e01 82
    0x2e200b10303007815000300c1ea41180352400c251070350740e18070341281c510101c2031018149000000d00441d081d680030b000b0034182e038040d40004d000d5907a541c0790f034402c4881c0d9240c0c2c0f01394884988042460228100000c1030141900c1c00050700b0604900e00090900080a65801072540402e9040102e00700e107010a0f030040c0012160f001641e880615030031190311900005c0420541d40d0544011000305100075101d4158014084803843e01c1d00b02c4001004200a004141000951900005803884c2207804c88400007400d54480c0b550344000c0091040e02d0f45d0140044403070007804d00020071543c0f03ca0101d49944003290307035041041455420214108050003c04000480c20400180010400001120307031142140c84001780c1d9030648000c03075004180385880a451400b8a0b03100081582e0701041ca0020080220309030b40c0074581d83c070b0444510b01c0891704a9030304000c10b98041c00209010361711888402d030040c14034009888080d000070784290b0084920b0481e4a10028000444aa1051648103101001e0912 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 147984226 1250 147982976 147982979
    0x1122050306070e10030b0a1505090909010c09292a060106091203092105070e0f0403080a020d020406050a1d0906060a021632010813031106090606040c09 67
    0x2041103d0300200f6404141078941b03441c418180c48404000005141e8000500080250080000c210344c0c0200a541d114107100004503d81a00600c86c45103a120310f600c07114a518079003070122801e801e254a49003050800103d08801d903c25150013010180d00701c01c00840c2203a00d4003074414400f8241c07074196000e5445500144481600070500c08240c0341c0402c0142c1d041788041c40d080391000c0c41608028181010a91b4000c0e14007148511082030303a11400990320b04036141c40070b01c59644411621024045150300c007040120727006034030043d04150304050251800180392019800d9a03c9540841c001803000910944150ba21941a2541d00e003201468200b03211702500060652a01a05d01c510480000590711281030081000603451701c01d01c090a03003000c6e501c8015240c15150702c42c02e14410307a040640300101c20f080d441c200002c40e20503103c1d03040d19100e19400381035412403000101c2c00d12229007101058810300300026071040042800400192500c0c0c0203000c2a02d08160050040c45a401030 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 147985476 1250 147984226 147984229
    0xb0a0b070507060503160509040b100207050f0315070e0d061b0318170c01060e040b0421020d050d0905060f04110406030201120c021c0503010f050d050a061122050306070e 75
    0x1e04144e100e00c0e1f01d8000d8a130043c2100140061800c2c500003070740415100da0b01c5000d80d80100d4a8021507504482d460220030b294024961a4407003440c03004046450701001406075030041101c560099000340c03820900240c1691102c0403102203011107104d440d090310390380300b49a600d400f8002c503080601d0300c52030300150341c0d43d626400c1d05148d4080201d60b03000132414400b40ca03403d5000800401c8000d030b15074580e00f000d003001400794105807070981d600f000d800c140520103581c0705800c44524420b94000c00d06641101411115900b00440c84910551141d09501c0460000c2040e94042d070344050502980b130410349803412600c0350300c2d10181d01540c1084003c20240c1e030082c9804200424030107000c1109203084504038180201d070b02104010780c0700d00401c0d0084962281c0550705941c8400b0414890a0f2110100008401d80b0781008025a1050841000245981c4c12100060052200582c180740c440c0fa0705070100d8450804042205c2c902c0d040030070807803600304642d50f041612814038020800700e000 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 147986726 1250 147985476 147985501
    0xd05032d040b0606091005091002010207020a0e0403030914030d0f0506030a02010513121a070306120f050f0709020a030501091103041403070b0403170708010f060e03010b0a0b070507060503 83
    0x600c090000b94588000900584400013181d5000b50028100c065541c280e110162503a0030100c901d1b801105c0c2e4003c0c080400b4014401c030742003580c000301100820b6117000d1105011400040085041644401c01c610000f40310303440000007013620bd800b0355250310013100743e03130115000c0c8614041980e00b000184002074034045a0014034a4080c40c00d01d0b0f07154160388880c440d6040d81e40c0007621451071440800300b80a4001590f1410503640c8020044a03101c942040b01a01c515010b00d1079003510f804072000004074200e4424089502c5003050320201c13a041d68000e4242121503000d01c40098000a065040d59407611030540540240102048904200024640203000c002c100070214400500700111426040050fa61101c0e8010320207041d520b00741ca4024002d18080f80700d151444115800704090328040c10105050324035003031000198502d488004c884444400941c55055542c500795502141c50703250541c0058503c41580c1e0b5514851880d00c146400040d90022081200500c18002c90480c180c = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 147987976 1250 147986726 147986731
    0x603060115030c050702130209011803030203030a0b1c0302162108160b150a140907050d060e01080601080c060f09010e010905040504050105061e01081303020a050d05032d 75
    0xb890001041c0c00841010758552042c3c2c100650f1020a401d1941c0741a00150020f00703020000b82d880404601211810401c504168000100580c106100258100e2413980c4541d0480900030521004900240c3d036960714100c3c124010f0380180c0100c014882496895586140100200c56691b9000340900c0144401300000c05002843c1140c000b43c9498201448110a10b03820740101c072088040c14603200c440e07400446080118001c0005441c005044210000c200c40300e00d4002d05071121ba42d03620030040342c00c1d80c0800300c900d542c5c0d13603501408240d850002d61081c1c0a00060001071005c0c1d414944054581740c0e480b41c1d0a0f118003401c200c6a030305000083c0503110402c4080c02c0a8021076000c90060360b01001d5070b00a150032a1804003080706101c8150003550007150700b40c0d01550400341441d03030001711541c848141d074049100c4401054040c045c04802c00600c90192060f01c0c42c0d9111039a8031030900d06107404101c0000c41c007201b4407009030030030760344a084184100d0404101d0101c1c01e00701e01a90600 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 147989226 1250 147987976 147988019
    0x907090c09081f140a02040807050a060c14031317071e0605070512030c0d0f0510050d0507090903050c0601050306040b04060515030d1d2704051006090e0606030601 72
    0xb0f2103640d28000601d40c0250450202c8180e0b03c0b4031510301014204000d4000d072050100300d120b0742d00b0020309800d02080d00000e42d40503984034082c9841c0f030340b0745010041400c0ca044145203c10800c0d00c040015040c0e18130701800000304549003418104000900c1e14440f50003040d21110101c003449424031001845d08212140307420100e440301c0c00da081950811002c0a461101d003003000041103800c0441d6401803101200814042155a809072400750807540c00307d4101c3e0071181401014015442e02c5c4c6440000d42d03200740704590001ea2101001000d07640b00401c2280403420210f8102d00318a414000c0c18050b24095000348114609501d6801141c103000e000500707015500c501181c0c0000e2444098000704402070700710380745440c010350010856a015081c2e103000d03d210202d0725883e0b00c0d001c800341e01540c41c0c0300d00300b201c104403110704190050809030088070b03548181c3c00240d8003111f05008500007482d0840c0d0020709004040307caa800c194006000b1031003900010010b21100c100e8143c82c5901468 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 147990476 1250 147989226 147989263
    0x5060a0605180106210b09040305090118050102250302060d09050d050f0d050a09021203040819120509180c120606030702071e0b040e01141e090a0b090907090c0908 72
    0x600703422207001082e13006d0804d5000030204040109040e04000208a0f0160a0303072060b041c00c4409604d1103442110307008450040e00480c40c1c03003015550303d2000541d113505a541c4280d980b5540d03030008446074020559a01a03d0f02c51210a050003001e010054401086041c41442d103d181036030010b080c4115030740801000e0303684c0040751003144142d106a8040d41d000d08050414003008072600d42c0c2c1e170040d1089034120700c9002440842031104c030800400c040e5111103650b001c840d1221090302d454004400305600003200034611902c41640082c0c0e01c0c052079000c85030a540b1a69142034500804000301851302034402001400b18071940091284215210f030b00cbc543c8c0b50001208050f08404805501070142200041000700b800045002d540d8102c40c1c480602019040445090104101c8441280c120300004500e031081c0361b00707202c15042d51083d000c840008a40790303100001135044c58250f8090f5110b81c0320407800d103c000759034441c140b070000c080c4c00c040c00f0f81858544090390f10303600a4900d01c031905 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 147991726 1250 147990476 147990527
    0xe04031b0c0b0d090605070f050f0307170106090911031302040f0605040e031206010915141605150601080112020111120403140606093105060a0605180106 68
    0xd20a01c0941c080c1814070405507440c000e200a810203440c40c224140e0b802442c20010808850007082419005e41c9651216410201c1c00b41d000020b1b500001c12683c21301c4000000040310400e80040785010340782c1502c03641c04050030b03c202d4104a0750702100340c680b544401c100380001c0c1c0030001404d802d0030b94122008100d000041c41040c001d8a050f07400351707410509010300840001c1340032010f0000101d4582e44100b1030750b035a00044480c0c070650b22880c1920f0720f518441c07240485c801d1840100c1c41c0c01d030b0301c0b00c02d00d81f0501070450051105080400c1e205900f0500c0041a010032a044258101c20240303800030040d410114202400c681c040002414005d00e003209200e803d10034020280f40030700c0105102c0d2519034a08265040110403030380080d142c01050002001071511080382800766440442c1c912441003e04281e41d5008542e954040c00c6c8002540c000000400c1003003202e114101c81345010030724034684003d04c06451000d14508180c1710a150040c0324103030b8809040c0401c8500700107000c4180 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 147992976 1250 147991726 147991733
    0x20d051902010b061c270f05120a0903031205060312130e091608011e09050a061505030c0a080a030f14040603060e06030a0201020601031403121504060e04031b 70
    0x403c2c40c2180035420101c003051801a12003010007080c0110303811a000e1107000d9108002c1c2801400c2c1020a8400710341c01c083c0240800c0c01d01038059101c41c451402c946410024034000300e442e4000076400070019034010800d008155019040030b1058004540500039820484c0002c0d03203c0400108203030380804045800c074508000144071400030f0550044600045c00d01e103403a59250101e251100c040404442e8002a2403103052041000303108000e604c201010720a0090000901800d107410349541c03050b41d103454003282c2e07030f4810007169001c4602040011403901091500b040105040b041c80740c5000413041014140101c0d1400d450707079162910640442110b0703800e03a0400d4503000d14400b02c00001c2404614103400d9484542510041204120f1564901c4200b503682c007840a0f000740140c1080700100001107429258802e1940005c0949040071444401d8840e01e0000701c860007012240158801458105441094094008810290343d9868103441c0505101080c03c15181c2c503841080002061 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 147994226 1250 147992976 147992981
    0x106030c1808031902120405100c080d0b190b1206010915030c090e0c1902100212040b0601030608031905040509090d08090d12090807170304030f020d05190201 70
    0x1d4480310380c15485500d0746512580d0750000000012a159151169095680000340310280b11605003402d07460302c2e0500d002e0000e81e01c501450b150a00c03170208000300014442402805a004030000c0003c0c0d145005000c02200c03401c0f400e001c5004101071a020312a804010301161401d00e00f14442e141e59032520801204e20200030303400003c18600d800c0f0b24004095040c1c0044804c00c00300d80c0c8804549460b094a104451000e655810f004c030010064601d480b4001041c6e0f14000c402801514032119802940409070383c0302900c03400e00c2040220411040103c1c51030080c6d00700000781f03000c00403103060806c030513500e1080070441c01703080c01e45207070010085108108840241c900039228004d14200500038560340c8804c40c1e11000031451000014101e640d0001e10300c2c16284080c0c1c0c51400201c4083c2c0410001d010002c0141c880031020010301011450000703030f009031004904000ca54902e01130400501c40f080000d00441150410344030210740c03c0d84031003510000f1010010300021001080d509a00 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 147995476 1250 147994226 147994247
    0x4020f1c111203040b0a090b0a050d0b0109050402130306050a020f0405090414010f050901051302130908190f14070b0408090d0506160f03050c030a052706041a0601080106030c 77
    0xb03841c4000240454013450b0381d0003400d404503540d201c0000e0903490b41ea039010240206001d000000d00b042c0984400140c0d10b4200006909044c1000c00ba55a201e0001c00e080c0d9200c1d40642b8410070b42540c0800402030b45200d000d07885416070b2401c50500f480072805000310301c12881518421103900000c9418044e00300b111218240c0e0300c60080010902240006000c0d0104a9600d98039501e84000258141078082e0458000c03a80200742c00030021444406100411004030240c8102d41d082c002e80e43e4881c0d107031484e8102c0c0b0700c068507003110040040100410400542c030019040110034000d0130002034002d01c507690004d6020310010b84038150000402c4244001078009050f9202d40c0c01030001c0d00c2c0700440048422844c554443c001904510000ea0980740252070300580340e181040000c05081e082e521880c2c2205c9001d0801030601c480c1c50400d8289010016540c400341c1040052000700311a4140643c49002032164a0f041441c0130400130b0800c8405114007014140c5031028281041c0c032a480411 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 147996726 1250 147995476 147995509
    0x6230301171f0606030507050306090a0c030603050f0303040203160b0702041802030a030f0e01020d1b0503070218060a0e06030613111503040510060f090c030b10030504020f1c11 78
    0x1000348070300d00ca090241c40140b00e0310011074504030107e81070354410400c81c1e205501c0501028403c0d06d800c0c0d18a00100340034244074040665271540800058000e00204410110701801075880c1d09103801014180f180c08082040c21039041c40f400c2140f031640206580bd6160100c0f4009000c20b6170b42204031000a0a840003545400380c01c04100405400c03000384615840c0c503998903a42c81070001c00690761100c1c2541e000740401e500d01c42240741c8000544200301001d1182c0e058904110302c541c049002e5101c40383c252414526044100304150402d40d00c2480240070000310f00d4414104203004c031791601030141c04070b80301106500c400c20034440321865904200f000540340310b0200485e8220364050760420b03102101e1034001c036250380154411500607682900c20b9140c031507650301e00d030005c0c10740100408510b0b0b40900d916111001840c0d030b034940401c840c482071914003240a01d02841000584207001102900c01c40c0780d650402c40144405820b81720380e0307a0105030301500018840000d0318881d2030036801c2 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 147997976 1250 147996726 147996763
    0x15010306030f2a0b030411011b021c020904051c090f060f0e0604090209040f0c022d1b010f090f17010e0601080a031808030d110913060623030117 64
    0xc42001300c000452280340204180160001900d0044490410640f00e500101d100c100c205405403402140c0600454581c050b42040ca00283e0b01041c00c0d01c2d81200d0960b40c40e00701d112101003004000c03044107130102040c50000603050602e0401810150b040c021841082207540f45078040c2d600500080c04038407001070103251516074400140000e5401444a81d01460414003502d1800300036001d43d05030782c0426000340a41007044000680c880021382035900032003000300a069504203042c403000c406031603801b403030464407484040094003a4208151007000c11484d603034204000702e00116644151000c0c03000205c0400c0c56044641c0c054042e500131070300140102000010600f0340040e81110440c4640c454042e460100b90300700180c3c800c0c5104500c89904104000c410552569001e0808144101c40c0d1794200245400825403520f480d0302c440003125918481408400c0d0426031003d42c8800303101c91201d01203000b142c01c08860006100e007000598641c50030500d00b03841401419503100706040507 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 147999226 1250 147997976 147997979
    0x60f0c0c0310270c0501030e1005010303180e04120809030904110a1709060c0304022d030f010b0112110f0711040b040209100807110307050615010306030f2a 69
    0x2c060050100052000810503c010303105070784121800c80c612101c2e042200a41154541340041d0701030904918650428020004c000100b0602440f41c503000e14040c1c0d035042c4811012038010b02c1000d249410071003c8002c41001c1000194a160300102c0c0040c182c0341c01d8000380c0303468010900d94094010701561150400c2220742c1004500d10180c10f880b000c6035504100f50f100714071482c2d600001621844515004070000500c988000001590400d2000d002c103200c0c2c2c9426903010b08200c4841500415031030716009142c180c1d180800404481c56044030003000203041c000c0018101c1c50341e0704811101561541e0950080c402c0c41d0060710407118580d0382481c0d56a00501e84284c20b903442e00e20992041d464900c2480e4181014800d6a03181ba102800040d400d09800005030346030240200304504101805480074224507041c4040c00c600c038400d0004002504160800c207010010034001d45041501d840030800110749c80400c0c03400542d411100c1c2031443c00c004208112700e400c1c03400790200040c074078000 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 148000476 1250 147999226 147999253
    0x131b03050318040c08130312020a050a030b01030209030a02010e0301020c15010306060806010b0421060c020f0106080c01090b0c0102160c05010806010c080904020d0f050406020a02060c09060f0c0c03 87
    0x1d24103901507600891440e4100d0b01084111110f49401c0304c0092100000a16010240105041e17074601906200a01d00c403001100f20580e404540080005040440c4086659406000d0080720400909081d0b040800420100303654000c070741000307810804c01018103a40f6403402c0d0b040f940c806803a8801e90740d1008240d00c441e07c5200c0c00707100c00c503040c3c1c0c58800001346005003c92144d05943c440d015940ca407500e050f008641100c80010001c12110100c254400002c0d11441031135070f00045500500309140d04000b0240c01c48003254403844481d08400c500e44016a0700146250581e4100703680709468000e40c0482c0ca009009120064111140000e10903052110201c0d8000032168240c4c5e4078000b0f562442c004690113003d0301e800400e216810f1201c5090703450a600a0f0203400e001c55400222803024004820a56030117450940790240e0000720005060b80c107210341a48000d0300400c1d245020b58a40110310248107881c00016a9407020804d010011400d100700812540000d00302c0300c11500d1020f = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 148001726 1250 148000476 148000483
    0x409080721090803090d03180618210209130b04111203180f010c050321060303030c030c07060905031308010e0d02070e100521060a0b09131b0305 64
    0xa070380d4021102048941009205118800503142050f0180d400c140782401440030354400414120309002185050703500c910036440303c40d401407049a813000030b5509401c00084041c032590304601d1200c0030b400c0000310500d0030303c1d07420808158107480d800e0076a600c1030325040103807112140040803183d59000b0300c13080c0840b094040a6541c81201d01d00ca03500c001503407046d80c0340b06850481e95880d680b01c3d41000d4070b00c0c200c4a00e0196042c10b040100611105d940c42e91f065a00000380c1940041c14003280400038003241160390b90041c01507005614506048150049034040205882c450000c001a610304100c1e40c1e400070885558000112910350342000000310884040e405032080e42c2d0b20b08264903c0b508000200410703200d0141d006015182c1c1001c0040c4d0342244003c1903a008414048030025071500e0b185c403c10390420001b136503080c041824070a00c0f4101003000e000117901c0703824801e41ea00b02e503a8500060b6080b40050714590048051f07890513151039400299104540814820008244038010 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 148002976 1250 148001726 148001753
    0x2203030509060a05130201120609060807150507050a1403070618031205160c081902030715051e04030c200103180b0714040506040902091c02090a0b04090807 69
    0x15041d10034503650407146100700c5a08a600119500d0000c1740000554040c7c0d404008407400d6400104149031904088015100036030300045407640710200400440c116005441948405442c01514107411601c1d100d5a40c002018050310000300d0405a01031f0050030011035412031f034040c0060084808003080a1141480e0050640c041100c124481c04040100d01c54944180c0c0309520040e19084074030400c41e242d090307a01e400c8440d00402c0151150b0407180d20350150000e0816801540d8bd0400c0380340a41c4000044000b050009061400b07102140c0c0e0480c941d0059090280603004466945003000c9404008894000d0f0488000200000d400400b41a044a4061007a20305004400c8803240c641e02c556a00480a081e09480304085152a84a002e01e550342e080040c080a08043e01c981c0000c82aa12a5000d614050740c00070300092039090030034688001c5500110750b410414000d4020800e00e0500410002d605682c0e00c0b0b0b283c809070b031954040c08107079400c11595030710707503140d4a4003c0c00007005 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 148004226 1250 148002976 148002991
    0x906030c040510170f04022d03062d0c07030509030a020a060306170a0803060f031203090601060305090a0f2a030c09050c16030c03050403051f051f05060322030305 72
    0x300002034610300e070b5000701070146a01401d004503444042460140c21088c0000700707512901c1d100400510f9983c02c100c220300907607006404030647d00c4000313054400c1d25041203020440e000382404000a8280c0324081d9144c154041c14010780e5074904400007401c1a200020084d4004180320010480d9a89a4482804d5030302e6660048280b0b1003480d40301d43d852545180043c8241000c20000340300303050102400580d5503010b4100d81d900c43c80c000c40c03e03075a0f07041201c5c1c0325440d80c070400041103003a81c94015940c0190902001d40400219901c958581c00e6075900017900002c85c2c0350401200d007404d10782d003408200b190b142a030340d03a581ba46800b1501403840e1198000b41810840842e10301380034482202c0c0a00c103000d212150340d007450343d02910400002c0c1c80c01ea0500000307010000c08500d0500440d68115041c8808544900e02c05200e00d00312038001c3e00000921110380422180c4001c0c2e00ea58034150b81045911688aa6a90340315070207042441000201c0386001d07000d804100754154004038007440d403 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 148005476 1250 148004226 148004267
    0xc06061201020f180a031a0f06010c030e01110c0a0810050105090f040f020609132f040b0903010905030f071518080a0c05191401050c0906030c040510 66
    0xd03045816402c0c3e00940710161241036040000c0125408900300b003d01400002d407441130315940c0d030741b511612814160042d603400b4a0340401c0050702c0b08030500d000c2d4071403003d0074540140145610001d10100c407032902c45040c4085036401d03c001c50820400d140b002c550040009a40302d03142c03690aa00d8800341d910910b0765600340f000128542c9080302605101d800319060760400c80c1e5440d00c0f03200b01004981e00698104000b00508136058640d9421801d40000d522400f103105e000c1c0e400c48010790b5941401d8034290944844107041c40b200303e002143d0445141480443c2c48078000c20002e801030001c5403000b00a48000183e1100c50b02d401c070050320050340207552002c90f0080301d10891040d105804c2108443d49040c1500b580005c00e2400981001402480d0440c0b2102859861901e0119602818403500c44001c68400811070050042c11154031240c00074000c508160740f0040060043c4400340d44110340110000d1158070220007030302d0003020003c0c4500914603903080c025010003a4109980c18600 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 148006726 1250 148005476 148005499
    0xf06020f060609040305070f05060c0c06060a0b0d0b01020c030a030323090c0d0501021608031005030a11010c050a05160609050d050c010e01050d090c09151224020c0606 74
    0x6101191141c800e00c0041c103403d0155940e958102d45070b900560003100c13100c00d02d401080214504110041c400d0381c1c1c0702a00e6a8400314040d80901d020310091002c4c2c890602d4000c14410901164103a4284e44030026007ca42c0f40304660042c0e050803103600d903140d010701c100000b0b01c007459031507045106901c002042d03d041070341100b0000d589004c1c0031a0020b4442d841002480c4650030641841c500f50740c0140001401c11f4160b0502401d034190f9500c081c0d41c26507000c014042c0760810442810002c0c042100100390140710781e0307140000c4408070355144ac10710416080020510809001c0c20032290f130f001080d640a02d400c0300100e51008882d000d2000020005040030980b0f04103050b0080c1c3c1c40d03404c034008080318081071004450240340b00010904015090144200640b80c500034260301c0c922504039811035500b04108101242c0211b9500d4840207080c0c4402c2055909441c50f40e103101d5042403031030f086280b08481c91040c2101e035114102e006480059001e0f500b0401003032090045404545514001 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 148007976 1250 148006726 148006753
    0x10e03060403052205190807080307231f051501050333150301031214030103060905120d0b0f0102070f140d050703030f030608010c08010902070c0f0f0602 68
    0x180000ca60040c08903808001010200c4d145941c40c1c510400070b140041d004e240c42d50086103100310094061655440007190030711031014203000e0100604001d200840c200b142e140c0f5481e080071800c0030300d6050100c142c0a83c048142080c050710036603503007a8a4003250b01c00d82120075801040b04560340c40268103202052209580f0503001c60380a4032300300b8004031004183c1e20551400303180d014032014600d0022400c075007007034940305405010f580705502e216480b1b40c5541030455400440401070010082c0107280c2c2045140c1000941f4192904000001820111031a0652814160b841219122600820340c03120b54075050f0400f1420040c140c41203004c1034555001a42c0d524014050000b00b400740da0f500344800c0241003598450144014103c220700896600d81504082854109800080e0340d0741d00000001c0d0503004600050801c1c9008010a101a2000030410326060103070006843d0001841822712181c030000c040a00954148801070035543c4170400003d40407031090390050f010b203541c64641e0 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 148009226 1250 148007976 148007983
    0x312110703050a1101150801020406090506070f0b0a090c0b09010f030c0210090201090b0a1e050c03030403030b010c060516020d0504050a0e1f1503060b09180604020906030c09010e03 80
    0xd035941521110b043c0300e0850401d0b280641c4150014000350743e11000c1c003030302a06900003140141841800140e83c4c6092403c0102049040d070007040c010340741003211800241480c15800041074105003080712070303200c00e11402c3c080d0041c0e82c005000c0010750100030461140c0700d0010b0a58100076264000100c600b403009a09581003060042d01503009042d00f4074008540f5080700300c806105151410f03440b80c4030456042d464000e5a12a00001c42041c009203441c220305101e050b2808260400501f07101c1c4480c00303030782d807440000e000504054841c01c1618031640100e043c0e03e003059215205100d180750128076040a511a80c100070014030641c01c951200038043c00489040d210003030803200c1c4041c104011a00041e07806020943c05226144215101710b400a0142015100c5011081d642c5080351070020141e55280e0089050f4030030400082c85640d640b408510a268080d115050b01030b910359002034000d024081640e0780260000013040f43c100d03031007401030846400980762280c0036408a020300d9038 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 148010476 1250 148009226 148009237
    0x703050309010e220c0309020303120402040b01170406020a0504051f090603020906070803090c0a0e0f010e010e0a050403050d14040606080607081801020717070213021309020f04090603031211 84
    0xd103040b01c030640c01e0250f90643c2050240c65800d0401080c10087c65010900e16480350a031201d04c03841950900c4114501360241c1d141403902440d01d088800a4200d1041600d0405000140b0703a41d4000390940d0024015400c3d02d0003820000c00e2071a4182015030109014901c0d0090400001c01210340800e07400e0091003524030019000e8043d038244003150351561303400d41c405440d00b0341d1031042d040c2c00c058651307416941740090560f418554203d42044c3c600c4070045d42041e08648000d844010040c0701141070000140c1c0d20042603603011070242c0b6607003001d65030f510a48002e6a001c0b820118190720b05207003407445a0080340b0420041140031794424809494840c00d031441c00c00030b2001d002007141c100b4482a90004140c44000045c5401c10513544c034124080329500c00ca1034240c011032103505614001035441c8103410b0050080d0314008030304000940d08100b074001c0a00d2030742d0101c1c940d2070040364074040d1805451855810090951207090182c001e03070340c03982d552000e0317400c2545a102e2050302c3c800341c81 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 148011726 1250 148010476 148010509
    0xf060807090f081f110f131d0f1003120509030f030c0607050d02040504020d05060108100311100c050d0507140102090a0e04210e010e010327080c0703050309010e 71
    0x402400840e5286000392184c1c0700b0000360f6403142085100c03a140c8030700426251029100c003075a19001d611540081d14020b901110a0415468100310401c1189441e25031010290030815610740d80d40c5441171188002d038001501e40c40b0000d40e046000b98103c2d008100c1c46808808613040d10740b540c858560360b44545400032010740c0120000c178904601174030240c003034a410f04001605041c0c0b240c01003001c0b42c00c01409252055200c109000036941c0041c1010341000f102800c001c0b4040c29a02e0b400e40803510708440314040c0440407940d10559220b800d0f104030041d40030054a0054512000040041d00315402c1a51510101082d501c804141442112a0100c0c080c11080a02d45040c400e142c0395080140240d500c441450842e6038996481700c102d02200d0041c0c0c9541c1c034040084030005040c44480c68695040c18a03002500c40c0742c3d81c0c1d4000b2240c002102200400b540c41e1503103021a064081c02005000901c507440e000702c104440400030b001c54000c02c0e6a000002c100200c20406203520052482 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 148012976 1250 148011726 148011733
    0x12090302030c280b0c1b0706030b0f0924060309070311060c063112110a0302030d02090a0305150610030203060f04090305130303090911032e0f060807090f08 69
    0x800055010300d11180e11107115100b0508241d8015045000003c2480c00500e20750041f0f1000e00c00142c1520515100040590701c0348490404c04022802c46140901181034042640300c051107420074070000664482d002422640e12810b100824541d952a507020448491141004000990810b1020350700400030101c02420a81c4034103e610343c00d044064002c00044168150b400791451078030302d050364520f00c610010042c010310150010b00715a54016980029001640e000000c40e500105072485007111240c010380c2c8080140000321804220f6000070800c1c0038401d00400c10305911441e451182c3c1c3d017621540030303016007507104070100e1104a9215502106c0703d200442c65090580c00a81054405d007003070b5182c4400c8015504052403503a10480004060440600000900d401100c030300100420000f400d5040c13400640d00300808140014414542d4080b41c4080004000508802880c00301c152100c040d0f15004010110380c0c0444c0c0120224038465400140c01013840c4412040350001d8016 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 148014226 1250 148012976 148013053
    0xa0c020f06070815060307021b032a0a080d020703030f03090b070e01120204090606031103010f0501051e07061a0102070f1a0f03100314011406090712090302030c 71
    0xc0c0d40c0580041e09106921264900700b21341c4c4d03112032000710b001c3d00240d0002c10480701c08440c030407808545034480e2030094000091507800448003601c0d0640051324801d40403150396060010400694090303000706900d105203140c02030728640120b821403e490081c2e13030303070b01c1030118141054056544080000300000d01400019200d0382c400d5480c0010004149019000314070120203580c26a0004d4202000456603a103041180340d4061080c080005141048542103615200c02000038000c0b9101341d605000f0001640704002c01e103002c8204050454542c0c441d20f602c91414484001c19281d560030514800f1401c1d041d56541c0005040b1084998890440007141e04113880081502d6591541c01c0d1000800d00c00e07503054100e603501461282d040c40d15405410352035400c140d60340e1a0482103c5400380d24181941c5214452192505d40c40501a103500700284c58079030046421421404002d1012850024810708042c6d0200080c406001d02a048035024500075540b840088000c3d008a00003e400b41d07007 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 148015476 1250 148014226 148014241
    0x61503121c11130605070c030213090c0303020c0a06080108060a1104080601030b0106030609020c0d050a0203070203060405030a03051006080c0a0c060906060e0105010e06090f0a08070b070b070c12030f1d060a0c020f06 95
    0x16900c3d440a40ac0d0008102c54003243e40d0000b91a005802c1103000da041801002c01c01d040802c2000010038840c070b40948103501d0064001d49a51000d8040d0072080d0f1234040c10520000352004990080c520716080b16001d69503070070200d901040a024000000303003084070008145003d402510941605030001d044580d5882c4004c3d54141d01a88852055010501c0854090383d000d100940c403460084000c1c507a0341001c041d006003141d10041c1150665a00b401d401e000c81580202080c1d030012039558096501c1030003000a0b5481d541e000d900505040c2009407150801c102c0350404001c842401c05000342c241d89401c0107595107070b11407540325009103082c00884402d150203440d01e80c1191002d0400c0342c0c4151101c071914100340c0d1940117100b1000e8005912003c00c01e0041c440da6001e40342c3c0c9444091801300c0c1d030340c48011000d10340c0b0341400c040c2c41703400040211200b54000c0264044400003881e003202d548106a840354011511001940e2400803900070842c0007141200c0c84100070700261019560310007 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 148016726 1250 148015476 148015489
    0x150f042a0905120307021306060914030a0b13060c0f05090405060423150103180204020d150f0501080603010902010503010e04030c02030a0311061503121c11130605070c0302 76
    0x5003100030040c40309000580c0d520340c1400010781203241c1010715510394107801840040f4000100c0c0e0a8103500d054800c0000c0c40c0e00c0002d81041d41e064500920902c1500303000607103040a410005050300c1850b034284140d103038103900c090705070510952041c0020940b410003038480c2043da19015000c914100501c01c11468580d00c2541e226a000300001007605000322a003812401228884107403608840520000c900f0800b140c85542c0424039081c07007041c0410040d1001030b48000c1000340100d4003c90703418607080030794001c15601c1c0c9504e43c1c43c030042030356104a401c1e610f85500c0b0302400f09509401250003030606010f0009a1501a183c10b0b1450f442c160b820816004014810b400304107040d903414006036001d02401c06c4a038040d54072040204010410607082507405051014043c003079103d0b00d0038a889c04602d00981514040380117440700b00038000c0c10030380002d00e503621205c01c0c0744c40c0040c0000711100d00900350503050312041c805420384996080c0d032548183c5a0282c210010090200010701e0050b = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 148017976 1250 148016726 148016801
    0x60807021b01181505070309080105040f02060f0706050702070914090d11030f0307031406010e010c030e1801181d030706090c05060d0e010b030a020d0b090a0803150f04 74
    0x9118a0f5010350f40c9a506900c1004420698800190300140b140145540010410080c282113002007141b42030540e83c03001c403841d81003c028010100800c1500038019031209441c0c40310307004a0144454504400c0c0252941d02c940512039849140c0850800c080300d00c1c0b013100b4800c099100003000e49a00c0120f09942803851014058060301c010020301074501c21082c0030354001e000944000c508241915100d4041400040c806410469901d072190380c0707a82d1007505103a1103509410304042031104c21005c10403c184100d900c0e4803140021000054411442d03101010000c0d103080204050f409202058260380191005d04840340c0c420b20207040455011b9100e0004144903121003440140e9840101d06160000b03241020210399410b1004604a0b003070040981626044000c0c104580300350380064180300c41c0b03c101900710445c0038000b4190013800c0101580e07980c0c01024441d22881c007900b16a0304080707020b4482c1d0280000d4540e10400c3e007020302501502000180307140b650700d040100a00756035a402c = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 148019226 1250 148017976 148018007
    0x60306030a0804081c030903020c0904060b041103060f1503190b0409110f03010606051c02040e10060e03060f0a2d060501090b04080307020d08070c0906060807021b01 73
    0xa54028400003035500004100400b00c0001810b26517140d4103107078091419003560401410309000701d43c0300095010681c94500700080300d400c1d1716520742e42801c40c010f10590b440e03035410500c0c0017502c02d80d44040310701a42c401c45041f00e001c610b0700c07613603418001200e031582c0b410304c03030f501c400d00129441102c0b107034451612544050001034580007100c0060103803800070b9001d640803402644c564642d030800b02c48402400e10190003d108180c40c3c100000d22a02c6407518a4100c285000701180c2c0007911901224000c1c08401d4000c0e545080400d007a140c542658860754001c204404059001030602081003172056130060084c2c8000da88103080000036007850000b103039207029141d503410444c80c0049e0440c8503094040100182c11414140050f048000ca500040d90b10326041c0b104000c80300000040300c404580c1600d0011a074021460b20104a000d1102c000308818807803000480c401c00b15500850855000340c0d00c044541d01d913000240e80304d03140ca054140002d800c06c000035505d9401058483e0701e0884 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 148020476 1250 148019226 148019233
    0x3020a06080405151302090a060608010902090103020c010c050909091504080901020c0d121709070b0c190807060b0f09280614030c01020d0e01120204030209090a0203060c07030c0206030603 83
    0x2404c2c0600d6078010011201e504008000b8103421081d8100310500b6503010b040c1103420003509040030070181100a051140e43e02c1c0a400103903000c45644260150341c2c0c01304081d4000e11401441e09809400c64001c0c046981c099401d03800065810000000c64044018003152a440d4645564490a2141c0d100c0d05910f810340c4a48440f0820b607486080c0108046801101c20420010000c3c100410310314140c0088122400c2d102e0034032400d21000300e081422a0451020240d448056000c454107005c41c403100000041c01080d4090309020644c4000d19905100301750410600b079580e03040241e4a51a0912260090300b080d001078001d8090b81001028a040c07103080029840d801c083c554180c0d005908945c11034101198215181c0c1001c02600c0d601210034005058102d80012000b0700000f182044141048a1803041084e5045140d0441e0b01442d0064400c1c2007510b400a00c155441002400c00c0b40070340b00784000a50401284030a0701c61055242d070f60072403030441070b400704000c58102903c8580e0502 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 148021582 1106 148020476 148020493
    0xd050f0a0921090510120b09011410020f010c0c060c02190b060609060d0509210d091b0608010303020706091503050709080d17010f03020a06080405 65
    0x2c0300c0c1012400302c440e400c040364007200f1903101c3c0303400030328603440c5060055000c0132a01c0841208074052002000703820034440c002009115900008a85069821061600040c4818541390342d10485540d043c540d0020741c01c50b21000021004241c04c11407403002c010907401000200c01990002d850004491803210006183c03040d401855034200e1000204199154410b460740f180300941040d440312500498100184803c0d141204144920080109283d0410103101040c02d4503610990501500c4504200503065070841100c90308070b1801c1019000046100c0d01d4014078141d65510303441d501d1401c2c00390034030745c0c6071f0444820411103050901100e41d0b80c0c06130002e079a00c00d160000c1c075960ba40c4822a011816030300140103038041c40001074035048d07100a03000e00c1600307444650192640d9646450521032802d2100940240001d0b500700602c6000b040303096409801803040e541c644 = true := by decide +kernel

theorem cover : BRFrame.Cov 147841726 148021582 := by
  have h0 := BRFrame.cov_init 147841726
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 147841726 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 147841726 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 147841726 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 147841726 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 147841726 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 147841726 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 147841726 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 147841726 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 147841726 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 147841726 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 147841726 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 147841726 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 147841726 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 147841726 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 147841726 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 147841726 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 147841726 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 147841726 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 147841726 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 147841726 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 147841726 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 147841726 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 147841726 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 147841726 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 147841726 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 147841726 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 147841726 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 147841726 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 147841726 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 147841726 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 147841726 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 147841726 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 147841726 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 147841726 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 147841726 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 147841726 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 147841726 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 147841726 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 147841726 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 147841726 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 147841726 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 147841726 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 147841726 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 147841726 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 147841726 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 147841726 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 147841726 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 147841726 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 147841726 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 147841726 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 147841726 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 147841726 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 147841726 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 147841726 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 147841726 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 147841726 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 147841726 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 147841726 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 147841726 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 147841726 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 147841726 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 147841726 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 147841726 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 147841726 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 147841726 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 147841726 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 147841726 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 147841726 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 147841726 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 147841726 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 147841726 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 147841726 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 147841726 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 147841726 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 147841726 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 147841726 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 147841726 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 147841726 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 147841726 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 147841726 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 147841726 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 147841726 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 147841726 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 147841726 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 147841726 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 147841726 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 147841726 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 147841726 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 147841726 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 147841726 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 147841726 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 147841726 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 147841726 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 147841726 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 147841726 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 147841726 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 147841726 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 147841726 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 147841726 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 147841726 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 147841726 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 147841726 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 147841726 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 147841726 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 147841726 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 147841726 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 147841726 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 147841726 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 147841726 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 147841726 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 147841726 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 147841726 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 147841726 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 147841726 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 147841726 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 147841726 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 147841726 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 147841726 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 147841726 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 147841726 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 147841726 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 147841726 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 147841726 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 147841726 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 147841726 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 147841726 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 147841726 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 147841726 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 147841726 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 147841726 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 147841726 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 147841726 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 147841726 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 147841726 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 147841726 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 147841726 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 147841726 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 147841726 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 147841726 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 147841726 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 147841726 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 147841726 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 147841726 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 147841726 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 147841726 ≤ n) (h2 : n < 148021582) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
