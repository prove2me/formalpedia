-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_1491
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T03:14:03.294905+00:00
-- url     : https://prove2.me/submissions/2a4eb839-cb9b-44cb-bbd6-ce7ddd0bf88b

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 267985611 ≤ n < 268165467 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 267986861 1250 267985611 267985639
    0x60b060d1a010f0c0209151908010f110a0503131b0f0e0a0606080f07021006140102010f1104030308060d020d14160b033d14030610180b060d020702 65
    0xd003103081c102d0020352041b0038902103103c0c1040c80100c403015007030042c4040344c00782c18545c0c454200c0e9400e5000a074282d4403120701507690703a85442901d51500c058010b4610b4000e030402c0040043c403000303008480d459a1141203c080c0901c142c1080550b03403070402d030030b400c00380c81301e0003445180343d144648258841d0703140001d600132620b400380c2400c60301c40f0381f14500e140d01d0301c0b43d41101c0d05e14024000e10031071080e1200c54512020600541000300394185802c000482490002802e5407039190b102c60341030382400d40045201142c0030403241100d40501e48048076440d1301d00014092848035401030f5200080c400c1c440240000d401c83c4402140d400e00c122400c00c540e0881d44d1904c40020301c00d207030701d0000c14000140741d18100305082607445801440c4130a03001070a21806003007255400d01134880180804c05100c4010681c4610300c01600803130042c2044c3c9400c00c1182d0f0142080d0017a8040380461100c1c0161081441c1c00010042c50f0040c00e0f5610745041100e010001c0d0000d80080e4804d20340814003003 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 267988111 1250 267986861 267986867
    0x308100f270204080742020c100e012003070b0f010f0305070e060f04110a0f020102130312020a08070b040204050f0601021002130f0308040303021203090a060b060d1a010f 75
    0xf4112050b010140850f2890440e050000900c0d80760000144018000226041044003206000d83e404c0f1699091040303820500007440c11005c402c0300e80c080c005900c010092030b9080201344802c0d44003482c004c01c522190302c822030444c90302c403034107140c0600c00400c45004100c109891240f06925110208540d680d0382d450804075017903d0710010b421500009400d00400e20b00501d241c1d0b2205000d055071686c10110004102104c0c9101299403140b0808240d014902d82c4c002c054555003107651009500300010700000161541d52480300078038502807820450301440c0240511554030707401950190f180e0101d414240e001410450381244a01c0ca48000070341050024050760380960410784c0101000301810404000a500c03c80e015110a9004038000030fa030710800c881100558450030106494514601c3d0207840c000601512050100c1e0510400c98004000128800700d503411140215100713541402260840c406e003419824501d0504a0200c0348001104207249805d0081e41c402c0040c0c98034010407 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 267989361 1250 267988111 267988117
    0xa1a090a0f12031b02060627060906030727060609080d230f18010c02010c080a120f0e1002090109051909150801060506040b070308100f2702 62
    0x10912240c1c0c4114501007800c1046140c25401642800100524010b00c206196100b0840d040e00582c03001040100605054410482c3c44d601c0d140c1401c0041e40c0c0f0010111104001450140500d81d0100010b09594007000010000c00b940492001c0c228020f0800000c2c82070058075851903181015400035113a07214001c91400c4901c800301030134176001402c900b151411245200c0da07883c01001404c41500008002c000c2001c1040000b0b165a20f032006d0303030004c101201a0b0360590502ca0310440c00b40250760003c20700940540e102e58102c1d5110300c0714100796050704448541c0003080b0b00d0402d03051019104e582c07000c0351681402c02181c01800c1e042004000307900c10000b91600280c440c07203040046041c00c1d84000041095075541d414031580fa000300354111803003480d8424801c0e040600800c9941420302c100005420244e031681e180c1810001c001c00548a209001000c100303440000036582000c2c96510310151413154000d13071441c7d82d219031510380c08440720500c0b00805018066010703428454822 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 267990611 1250 267989361 267989363
    0x1d04150e1b040603050a060803030c12060d02030d080403030917220f05040903050702032d010c0806090402180109020a020c01031b08060d060609020a0f020a0c0510110a1a090a 77
    0x80a0b1502d800c000302100a0b00014120304455915000080b51031041072015520411a1804094440e45140e01c1c0e00b101c82c00107007415000e8641e4208070030160700d010400c40141507250502d500341d40c42e103160480042074800c8001e040b03480403100c1d1b082481d40354401000d41d0034525080c2d00c0c1c01103041c405080c0c0d140d0719105400c8841581c0c4010003a6051070342181e00068040c0c00d1903410407000750042400c00101c07800d2000c01141c080f000d10382502c49001d800c07007800700708002040300e40d801c200c014210041c05041c441c131a41c40c4400140843d624800f122440102e000448007095940348000030107904500b0380800940184078030300d007041d4400c1c4590000c00004800303280c01c02c2034100080e941ca100144c540c0b0b4004e0117000d01c00300030800c90702801c0000c041c9290b006a81c3c07500420010001982d1040ea02c0031034210a103850042507a6542040950350200c1e00c0740104032034080183d40140d00001640c07064003500c0d6100041c48070803646070074015509017043d0410303580c48054540303a50503440 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 267991861 1250 267990611 267990661
    0x150c020a02150c250807080601090e0604050322080319020c1206010504050408090d0c0801140f150a05031b1503090715031e0507030c08090c011d04150e 67
    0x100410b0a180200091134a6440807031140000c0340c44000b540c0c1404295002014644e01403001007050713224034858400019000c00140205081c560b80b5142c40303105401006020000a001851218510a92080c01040c192007142c2d507410b0302501d280b40800d03000500e070026004481805115007000000000701142002c00b0b05a5270303003010300300802440d020f84141c52915050040c22034584411305840000d070b0103956a900d00901d400b40c000c0c295240910a6000300c20781009110300110072540140d00804888020000b400e055004142486402d5000c0b5a141c40751120070001c00108030001071142409940322071902c0c2d20810180316601c829101e20300c040d03008903030410001d5030441404001d14103916000c0b96038940505405a41040c1030380c446203007035a80c1d00740052503400d413140f80c4c200c912504024460b868145c040a44440d0b10aa0a5041c0071b00c04900c640210040b40c07265a0f03a000040003004108041807500030528901c0c021080f40f28051004100d4809581c99041e40540c0b5102c = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 267993111 1250 267991861 267991873
    0xa03090b160512090715050c070602070b0301030f11030303100905010f14090711070609090c020703051207030e130504050f030309030313020f0301091b0902090a12150c020a02150c 79
    0x15203c02c01455000340316611500503070b200400e801000980e0600d02c00015911a5182c0d00f50f039950f10700f03000143d0302100035580085010401400c21109a81c11640c002d015088200000d082044011182c4c0003039940c9408004100072000722a10810310981380d02d6a000c0001d680c07a9144032032800d00700c2c081c03200404000d000d40c803040d2030096105940248180f40081e4040801c003106480d0203415000040880c940340c1d010f0000001314414891429110310081600340e15540301d1544a2685015084259600042e6102418080c040041840d03102512400c03025015290302002007906a0307084507207014190403945c0e0f20f000001924011030010303000c0e5103142c41d140080c0162004020089030031010708050607080c4da500b0b00c60030300428083c6108401c038181c94650580341c0e28164125420301d40c41403000200d2138440814017015500d2880c1c2e42c41c440003190610440c8005900345840b0010f00703141e05e000c0300c180d000c42c00d00c80b02482a281001030380902c00c10910903006943c0501140e50220b = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 267994361 1250 267993111 267993127
    0x1090c03021809091c03050403031b141308030403051b010c0b0a0209040e1b0102010b030304031a060d0f030903020108130f03081503071409090105240a05060a03090b1605 75
    0x2d101c100d908140c0d00b1084660b4000d45a08122507010700c0178412011030f5031740e001c100606805020f550b9403c022616512040c0ea00c4a00280141d160101c620131500d102107a107c40241400880c04081e29480d811280c03a280e0f00d1410a6890780f80c1b5000300c0c00100000001c850550181d502c0e041c2d2154000040e40720303030f03a4001c140c00003500008241648180c50b0f688080c0580803d2014407000810160f9400b040c045010029003035a00807210203000b944100410404901d1540607103d88400034890410103407250400a003451a0011018200f01420540c2404054108125200303c0c1d00c00c0c3c0310003485075501d5148428569880300090001c60201d9158800a0300c21f00d442c507480b5003a801c60004517011800800e207003640c6500120300180ca0100d1000c801d00e0954400c07036002010318000c0c0801c1c50700e003020003101203410302801c0c401c0300e8465032070f5126a10582c0702005000d014100603150821840c004015010500083d60445408030100d52170040041c0c07506030340b02c56074503400c0c5800e0072 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 267995611 1250 267994361 267994369
    0x370206010602120c010207022106100501020c1e0312120702010b060d0905100e1506030f07060c080f070803011401020a1101180e010f0303140324010c140601090c030218 74
    0x2103041d25055508111f0980140c0d100984511200c60030540030060400c1d001d40d25142a001401045001d24842402c002583e8005500c02c8410001d03182030415a01d0f500100820340d002886c15503040c0102c507011a040030b030040c0a00200140c0d0304c2e03111000c0d110004203a0032500c00341a01c3d0b81000003003140001e03510080c6c11541c06584a0340840d400705040c210b49000311182c0b41c0d0300e42460381060f580400b200d032085543d02c1e0845011000740024060308400c4c5951070b516442034009104c0520305d4807051140720b0302581c03607090002e56401e81e1036109140180d4250f20902800e401c00c690b0300800051540f0028036000c1c4a40d1240009802c081d0b244010b48420908040d0000c14108a28000c617220b203040e03410600a00306034031080051429440d01401580c011036217030019201c14002c01511098510991880351003150032110388090580040b20601c1e00341e10090494851280c01104141001601604880d070414041000400302c4100300c081e07110740d90a0404814425010880602d8 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 267996861 1250 267995611 267995617
    0xf0804170309150415111315090e15011b0209010e1003020406090e01110f0f07030e061305100f020601210b0c0702090f01050913030537020601060212 66
    0x1035000704a4102840301c0c003c00d407410104541c00c564042c44004c50201484490142650030314170022214109001140c1c403e900107158450480345590311561003240c18080d180d0b1102400510034450681e1814600b0f90390140c3c40c40c0c6503e8009019402e0208210020302901444140d009100c00d21b564a0280b00c032803100000b91104800c003003c500000010790b154420034000341510603010403889d000d07600f26400c451070000388015022081140a9804a8001c11103203041b1100349899103840003400e045a0800c0841c0070740344c02003800a055020044190828000c07560119545134840302003080490f100181c002c0b648000d40c0c031010041c843d00b10352071000040c080d030080c0c144100d604142c41ea42c801420a480e0300d076280e50001155429400d00200040d8480c125080d400d10740d5241c0f2010400c0300741c000b02226030036021591008105485002258100e0490f034480410104660007240300e4101001c035070021a5011288076a182c0340041000e50494810303030054000c501100280f40007640c = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 267998111 1250 267996861 267996871
    0x509040f0302250f0501050a020a0f170f0d0f110d09080c0106300b0f0403030e0607090602010b092208040b1603030c080408030606070f0b090307030f08041703 70
    0x100500c000d076980003c41038144224100006810260749141c11140d101420450300040c0c1041000c10016000755000511b000750103502c041030080c16034103410107005490f4202039000749400002149018001642c0c00380600847c00001000825418202041100d8070b05012003204441800310b080407101c10f41c00142904c0c01000e28503d007580e400c1e105421101d484c0c1110b50801c19138101c481c4101d100f080d15007800d4a198a410184c80c425803a0504400c200034094049907c0c2600003038201442a00086003500c070f200c007240e9a03414800000b038030000942c00303490010b619161905a00d89840c0c0040350040c2009507081c0c880d480380c0e55420000400f4071a06807840c250030840025024451002400031f000f0207500050703001c8581c5001030a403003451211b0030402c0310f540709110100303d00e4800c80743c0100080b01e0346a583c000741c2c5401c01c0c10140c40c2d14058030300c3c6072050400030b0480e408001801080e201e99180b9641c0090b020059405540c16078024010b510100f400356a21142c01d401140c0003 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 267999361 1250 267998111 267998113
    0x2010501060e0f24030709060804020901230d080a0215043206130201081e01050103020d0603020402040803070606080610060c0201030204260d05091c023706090509040f0302 76
    0x2500c4e201c03254054007044a4400a41d000820040380a900001103805000d0ba40303854030080c00c10340c00040c0d440304c06014000500c00c42811262850f21100101c074800c82c00908429000701c55030420700c01079044441d141d030250040e086d2460078003a02c070200c0c5104c1c3ea8884882c0399803006040b0500c00001a1100d038441c1804c0c0d030343c0340b0340c3e442c18200a2140309800d9803500400740112440018000b84001d456003280f240d0040d002c420301d84002c090603055403000c1ca001600e8001e040001f1010300b201d944041d400c5440000c009c50107000c0440180010f41c001e03c014001d180c0d9036903600343c1da0502202e0040c868140140d00f8000b40d88a07000c81e0400500524000d81443e464403d5003008056900b5501d401117424131184450301003d1000c5038201c4003034100b440c2440c0c2140b02280012103d030542d07940e84070644408c4030440d9100080100ca10580f601259249801d0400586010750800301d401c4820f034207001d001079501d108014180c03d071007010348544810b8442c5d50310000000c1e000b110803015 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 268000611 1250 267999361 267999379
    0x60a0617070903230c0603040f020103050603031608030108010b0105070507060509010320031e06150d0905010203181204050d02120109081801120507080f0a1503080a030c02010501060e0f 82
    0x302e9255401855200c4c940150949450b204903c10b03413030132004205841c00389100380b04200c04201442040080ea503020b08000c00c3d96030f28540004d0642c0300d8101c0141c20484940004000e100082c00594107a0310903030000c00c0401010340040d02c16001c1c0a0b00102a50f101d0441031103114403690141070005c606041c00b0503114500f01e0050303002030142c403510403c10f0000c801c1020342981c0b03c40c02001907207c181044041d0600402151581c000c036040386031950000603000c0e068035581c2d4044000c40341c10030002c54480c24601c4003800348411160000004d8803401c200b01c40010804000c660840300000c101c119200071640c2480400e14011404050301c0d5610783c0b4440108807100010075140c00044144800040320f60b00141c8150200c00710070751220f15080412000c9600030300401c0c0c002c622101440312941d6940f031030038094000401400048c02101d00c001040004a8010741031144203510140106201102c0c22822502c00740319070400284000c200740764a0812584a004c210409403280709 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 268001861 1250 268000611 268000613
    0xc0c0f120a0206060a08100e0f0319090915150e090109050a0e0102030408090603091c050403020414091b0d0204052719110d050a050105040605060a0617070903 70
    0x420520354020180c032266000501c1c2030310660600c02c0583c0003904441900b4905d0806034100c1d0364900100e014030089591b026401d980940c1081600e20f4a80c2140031250b81c1c144007070360f0082d8806018481c8012030604907020840e801103000e03007450828900c548099480c5029080e00340b4607480c0a490080c030950400b0020b071521101c039902e010b461040300114030b6040c00340d5a031080300c600e0100070311613901c10b005120000b041601260310080040320110703120b1b105c0c041814180f1105900e4a50f480b241c6000700e0207250b400c00090412207008031000c004421540d0400031803000101e500c024590000f00329544032000c0c41c0140724002101401b180c1c0064107070b0b8003107400c03a0401d440742d200e80b9407121b4010510851001c2030340d145400050151890406140110f070b04611500c10003426040402d55401841c0c82d00040101419004000c5440010303180c1000c034020b2805580c1903d5a0781441c001803154100201c2c60b4007100c030f2654801c0d44903c410701c695481050040d010302d080024040d0004 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 268003111 1250 268001861 268001863
    0x50316030e1e0310020903100903110d0801030302330406020d020a0203030a110405030d0806040b060d050711010b030c060708040e070f0f0207050d0b04020a170a0201090b040e0c0c0f 80
    0x21035903042c149800c00c00c54a40c0340c1014908600f51080044207801013005500d59100401c1c5594034802262010a000d061882d00f0380704030034040352501140c400d0a034400c1e86140d0100300b003812a40650260b404ca00944803a0f4244e17011482283c08130020850312440500e09079400403503109018a5005003003904414525090fa40010300e101d006910103c2403180048881c802d00002c181d01441080c51b181c500b2002c80c0c0c031f07145500100014481440000b458a85550300401d0900d20003d10460340e900c1b40d411000001d0500384c9818001410101d0400180d000500c25100e100f8402001011149914020018654005c00d001c40340c40d1411304c40082c403860408201c41c001c04194032112411303a05608018916000081c0c1442194070203041000f142d215440c00880d2660007031580003041c2d07268004201510140d84c0420841045c00e20740b03544102d40401c540300094802d99640520390742c1c560002e002c60140b40101e11054810b43c002c500c420307044000170b02502d4030031420740d0080c481029110b = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 268004361 1250 268003111 268003129
    0x32102160b0f090d1b05070603051905010605030105061303060c17150a06030b040e06010b090a06020c06090904020102210301090f0516080907180605040e0a050316030e 74
    0x2480103440280e054040003000e964039644030001c0c0c01061042e18040c04100e5032005080c060304240f266034260100ba810095190034441074010048404055450310010020300040360740f0800b00b00b0800c005000c160b103a005440c12220107071b80d80360940e402c1504126282e404558105680c1e000030b0800000a001c2e8011000180b0300394959403500c503040c001a06040740010103400c100a00c0c10307004426039854891032000d40d1042e1800080501c150f0001c20014903074500355075000d10500700001405d85800c0d00420700000c0175600445542d50b10442680c0e07038070104181541c888801c2c00383c54441e060941d411a4401e0051048602e120f08010040d100e800c43c40b42a5000c0080000062081e100b250040c50000e007034600d400c0041e46040c03910f04104200c0902d151080122035000b003410b10721b0030460340c00a4810358405000c08450362584000805071071065070700507401d0030491030342150701048031054240c010028600d060b18507804249410001a01203003031005003070552480c2c0c0c44010300 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 268005611 1250 268004361 268004377
    0xc0509040504050a030315120807081b010e010608070803040e04050106170a2021120d020c0c151804060e040605061f020d1202450a03032102 62
    0x381980911a007001010f6815180c54054405007c510400c10b0b40d00051201c0140d42d00403540c1612000c4a10b0314030f4540c8241c6440f4801da1070b4051030480d90440660043c040740412800820030729503506402615a81e4500c03400b05960824482002441d40050780543e100388204000610701e42c0351a190002ca043d0408050001d03400400b00008002c2e0440c8008920440390208a10203078030b540016038104000e19002424018100c90105c2c1000c04000d01a08162001085a2540214075507040250441d0f90000624440c280000102e814000c50901001d90032101c1540b4000320000110700680c0c034000129000b0341d84030307800a10000303843c100d9800389104250105075070410608202c2c0711182d0b103d01c2230191003075680c07400000e50009030140315221142041d030f004c2d522501600c4002d008066521300085280c0384031454200d482d644d0380400941015003143c500c0a100c9500c5120359800c1181c40c1c0200c0c800e103042c404640120440040743c1d0341034540b00e03100d0b00070514420980c0c000d862 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 268006861 1250 268005611 268005613
    0xb18040b07110a0c033e130203011a1615021804110901030c03060f0815010602010209060a050313021201020a0905010e0a03020d05030d020a090f140f040c050904050405 74
    0x206008285034080340340385500e01c0c80703401400c0c031003d15199014081007910005200140b000c9010b446424200c01c00c5000c2c1500354001c82084804400d80050f44a03044140c610a01c0c40c207860000c43c800c6442030340c0c1661104145040f04103040e00b03070030300b0b954008403641c07a0300500c000c0e0303d1000a503044070601c0b01c0c0c8282c1e8070140e02c4860b450842070b02d03103880c8141c4034812030034440c002d0090701d609025a11000e20900c0c0100d52000044000d0b0014802d54022404200000c1001f042c8500f0004106139040c40031030920030b0780d0380e0380c8804a00f00d01035002096880b503c10007001401c2803207800616040501145215004507250340099951296800f180d0403a035008113180c0e82d8660130408400041c8000c2c2444511360100754009002c0507418040284244503445440c000d000003001514185040308008565072014940c02520003003081c801d0980e242802c1801081381640000265071101c0c0141102807816511000c01001c0c10f6008004800c102042c0101d42c400e545074064103000d140120 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 268008111 1250 268006861 268006883
    0x60715110405040e030a0e06160f05060f0f010f0302060f0c0604140d090303090515040b0705030d0b12060a0e1c080f1008100b031f050f0f09030a030b1804 68
    0x1805100503106104c6060099400500c1001951504034031202c280c1501210207950720000c0d82c513409000c2c0e01484000c0c101c080c8008041081050010389240500350301d03010f498969644001c80aa401000d0041000c2e540720b04c2e50420040c00c200c0042c0042c8508036509038240f19050078054a00b1a08331000d0b5401504030070980c44504040c410b01c2c02565030780c85d08461241c01c58070702910749c0c0b10310b02c00c4070f003e044101c0440b01000b0286056502810024440c25580c0003281021650794109542c0000110320380080180035240030380814011145401c0500141d50381d00306410001c010f190f600c90400e001f0301c1000b62a01041d181a601540c51703076158803046040c08200540110320081034581690a4103800380701e4103c0025940e500c01358100400b04084020740040380c00c156042c200d605000c07442d0081d10007081d15503000184140c0344034416805554512842c880301e03110507103003054903802c200220200c0c0c51080c0c014006016002d40944000c1500d43d51040000b80c0449007500d958502d0 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 268009361 1250 268008111 268008119
    0x1107150c030f0908033c070b0603011404080d0b060307030204031a071e0203070c18050601031b140702031b0909010209011704140706050d0b030601080c0607151104 72
    0x8410024203a1040c83d01d0305256042215056881c42042200d980e00c60501090445007856403c01500d40d0180d036149100c2911083c850304400c0c1c01403041205d030680300e00e0024490b030505225942c90040714900380030098072951a140c9269200800e60ac076034035200cac4403010541e01e4083c01180034481e5a500141d41d00d01d5400d14203104800380e800208074034180300600241d0342e4045400756904030300d00c890007940ca04040d410391a6124100c00101802c0c810040001e2000b0036002d0310560361000101845242d48680044046030302d522094000e000c100141c0300300c504c0c850880074180c0c01031503045602d08805a00003030b14040140b4410106080d10006596003030500302c5a00d03410803158802075042c003101c1c900203840106024842c03800101140c00160070300100c0000c0d2a5410060030542d0f08403521050014103540c451403451b805142402660800c0d803e00040d15030403035030343c40e000e03000800184041280960100e00b060f5018004c10100380b0700660180325510b18120980130059440f450 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 268010611 1250 268009361 268009367
    0x912150610091a1b100b090c071a0702070504090501020a090501170f070309150504020319150e0109050303011409130515040312090503040f0806090d1107150c03 71
    0x21020440c0c04101d0000003c001c42100340aa10940e960a5150103850380c00c2190030520802150031030740c1d418884c0e5501950410116480220385c285c040e11400004d40d100c00110901e40324242d0010039064080200c0c00d4a001d640e001282c0000352841520307481030355100005c06a84d800c41007950942d500041d01e100042d04980310100900003800d18042022041c800d540f00028020040801008490002450b86100707a00001000380c1c02400c805410802101000c0200800c4508078001e05c10310340203015542d5614040f05e2202d83c0044031066211150b50101e000e00544902d442866488009201c0083e0701400654003030725040e5030003481d1000f41c80c1048200e07400501480c039030f4140c9102c0400403e0000c1000340607141c908400d144603840c0d52904594950704100d04220051401c10360b1420041c02200520407543c0c1c12684448003900c0c0c01103a62141d10503202d13403400b031344489644d00185015031004a04608402c09a60740150740f20b0009005443e03500040e000a9842c540b03100805070 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 268011861 1250 268010611 268010629
    0x19030305100f05010c03030b150f03070201050903030c0f07020406120b0f0109050421090906230301060806010303210f060504240b0903030c0d050304140d0c0809121506 74
    0x40341c2c140140420303140c00c0010385000304849018041503116010515582c894a4449001011003215039a07600f4014a0010440d041590000015420140412905000001a13070701800c3d44070b154501d041e046d03132480c541039800780c00200d070070589580c8000703500c1d018000701000150082e1035202c090720300710b8810320400c0c8050700b01d43d0f03034140b400041c031011a62aa00c3c02829558800144010002c3c003402500e180c503259114800984c14468081000c80507500c1e000000740c9400b10301c81585280004241c00e0310400e019280c102e42c008001000468400d5181070640803500000c00402c403503e02180e0156032295110745145900c0380b00c20000742c00c0512400031080d10081c600c1e02c0941044800da255810148600b00d05070b540400c135110550750600c1102c09000024040701c4034420002005012500100c8054510074100500c44103100380108035084a40c13140d58038a412815207686490468120112441d0070006007102d60381604010000142c40d2114030540108a1501c1410041808 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 268013111 1250 268011861 268011869
    0x1a0907030308090105220222020c0d05040e15010519081005010825031e0905160b03010614040302030a0501151205030306060c03090d08040302010306090204080a141903030510 77
    0xc0c0c50300040010700a0041700c050f55200311491031b034070382943e90300000d402c6c001e4410500340344209600000c1c00200c0c143d402030903e0298041600c4032074056480950362406503104196120454500240e044c3c040084415140101414218204101e0075820070b001421465035001150440090140e5803c02c4c1011500412003460300c041c0a10302244c0d20070b0380e9681514405002502c010b102a01203001c1d8001c1c034001d509200c1841140300d00a05018050440d91000340c2d80d60250700071544041d040c0808820564020404051440c2d103001401ca91441d0320b006a141e60140521010005035014890f291400d4013400010840d2240043c1e030400c00c0c2c0c1c1c65407000c4020102c2010071000603601005407644254101c0d92a6154445011080e04500c05e2803c103030352081100303005404101d1914042d00c05d0324000e1b42d04100c402d44400301c0b28100d101d6401140c40b1584124000700001c1d004c0d220421045019000b0303130b01c03c02d20240810301c4100b100b010403000729440d407040012110145440304024 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 268014361 1250 268013111 268013113
    0xa080d020a0909060b180103180506040b01050402090d121209030e01020609030405100c1407060c0302010b01090609050d02040e030316260105010810050306040f02010e0123071a090703030809 84
    0x81d0f864055044c5d0140314041200c0204020400c580400b68003940c40f40c01c959101c0c03100c040c1344051614025444440c05c1320b013152800c00305000450103042c14400d5540d198000b40504184810365114907402408503107200c01044840440740b0410640340c041e28844174480d48036640792514000c0064201840104120b09a500606c01003215555000c12003044100d5424141000d07042414222a0740c140208420058814581d00048103940620200900340c081d5000f0003480c4055401152542100c0c4640000601400400e0005d8034010720318013142c0340700038800658011104d40c014110341007118607070315203040c4a00800d83c060704410074920140104080040c01c4c120b51000d8003c5c1c58040c01858100704d0910002244074064420302006404010704454240ca00b41c505003402c0301007100100c1c0080c4650340740c000c00c3d50240d2490b01c580d00d032540030400041d2302d0781800001c0b03401c045010307075a054040480320204100c0d104128020441c0002a220380360a500f00941000c0c000b920460407 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 268015611 1250 268014361 268014371
    0x806031903140c0709091103060f0f0f07030906090b0618010f0608041b090906060b07050d050a0e180f1e06010c0807080a080609150609060a020a080d020a0909 70
    0x2984102c024081e505001482d03500c030502c01c28500c0c42c0c038501e80c01c900c405d9442c0c80c2c152418010711012261003914120112202c0395150502c9152600042d11341814401e1070704003189003c404001c1c8a540a8918580061117074282d40381c4a058500c0765205a4612054070140061818014140400000e58005079010380d4034151080c0103290083c8510b00070070043c54041010400186500c0d51080c14542c11404c040e600d46e039806008000900c412180549880000600d001400003603440040c1c2010107840f8110380790500f40d0301640b0580c1c1803020407000031010201c0d9510142c011b01381c2004802da9411a2600703c04501c500640940103004641c00d83d490054034074032034180c80760300490a00c3d080c0c1e500ca0551400580900403440010700409001ca428658960b004283d148120381c1141d42c5c240940f1400ca40c03c0099200701035040d0030031070810145405007004c1005180d00000e510440d04410000d40740c0081942000c00144480c40d0001000003c042c1d118400ca40a03011081040003 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 268016861 1250 268015611 268015613
    0x60402070b0f060d050303010f050f0409020f01140f0a0207140405010302030703030f0201200324130b0604050306130311010506090112031e09060311031e0a020c030a08060319 77
    0x7648107005100b6600c18111100203001c0b030f1120500d03884a10b81c4501140c0d120b584980500080303001d40d000303032802486054040b00d15403400780500000d00380c0240549050b005204011518060801d903404140c40d02004204182542c8800034100d00c803507075000d82142d0b03084c00000409060142010f601c5141460010b0016a03004900ca804032030b81800c0c0f0000a424085040c1d01420040300315100c29000c2d8400211070311030b03a130000e40c23080300130320b9049841070034002c10841c0c181900f00c0c0e4541c01504141020507099020341c0b01030700c51170006007803505090752400001c1c500b010403103e01415001001002c0708264100c1e4454071842c042e80004d00ca5072610f840850750400b81403040340303904c0e807566807441c061500a10009800d901003001442045403217910161400c03596200b52000a4640a01d00207600d8034002600d00480003400d03c989a6031900c00d0300d0340ca078000035004404440e42041a019445000c00080001c0401038540f6641842d10000b014140004100034410707442d1080c100700 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 268018111 1250 268016861 268016873
    0xd120c15020f30130b07080106080c07020409050f210c1b0609040c020303011805090a030c1704060e0901050108040b06090a090203030c01060311010903110636030606040207 76
    0x504041c0001c41c03071002c00d50320419450b1201d9a1514050f119030501014002d8400c1103546840d0418010751422441c0e07110480c007180c200343c0074032403030b4005403207100454a000e21382401010510300080010130f0400c15038840b075003800c0800080122a0303104030008040104004402058800314000c4141401c00c1d0404158071001d482902e855158101c062012055940c40141c4007100c1c40984100041840450302941e02c0d0f000780514404454104c8803524a000c6a0003110b20807203a110140400e244aa0ba05554514114008491400c0c103100c01c0400c054a100141004200303540d00c00024401003c01d0100c081c03c1a0400c60400848a08000104506e00784440d08810261048182c540c0c03110640002440100002549400006110172401d04150040e50980380502c103140407840882c4019158180244001032210a403c1c5d800c0783d85c3d151050213410500904901d540c0c2c281e0418102c06002c460b281d02150070260164112409400d00304440384d44240280c0b0114585800c2c0c1d1601 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 268019361 1250 268018111 268018117
    0x201181703060a03060f09030806031615090b03090303041a01030308040f02031606050c0714010918020d0c0201020d06060f0e0906030f150f090706050d0b0d120c15020f 74
    0x214100003000000320b8415100c2e000a4001036800c40000c02c8101107103440707440a4001500e05900141c4124003041b040c0c9404117040504030320380820b0450711b500d00001c080d0800c4650710074030107010001000148100441c00210300c00c0d107a82c400340d60381c0e1030189007011410313440301328122103005e2080c010300019030045942a08107400c11380c0e1401c0400c00d84006490f0180e203215005c034030740e02c4040c0000e24a030800060040890722405032507610381c446840c4444000310455032400110400c200304418030ba070450802000304180340140c81e20700c0c4006074005441120b01d10200603980040d010b450b07602144650b5016008074585040800400040240030302c0c21612114400c1070100c0c041450307a48d04102503494001c0910644417403e020301c0642c540107100310380e10082045640001030364000d0109034081a101c8988490303080a0802480300007c205644800340c0140c503038105c02000ca5161480f01034a1665951152160040c500e410114603070000b4245213464010302c200103c1454110503 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 268020611 1250 268019361 268019393
    0x103120809100218011407021c0f050604081b0c0f0f03070e071110021c0c030b130c020d0801050a0302041104030f0f0b0705032e0503100507020118 65
    0x1041415445055030305082c0164055510540791000601aa40c5080b240c0300042a41e0241c880104500e0b8a080080c00c0c1c0c460301c680250310400103c0d4482c549103c4581d4100d0f0a40982c14409a4500682c1d42c28540031303056406840c0e0380e4002c200c2c4e26458480c150038410a00380f81010b0000c000001d0b000c6409040300c8504640700350214115041261800c00a020081c94001c0c050b9816040c4581c000e42070002c03809009469006541c51280d2030b090343c4c003c541000d02255190580744040d02d00c0c5100418815046004064549039001d125980b159101c8005541784803000800c4140d00c80064540b61a400248040c090407200410455548030110385c1100d806079000308001e6a410201c20306440303076802c0245485001a8a1414481e05044000d841842240106440c0d160210180c58500040350b00041340640d07401080422200300c0411000250140d401ca03454681341d80000e82820b0007482d20401c0203607904100a40258240101d0342040b800d010342d10009005034541500300366034005 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 268021861 1250 268020611 268020617
    0x1090c0315090b190b0d030e0f0607080d05070905030703030c08070303021902030702040b04020301030b04060f02040b0d14100302060703180506041d010504020c0c0d06112b05010312 80
    0x141400303451060b007001004590103240e1100038a0900707480d80c000300749040c0d1207130f19030f00d005d08282d41c0e41090b500d146521901030720b81240010000c0c0420694841a000384c640000003806024002011480038101c54000f40b1008035881c42d000701d004002001ca51b100c244a036114100400200c7d401c41c02e41e443d03154014001558821640c10150064820f0104202841000903149414168084040d0880a100300c80600180640c9801c00090780801c0c0805030845400001107000560341c0d0740848802080385201506260b502e82c20035070507800c00d07010521840e03110b800903a1100341c0c0081007607014082c1302002c0005821600421024041e0310700080501550348004902d444d80c0c00d01c3c1000600e4006c2c00c0301e59580e22a202d860014007120348843d81600300000104d00c0f440d103402070700c22844400b4020b10341503560008100c506087da080a0321007540d56000d0003071000540004000d8084600000e49074020070f030078115040a0200c0207400154603213030051000440b5044850040d000c149 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 268023111 1250 268021861 268021883
    0x902090f030c1507140a0c030b09030307090611070906090608010f0905150a0e0a031205090609100c050913020301080708011109011d031b0a12080403060507050706092301090c03 78
    0x314003002001503091740c0400038401d44152008100c141c044100680741b040c4c80310052a1940140d0b1950b13400305440b00d80120b04103a40500010303101e2050790f2650f207101c42c21518001d5581c00c2c10011aa0140c1195420507100c2c5e0007803000d171509020314000e10141d801e0401400251b81c54040d118810b10032034800d00550b207004281c4400d45608605246a5004c05075420f100c030030719010300420692041101424100400030700f43e24804985684034032001c1d07010788020020740d0404c20042264180c03000c00e00030107102d480341a0b16070008042c0302c41445070740142d0f07079410035a4a030714144181d44008216810541c550207241c9810741039030a610020300707023461400c101e10210040191035840305501032181682108005c0a03185c050340d4102410b8900c400c0b80e42c3c8a0410400303500600d4000b41420a040200708005170f1940d1010768061010b14009080418603601c0c0b030242e642c144402d5880c0030300c0d0442070038205403081e140000c0041c118000c1001c0c284030b076108014014103200c0689030000d02 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 268024361 1250 268023111 268023113
    0xe0603010b071b090c08040c05030d1e020102040e04080a02070f230112021603090618140604150c0308180c0907030b03030c010519050915090106030209010902090f030c1507 76
    0x3114150054000413400b80b182084820000b401041e040714260f0b05a181c0d040d000450f410082002e540f1044103543e2000032001c81c1c02c81302e00318a0701082180c21503508110014038840410401802030303100b001e205564100c0d00c04000c3c0b4144581c1c004541021050354100000034001c8100741580300325980020b039448030400180d441e200403c172000c155900002e4403c000380914030004d400d0724401d07224620400c1c0c03210710403501601c0c1002c0007502d07032407517610520240b160000d042c450120b00034206440c05807111480d18134155012040004107096100e02020190080904d90344003491507095a189141e115006560301c040695440c000c941420115804034800e03040b40300d0106000c3d04981d51520700340107890081100b19080302400704d84a549000d1814180070b0b0034024150b01c00104040c0506c0c0c510400c004001400c1c0001c2d41d96200000401600c80480450080a0000740140c40f9031100702030013281801d0301d126500c03035004003110704210354851a21802c00f405d5044d5850302d807034103 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 268025611 1250 268024361 268024403
    0x1e04180e1902060913050a0e0c0f0d1e03020d0807030b060703030c02010f021305271803040e0c0408011506050f0f0408031308100c0c141c0f0e0603010b07 68
    0x400b43d080d80c000002da550045c25201c65003200740200681001040300d0780c07024210f143c0725074801041360f500c4000192141400d00d410281120041c0c001c4a05500b0801000100304005199800c11009038000d06802c000d903680202907240d2203000c0d030806215080011000600900c16103400034141551000301a140510035800003100e2116040d086584050280e031703111490005106580c819011408041c0e195a0140320719001302040c003000000c25240c8100b0300441d89141c41544800e88800d100004803640f60903099405541d01e250900ea4403400c206446003900c084030320700300d4404565841044450340c001d04440410151044003038403a080e40d401c5600703600c07490307202d08024031002ca2580803203650302450104544061044880c0303215816420000e41e14064013400111300b8110b40540401c19250a461003442d030b00b400c0d6000303614a00001d003031042014580e20005401c4d98807002a00d030b04081204140c1200b112014215850070f4010009403041c88001001e014806040940b8081c1c = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 268026861 1250 268025611 268025617
    0x916030f081201060207150203210606070f0b0717091b01050d0603080d05101505030a3801180510030209030a030f080a05060915061e04180e190206 65
    0x1c4000550202944d40d040002d542d50440d0040d91844080014100b03401400041181d11200410b291200440d550018402a80400400180d00120100f10800015404402c81c55000344182e0038004a410841401440540401980c1f100804d121050044100740011024050002d84070605002415071004031924080c0d00d4521544174185040481007001c40c00c046c01c0c00e4031840c00200600d5492215000a0901c18822600d25600ca10581c40c121885030004680c070108002c2c0114905038402103602c4500300c0196000700390110008840000501c1c0c0d5040b18002c6000d184c45851803020f04140b1080102502c40ca5105000303108440807aa8007a40503140389000003010755010612504014180030781d21400364000448030f40004514118912880c0d005a0003d40403a980e5911140909200d01d68080360b640d1000b02402038100e581da03107000010420b104800310584840c0703800e5201c5440c94030351031089a9507040a620010070140000d8055040b030328803111a566035440e0002c120984 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 268028111 1250 268026861 268026877
    0xf240103110403060516020303072118050c133c14070e0418020d030c02040e030904050a020301140d0f0c0603020316020c090a0e070b0703030b090916030f08 69
    0x4002c5400428031506500a0f8481c1018065480c198100071704100d80320f1204640c0e0b0b8001c030b4a440018100d440c022066420384013a40e6100061580300e4006c40c4c6a0744031060002c564035402280320580034102175001d01d1040b003c1c04d005100226030fa07030701102407c01007441c3c6560400300c84007040c460700d10403024080a0790710303032020002da488040b558265042d0895840000c585141320805460600748102c1000001c0c0300840400300c0400d40c00c100900d003e1020907010040c007400c103100035a58910940241c50600b00007540c0da41c605400f804195a8010454401c441c4188010410481c81160280c4524000c454014090f5454a0039004c010b010a402500744c11107010302080403038041c1c4c0198040c50400c42001003c0b401c546e400c9903598071a0640e150056941000f04030102155000306229015090551f0480c5440340c00145041d00b15001c250002502e83d108641e03541017401c4401e8100b410100600b5841c2280010282c01d04091300c002821000018100ca052081c03c8041e10111 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 268029361 1250 268028111 268028141
    0xb09010501080a2c0313061707050307050c070602030c0c04050c03040b040203030f040e06120109030e0f030a080304050c0906031b01050a09031a0a051503060103021509270f240103 79
    0x40b01034142e031740c0350000e20515034510810040880c84500418224028080e2400d01000f55a16030408072410b40002d06a0f80c00d0001c148a0300301c901d0424032880c4042c0050754001d41d02c0309284000d06203804255034034540250b140c2003e01c00c0038800c84040300d60264204458503a65103403840403a155103d02c0c11054070140c2c010501207818601c1d509014020801150140303200415001c44c542225010000100841c1488040f091070341410140d0520f0b00c0e1008007074a10b843c1240e102c40c203289c0d208403011a0a40c1100403060090700e40f44030383d290401c2c001d130010710070540c6c1c7d811800700d00b4184444440c14000003244110095104107559009036900040c00c44c0400e290103448594030700c050700c9680c2a203080000146c54500b09401011a02e0001801000d050b480c64080c45429200c14a00c9003c061080011020b16100e5002d042802550f4850350f02c9400020800010554030140016000c5048041032200011007041c0308408120350300d0706801c150440000680042c02010100003503 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 268030611 1250 268029361 268029431
    0xc1e140a03080109020f1803070902040306020c0106240309111314061e060f0c010629070804030b0a2a02011a1c050309041e0b09010501080a 62
    0x10020a400424a100e42c64240180e62039282500903070082c00880c107030841c0184141e907903000713002d64900000702c005815103081c141c450554000b6a03101d41c06c1603580325000148220032000c2407150780c0003030100f100400104c805010100701903a44043e00f02e4100354441c821002840261801c8403840000140403203482004030107540b016001c2540e0001303586000000040050910b10000040040c400c400c25103004181c00030001550042503590941810600c002c0003c044248206006800d0700c092400603500b460094002c07601103034450f9035842e43c0074001e18000036480001e46040d01c0e1700c810303082e540d070396000c0401004068480c0380c006100d11401144200510301c4410044801c415402800140c01b013040203201041819400da07004803032505603050700c24070b1036000380c0c40c2d03886007094910b0940032000103400d540c90118400f21041c40903245020051892040c0c000080c03056802c64241c3d0315000010b001c00100811036a80540c0703603070414007400c64400594080402c0150a40c003 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 268031861 1250 268030611 268030643
    0x50d0308101805160908030328020301061107090606020c040b010c020415090b1207050d0819080a0e01050f0a0b13181e050c01030c1403090f0601050d030c1e 69
    0x5000107485800107540e807056032104c0c031440361a000007030b65198801507185880e07030360f8200c4480d46d01da1400740c000800300b001d01301c3c0c04005000450007045607a41d6800809207003070003a4141101e0781c0c00341d000396152510810001d90045241d18408008480c00156007914400503106100301c0d50000b98400e15102280e2041d584040d4058280d40403102d08001400f00c89082c0701c961072000c20306100b143e20000c0100481d01c0c01b06150880b20b4443c1c546075052881164410020703c5004814a02040ea001c00704a50442e0354442c10f11610b021400074445802c00b01c186c0b01420102902d501c1c21360340c90314806143d5440d66100b4906240b00741e00200080c82d4000d58040710501415003c40e0310300d503030785518102030004030301e00f20505410070060051613440800640080c940b10821000740f010039600c5030b0220341c0600107540300341c40960107003203e5045800d070242803800507004584100e05000301003000c6607000d04150800342e405801d100b588200521000146489080c00030100341901709030744 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 268033111 1250 268031861 268031909
    0x30e030607020d08090c09040602070f0f0305040608070906170c190c11040903201204090c02010e011a01030f020f130e090d1d210124050d030810 64
    0x10f000a69503481081d0302c0c1e9100b040e0301d0b00e21140030f40f98081e6011010502107900c940c01800c040d442907480c1030030030001e40da440549001420f030503004600082400c00030113803c0588690b1001c001d160101d6010306000015100300c0c00407c5c01d022000c000c80000e42e0003011641194161440110724810044041000800704160420308842d1401560500c0306582401e000d0a41131540c0b5440d461b1150ba888294000c42c11040814141d10780726261b841d0502c107200d04014009020030800110340788130440406801c0d201c1080011300c080e85010b201d0381100304488002c3c41c2c201c1e030034038010504540c4c2248290103406081c0c04080403010000300281d06809107000c2c001103a508061b10062651804402030b11022003803c1200416202c1c110742d21007089030b11510340c14060080440c00c0384061000181020725003203041a2150f03540712118141148d00d50b030840c8203c0914213544003058103005c0860031807034118a00400380040e01c00440c3d88040e45442c01000307068050000160705507003070100 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 268034361 1250 268033111 268033123
    0x20f06040906140307060f0c060603021e090f0c030105010302070f020910061806120e0a1203060918111c0f0602031501110d050a020102090d060b032413030e03060702 73
    0x1200f020028025580700754100400c505044071140d0711520290111000c0644401300001021580669100c40100050f078400110f0310021070b080b50b40c0c2e13041a400d001403159100001d45505182e104620801c0350206a03201200c2c1035030428640982c0b2102607180809040c0c01d03040c8000e40c07100755101007011460f82640007808543c2203a0700d010b4100d0148008900100c0c80380071f084001180741c00c2d2a20035109940004042e065120100c0e502c2410303507160450b0200e40301e4106070002e91100740c02c0007024038034050072035201c69640c0038102c030201e1550344040c070f2410044414082d8440e0145a0001c1b002585600c0032640c0004039000b54074002e103881002540221542c0207071450424540810394400d080004150921390018205440d01c54402e0b5030580001d1050300c01c56401b00314001c2280c440c41080c081d4107118001c08999000200109400d00c19159542d4040c9440d01103060300084000000c40d030801c40b14440350040c5086400c0480300150351a4845030140310709030038821551f500180c0c5e = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 268035611 1250 268034361 268034369
    0x506060108150f0d060e160803090a12170409090b0a0e03030f10170313120201090b07060f02030c07120816030f0216050d08100b04030f020f06040906 66
    0x15514656506001990031034801e0715454040816140502000d00f0070f1905140106802043d002000503265280e5054809030400f041094100b20081c0d800901481c401201524a8202940c10800c41d000071030410f10941c0306240000c01d041c1111000d0003548114000d03d8081910188c3d82e45482c1c458640c0605000c002c01c6034941403420024141c80142c4c0b0404001d814040c020310f2550315150a00d04c2010000707070800300c0c014140100080c0c949540b45165110000d03d038061911b80040b0116440e011500342d11091b1031041070041640142c1c1d01807a500d0a40b082d0004003501e414841c00c3c80310043c80110580b01c41c0510000a02c030712445890083c0450a2261988522110158404a5400341c00740c4d11f04241b803080c110a885414000c1d00144111203803490f0060900302c0c1f0425100781c801ea410000c2c2c1c1d00c3d8011040c05450245c0c0004030540c440165080b010055140142180c0980f00d503200103800b42804000e150215940c11801003c654401004140c1f82c40d2150041c200400e11442 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 268036861 1250 268035611 268035613
    0x3030801030c1e0303121b0e041a060906180a17011b0e010c1410060e0903031e0c090405010b191e030b011e03020913090b04020f01050f1605 62
    0x1000507102c18151118400c8142583d007401003034a10782c1c0680d12440c0d4295000015030f00d41c1d00700a00e5444100c01c10701400c001d540d608035500c80e04020700080352041001307000c030790140d014000c0c900c0d00c0301c2044554030700090740c40c9541c4508014284481845200d50294400426040018140906219082c02c410003070002c000c0f1069171032031050403210440f800310126410110718041903004034001d2050398040c10680c12448030a44030641400080010250749507503c2030140040210320b55916403068150b40114914140f90117091f07900c40b0218500070309100c1c9800010300010018003903d42000c0040d1040c010340d6164a0000f803143c100020505902e29500c8080c01d01500c10fa003102452560700c0c070451954500003d084010340380080006040c8880c04010218050004922801010155800503210550041000f110780401c1460b117030300300d0420a80d840810300241a5a4105504440641c0381e02c2400006039210300032100c0042000c080800c04410089000070450041741c4510 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 268038111 1250 268036861 268036883
    0x50609010203060f1f120e1c17190908040905090c0301150b030112030311030420060c0d0f0908030d0f050a0516030209030c1e0a0608090d0c060212010303080103 71
    0x442401090b05e610743c500c44d50000d04e1115190103a004040c4488500c0b840d00300480c9250b444148185440d85140b00603031247c0b043c64014038a581d000e0340b200d0307509401402e9101c00d81413401d0700c8107140303801045101c2d0742d0340c0d68507a410810500404a81c000c00448400340100e2801146660f10741d130400e16498042c0d4200075000101c448107245960944042940c1c19013142d0800b508540e4a8480759021800e0541e42e1103082544550500558411442100c0282e10200890300380d1040d44140d4140c1030040c0c1e424040c80f606c0c80760205884050b40708901c0d01c02400c02601c04e04450341007603138cc4216103500001500c022885400c0d0400420303805054010f0115444a08030300301111000c8489555000d0b00801250401d4030a4004109895004040310600041003001070020001e540d0760044211381c121400c004c6050580c0c0e2140101a903060202440c90703c10202d235160f080000c01e103c01c20a03c00850820041c1950540d41a90b28401d401c0599603181e00d400f0700600003c3c0403e0b19005009 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 268039361 1250 268038111 268038139
    0xf061508010602061b0c0c0411071506060f030c0e060a031d07030804030227010e18010b1c14010509010c0914010f031109030a081c061a07080705060901020306 70
    0x2d9a900a003052204140ca98808032080c43c2c00741c010f607403540e250340903501c5686a2036072340b40151031400104520303142e07662541d1300d0300f1003034029040510307040c46040c52402c0090315003041d000014201e01d401c0100d66620b080b002283c1020345107851607031048000c1001102141d151f0300401030741e401b40f281600c1d141104918980c2d1082c2910000307110b15010403042c001400c3c9040b0b0581c10544000c80c0942c24140320210400c111307801d81001912070f42c00301c1001189141c440010724201800e070000c01c071151b26440030400410444c50380441882101c41d600040000d100d140c8801e50f5601002008142880007060b030280141da00e054000483c1c020000c02c0d1070710f0310114901200c10503160040712604c002415070180c9481488912410418411a00941c500b8030208081511030303c03007540d40e8060008619041c2200d0000b0781f000390310b0080b0511407513840308650403052032181c0401c0d482d21003505d440d1000d4800c4440040c10750050005101e0300754815000355019490032074440803600744c0c0d = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 268040611 1250 268039361 268039363
    0x30d030509070324060909030806100909020a020a0503030a0c080906011d0a18050f210f0c0c030a030815040c0219020303040b07050604140304030209190f061508010602 74
    0x20654103107003140c2044400300f00007016450002c011001c03403c1924160305941c0d0f02102164001d500440c41180c454406104255024610035030010040350100d404140395200107001c080c641c085c50b10515030004074940d101e4001c01242e02083c0d17024040345e580b40b41c00300c000e070007814201c442017012451b220041030203d140429030505891130b100800c51601400c8605241c0c4403000b80040d000142d861010041842c5ca0312150003140c0d000344010050700648900340391502280796840c03400d10309003003607009d0250351440441c0c4850081c2c5980f6a21a501c283c111800e10802101c11a4184039034032041c010150409241c40c410948201641b0444404400703000c19100054503050041e0004d0244241804298aa0451190001c0d0490303040075102d03566241d03517034041c8409458a0b8040802c100400800080c186902010007020f03600f4249142e01050107204040e000c0700b5613070741001100c060200303503a010070001e19000360300b07004695580210001350141c2c00e50780c034000362424001180c2240 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 268041861 1250 268040611 268040621
    0x50607030210050411060706090c060203040501092715060906020307020108060d0c270e0106141e0415030201020c042a1e030605270705070807050703060b030d03 71
    0xd01074002c0c002202c1540c20103801400000c004450124110188100580b41c443c007a180d030310b11a04d80040e8809a41c14006030608140d803001d000c5600070842482a664440d6004041740d200002c9520a040b5401c01c489d07092400c034a14624048c54207142d2060850790440e1041114001e44581501c280c640b9001c0340c90f4880c070500680851040030202d5860309105011955290081401c45152510749114410711086a520440c810003011414100c0e1221031080c0c45003894448020040c0901e04900111200b6084510510420710f5028103001c0d510240540701c240c102c001c200f003003d2181d800b0340c2d102159090001743c1c0184203035685041603060900c00d9440000c80c1480401008101c070303000c08912070302c000021040140e040d8405a680c1883c803964004c0006544001c1511f070b003000217001d01c01401c1446003905054005181600e010001c00301604800f8601e0034a90f0790209050150781c1d413083c00c0f0010aa4410301000005100da0b40d8000e21140d4411819504100ba1888080301511 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 268043111 1250 268041861 268041863
    0xf07080a0f1b23060403020303011d090d050c1906020d050a0504170d0902030f0601051c08090f01030908030a05150a0311040c0c0f0b1f1404090501020d060308040f050607 75
    0x4201212201c04949900c00f49107014507021800040d02015441c900d0420f00159022809a1700120042c02100820f4214801c0507580384264002c9107002c405040c2e503001ca80c0c0044d001c2c0710000070a22031020051000810003481720346501014000c914244c0002e60111040010300d034906004a00d54014602507140540e400c0040300704203032003148031050319070720645801c14000c1d5203442ea0700040c0c90520100703c69a170040d0103414150700d004140510301505807100300001c004060020001200403040c3e82c4900c030142c0700f0344854040400140c008014600700509454008410000312540580280e4850940b0303805a100c0c00040b64148038a40b0090300005102c4100110a0300d03441c2042d40c01211a0320f5545004804000d198954124803540c02c1c8042e60245070080400ca5206645a04015003151102002000d1131801500510950441450910072901e4816220a1000075015516460a072000030000903075649091003403a4028440d1407030f0a01e114500094502d000c0d41594803035 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 268044361 1250 268043111 268043147
    0x708070e0f060702040506190306060905090f030a080402010e12030310170705131b020304060206060f090601051323031014040219260c040515150f07080a0f 69
    0x800350303650800001c0e00c0020030154004803500d00d20441001c0108008c1c000754001c0c2c900080107410041254150307040140340702e61075030041c005600107040010880e10700804600d803140d44c58840e840100c61100721242044e500000072003840c14040008030045000f60b00c45000c12074420b5451442003060030300203d411042d0b4104030f00800142c02c1c4402c040c14031140d1105c0018850b02c515082148800c590680100164004079003845402d404014140c3c00c0384007190300c611050360040001d100400c004055504002d00850f40c070826a030242d410b43d02402d015600e0b586448002c180c0c10441c2051201c0c100d21a11610b040c100c00b00320305110300c10181002c020790240c00d030790f55000d2025400d0501d580f200100e8055000082e56040c41440d0844513000004081c940f180302800301e444d01d0341446400d440b403440c0800b4001d00440e03281410955017015030380416580e08906041015000d001107510901c08006049010020100010701c0c0c01c90950f121030b180c6140e1040c045a880304905810484 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 268045611 1250 268044361 268044367
    0x406020f1507030f090206210106030203010b0307110109140610380409110a0801230405090a061505040c141c06120f0c060e0102030f0a14030708070e0f06 68
    0x110b43c840c0d08150748044440c0d0300802d07024040e501264040e800070300c803828280840f200e101803000c0c410700c04a00600c040d240039030640d41401400c00036440060410001e00509540b000300d4640290840ba1115030016110881c0601040d10726484503006c8030804074036240c4600218070403003042c20200c0032201c880740106444101140c80302072040701071848400114103000c00144c0b850f0034002d0541e40005034034400d0701c403903004202802c2c080040c2c01c1031201c04c261100525070340f90010300304140c03154100d8002c1000d8651503080c03820f0000020b000382106040000c00043c50030440a18400c407441680d0802c9110501581156203200c03a10041000ba801040707401c4030410750b0156884030008840700000c1103940c445803c013001041000c02c90f2994180440d110900001c180210300400079070600c0741c4644001c0000031340383d11608240c8822040042900c1c4a064400d55040e60215030615004c0d90b00e09040c01e000e8140d0320201d810000040c44140400304505140701c1885e02d12390042d10480c2 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 268046861 1250 268045611 268045621
    0x1030204090218090d030c031b030b0a0f031103060907030c12020a0b0c010509010b0613050405040609050d020f01061d01030b0a0b130e06010f0501271a0406020f15 72
    0x5003a0200c01a0ba103c1030b95062039204070300300c160709405008504010901c0640218010f0151112038601c40c05140c54010308203a1040100003c1c0c040401920b000030750560818001501404030340c0010b4048a149280842003004103420000700c50021402c86003142e4034219401c1c1e6601803808020071440440b036041201020150a54580e03510082031400c06075201c12002040303400c11a00f481706a03450740d0500a006000b031280c01e107805401e54005107402c0c3e84a210302481599031043ca030040340e86074009418041c1503844140210380c408140e608030148554001d6461840711703450442c5510301800041c08002c509902c00c09040c500018601907840c0d61200c9061032801883c1a25032611810441c038240d031404007400180c0d18034540099040303030b81200c4625100f07050700101c0b1906505001440310341c0c0c200b000da60910064581402e180750500c0c15070011010240d101d54410300000a000a80071001005041900e190340d084904207031910320a10380d1030070810403503241d04200d900420 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 268048111 1250 268046861 268046869
    0xb090d08180612041401050c03010b09042003010e011e030303020705100903020601091103010810110c010c0302030609060d0b0406051f0f0f050102030301180c120e0c0306061008010302 81
    0x4407a42040354041c81d18001d04402140d4a980443c55000d1040b19003000c101c1000240100c0b0f81000c4e20410080006182c41d0300480345612042c051035450040201b2201242c4d941c54216101c41c4800040941e40140030056030b60722504280503d202000c040800450565a920030080d4010044002d134940c0d14a9074034190029030040d00142e81c2405203005540301003140e0300500c0034192082d030080c1042d601d407001c0541120025040803d5000d001c00040101020010300180e010b00fa40000091004980c1c2511a907442001040f44055084c140000111038042e030203541b003540140d0701114241ea6030010030640c642c4c180d50041a0030444800b19001c1001d60b44600d41c4001c0c03a0803203084802812060b104a00b24540c0208000d0000080501550311101c43d06401403600380000c506550400000c40300002011400700c040d40d0340e602c03401c4003880c4906807040c1d04c1e0221100801103050345452451f110400404440c0c0a44a403002040c298100400c1c01d00c108940c80e90341500d240d003143c2c00c00c = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 268049361 1250 268048111 268048117
    0x1031e021e04060821030c0702030a050a05121206060a05070512180d03020604032304030615050904031e0302090405010611060702190b1509130b0f0c0a050c0f070b0706060b090d08 79
    0x1f1850300d4809026003001038600b004440000390240006085034289482c00c0e0b0703c0e140614603800400e030700034012a00f02d00098445250484c0044603461b403245001082181c0c0d42c01801d501030510321503556103c0c4494518001040c800c450321200402d0b80040005001d184e03020900020016480640042d0100703100d1440c2103805050000c9180c0d84940754403154915800640013a941e00350307651145e0301e5180f26401c00c04018181500d01030b01d10314058030051300940004440349a8a0908d8107282407540c4245c1c1201e0001000602c00c02c01c5513180e040040c1501c1e6031200d00c221503c14080400e240b0f0b8000500d925121102c00940140481c42d5502d017424420b002d0011010310071084d040d505682c0d6055015403280307003442c0c1c0216864050b81000d1407100310203410640c1b13001e99a024401c1e612140d00c100c858866550401d40c0c0d4941400c0740310341c070703248020140281c40d004141020803004902c00003088403d000b01c5041c00001d444901c43d1050f03103e004481ca904c2035600100c500091844405 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 268050611 1250 268049361 268049371
    0x1314190b220b04050112090203070302060319060e0103050f01110d0b0418060203041b030b04030528090807050415091806050103050d1e0801031e021e0406082103 71
    0xd0101c1c5910900d0500582149900020550440030034203019959100c00c503142c901410300010700c01c40b505600800d80b15071041c04043d00030b00b00040041c0c060205100e4280304c0490313146040110f00c0e0340e66440c44c03200a080c0000c40d264012244c40901505050280038404690079405515244181c0c060750000c02c0700070313061904251188088022540d185100342e1340d140c042c3c1005a92841d041c64411800403410b07201107044460300a091010880745a9000c2e405681424543e5603880c0301e02c602440346c0706032070046442000e40c0400c00c80f2a68403ea10500311a2160111a045030f226002c01041d11020094421404640b0341c040144c4105504000380e5001e41c1501e008a94840f620b4801c00c3d50426041030341c2c1c031303400304d805100556031000c101050307210320200700c16102508a800034590041880080d10b0805156400c0b007402d1050704946c00159402040000c0130982c042d2924115200320441c40d1103186410030004070070350f01189210700c1c004200489040c01c03181042144050304042c0c6 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 268051861 1250 268050611 268050637
    0xc0a0903060e011a0603130f0c0b070f020108061e0603040c12031107140f0d060e0a06050105040c050307021c020307150f0b041a0607171314190b 64
    0x14000010401a101d440303001e006810001c00c92810a013044048081d24458140c02400c08004004021118410780c0c00c04d581d012200100460580c01d01600d09511a003180c0455800082c01c10200440c0750001078010b03200ba21044604d0f03a4100401205441c01501124000300e40100e2003660301d0040c00a503070007807180310081c0c4000e80361021140c080034140303000c0f80810308001e00d0007001c07502004020000c2c6045503650441e43c2c02c10000c61140039a901c1d034980030f4141740d0044410085140c00030500c0e0202d45003103c0740200241040005480f081c49101d0090380703003140d101c001ca40701d901100c0c801c1d031140d00189a000103d040303260100444061000840c0024400200058034501041c622400c0c15003010600201405040c0c00311421020018820752801081520506081442c04440081250000d4a44401d030400c0d0301c444000391841d41640000250300c04100180c201b0550907201c081c07440e113420a03c8403090185a148030f4124a00307042c44518108003116000c1c0045c200081041 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 268053111 1250 268051861 268051877
    0x9081c050c1e0a0501200d0f1413020f0306091c09080604151d1218041b1403090c0d020d12110f03180d0212030c0c010e06120c0a 57
    0x240c42c2c1212003502c05103482e030303540041c03d0400034080240280c0640840320300e010750180c004c600d903100340e61142c0f1403102d00143d01d480e09001c124105501c0641c08101d030b007a4940d80381c81d0040c06000c0b4080c3d07200c0100c0c41f404805400340414100003401038803c8844000400c1441428003a076400b11900444800030486d2081c000300e50034006011300e0340214490800940c00302100030420741558030008406005a0b4104000c0101c0e03240040e03d20310b2940a1142142c1d100801802649040c0c0600701c0e10750098206200140381d118a81501c05d4400085c1d070f94510750038016045050301c1d10050f120401107078010340c0648000e01e410f048100b0964130040c00c99502c5030055a6120b4168120300102011030208038001d12000c909202d4810141042000756241c48180703401c03610201d481d814690701960b0165052402c44d1600448003801e000b2030300480f41c4481184825955070760814600300d00050300420005020704281e02a542e5031100761010005640e500740184456030070020004040022030 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 268054361 1250 268053111 268053133
    0x1308070c0305031201060309050705041112090d02062208160f03030504030f0203070503030103060b0415150e0a030f02121228050307080a0917030a0b0109081c050c 72
    0x200c00300310000d610401c040c5032100c1d5102048907401c0f105078040002c1c58107111240001070300c04114503082e030320304490005420f00200100c490900403800c004084c07442c61018070039880b01c0010000403507080f9600f00c4846559400074103903440c00041c0101c0c1132500c96940d040004100101070007010501c90420719003501c881d154040c580f00001c00940200b6a6031043c0010305a010000c0d401e100c3d42400114076103a01a03480f1540c034441488007420441c2d843c0c0c0300c681f859446801030719a040100302804e5110b80c85040780340700324024004002c0402d0b0111044d04d0142000c0164000700d80d0001000100d003c1c00d81c00744040c40301003007280351150103660240c18541031954080d00e00f0444a42d040400040c020000c5500090950080030170700c00d09004200c40300b0350000c0c0741030b8080000030010031118114074210400c00310300c10401d1401d80c0b0200400c4004c1c41d142d0300c6450145007d80c2d805249655a00d092a10b80340b22201402c00b210300307035000780d00d0280550010410741045c1c1040320801020 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 268055611 1250 268054361 268054373
    0x60e1e011b0f0b060109050d0b0a0e0d050c1606090b030709051c0c0b072f09160305150f0d0305090303040303081803120103030806040f0e03090109090b0603130807 72
    0x5420720450300c01e00c03030490300e500740000c001001d9400b00c401c1c01d01c00c4260f42040c2c001031854450480040c5000018030000f160303850503411000380408030700120362424110480203002a00102002010740c4550304407840c1e07201c2055000022640315859600c02039043c00510401988010402c20900c01e0484000809440355404285106500315555912108910381003060301007a900500e801e560520403180800c0c0880108510501c0c40d034880582c502c50780407062662140550040c1d8001080010400f6007103050001920039120780d80d040101d9569040746008010101142d940c002c0c600990b40c040d00d060441512100e28003d003002824213801d400000d1440c0c1c416041180051004400e100c3e200e0003d0201c0400569554091824100319544041000d03005120140800100c500402c0e00c5896030b0740105180b2085090074091440401c0006559500c0901e4075800070ba910440000d021400d880ba5802841006054601d10380b102004442c03504194482540c284000300802d10000d48 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 268056861 1250 268055611 268055657
    0xa02220305030a030e01020f160302070905040f060b0616080a030f09060b100c050d0516050f1c0908120f040803180109050906030d0c0c0515040305010501060e1e01 72
    0x7100e03030300540c0c2c2c0306031018000381900c00740301d1582480c0c0e005010840311100d0a0080d925034500402d0250f964090909080386485450744c071580a15240006000c00d02c41c00b10340b107072819806880141b01500c81001840045d1042c0c3c1c504281960400710300100062107540100000061450f0100d40a40352904c000c040700c009c1d4004071402652400076603040d00700084015064410750620141064058864a40320384144d10000c08000c40024a0810702401482c0c1102040d0400b0440b4246072036101003541c0d942c0311035032142d080c28a8100310b8004c5071140d01100182c0d40d00c82c01524540481e80000300391038202e0318083c5004841404003103603500b0208041e1042c00300d001c0304480410840000074109180c03a800c003d014415070070030031950b618005109003e000044c0307800ca040d5000c03810444142c030841d4021650062144440162004260000c0c0042d82e000c0da008024a0740c2c2c441040d901c1102142e5035640041c000c80091a030780c18002800740c210750040c1007040884000d0f1100000c065 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 268058111 1250 268056861 268056863
    0xb010e0a080604050606040b0109060e060d09051b030115060305040f05011b0311040b2502120c040b060c0705101404090504140c030601050609061201141008010b030a022203 76
    0x580b1034400c120074450100115500110250303020071801e81003000080c51482540101004d10068114901881d19180f04441c03981c07050000400402240386002925251608043e0040d00f8507200030030300340e140605c9104807010100c40040c4070f291074007901b50042c100c02042640c01003500100000407900031300410201d0b141c0c015105408884840c009422500311507054220104103000500840000340100d800707a0f02c00310b070700e07400041e0f00c103021101d40714a00c00020b41196480c00e07080b003412303000614040148030403a401e00080340070034140900c90140840640031544401c004010070704000210441e4000b151030310052101d45e00c40c20300750961060b0701c0b1600c50383d541c4041200b030111440700d0310307034401266000e841d9076051040020f40c0c90308180100c51040303600003001107170340d6207c070102ca0045000b016410a11360f59409060340c0310140054080c09802a9034006000034400c1c401d4605a070380700010789045450740a1094000c1d040058643d400c9800190404008402011150019 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 268059361 1250 268058111 268058113
    0x30405061306090e16080603010912110c0d05030f03180d1701170616031404050601031e03090b0a0302270a170a060e01110d0509010b10120b010e0a08 66
    0x1c0c58180d00410720071182d8800002c20001e0820305c50810032400390120704030914036140c940780d2140800a8014503100c00014130194450141403445500f00300c51241240b140001d5a07028181c1c03505200b500380b4610790041c81a0030030800c181802408402640d0048010300c0c0e100b088c04442403c7c54a0244083c00440210703c4411340340400000310665035000d40403000031011401094043d05546400c00360070031440511103103040c2707481c51082d404803e051043c01c0801131942080e08200d80c58001c21300094902030006541100e01010503814001429450750358001200d15181e603a00d615003080c0d00034000c040d000c1001136080c01300400c42c03001991004481c124103550340c0d4100300941c0810703401010115440581450035541c08998034002e180c07c0140414100813221406004201e04042d800505001144420f44513185500a078400e02000b40204440850b900c100901644404031150024041400708007084d10070307070015007200310181401d2080c00164000107602c5009178102c1d481e5 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 268060611 1250 268059361 268059397
    0xc030c080c010f050a0e030309060d0e01050a09020a1401030609060b030f060108100b0f0c1e0c030318010c060b09090c0103061203020606010c1a041515061209020303040506 76
    0x40e80c030041c440030422040034200f280241c2c04400e00548140103a40c4500140030700c4118400040c2c0f000e100300c50900200800403940c0780d5079400c140c0002c003c400c1c401000ba600c1c1c10700007248201c0522400403101d4000780315a21551034040c20f2544c440c0340c058500e04054991702c5c001090303246805800702070207820107041d4803803500524010512500401003410011404180141c00800114203025600381090141da40d00c8200849002c52089041a003118800e11003040d041e82098200e60304910300400540398102911001c05036603008080804483c180e40700521b00056018246502c1040c4c454500803640c2d002d8400011084007048801403a590083c0c4091109903030300d445404003920300c040f14140002443c0d14000d6a032500200890306100c07065144c5c1c3c0911a0030036901003441480040300d1404d162500d80aa00c610036002481411801d0500e80310b250300e941075a0300f043d0340055581101041d401d49209025040065050340c141c0010000030a040d00d40c1d0004154151509844400c = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 268061861 1250 268060611 268060619
    0x3090509072c06120709030201020f03120a051312020c01140304050c010f2a060f0e120d020706020f0919080604020402130e0906040308010801090c030b0a0204030c030c 74
    0x44100e002002001004201090101441070002c41d10403003140c1c1003081c034488038206010505a1040c0c4429803140080b4604215101d503200320174030180ca100381d0903a000300c50128480e959070302a04500c804080c1c15240007550041c00c80c0e010540c8100d1040708420f13885550707101c0580313859002e60309400580106681c0c030070a50b00526030a04039403d07241c40703d00d94a40380d02d4103030b2a180d601e4441810007240c00011250079100322070224442c51905a00b400c0345803100300016889681ca0003c4a0711800c107003030b80d1601c25880c840e201e803d8810b6000341c4034907400c400c40840c40d03a0140007085c039840da0074410b1074003041540c409403d440d1041c6c0d01460b514040318041100340140310b41109101800300009100403980860400d07042036043e940503880702d0040b140384400111682000028507030f140704200160000040c103500941c003030717100c0d505241d0b02c50750350750b0903541c1040000e000f410400c481000007e0391031620603448100104018102a00d0b41c7d141481c15103a0350040c0d40c00702d1070074400c5c0 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 268063111 1250 268061861 268061869
    0x6050405011512020912161a16030c02030f12090f040902060f07021c2301060803040308030a0204050306131103010902090114030703150218090601051b0708010603030905 75
    0x35015286407441c00b55041030080d0b00a10400d41d101240d00001c0c2c000c18401029100c085a01d03044411000c182c42c42c64070341c4640320070030420910541450038291a0380c008001150b038202c0d551400e1000c4c01d00300080207600e040d520344000c03071800c0342c042c810050341d0301505205100c40d1a00c02900522640d45400c003c0c1045103110807420602e2140385080703d4100160361348000c4810039214012440c1c3c480c0f019000040a900000c0040192050f0400031181040041c9141c040460035800c00040220503143c0340600300d50203800344040980c030400050012410813000396600c4103038040c000d0303d42512400461b00b00001504c03c03010050210217020100b1035400e0b50081d00100c01c1d0300030407140219400007018010103102e102401041c0306a8124161024001c4401440d0854401c5240d40060001440258084a040e59003d6140804440b8600c2d021194074020030059603805c1c03d0011580703900010503a80181d0141500c200f82c400100c120081c05510001c0d40a500c94542a903c0d142c01c3c0 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 268064361 1250 268063111 268063121
    0x70210051527010521161e0602060711071706060a08010b03030f0c0a020306071115010803030c220b03160e13020a0201110c0c01030b09131209050d06060504 69
    0x3864500040b40100d44040e00045050304460048822401400010301c2c0081e07214984030f0f401d0b0f1980200100c4a0342c01c100000d0200840300c000f02007141707042c5100440441c2c40c0540c00344000603004400458401ea2142170803140b81d00c2e0203419200015641c80d140c9112607600b50740074405811040400116140c480503400003403890708000c1c401c01c120480084d441f40b045d000800c15031213012070a40c611900400400a429034058101c40c2103081007000544215331181304030b0524441c540000101e00110361003c1c0c120782840b00110308607118401040311300e8006410301c0e090b26a08208130000049410050780060170001c0340181d03241019442141d01c0d2082d410b010050101c1012140030741c2d200c0030007000c1c800d00200c030010703100e68074600c089002d008602c80403401c905010844460700040850790f1691a1800d032000c02c052071001052006041044507004c82c0b0300c441e5103c0030082a40c1820708108d000031843c00c404403d07205d0001078032a55101d041a14215a6200c050141781001d01c25 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 268065611 1250 268064361 268064389
    0x110d09060c08160f030f0f05060f0d0f08030405030c0a080702040b09010308030f04030207091d0d02070b0f070309032306060316031e020402210105010903021302030702100515 77
    0x100381e01c1c0c9842c3d10300d0f81504a50b1032040041007207118865030042e00c280d00c04d12a000301075100f80030b5062082c1480b806020103491203440f4800000032031899140007942c070a841e40d0b00c0b254254000203141c403508019000108292000d000400100b0740d000e4080c0640d00502c0c0c8142c2c02d83c1c5e100c928a0041c002140e0755038100c213024000780401071000c10051019030350f1104019003091240e980c1c5140803400d14006038000b2160600340364147c0300644142d2046c02666014404490120340043c03001c030707078512951040c00c410080401c4081401c1c01900001c004050080c07e01e19880c07580d075624201d1007444030352040246000f500c9400f103144002d003c110f0300040c084004184028142991160840b01c5220041c00c40d5052514000a0080c802090355000d400600854594880ca90b828400c00004036000c10b68090b03010012a60f503005050342400d0707a4014103510444041c0651120003984044c2c0038400758810b2a03040d9680130010302405124000c0708500d07000880f1800e00b403183c0c1405040d4 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 268066861 1250 268065611 268065617
    0x80a0207080d09050705040e030a11011505010c030c0206040f030605090a08031801110c161707050103020c0a060e011b0509090a0c090f0e0f01051f030b04110d09060c 73
    0x404040340ca400150b07290310764207020018a4100d14a065440c096440d80b08603045030416502821a080110291100d5249500c40c01c40c200d505915450896804030100e89031061000014082d035482401e014000078840e040c010b9691300c0743d4000910381d41055102c00e0051841c01c0c024810803d907400745a4012a0b01d600400c007101d601d58a070129400020050743c0e256591100c00c4146420940002c011440f034180d409030f85107842100e41d074450070381c2e000c584040d9030740500001c0c5070190b4080401783c0d039840300003403c0d0315418903004401075840b841c03030542d00d44204154603003c9501413040f4511a81c06100000c0e038207850080071a03603000c4d41141c50050250500408505407500302070035074404150a0001010f002007001074030541840d80000040005400300840c0d00c0043c840340300e0050314410350340e41d080d07a40c0342c0030011000d40403084040340b0780e84882094261802500080b0b001c000007000400e048a03041c8040032941c004e9411040320725100c0e04007106204180c03041d0044656245 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 268068111 1250 268066861 268066867
    0x30c0c03020606090907030b09010b01022512060b06030a0f050a0618020309030c0a03050408060c0f071b090e03130b0301080a08093c010801350304060f080a02 70
    0x186010392503160043c4034074010503800c400507101500c04d22400b0003450f40b2200380c1c05d441c03c0030004217000f01610302c051409446100407440c1c51000d02c15554500b0040110604c05090510a400048400328070084440644803660b070002980d680b000b45100710490040001c012510084c15002c0d140040d080000a502c4c008040c80450384240c40e80921488040000d60f6030388401d4185c0b49035210300039854640b401491103190070180e100008108a41440b022030341a91101070305410729102e110364107440c012003040408002010842840803c040c101c032005070003136440c491001a5040c2c0c02c80850140c100181941102002c0c00c081000307400c518403000c0c25581440d1304181e641946100141a4500100e480b0b58990785401d00d464040758031020300c03540000303109800407160540c00c0402c03c010b4042c01042c0465403240032214100c420300c0300412801c0a10501c103440c240b03c0021030a81041c01400b403480180402c200420040005544024ac0581030640042514030050321507d4800c0c010 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 268069361 1250 268068111 268068113
    0x1080106050a20070e04081206090105210718020714062206020d0f0e0105060316060f050702040c0801080601060903030e06030606130f050f010e090106080c0f0c060403030c0c 77
    0x2c00381c3d88145400070381c25884465503500d0418600529540038891030950b030300420040006200c0607003040c903140340b030380c8213503032901d40c100304843d0320900800303070081d8942d00090030341c1400c6050003902c05010310a84040c01c0d1500c0e4030359020b4446e6040c1d014070b26000a0010200601045058203d441f0040079005505040039542c150030310a0a00003a150350002401c024420a40d0403240300300d820b414100641c81c22421040003410152030901050351074900042d070300e07080108040b80d02400d20100340800904201060714000c040913080310400000b4401c2400503100c0d4424260311980c07a132204000d0b50300d0002c0c402d18010050300080c08000c02c80604000007600300301c28070100e4204503410703a1a0707542c40011400c41e014009411007000c0389180c00003a066a4514a442540c2c41a20301990781801280152900400d482d07440d900280b10500401a60384128115074010585522003440c12210035607a210075040590618841d40010061004250f09403184160b0942d003801c0028030704000f = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 268070611 1250 268069361 268069367
    0x3021b0d0203030a0315090c09050a060302030609040209130602070507050a1a040b0d09021003090c090612060c0e09091605010c08030612010617160f050a06030f1401060c0201080106050a 82
    0xc0e544401e0241610b42d910700d200c8442c4014140087e2600e100100401808864010076645680c0b103198010b102c521004580b0910a0003200d221703e001914081c801d4407a41d081c8039041e40000d0114840340c0d503000c034403400a0800e000810401d0f02400c0101203860a00b003c016148003154094011040740b50f00f15486040d81e0400d41d0111818841a2900d56001940700030282c00000c42c0207604c010700c80701004c155a0181d0220a1a901801c8042c1c0a0340e00c41c2c8140381200d00c6400f415043c5007860314010000f821940248004007010310703120104106420204480070419651500f50b07800000c81c00510030481d000c0540241404d10b044035081c04da039140c141c01484094115170048100010350a60514250401c90041c40d0126280c0c880321001901e0300d0300c503400c003040c000e550040118001088901403101d0816248000c0c1549400e07854081c00750000d02541c9100d55880340c03144100856800280c16660080115480741051881648001404c1110581240e41440014049016030a80c = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 268071861 1250 268070611 268070617
    0x5031510300c08060d110d0b0405100b0109181e020c03030403020d0e0a030b1305070815010b0405100f0e0907030507020d0305040c1e0306020d0b01090e060108191803021b0d020303 79
    0x71b08540709500d00030048011486010f143d20015060341c4580003440108200080d0204103002510000c00682e00504011202c052040c80f844040c00e1074511080c1407500540d201c0c0c82c040041c80b42c3c10341e200c4242d00440059800805200680303070004002c2106254040c0140b80c0c48800501c2c180c0c048080c000001028403140340030240020f8480b40000c0d46125145001c1c160480c1c0010440c0c010a80c0c0344816661a40405504090a0354103000000d6807002a403d0724240d5034010183c00f022640903108031644000000781c0c0b802c000204480c0d00003621041d406d140603a01d9907901041c1440c02650107860b2041c82d400c011f080500d0902004042881a00c50900340d0782e81a80341c64034031603c0c50454402c89800d80ac098011032000a02c0040004958040d0501e0035080e21481c220907556101c510b48044c04592850100b051900004d403091542c04802e0141c0840c0d41000500541029500c0c014003a0707080308401590048a0b001c656045110440c0c26048040300d1448070300311240d021a0b2240 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 268073111 1250 268071861 268071863
    0x5010e0408070302241611031b07150f2a03080a0b060c01060510111507050c06070206370506061e0706060605031510300c08060d 57
    0x1d40124000c41094800d0010300045201a0782441001c010000a030720760340300c240c58042d0800002100c145049000d4003042c0010842c2c0405581411080704624500010000d1540030a024000d404201c042003d03420209014060b83d40203103980701c0c407201074a00065008045140c0c10844004409415804003035400e1503498504074103240c980c60000000b41269484540d4496800f0410404400c41580800121030007103402480390300b5000d400b941c28807200301441005410044108080510014040341c100c6428688070307180900c100103440c00c1400c01c1e2501c40050f0002c00c02e004485001407203032182c000f0601094200c141d0945500846a030083c08149159038440c40018800d079a900140c9800001c80403106940008582801e0b5655003d00310803904940b80005c00300d0011300c074400341e0703208040c00c41805c13000192002c100082d842c888243c0d0780070842041041401c0c1d40c05000c400c400b21454212080080c0c51111a5a0541d555101d02408000c20076080080302c2e9500301e801c001e59 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 268074361 1250 268073111 268073123
    0x1b1d04060501170309152104050d03020c07090c020309040608030c07090b0105090d0c0b0408070e070c0f0201051b0304230405090607120b1804120306080705010f050c070602030a0206010905010e04 86
    0x1b00000740a201103405211380c0020000d1080f07a91000c8141050794a0703116901c00d4080e03030550009001d0540481c020042004080c3c1c3c4003d005002e074074116405800fa121550044074103081119000a0648000790002c104540000c20000c100810800003000030741082c0a040c01903800c41800200305002d07042c0d24030310504a80140742c0900000088101c007400101e640c95130b5490300c030100e55607940610f00c0780c20503129028000400c01e52003561200c03207455003d03c4405c140c0159400444180c3c0203003c50041c1440940f6141e802c80c103040004200422043c0c0c08007010900700c1e00800e4815540080c56405503003840d0400c540c420000c00c80d2940700040741413a914002c040c0d842c3c00000d040780030140d500603142a01d80c02805940d030320000c1c840c6101e540c4d820165041031034102d00381d4a9074820346d4030b60361102c0d41c01d1182e50b0148075901012001450440c0c1004a046210792400110703030301800250300000758a0702e046906000e01405000c01c20414401c6501d0080000d0b05c503000200b010b458 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 268075611 1250 268074361 268074379
    0xf051905070501060608010e0c0c100506220e0d0215010b0c030c03030103030e090105041808031f0f03020301140702030d020708040503061e090a030c1b1d04060501170309 75
    0x20a6010350151250180c02c2402000215102c02000c1c000c80340030300500c20b0300101140018207440340751040740c00820b510700140458450f501c0c288009400003900c059444240d0340002d240240c6441083d5003d44c0200303c0210f46c0c0c040001c1c1e042e0030203080c182e02104540246886030091150440c4081c111005541c100fa6100e00d0322008070b086004d0960f00c00c4e030301c1c000080004180340e800181c0040c14481210165000d0b41c0e200304000403030b01d1000d10344400021485941020956400242d03a0204150f0bc0ca06400e280d44032000381092303943d4100c1c0b00350401c03a2038180158102446110708500e06204011664103155401954070f0040c440c0c0e511669030001504400c11812100303072402080003408507a114203003648680d0303212000caa002041180c469000852502002031030b00403094150b121301c4e407604004e403501c09140f61900c8240d1114480520002029030540c42030204652400007104158241441e001c800e81744180d00c4003044030280000c2d141001c1c2c2c0401100e40c0c03200100e400c22a = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 268076861 1250 268075611 268075657
    0x60a052d0402010c020607060e010f0c0804172a0c060c300415170c09010e061608070605130209070507061116020a0b0f0708070609120302090102010c0f05 68
    0x5001390f11000094000c84082505001c100c6581c000e1200280800024071010701c403441000d040701e000c80c0c034540000350400085400300d0307044151000c0c82440c0015940c54900c0e05682c1858401d0904608416012a0195900001c00902c4910211001180d82034a80751520341169500d6aa02c21203442403040c0510021694800e900c0c8aa80c81811000460711556140210f00051100c0480c007008101d42e1282d51420860030480c8500c00c0541804007400c0ca035081004403844503a840310b0f1070b0409030030460001080380c4224518285c0d441800d00a90b00c81e003500e4088141d0b040a050341e03c03c800b50a054100682d141000c542d40301c02e240c1b038041e80715095030a000c4003815401d5090ae440010002d03440c100d0083c0701d04024012802620b09446035a41c90b16102c0040c441c121851710300c064103204000005035084000d02c1c0141c02000c0104000d8040d0300c0c1c46030005149078000012a0740007501d8581941c0a006d074071450680f03424101c4e41600c00c080c02609902c0b5094214414441d042d540d14 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 268078111 1250 268076861 268076867
    0x1090b0403121d0307060804050c090721060902030f060a080d05030c0c0a02120319020c0f0d020613090204030605070806010f39060b030303090a060f020706020309060a052d040201 79
    0x140c0c3c10b039002421030301e225a0714400a04550000d031400e0382d0a00601c0350312107c504103000510300495071641e558480c0c0c1d8071500c80790b0308070b003d04900020243c0c07600b0000802050300d0015501500c601038924915003000801c00c540d40c0025030201007203800002c440e12600c1d40103800e0720f5008910600190365001003444240c01c281041800950005d480849a00c0c842d40c004041d111610a082184100b02ca07148010399035200c44d1030500d98055100100705400c0d041819450015030305c0074064a080000d40e118030703040344016400000100d540172030108140120360080582100443c10500700904151000038026141400c410080c000307056034940032021403030300d8400c042507402009405110900c8817076100440b120f406030b5146060801d03c00c03540c9000b0007181e02540c001d60081642a1250b6103e00261601341e0021b035000307509204680100b40c980c002588941c905c0c001406142c90f02d42c2c10041115000303090003000c0615904403001100218040c100c1891002c3ca000e0302d181c0d2688012 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 268079361 1250 268078111 268078157
    0x50f030604091506050411042108040e010b0c010c031e050402030c04020c0f0f0705061902070905010801090b01060320130b070b0a050714030403030c12061401090b040312 75
    0xc00185840b51102070103c1c07507600080a49904807010301c032540142c0c014445a00a40c0140404200e079020315003008000040c402c44210b104110315810940e44161428601809034013240e02c1038000035062709110300a02c90b12207001c15505040080d84810691411101c4061a411264990b204042825950100100c81c25004020708c295079620b20714028940307442002001c0025480b8070580c42d0b8007120041b03031400a0f1600648250b08180c0c074011000b4030702141215440950142d102c01154080150188c14040c05107940017003034a0700c86280050304d04e0016030001c4101880c00181080b101540702c3c01010740401120541d440f1030320719509034800c41c1070754070110024000054141c00c000312050310074802d68100e8010080c03540c1c0c403582900e030710b145070310f8102084004200080005e0b000303601800d8149114074001601d44900510b10048403950f0b0400303800c1c0c000d6a28a2448c0391b900c124660302500c6d52440d4281080d2a40d500e0030711001c2005c40c07400902c091000c0341c0d050650b000000c = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 268080611 1250 268079361 268079363
    0x306010e010c12020705041a0607081c090c05090a0c0206011503111303170304050606060c0a0c09061503200903150c0d060b0c070510021212010609080d050f03060409 73
    0x54400b410403d44041d60b1400d9521540f800307142800005641031010781d03202402040c1c0074060340e16180d200c0d03482d4106075020074101d5201c0d240300d541ca00c1202845104000700c1921521800000d582000104019000c1c02440035500c1418159040c4501e580030800d14110b0303d200080400e01074180740141c02070084040b0006109030041007044545048150311001c41e03025a02c41000000110b1481403903103c22100a0b2007a031140700458040d091501c02003c050780c0c1c44003501c09100a6648840961700d460380701140c282d0715400140025080f90b15651031400c03160404104101003c0342007150004413441c03000c1c503a100070440c070559031021b2000f22a451905002400e880c900145025020b030050128160807503c0c106010405031000300842d40c06828200043c00c80902c0c000400505201e03010303c0d10214000c42c90300000003200d2101511401d07001e1781071184558142080100041059480315615500074807903c4010354000c0110344503406c03a641c0159682e03031810301040241000c484 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 268081861 1250 268080611 268080623
    0xb0a0603051b10050a02031204060b0d060b010801090605030601290d0618050601080a05041707030801030506071e08090a0812040201030f0e0d0e0d1a01080606150306010e010c 77
    0x2c182c6a501c0a4581c0c03045580c1d0342100c90200c4400600000c561a02460024038056482002485024442408007551081c800c10000c104554403a021550401c40c49a080345c00d141c0710124205150703040703892035000d01400c08003042014078010000c2d641d04018440c4444c56001010070901889082c544011404556035030f0030b55500b04250210300401051090040c180e0181c1030929038140300c2e0284038090001652141103a46503014800d00400e03000d40b00300ca20f0401c1280e00c64811224202500700617009482d01e4556600d903040007401c0200003004070b820480340c1e403c03007142c999460345424101c20309440e1100711799464800303c1d45044e40c880703005410318401080a00d100e60302050403500c02e920030b9070144905031190351404e0940340c0b4400804540d030009038085ca00c1030301c01e05826041d000010301d264030003041d544914403260920400d80c00d040c08440014080410b04211047c2c0007242900c0314240705883d0000366419010140030075041111070280350389030381e2280c10044030880d0488 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 268083111 1250 268081861 268081873
    0x1e03060504060b0a0b030714030714090307080106140f06030106021914060f090d02010b0307050d1707050c120f0c090c0706111c090b1b040e01090207021503060d0b0a060305 76
    0x280300d45c806810860f000800210b02c81c1901c0051581c0c0b0003680d000d250561512614030b441481c848980d90089140a40c043c03060920001c0c41f44024019200105000c94601958510361014891030f81d15084506024610400040110a82c0054480341a400501040c20408003510b0040e6850203404d0069206100d03910038030035a00c41009655018003084000c451601d840403500b40d00340c035540c01c049a8181c025110030070072401e01c24034940c015845000d509150519800d12104540c1041005030303400d60200382c008901d0b0402d9210544100c10600043c10800ca40300700240c1d44001001d0705500540080000c80d03a40ba43d118250f509050b440101032021140802c13006007070303420011f60580d00407504251503451712118443c0040d01500a148688180e0b0f0b800c800d4400070302c51880a080242c810840083c0c0c1d1078980c0d00e0b440c047c100c41400540da5a040e401045006028402c1d41c2864040400900443c2d55907a5458100d1940c00440009142e480d00c01c0c64008149a0740041c0c0280150 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 268084361 1250 268083111 268083119
    0x3020111030d061805060906130c030b0d080a030c0c08070204090f0209091b0a06080f1003150b0301140c19031104030f0b010e01180e240601091e03060504060b0a 71
    0x4c2c0c50140c07060100041c01c0200b9a2940104400b440e82600c01c95000fa0001d0600c82d200c1e807142d0803461007075041d800d01082944c164004903481003640d02058a1440020071000710383e0b9410f000b1204c01140a28066918403915210311342544504c0d40c00911403541c44030490100031010b142010025001080e852107803400300342c503c0c0c8a415140c041e0501e40f036642e44200031441c002c0350100581d0364a941c0c0c2100c030741d584413842502a2000d03201c480c0034040c0c8400000016a42c004100c0a61100003000c07507104000800d240c00d40f00180700c0d40121815080401581000d80015a4a00c4040301035889080c500d00009030010300291a0755900745030000f0f004000c0c400305140c603020780d0b03100d4521220541c4c2d884d002c025043c8020f0040c60a1060f041c20002d02d24402a00109624002030303081d03403445c1101c01c050110780e001c94a8084042d022080402000c1d680140840b4001c0040b03507201301030344035114814842c0b60340c0c1c3c3c01300405540e42d0318013040a00506a100204030720340079040c0d01d01d050312 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 268085611 1250 268084361 268084379
    0xd020402030103031205010906060518370608010501050a05030a3209010902030304051509040606090821030c0a0504090905070305060c0406020a0209060103140a150608040c03020111030d06 83
    0xc1c001017040c03181c24040000341c0c5009a01c1107400300c48550790340c1d5040c030300c184041d0840070710440b00580d0f000441c035141d08a0300c1c00b402e28042c040c0800d0305208017100c3c00c0547e00800001c13240c0c000c4041c01084001008240d03004811108858082d00e40280e07280c0c1d0706032480e001084d101130111955025a17400881d8801141004464020555079814440d40d86455090030707140e403404000d4043e0000d0004101340c2c20f099801a0b0710004d051029400d180058000c01c0c100c5905610100000c0d205071000c10800300144901188004041c4020002100c0d10720000d403940300c050200101d111000444007620341c4a0700950307000c0d103a0f0b42c0d4203204a142c3d50405603650412804107540754042c40b004582210010b40850b41181c40345e401500e000c101c95004c1264004004024506043c2c44482c003200151680c2800ca12071a5403e00002d111900b40c0301d80f6142480d2a0001d01c1030007012400c0c000410400a44041203c1d42403801004c00e1221950450550050ba610404000d00f040408105082 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 268086861 1250 268085611 268085627
    0x40e041401051f141309080c030a02010507030608210306060c100506031e120f070209100602060601030212130602091c0b100e1504022a15010608010b090d02040203010303 75
    0x1d40c000140344151208000403404040c45420f03544100000c1c040c402100d8030340c020482c6c4901a800803400c10f0341d1030291500303580c4520f41c8200103075500c400304041c0640510580000d03004038001040110505400300800c40c0c9241c0c2c0b40e007111100400014000c2e5591800c8a0518910030300b41c0d1100340414030031201a1005803040d9220b4016a01c400d5a0b01d00d40140c82d00f10780860200901c51000030086020fa903910550030341000407010400c22015807514200e4034016030f82800161002850150000d0414201804031410180104000d41081c40c0b104142c68101d500720700c41411034059403606200031721600341055040505e41500c40b10b094600281403480300d0003450100752650b241c3da5a149081c00502603a03100000140121300300384209081c0000204010340014900307501c0003c0d5144000e44400c1528000122802d4841c0d1840c081c40344c1c0c01c81141c03610a6001550602402624509050160031014000130030036114a645551103142c00d20780203031085650356124200180980 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 268088111 1250 268086861 268086901
    0x110f0706060501080613020a020102040b03090a110102011b08180a050303010612020f0d09020d06110a030e010203090a08070f0c0609050f01020606130e0a020301050c0307021c0203040e04140105 85
    0x1914007500018554052401c2e0351065030010158003904410714000c4000390811040f100441d0360034800440e010900c030009502865449001300003d80b42031812184400b5031008507070441e410040031050002c000d00558289030380c5030810a040b07070b0b16400c03c11450710f41d00c0c00c1c006c0c040c8501c0c0c41d032105102e0b0101c0154143c0e44a5079458110440c7d0050300300076440b0b03603045071a894208003ea0078400380d4640c003e45407148001c00306064203d254980380207035900340702281d00c204000602c9906207509403190f4010100c01600139400c500c0e0506c407450315607284d4840038100e61800194501080040c40d00701c00c0707280c2e001c90341010b801e80b103000042c246022801007034007600144824800b00c2d07000003450380c132034500101020600c1c003041c5200d902901c40c003a1000e06500c94003000c900142da0038080e882c070034580034210a40341e14009400030301c0d00785090406039440208c80c1b440d9400075404011175090702c0c2c3c0340c0c485070841e03112490042e00030184141c0c050740c82d519110500c41101000c084001501d = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 268089361 1250 268088111 268088123
    0xc03140a060f060801030b01060f03090f0606051e03120702151315080411010513030602070803041703010b0403020f1807020708100606230f0417060c120f0a110f07 72
    0x34030b0f1541c1e016200c007803013070101071304d4112a6001001010301c100d50120b00b1030b09619001c105485140d42e0189a01e5074a90122882c0e910f0390014410350510089031800c1d080c2036031650411000010109440306110405001c011000040c000b040d0344031046002039203250700c01070f5507407a0100403000001245a000d447d91345000029002c80c824420800c080c083c1c1d4111900700c036901c01c031000642d40b81e0f012503110581074008040003c00301d0820310203045d8540c000c840032030b543e2809207000d4001d0009016a00c101290034401403042ea0030040a850580794141c91121441118200003649000011898400d03803504400304201154082041405c40d1060b500b203d40c2481c56000f0b0740c06980d61401010700103440790962010b50030070075440c110074000c104103c80c50403035009604101644a6000700a603079103551000034145208000311640300402c042c5050030044008900c3c0c5d42c0c00c4000c0c005c07041a49440300480c034030040b10390000c455850076450603527941c0d1305102000c1464110740401c0e114 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 268090611 1250 268089361 268089389
    0x106051509030709020315041a0a030308060a0f1206091a0405010f1104060e060912010c0c0c0e2e090518160608061210051003050c01140405040c03140a06 68
    0x81381801e00949001c0c00e90826200407005c600c405001c0206801d0043e03602c0030510240510881c3c03039542c40400614000c0d9101940c519001c0e0a00080300b103a6030003c2c09001454504010004a0380003c1e02c00c1503001c800440c100019003000c41c02510030050000d6456400000c3c0b00420505502207400011140d00500c0b02c1000725030407000c94000d40c860440811200705441102d8078140c0001c00c01c0d040014010300e1512540300015085842e100111030201d035034810800e007800b4000f41c42070000c1c04402a0401c0501d452100103030b85402c03403040419141e15408190054200c07102681001d1303c10041c04200600d480464080d201d81c1d00701548203c0e004458800d00e00c00c4181a0003000d407085070701c400e041511018140244004200101c00c681e0003000480f0400790420b0041c140202050041401400d0a500705241410245407000381403140c04006001001e000c042660119181102d0019424616010640152500c1500603a00f6160031040004004669201c0410380382000c0103041 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 268091861 1250 268090611 268090619
    0x2809080f180619051305182706060d0609150c080a02071212020d290a050d0f0221030a0306060e030706030c0c0c031a0106050a0c080315060d05190c1209020301060515090307 76
    0x5906c080c103048048242e0481c0c80040c94502f051044070702c4442c82110000350641642c1c0798940000300c1000352001072500c84902d040000d40c003400a9030000c503412001c6241c0b008030358a250b14180c0c0c1c01058018041c10130003c00ca1400d142d07040c0ea542691100b0701344210821442030b90400c003000e4240d2006180d0318070729518a82041140101035900c0544600c103403110300d444280384003e0344001242c4c422810110715000c441a19030384200324495a009603207070010f500c406410b84000b03030000010003800e8a46403007107070313030003d5440200c0d0504d040c0001d643c20b0704101124822001780e00074001e030862940020403c02c2030724442c3e03030340c1139226100c0d416070340ca54030110740610441c0c410f10b00003000e86000c400850103803030065410000c0384503541c010300344c200c001c1042c40d0004804280201d540b04100001c0e46100d841808c04440f00200400c441d4600c4040a04070248114031105055552052841192400d50041c0050907004000c41c1040c50240350a43d04c13075002c80c0d02c00b03020f4054804006 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 268093111 1250 268091861 268091911
    0xc0601180b030705090a150605070b0a090209070c061b0816030615270816080f0d08180a0f06142809080f18061905130518 54
    0x1500720900100542145071901c010000381c01ca000d00048025641d4551142040781007002c140300030426600c810f81c5654503410703e1424070340010400d022160400390b0302130040c0d69104080b40d000c272007400e0140751075070f85090100050001e080901c400e124030122440302c45400c1481188038002c052a801d841c1205100110256201d030310034600004110645c1c0325045000d00007910051468009038182890018012084800f8540c02140030f60010020704a45490380d03211000500643c100400b00d5101341c00b100c598405500d00710f03c08110717000c07020582902c1070380050322480c54038104803149134010b400c10031400c02d1a042d003100c0c0e907454440e038890000c001504003845041c80d0841c403605582400a0003c90741441d144c04242e09640d515501e00040140c0c0c00380100d44600c5911640f03556590340c1100b0f00420b80c1c083c0380d2145c40300740484284880300303c0e0241c00c1940c0600c1c0c02a160034000906100c118160703003005138001c40c40d03000c00140320203689903548a40c1c3c01040344168049040001 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 268094361 1250 268093111 268093121
    0x220603061a0c070b030c070503070b0a15030203030a0c060605040c0f020d0e010c02010f02010e0714030c030c060a0e0d050a1a0c0705100506130e010203060f01020607050904090c03080c060118 84
    0x80400b41c000a01c200036106130300e4055640042141041442c10360640e03103136070a55000c140200ca003148810b050240505c494403d00040c001030103140800d01d41035400007966405181015020004240d154404204980c3c00000040001400c00e0200020315000601030070701c1d08100e840180700d08540540c225129482c000c4e00e0403810303144d61076074040c13640045070318085010180b425992540c002e903e85500070001c10b00106007503600828603411001c100747c140050828024031035407003000622429030b10581100c1c44030f41c65003000d1103101e0540300812a00c54601f20003510500680b425181800400c98940800c4031030385443c080b080d584d01e40400b00314001e808002c0c102c1d500585011940300300340da0126420600003040d030400640300c0400f4038207650000c0c80c0024075940210602000c3d05000c3c24021011a00340050415803805100c018041e000f0f41c5040d5100766203030303d20b120a1109032aa14070144d90410b884540e02d504614045a55210a100740d0405540305101c0e040003d60030311603 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 268095611 1250 268094361 268094377
    0x11010804030e10094202030d1d031206041b0206040314040807170c01020d0804060b060706020a030902030f03030910020c12040824060a0308220603061a 67
    0xe0a0344095014050103801e120f0680307800103104521030086400704504400501180e00003003050100c0601030480e0303031240700004a05aa155841c03542000e0143c003c03040e9405e42d02c1c54000014011b030501c0f004000c900081c0003c1001d0b010014042900c000600240c5118240c180e8080c000ba0000c0610881070f40d44500f43c540042c1c009501040020348100c0c001c5124010400ca00741c1010344800c4040e003400142c0c1e100c5a0140c0030b0500035110354901b03200c1025002e100340041c00d0007a034940380240280200820080001340d840740a480e0711360700c1106031212540c010604548440300c403140640206540503060f4030034440c141010301c0781c60001040f2846140d140e00941090045107140300041d402011074041c981c011240104c1e801c0b00b49001030801810340e400207000b0000441444086600810003440d0305410344410030500340c0b6201d028004995100b9100c81c0e8804119009030350204800d008078100305000140000c026a054201e24240e0b41034085400120801c0303058081c880c812004 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 268096861 1250 268095611 268095617
    0x90f180d050706020702031507020a060e03041a0a0c050102160203060a05010503030d0c09030f26030c090d02041d070f061701050f01090b0c030a030b18010302041a041104031101080403 81
    0x11010b8001042c1380c0142c1074586c4044c00702d80c010304007402204a5250300f11348002c0168855203d1200380301d41c5000c1d80200c1105107015500c0c4c6800c0101d80c90084648480d54030307541c035000403203030501e40c03080045211041d00310008640311141e01c10303140c81c01c60003d20f00741e1090ac00c0c40042054444d1911442c0d04940b0014015444c12002c1c41c06100070f4065882c0e240140b11607101e002000c207412030084501c007841070701070300708070003103a500c590951046803500c0c0b1026409204001384100118100d0380e07992000ca440107800342031440010f01401c0f02c2c24513890030503044a007040c1700038000100c40d0240d603640800162401d0b2100002c85852296055905201002c00700400540c10810b0b41e04440c1c81e010302d0900b101c9a01ea8035070150340c0e401008c2403841c550000a201c08980d900d8410140c0d0814120f454148405184103c80f24990041c04060b1041c0d0342c40880000d544008100303240e40c000060401c2c41460f0086140300d286401604c400d84901d240403032807130030319882103c1c0399200d01d40c161 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 268098111 1250 268096861 268096867
    0xf0f1707090506030a1a0702010c080f01061d0301090606030b010515040b0c150408120105060405010f11010e010e06041506050607061a06040305010b030c01031b0c080405090f180d05 80
    0x150111000e031001501071074240c041c01285e02d0101b88030380100c044503210711801ca403803401c00c0c060090841c1c1214071828200aa48401d0007152440009214119021458a0694517444004280ba1000d200b040703942d26610307101c0c0050030402650482811a0300909000780340344c2c0d0300c3d42449007034076036048521041002008288203c0013500040e1001c4c1c8440301c1207585194011210a80c2c414045d1000c0d00c80301c4002c11000a264103079a0400c1c003404040d0b54141c2014603102c0013034034440009912000348190220480c0c1d2540c400d5012030300100302003001340710300600f445642e9101c9105a8060301c2c0300a41c41c1c402804500d00f800307820211040604070038541115911550020420031110842240e400c400341c020f140d0f9900c0141015501038400003801064003070815141c42011204503040c5030a14000c5082c0490580a0002402c2541001c01002c5003910304094144503a4000e0340d44640694180084a855540b0040c854004084840d501d42151224507545244081c00500050010 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 268099361 1250 268098111 268098119
    0x6041a06012703020d03050c01110403030f1b0b0c0a020625081005090f07030b041b0e03120a020102121b0d1a040c030b1503040c0614040f0f0f1707 65
    0x5401002251000c82030500740c0951282c0c000b407485a005c21342640094030101340c0c07207144075081c450b0f041c40d08680b0f5250392800c0c0c0355940151180510f0850340052103403890442d4030b83e00c1c54007020300b0b03225403241c900c01c0c083c58084c0a40b960b41e04280b95040c0103100e007800088000341200440e40d04d15004101048010503604c40444d02011300034152101c0c1c0300c0c0d81800080715244c10700001e001c0d18400d608014685004000102128028445070b4404c0d8140b0b22290701c0d1004e4002c54a5103a03e80d450800410400900030902e0300e5550a841c1550120000e4044416139043d806020b140341e8100c409481d030707100e0031013040704414030500380800c0640402120181441a90080680c100380000c80a0f0703200d4a60700190031581c00d0140725000c03a0701c031030200b000c0c1d00d410400d0032400c10000c0040c50440c10300d902d070078564070f001d4010308050101c0307291403054ac0c2d2907520a4600030002004d01c0021240c90b0800100541103d00c111030141c2016080898045a09003004003011a080010400b05141c = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 268100611 1250 268099361 268099397
    0x106051c02120319090e0c03040f0204021e1c0b03070806010902031003080a0c120c0803060d061b020106050a0501090806060108060f040f05010e0a0e0618010f0e06041a0601 76
    0x480c1102c0740c00344000c1001c0c000d441c00450090122070f1054a44408951403c00c5003954028001c01d1240840780400070040020404c8031100340c400e4042e100181c0390420000c6c45d402404c0000001044410041008007074000003151400c0e124011400c1409901145000d0650311840c0c1e000e0705d000e82c3c024600500c03807104107601442e40310920b44042e00300d541d0303603840c3e41c02c6c0e07584502d80030340000300c8285008040c415101d1108191610a00e040900700c442d5488101d0640005050036102c2c01d5420f00280510045030040407060500c41d51403110040c0040d000380c0202100e10810f4040c0a112000092070b40c041c1503034604690380381c400742007165165001100e021100400c400d0380725404200010301a15140706101100c50755680c00600c65041000441803031070001e10002c0301f6400e00301095a5140046449078011034080d00b81c040011410120f14094048042030b905894541941028070460005120740104e014500c4034519890740c4031181c40134802140e0141c0490181e03020204840e403 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 268101861 1250 268100611 268100629
    0x41d2d0705030406090803090d02071401361805160e04090f080a0905040509010b0a0e070905030624010e030c010c030201020717090a150c0809062107020106051c02 72
    0x1301c14103000821007020f944e59181c9400035100348810740c2c002802d032800c42e0340410540c00a4034824070150840480b00700001c058014040c0030320500030040d820062205c0d0411000000c0350707444040103906944a910640d003484c0b490ba64060840c1c00c001c003048941c0310b80600607074000c01a949024000001d00705200181045003006c0f503a0360030b07108505012810355405400d10520560b500506107144c8400c01060b104003500014581e49480c01100c41a071310a141c400840d068521683c503150341c2d00360305565801040d4070098250090400300300d2220741c100c6031400d00650103081d481981c000b89004460b46240c1d00300b000d0305944481d101aa89600078420741c6c803151300c06e100140c034010141d82c8080090a40c101003503a0110049220400c0d4548400a50040d2000210000702068449001448124a0407024050420015060780d85032203030011038181c1c22001ca0307100a0000b00c0079038002e80f407104540400041d40b030b1081c04945450858202240b030752100d90101e0f5007910300d80801142c00 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 268103111 1250 268101861 268101863
    0xd0806010e090414100203070f05210601120218130b0906011101020d0911010801080a0b06060711030f070618030206180d0b100305100606050a0309020402041d2d07050304 75
    0xc8628a040c0c0b200013401c210805142c0400180540c890410702400f034900c0280c80041824040c080c00b2f601c42919580f203a400072404501c501281d1a00c900f80181d507454010701400190303500000f840c0241002001a204904100f55103403100c0d006032808003c200c8014041c0303241e02c440d0203800302d140f641c400c0345420011004e82e0001881c0c130f00782e0255582114250071044802480000c0c49001668009800e03e004010080203051a0305443e0b075040c410f2140100618130a64020914400380b00d0300b29400c81a4079400390444414202d0f119026540364118410880081c080c4141880c20a0400105070110307035000e040c071401d049042c0d03600c540c403c00c4036102c0398000060601d4440840e4503408100d000e550801a070040303450542c10500d06010140d214080300c1c6043c250304000c5982e02404445100b011851b0000b10030400c0c0c40082c000e8030455102d501d10903c58032014801d5a01d4003600e9025040d01c040b900c2c1400100b0240342c1c030b170b411345007416950075000c000001c00003400354000b5540a = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 268104361 1250 268103111 268103123
    0xb3301050d09050a06050a0203192403050609010507051602152a0d0201061505090301200c0c040b101b050105010b180406033302040311030d0806010e0904 68
    0x4845000c0140c002c5841d4500156850b41c8140b42c5101030000c42d202e01600005c19917410742c43d501d040c0e040f0002c1070011a41c0e200c030340350b652001c1c04030b030810303a44840d00c10318041452084d5195980c10500c1d60707606c4c241e680d84019403030300d03001c074064038003a20032201d09189040341700d002c00090340c00f0040f14050158008404100070403180e002030140403095042c9500c0a03a22142c004025107519140901c0000f460342560b00d818418410031404001c1e00c25680000d1401a07600c03400480402c3c00340c01d0401e488580e4002c00401d00d458042c1e510080c2003d0003005080743d009910500c2000700380c1e142800a01d8025140150b0514094410103080d00040140d0008148030b000999174582181ea00342c0c0009500c0302e01154030032020a500307400f08078070b0300c0c120340c1031100c42e045441d10300c0802c0c654000c180c0d03208414901104001082291621160060841192100d40e6070034540d407008168030b140f138030a01810300d4031301ca0280181540c901880d41070b510241d00c484d0314028020201c1c0040e00686030 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 268105611 1250 268104361 268104367
    0x105030601092019021b060702040e0f071433030907120309030312090203100e21090405070207080d14221509030512070f1505040b330105 61
    0x343c50b1407180140324410012000e204800f900c00d1000342059808040e12205588220980e90079558032403e4500080d0102d60010f103030150702c035845240c891001000b00b80c2d4090344d040083d01c0c0c03032149405041084203440c0d020b001421500012401c41d032000c010303c0810021040781074490000d101441d44032152004030b03034071581c81d140c1d00564201904c00440000d001c2101c24010580d214202c0c00b800c4c5403c200070b210b180e0155002070380f03402005c2e83d170905007130356204102e84500b4200070a05c000c44201034064074000208001c41c03200c0e40048615401581020f000c5280b05100041c01400c903880e80c00645035503404400d0880c1c002803419641c007149001440103440d404010500b04050a0061155041d4a4680340f0b00a643c1d9000c044a10140020b40204101084005c07c1000d116003035580c1440e070711580f500e425400e0007080d42020b0325a030f440140d650030200035684103600071402038490700e07902c0e40d50300d0702498100b011121051541118512950079028054842c80411034141001e0342 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 268106861 1250 268105611 268105661
    0x1c08070812100b0406021f060b040602030304021c0209040807210206070f02030319020313050f0a151e02070606081c03050615091509131a09010503060109 68
    0xa03680c2110040900000d1110180500e00d400ca11004000703080840340203060503c0d00d100a502c13405211b002d80c580c59030744a040d03000d501c03140d0711150107007141c05d51594640c2e0311610002c1d50f07078004903400c902038188034101400b98401c3d5404180d48a90082c2000c03004d80d51a950300b002d40c0c001950403203564082d45074400a4485a4400e10a0501554000d00e01032034030504c018004440c40c210300042d5001002031020340d580740313400e5240d503804503500580c2e280c0302d11008580420320030380c0240c00349c00ad4254000c1050004030700f6a0040380240950b840305030030003107a04100c5424000c002c103142c490440c625403152854001d040c0c0140903000000310782c1e59402070270741412041c42c2d50100e5030340355002042000ba054413500e508900b0584180c448a00000440c0416100740d94509104550041416019000ca8021101c6000002e4442c100c007031480c1015001070b0006140d081050014192418014100845107504a40d4020700a0100c0c3e464010303400014004507916a680204440740d0302 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 268108111 1250 268106861 268106873
    0x2010f0e040204230d0b011202030a05030f070c08011404120c05010c0509011d0303070321060605040e01080c010c0605131718100f12180b15010c021c0807 68
    0x40000c0000042c01c00ca090140400310480070031300c04640e8490101714201c1001b0900c0f048050741501d510740b0748006078143c2400064500b000950340148288000105a1091544c807400703016064071900d180c0c03a010303440322209826640c800c0f409140d0210f001e00060302182100d90f884500d2010750800702d0b42e483c3c05484142c01c7d10f086031002c40101b80700041003034403941d0081d0144842c16647c2c00c00f49004502e0340000707851b0f01c034180020b4100802918095548010f901c4094030030740a000b4200020365481c00c1c060159003042c400c8100d030a021400029440d00302042c2c0b0000004160344010304c0d04401d44e1201b0081c82c010301060f800c0c1426100110000d44402407141b06e248011880700e0b260105000c1c0100310a0f002e03e0401d0040300140d5007410040c0d00403e00148240040c00e108482e1141d4141e620010021611000c540403450700d18481404400109240503610a00900100030071940066484c686a035400a4100c1c05078035480041c0c01562407814091441610800c0c54808592224 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 268109361 1250 268108111 268108117
    0x5090d080a09140f1b03030901080105091b1602010f030603120305100b0418050105240705010b0d0f0506060603100314010e0a030503100e07051206040618060801050f011202010f0e0402 81
    0x903002d80d00446006502d03500f540c80721700001d501180210324040900c40020503180b41845414001c4188501290300e107a01882c0c00703c11404480d240c130740c0703d400c8900310a240080810059010400300010310303580038403e001d40002d4030341140758080a8030324800210000d04004090008000c3c030301c00007041c4114064007e100501880308000081c042022200381100c1040c3e00c003510818040100700c9581c01c0c40b20140401080c2d085425480b5656401c2c918050402000240e900000207000c9804002200960381c0000740508100c4142d43c0c0d601c400e00ca0340b440242d400703070007107070700d4550400c005007040150900e820180000131403041c04e40380302c031468004009d40841c045880070040240c903c1155a50030000c100d03249003401182441000a441441001518032040040303000061160300c50350812801041c440c0751003034004943e60010300091032680603520040d400c200100d11450310103c9418141c40130251152034500d055030041d912000240040e000344645410068141e5840c4e2020f = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 268110611 1250 268109361 268109383
    0x5010e030d0f05130309030314120c12070e0a0b09030c09010b031902042102010e0d12030e010603080901030509070e150f010203070f2003010213050405090d080a0914 73
    0x451050b80c50715088007a0b0750000c0190154044414501c0040795001c0c00007011207805080c0140801a4034594112a1040103050b40061980d0000d01c000320f00240024200402c02c0c11907814a9144e0580464040d107c58140c254003104c034032028003008200702c0082080350b100400b101c0404410300046208144240d0117501c0743c2030040700300401d004601d1118840b0164400003146400c0c104440e40115009a5502d081011502c0304c844086900481b480d6070f81c680014581c071210003151900d00e032841e111405120000782844108662410140a02800d2fa0b600c103940d80e04050603c401100200b10040c2012810302c41c44070005020941c1d21410b83c003c2201d80c4108003980003200170720010081465907070341194400c02910012602d816501d086456104498940c140c411400b851210006001c0541d0716510000f14000d4242c070490203c01121400d0b1002d01a603611144001c0d01d0750301104c10b48001c034509000103214010f050f44202c80a900c42c000400d10300004101d01841d00e002684 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 268111861 1250 268110611 268110637
    0x30b010e180a02010807051201120212150f0406110d0b270a0e190c152a1115030a0e1504060203060a030c060509040b0a0503070b030915070c0c09090b06010c05010e03 73
    0xc0c1e02400d508041408ce000415158014417200706010f1060802c0d070f030001d148000841e001c901107410820725401c0086030400744014140c54104000d403d10080c503032001c19521500c18016030070880601c54040700380e4a411a202e20380242c2e65402068013920152003c40200d0041c4660032001c0c0c960301d0403c9900d94002c0f0312090740a800c11002000000e2201c1c0d00005110311054804039400e05e07000b540180481001c00a0301c41c080a00e49640e100380220101d69100c01d43d0461401110503210146115489001040c40302458034014941c070780703514005126007500c1050004022031001e40045401070005400310100d07079902d03207480380c0582107a04000001307040060351410174500340c01800790114080ba422084240b6140000c0ea40350102d100341d00600401100040d9000d1050102035102e040000c20102c0c4d9140039600100a082203103001c0700c0b80c1c110b8a4022600800a0ac120301c5003540c80300150209849002c010b40d04140500e400312155921201c914038403160a1029040001c0040 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 268113111 1250 268111861 268111889
    0x71a010306060801021806180a06030f060e0402030a0224070b0720070512010605060c210a02101119080a110c07030f0c0f030b010e180a02010807051201 67
    0x4644501a01e4642d40100f1490780184082c104844c500242c110f10b106046518a55443c42c000d070510110b150503a140754054500400040c2c803030740603040308503e0206c41c0003c110550b140c59140040d86001e07180039426501907044580103007805510605800c00c40d600a03a0603c59506200085034400c400880c0c0d0444148240140942c001c885c03103240c006105499141c02500c0403809070307101049e1082501c1030f0081020030341d1600c001e6000c035015200240146070f840a04120320b540e9050f000710031200018200080030580785090040e07440c03000302903000e0a5070103c1068000083c10b900c0b0f8104041140402642001e580c003800286003100b000d8079604a580b404890200880d0310f03c8030004684001080840140480800c100701a240c0c0301c403900c1d80d003403001c0c10080080c1103207810001040d490001d000c4240508003290b0f40c102c801a1340000c900382c0d10303444222400c0f89440f0b00ca2040d070b030180e00e40100540c002c40596500c901249085424460300c5007007500030300c80030f81c0714008184c848 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 268114361 1250 268113111 268113113
    0xf1303030201270f0b1803030c1201060903031707030f0c1101060b1e0a1b05030306030d1103070f242f040608040302010216050309120c0d17071a0103 66
    0x10200000340f031001e0718030101d400303c40d44a00310200c4102c28020240030303161000035080c20f01d01c0907404540d400b03017045a48924016900006039400a20400c00102e154000080c805116003100d00c2541e03890f070b49030600c40d031040708050220140501020141a00d0b034890150b500c00621a40c60150b600f503880400d20f04902450740d0850f1407540102c0d0350030310708100031095205040c41c00c8504001c040401a80c0d00d4000f04103c03850300286400d500508090884203042c06170000140d80582401c5041d50145500b014081d5802008645070340d01d250400c0c0320500116841071030541565008000d08405007055480c102c0380040c40c03410410069aa6041540205201840200c446554040c43c1c80801404126101e85402107100d08001c1048000c0001c081620070b40588541d04210740d055001002603103465610394100c44003050207005500e8109020030740c001151844d0000c050301408014459880360b007010a074000c551200024200b0841002900900c0c01d6031102c0120100b40c4899415 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 268115611 1250 268114361 268114391
    0xe040c0e0a150c151103010303020a0507060503010f03120309021201360b1b070c090c02010908040b07020f0a030501020405010210020405010806131e02030901060b070f0204020f1303030201 83
    0x40c40c2c0250b081c2c070715848461240c05800514440980f50803039014060600e081000c900644885124980003100c084000410550006410030340c46120b1810741d1446500e403101210140000d01c105007101d11615800c1000c6402c1e1810b82c084101503250200b4801c10341d0300407a41c41c4950407400e91644e0342d945000313004824081c4100d01c52035503154002d15801c10840030440c0c3e030240c504014013424002c0001c0b0700400307064045501000340310800591990380c14201152008524421811030711304103030305543c04500c1846212603450348075400e181881c0c00c2c21080541d5422440040760006105080c900c480e80c0c1e03d4036004000c0d407040c0300140c0d4441c02c18000a00b0205082e140446c1d182c01807000b032003507030f80041a40e603110b0350558421b030080c0070101d0120064445032890000502c1c284140c10396140e441d800441c400e0400c3c0740240716450740e4404503601c47c400c2e01c40c0900801c19480e0350100503d850380040100b00b01e40711640741021001005e00180000303a44c400c8015030354134440c007403038150 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 268116861 1250 268115611 268115629
    0x20c0f16050301050402060d020a120e0309010905100f050a0203041a0c01060608040f1716030c0318030809040e0f070815180a030f030216110420070807030e040c0e 72
    0x4068001340721130308060307020039180e000325076946810b81c1c1c000c900b2160151050403503d10003840c1110038481010303054032a07038480e441800c4050000c1c0085901050600342032824060108081d0b40e90304002c1124542181d103034020001ca17030110300081000060701280103440d0b04521030251525582d824444079001d003158802d82c0f2075003e02036200c00700004500d0500070100071702d80140440a107182030340a68100d6105264503000170048648911061652040118071254443d8542d980035001c88122400759040b540320050100b5410004031034641815000007400c005080121350b06e00a03807044041c100805c541008005501c0980003240441c1006181078201d0494409246900803c075140354890f21803c0b0054240300b10b0400c882c00442c0310fa411201121803103200c81c005000a0f2410649910304180344500c268204900c0100e450956050100240480c1c0042e41c500b6103955108402c540000c9000c0c0c050101100503000303107440740d001d0240614550341c0c0d10031540b1052010411486 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 268118111 1250 268116861 268116869
    0x50a050901150603020307051e03100602060c04090e030c01060605130603020910050310092c06131212050126010e030d110c0d030902011b0503040e0a020c0f16 70
    0x41e040000b031a021406840e402029038a8a180159482c0d6800703d003501e01d40310303480c03804400d00d01003444002c0d1003c5040c0a180aa107190101001c2d05540764000c80c0c2c3c0d504107407008086614204420802c0d19400c0d0f01201c00840d81005503402c2402014900b400c440745035200d080410400500c040403030348842803030006070045090850404d188440480c4070540400302c00014070200201113028400400381650040c8240d00742481000300d442e070b035161013001302c003081450746003141c440c41c040c0c0360081380952040045c1c0c1d6601d00100c06607243d0b2008a2012044c1310140075115040e2170402410380503540c080c0124020180008986482004410603880780304250f6034500130200342c03141c902004076010300900c0310380415090480c035171501e030922401c84000554443c951003582d00580641200c66030078000d89500701d6691002050301142544003000030201d420800c81030004103645501d0980048180300b005003001684511103140c500c2c140e8241c403107540040480b03144040c0107001c04000e4 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 268119361 1250 268118111 268118113
    0xc15091608060c040b030903070203010f0b150301050d020f011206150e01050a08280510050f0303031009020706021b0c031014160507020315061e0102060403111906050a0509 76
    0x2502d807040f40035a00d402280505075806400001044001300204103985110340c00a0081262104904500c0d0041c06411800d034010b0180c52103c40541103224140c0e4100e8001030180100e4005c2035080110308006940e031641400303480804a50460341c03510a80000c1c0c60070040c030b50700d886d61186018208092141c6018104030017089407181c0c80e948040319a80203c400c2002a08403056109190500354140100003040c51a10041040c42c003607403191502102d100f501e101c49007513603140030300d42c5920003201c16021400d241d09040041d40203c0d801841554000c00c5c1c01401c003104640d103050014030440400400d50701400a24403145024440d607019642c085100b000280d1080261550103103000701005906041305911f1b1030500c0c008d034211816154020291050041c109090301c011a9003682d415006d101c041202220511003010b0030301640030141c0080004e41d5455508481490312000402030030300645420300005071740d03906d556148074411036020a8134a401d07c8104111030000b0552086 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 268120611 1250 268119361 268119373
    0xa02070501062310120e0615120a11063007080907180213060c03030b0a06120b2b020f0a12080307030b03034b0c15091608 54
    0xb210410711070f03c04012000d50301c01d08461034500c402c0d00d00d1041e0801001d9500d0410780d407150b10785400300d022403003403403804500b40710100803105101d5180340002c42010954010240d00020aa00545040344401c00428441c9000c0c1d40310350b0300403800c0d41d1580380720390394103e0901c0d6000c149490740340950100061414000c58900715881640c0d5103000e12a2040c03512854040a242c140c041d01282c074400c03424580e08417081d654a01c0240003404030013080e00043d10701020494a0314000d815942110301c56a80d42e8a004460300d00d0070300801e0644052640303c100216000b030302c141b048680301800700c409030b042e00308500c3c180188000c880e840b00742144900c1c40040248000d00b8208810a503061b00a00320648a48d03c542d0103900410340c9040303c0c0da1610000c50507010b0300609030070040c4041a0100c2c00d0703a4440280071620550307004481c00c0242103000000201a841500000d013074071503115011986d05840124080d050600d00f62001e0f0102c0d0071107101c20071020703400b40c209401003a0350b03002010707 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 268121861 1250 268120611 268120649
    0x6090b25030c12031406122503020306090f0c04050603030d050103050304060e090112060b0607050a0804050a0608060a1707050d0803181c0e010903140a060b040c270e0a0207050106 79
    0x917152100421152203030081443c40f40d0589810071090750b2852080c1489a80740c400240a0f4010180e9480101d10921a005c0042d62510300031580d2566120144014170b402c142400401c00a0b040003006541c0501c414404181604507070f00a15009500401c05160355a0511400800781d4051031202401020744130010841e61107170704445030000ea00444000745150801c40010303240e105602e00506648240703070201d414041c600700100300f1030380f084500b401541c0c1c2d1801c0c00e80e65083c046aa140d0b200105610030000040c22068483d441e002c2c50060310100e58540f00010305028052000781c410100100811100500314003c550b07482c3c2040d00146200070084865055040d072200d100c004001c448081d00c1d84a0f4015030001d0061035111209646d842c03100f050f2250f03201b40310b0340f040d40c2c1076003800040d20403802c0030f00c5072503010517540d5590b502c22458031b0355422461390820480710680840d040c0000c3d5150356528080d00600000a001d659a181810440d0940b0700a401007603c1d0702010b40c00700 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 268123111 1250 268121861 268121891
    0x3706020304290403050303010303090e1303170603121303020310200c070f180501232101021603080a02041d07020a14010603051606090b25030c1203 65
    0x1403a807003516142241818800707002c200300b402503610080043c40048000300806030042069070644907601d07241030040e40c40c0c0c80990051104400f0103400f0a06041104144059101019034003401c080e04961384844403101500d40d60344642c3c0b42905c1c01c100030009004600d01841501c05584066800f070200114840c60440e0801103008010129240080d0181c5603100602908000b44881d01c045032040d07544801c05400c0e480790300000800c262820001050021103079944105c1a07461302c0306240c00101e1801401640805502d03644041c002441b0490b1203040240000c0074003000e500c09541c9000003600d00504060800b80c90b40b2180c50060109001e080074013340402c03900c411b0600700c0200c0d1202c550507400e103003184030007802202c201c1200701980c440541120085a10450071100200b510741c0820004403602c4c055140024038120003004001c817144058980a12251540c1602c0c0302c0c0c00700c5424030848094421800318030004800c10501004420326404401c260030103000a640741e490b04 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 268124361 1250 268123111 268123139
    0x2150109020f0426010513060e010e0d0c0309030b0c07050d050a080402040902041e051008070e0403030e0f0d0f1403060f040e0703061401050f011403010e063706020304 74
    0x7807512000d00076401c468101d913412164400d40603000017088035040007a0740440000135240180e40482c1031440b0140d800105100c0c02e41a8a44c0a01600e0f090a51410444429a41040035010014000c81c08070115049039011070090040052050b40c503c3c0742d03d00f6605001502c101d24061281c14400d2585468005e003125511660480f400280c3c2c030020310001d0002c00c1840148281c1001c1e00b10004e852006c148c5c4418010321602d485491090344c0d43c11364035a180114000c04a0480c02c950125000a0003a001600c44080c580300f555246100004803924201a40c0034400014a0105840e00041e0300040d0b440c0c14024a06c11a51942c5003071004502d00d0703407580702c41c240501d50b80d4409204962040c0291009194490018070185501c2281a002c1580a000c1d0744e100b6a1190b00009556004299084c403094883c1401421a8a0210400c280c140000d0180c4c1c0c0001d0610f05000e182c641000703800030103584009e01e001450180042c141001e6280b07030410425580200020f0045440c10300b51 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 268125611 1250 268124361 268124369
    0x31b0b040b062107080c12100e0c130c0905311104090b0a060206130b040206040e0c03161b060e01090611120c12040305090d05060702150109020f04 65
    0x41c1c160316902c0c082200c041450104084000e0500301e02c5481c0344000c1410022039125208036802c0d5500101001040313041404446000d500c08656001c0341c5032030f50041c850a0303101d60107541c110145e440215010340c03900022200f00d690744012502896402c440d610000e480300351045540e51140c2141c101c903101c2c02100300d0100307807101500920203903000e80154031109100d002994031155200d42c014080c000c0400f2040c4692104440444c54910010346541326000341c02c80000528460f0722640d00e84c190241c41139800110410022036440030441d1038a0003001d005d244103640307240c180550f00040c1000b41482080001d0620318240c08014181e00d00301c8145c114000051456a030305070035005003131110000302400e040c0403001d00882da1860160401180007401c0c0c00c0c0300d03619100e1707007455489810794400103910f8403804140801e115001500079207401034034641c20340101c2e80b92185405401c03034903000140d002c2e0034224080e020480010380106029076056082103c2c02c040940741d400f035401 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 268126861 1250 268125611 268125623
    0x106030203130c06020c04050903190c061104030b01150819240618060203070201020d0305070509040f0c0306060c050c0906030a0b010e06040501051903060b210a031b0b04 75
    0x10201d001c07800c48402e42d00300e00381d000300d100e007001e680c070840030303445004810b12184214034003000520801e81c0030040b200d03ca503c54640301c0c40c0c8115281d00b0742d400903c0c4103050768070a9841d11024500900080184040c500500f00391030103625000c80001c1c01c40044030404200301d550014002c61201d00091080300000701c60000c1001620741905594404201902d10403a00c0003000000c0c50742d412100d0302e01d841c01c10003040700911351194810713a543d00c1000d1009005a11022000e051a4842d40c001504504140307040c0c0e18050356900010155141280313403100d00ca55030500d0013001e03a003511420740244494140060100d40545449449030780c00303003069024129100000709035641c2444202e01280c0d2150003080d4a58440d4001002800d0480d05035010354900742c008202c03854403101450191040c1c48220b40c0340e40c07c640d5480085c0048a81070743d0051180c91443c5004002500a418041e045a000700701001c2113040051417850b4010541802d0451010210301240f6800a42940180c00c07007 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 268128111 1250 268126861 268126867
    0x10503180109060c18080309040f14070f0f030b090f2e060801050901051e030118210513090207081306020d020606100e010305190c08190b0901060302 66
    0x160a404005100565100965181030800d0081004036400303d81c22002c25590550021040f0170700007140390b402c0c0a21140d560003803000b03403284d00e003030b800240c0000f188001c040f4041401c030f54441e64000007507691070042170b2000d601e0a1b68035072011001c00e2080381450140a442d82e508003080418901070f1640d000b00c0007010000e0081501c0d0f00c1c6241a602801c0230b89001841d95200005204040303004400c0001c034520000220f52401c2020729040e54401024548030224101d802c44070385000264150301952110f011182a051421107003114070f016084c0d940c0030800e2551001e01082c0c44140c081d041c44030a100e00f154818030401e030082900d02002006a40740d80505040000303004035044422a01c132656408900c0990100700b2250760341e0035800329001501c03070100300004050031005a200141030010140301d6503100b80c01031900701c05060744013010031601e0b805000c1a00c051910310b00102d405c0b50288030000d4012412a80c5942100c0750400c543c619075000502c65188c1881109d08041d008 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 268129361 1250 268128111 268128121
    0x30903161202040b040b0630040809010305130b3d0b070c050603150319020f010e0d0b01030c0e10030506130317180d0c02101107030803190e0d0905010503 68
    0x3540b0486681c6002013810761034109040d000100302440412301c2444410f200004e00b0308000442416000c2c40e405103602d4100f0a107000110018080203100c00e4020100d00619400300b1444561a801180004900600c42c9100c801c0070340010030344101c42034103401014880103848002c030602c805071040d5980302543c1d800141081d11104510350440d41d4407040000a10000c002449000e401d68681601540d55a04456101c4440000041006034102c840708010000b1036228482c8090744040041500704529403c3c0c80c1c07031550320800d03001101c40c0d0815a01c10700042ea1510310b4242d02c1403402092811603802e559030f041d1510400b402c80310100328034641c1082014004e12884499100700d9042c0e518918260b80c24060b101a01c105c40507442c001ca880d04144544108000e082040e00503102d00c482c121015012564049000c41d02501405244000300018074508015405607100ca03030303402c030400c4c1031b1029038048502c803074003c1d00a0f50003c3c8607005ca05401c910840110381e001d007406030301c982e10 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 268130611 1250 268129361 268129369
    0x708060112170d0f020706240b03060a03050604050a0b160f0e010e1305070306060513120602070b0727060f08100902040308030f0f070903140309040c02030903161202040b 75
    0xb400c142224083c102407051110302c8250380645101402180140a410042200c0c1c9031086008c11051001c4c1c841d4007070038048080ca200003990041e40c0170748035187d400c0c4d481e240c003802c00c0000d41e02100d060304011060b07001c0c840c41d4141c4070703000001c42141c140e460301c2262014082c0301d84e15402c40144910416440d405a0250100008000380540341d011034220101480d0300415080303e076140402d14021000c68114402c03801d50782d4584c91a40d840d4003103420314a280b00050114042110b1090b0204150000035032501e0320140a90000d407103c09000275000c0848a420040000740307640105000000c0288903480b403204c904d008030300e0500f0710140c1c07030f4040c40c0d020762201a0400f904160000400000b00154480290300c82c203003c0c0800303802c5484040c0340c040101e00558011001a480200a01c041b900310130b808503d2180c20402c0300c0c07618078404003080584c0d90304441b940158102140b5400c0c241070a10696416403200400000110b0030030b108203420481400000c0c0c06941e80f02402411501c03 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 268131861 1250 268130611 268130617
    0xf030115033008071809020c0106090c02030f070507030609120318151d030c030d0e030406020c19120b01050405090a0210051e0d0b1c020901270509010c02070806011217 74
    0x17004a9000318607525201c00401035801541421071540c680348002500048503c6001c1d40720701d40d940a18030b840da04480070030984d000300c0400d8a2034010914004001882d51152204041c4101d0f00150303044e8840001404440080084507005602c9040050000d591601d0140c0902054000018007400307440c40d205040300444070403e458070000a091103130140c000098800241c00341c006010070030180515170380b02d003c0d511030200983d200420340d0f030507440c0001c42829112600c05000d2009a40c88483c045c80d07000b0b0500c142c90405c04c0c04018041801c050141075448005c00c0e0042c102c2d01c19503404508000c080318020b0b810800045402d181c0b48070428415142040d5000305141c8405160721280010701c0c1444c3c15922481c07143c548a142544006618195250000c0400126070310f4080000180700ca042d00560309095402c658029600007403051600591002c40006040c0e011841e000e881c000782c5801101c42031b80002e004004e0115462450030317440e50301c05500804007c601d07803105030303c3c0 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 268133111 1250 268131861 268131887
    0x1203181002010e0a0c08012d0507020a05030a0f08071110050c09180f0f09030f0304020409020405070206061504050310020f07051c081b0d0b0f03011503300807 70
    0xc065011110107022841440700246c80c0614000c00c00c05103d003200c0307520000341c25541d907186004403515a442a00e2a440160f119010b801520502003055030394070b095a0120f24a80041801240c11000c5540e11086055101e1020b081105d521002c045c10f4956555401100c60040c9031a41d00046c1e00e21504426100d841102400c03900c01c0000640031002c49031030886808207401c00302e00005141e446c48044c402c0c090031000f0040c40c42c1c0000000d4070291640010402d80c0c00588484200e00142c4940c880d030b0307100c2e407002d6000e0b000b00d08203802005001034846041510381d2030180f20600c500c0d54007282d40076124400500045e6101d1030055144414007a90388040d00c0c0340540307405000500070907510b886880c005036454541513511110311001d208070304040c0d002007250600100d140810154400385102000500c0346038440903480010782502c000d41c1c4001c5100aa400f4100104030190303604c140040c1140341c4440300e4540a02e81010b007000c0f8082e04400300105100816029406002c03044686 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 268134361 1250 268133111 268133113
    0x1618110c031c020d0f09060f0506091f180e0607110d05030a091205070308071e08060307080d031505040209091317070f02030f0615011d030a111203181002010e 70
    0x101d000417a510020b18541c101960421b041013a0803210820902c00e083c860b40f001000c2041c41c2d02e4501040c91590a034440d892044280d4290101d09000350800011102010725070101c0c0001c000c1c600c15003880e01c0a800c45050265625001201c4040452902d031840068a0320984a41c1c8015403040070340603460b0040c0c00c6074035015903160b03000e03402002800343c540240c48003500390319002d0040311400b4900c0d85916804000d070711a450802e124032105078100c04024225004030b5150b00c80142409011411500070940e60130550b214104c01510580040008a07030031403c02e603500c800b00d909271b04001d25880780304181d02090720030001c203051241c0f6090413001031039850380b62510385403015a42c5004103911922414a9250801000040840c0316294500c00001248214001560401034166058203d42106011354290b500c0806c01915046d000315000480c00046da1300f400070b800001004005d0070b400c00c01030906e84031300600702e16200950070703140ca00503854001d40480c010400001c03e4981 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 268135611 1250 268134361 268134371
    0xb030709020c03070b2a0702061b07050a08010e030f1c020c030a17071e0e1810290a09030b040b0103020f0402040302031207051618110c031c020d 64
    0xc0d00c00000740c800c5600c5071019a0886d222034060240004400400da078500c580d800300512002d401101401075144060101c0c0d007008000d0400480f03000708807076042d00301d52010104006600c1d18100210050480300f000304010800714041c0d541300c2c400c820703800310b450a0000d503044411441121603010299661f00464803001e00503026500c1f0703400b400d11840064440004402d5040901c014240900441e8070303845a850f11900c0c0d0181402c00040d282000c0c4020401c0145903034070380c01e44c60380e00c075008506207424925048a62102c40c0c1c41542044c0c0780e030b02180c00f40042404a8903100628071801200060b15106c1580c000c4600d02c6884c1c10060030303440310300c09000c100102074042a06070303442111341c1c60a10b940d541c01c2c40201d0141c1c2c40043d40c1036010303602d0321014030301200c002c0800ca40280141c0304511a04054240310284540c402c3c40d08a00388845000c04072486e1244884138000ca480040c900811060b040d41d8a001c0c000040400d1000d500014912070080d60403541042c54806040c04 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 268136861 1250 268135611 268135627
    0x905041b06081f12020d06110a230a1b0f0c08060a0c020d0207060809070f0e1609060c0204022206050a020601051005040314030d02070609050c010816030b03070902 72
    0x10010b01614078450043d4242003100000c90320001c2001900c01c0c000e410741013210306400f000111071003031070b06454069a44440b651203980310002086548895217851160003141c0d06144149404c10500e040908024000b03440f400364018000800304412070a80c203c91030590400c0e0301080100c450042a020440c00000342c503490204880e4403c1800000c02c11040d0116542640c07600001d400040058101644c284540e0740102c000b190001c00803801c941c60180c54072400010302040c0d8109001c002c0041d010801c00c078240800003c4146501d1814503a4189000d501600e002490740b002441540c002c035034081030b044402c003d034035100d01c0c252001c22125030390350001d0240c0e07100148590060044c0070020426051444d4a00015121595001d14152542d00c40d0183c044545005124501040041c0c100c500d02d01e00240181900903a00042c0c5c2aa1914085240214010099040c00012410000c040104000f82e51901303000b0b04000c0b900d04030200029003000c80d650010101e640c40400c2c088 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 268138111 1250 268136861 268136867
    0x317010f0e060a08030a0f20160906051806030c100503090706020c0d23010504030e04060602010516110c060301090603030908031806071a130605060d0203070905041b06 74
    0x40480e5104201da80c4203480b100305010102e001401545510362080007180c50791840b032000301010400358508004a0300031032081018103480351030760381210f92201c0070010b40044168146d20003407210a9041003814074100200711125020014149402030100014441d034130141f1900c12840e50040a20004091011018245400c20380710100741c4c0c80703521404202c00b400003ca4007e988c80c028201200841c0d50395030301032017206483c5034000703190306090403482c140c1c002d00805005a03c291248030602c0240028402181c10562205d000c5a041400740300b80351030001c030060020300700ea103800e10b81c28400103000c51601c0d01461602d5040040080000f5000794282e0002c1d0980f4030a5442001017990b070103e2541e03d0050100004c5505104994407081c1d1078803200030b0845500c50780380fa803200d40358090310220700d00089a48418802c2c046050404110b000d200717082d40a41c00b181e030780c1541000c980100766102854011400d80c3c0ba91540800c00303001000140305661170316480c5000b41991259001 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 268139361 1250 268138111 268138139
    0x7180f1805060a060509010302060c030c030406030b10050a0804060e010605030d1701080f0d08040309090203090a0b06030613022e021c17071d03030c030901170411010804031701 78
    0x5807464001e030307008a41006040d000f03010490704010804016a42142c080007103a52211000501d288001c11030544640c500b4009000140042c3e1000607000e041c02d41800b6058082c81216801c020b0b04115481a4641051b0520340050308640001128928510101c1c0101000d801c1303aa49407084450380d0010580c401800d4a074084040649002a6641c09409903148026400401183c1001c106d070035610f8858a00540d000d4001d2500300103607a5036004581c02c070781c401c0c1c0c2c03903812507003080360b5403424090144152500300340140c2c010230591902880e203111500710410700078400c0d89001004940f120707014000c1011044c54001e01009500e00b500065980d1a1003a40c03203171601028034070720b4078881c00f03030750200700d0070120421030105541daa00c011203640a2041c400350504402c84801c10705914200060a0850090002140e444901e03000140485400c1d000c1e0081c002a54001c00000a0800300f03062076500007804d140240e07403518542170311010f01d4020950402c000344000001c0c40350000440c = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 268140611 1250 268139361 268139363
    0x109060203151801031a04050102040f0f23010e011b02030601060c050f0105010b16061b180f03080702090601050403060e071a13030308101205060105011407030207180f18 75
    0x1a140080c0d40760f64202d03400942480090704402407032100e80c010203000500654407a01c00d20005192035210740a8602440d6a41c01109455000030424420a2804c8038507024101400510f000c0001c0e100000801503511624030a040105001c005a800c02c0a1224807201c11303402404c1d80c00035078592800900f80c070150300094940d880780070480200700c43e062052a0584030208041482c5c0001e5941d26010441d80120841320243d0701c00400c0b2688581c448540701180507640d64008610607440d0001c644503250f00114a00e0842e8082040060403801c200d410155040e6442101070740c030b0fa0010b94850080e03074000b8050300c0c28a100c003103440c80d002c5515416901e460200725510300400000c0440e900900c03809841c0300c0c41501c402c0c400300707006401065000c00c0030b005000c2c01503126410303803400b0b0101690485050f481240188429a0800c2e444400001c102e2400c609040f0b071904c00075a41c502c2c0e485841100c3c0c1ca2402121038000042d0000813080740c03011000d00c03850210a60220140b604008 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 268141861 1250 268140611 268140619
    0x80f030a0311070f08130506030a1b0306050a0302130608060106050a03050717041103030904020708030a060501020a1a0c0f0a050909061504060302090301022116032309010906020315 80
    0x318008449030b000c010703a9001508030981212103020f0b6515803d05038058200d8003e442c190031000103d55a038640114412110a0004503003200445006100300c94003d85140a05051040610071034a030070b24a1030450b9011a204048c2a542c0706404d0001c104070740110030300b40142800810440d400000528079488c0941c1c04108540d5490f0b4200e0b80b42d1504102420318064803004540410042258404544002030669260410090014040707901c1242c0407190b80c4404400c10041207803900c0b440000380402e0019182c141c4003591000940c484480311900101e84800c0800c0400600d88140e9104c0b00c00d0b0900d86595220002000c0d00310707080340300c090f440798112a0000e501410700c0d820080d102058001c00070b01340790504000360080e4011000c543d42642d405d201c45140284c081036103841542c42080c8089950500320f00c25400c1c0c01c110402403003031604042650100c444486031f0040a00c02c0002404010303112146c05501403e11148003078040340c00801030100104898480300b1038424122 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 268143111 1250 268141861 268141871
    0x20d0206010b12040311070b130503100504030c031124040b060f010f0c03050906070b09060106030b01080f040237080703110d1b090501090b03010b09160207080f030a03 74
    0x1510280f03204a40511464004807808140001d01406c2505166030219042e41e261a4442c1030010150300144154502c3c1480b00c441000b01c1d09040c171540805040c841014403141c509a10080c0095501d5440201000504400c28440044c00d00291180c0a10414419282590200d070b031122210203071001d440b501200300c003180e070741e1405500000910b901230311b4030406045550070944841d40350403419800d01108011609465598100030481d080c840c01d880c0d1071900f004036043c0c0c5808416001034040c9072418001900c5603070407001099004050b11070550142e0307224404035084103075038124039090b06c0c01203001807000c1040e090020020840c14000b01703000751f03031484803c1c0d40e0419844040e107008024000311840b42800f5004034202e5011380040301c4001d0780a0b0012540380c810b03a001c2c00da8140d030341d0700501c42003045001c0c0109044080740240140c06040b000a0b107800c9010f070010030b00381c421411600d4544e000f0f201c046c004103140c41c203640f0311240e518003207a04e03940300d1058840003d20709 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 268144361 1250 268143111 268143119
    0x90105030c01020705040f0f0501090e06070c03091206020405063103021807020109080a051e0906030a0c142d0408060c07020109091e0f111c0f0903020d020601 70
    0x10101d0003580140e00401070f6515210901009000150082c2c40d141d84441c001ca043c1038103030091600800d51800002000c3d00800c1e005824040c014100b40d0410400300040d6020903400100c82d020b5980d80c0032910854507841ca4401c0c0248075640c4250307040440403540c02030404d2529040d201244161000481c2d920306441070040e2210b207030000079030002400d614000310104519210350300c002240000038554485807a403a5542e0064a900400544005442c4100403404081e2091004a0150083c14041c0440004049010003480300c51103030750385c58000d0802440385c400300c02d4020f0565426982c40c0f00440040c0410300c0c460f079680f0b85a071520410050b8072103a00085908890101001e1f00701d0f41c8988020511651183c4000d030b0401a40c24008619240984a08180b4460600c910b00803140f0000d00c95050f41d680514080c8440e00d480c07140e01c85140c0e54001c075080c1c4000388070000200d80030841b83c035005014892103401600e18101980b020140c0005038205407818a80803a25940c2e61 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 268145611 1250 268144361 268144363
    0x9050c07021e061b0c03060c1803030403020d2616030305010e04050606120c18090c030a02030d0c080c030a02061e13080c011e0b0103060603061a030c07120e09010503 73
    0x220800e26400c0f8038108030b0f43c208a10107201c02c943c0036103144160358100e00d02e200068901201551289007603000043d07021400302c0420740c100306244040e005503040619540014115004210002c1e00392070f5a00000c0c815084c034800183e01c036103580c06802d91608030601c035001e00012103010440c0441d140000204035001109402440f99030320600a1000b95221028064900144034500819100e0348110318050354500e01c102d201b001e90644100c2580c5006022a440d041511344418029040000d4510147e24003144900c130914160611000810f060301e009502885011132000c80c07800080340284100b94007003100c0d030043c00e4072040c450301c3e40c0704415038540460054070b000700105a140361420015287c540941010f0361001e00009045075911041d03d6800c00d02c11009006581c1c500350014190382510074007004d403005160411800d0305101c2d84495120740305240c030500c030001000081c11005402c0448442d16030081903240311444c44a0050701580310404134500c500d10000c000f10301410 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 268146861 1250 268145611 268145659
    0x10b190503061516080f1239040f03080c211219020c151602150903160507061202070519030e030706081603050c07080d0609050c0702 59
    0x10000380711100240440f465140298044003c0680030280c81040001081100010b080380418024031141d48034010701036208950802410f4060484802c56400546400710440e0000d40614003020186542124282c0215000f0b0750b000001c0c03488406404010450188003405804500d8003c03034190b0040a00a0b460f10803892042c00350030b036414000007000d0010f41c0031407030300244c50304132030151072180690890680e0b0000c00c11201d250b022071120b003941041160f485070f05c0440840c544084c24510b400082d1901055088240c060a0b40e4001c19070210341030003210303c1c19000c0014003820300320780d14000c0d40b10340c56031240c10041001c03c1442040c01285000b2148843c0c0d102c00540007180c01c0310b05221680b24000c00603020030098407010071198a0401c0300401400c1192070b0440325107800b810f002070003e084c0c00000200760a180900039080c5c84c40058441003503008601644818220003030000510041d40258400343c100414400001e0440000300f0700c041c000e403856010001601c050300d581c01 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 268148111 1250 268146861 268146871
    0xb1206041517060615120a230403020f0615150c0604031e0906052a030d0621030206040f05030c0706120b04050420040b100302091c03020c010507050c0306010b190503 73
    0x282c2c0401c581980e40703846c0c3c10a603034072400420000581a2040b100841c030400002007011600d002c1c2002d21080c190100003c2e8014880800203110505e040c0c0301600c0805000e180c0e50340600f240c807120040c3e03095604241c60000f1151401c0355814500b13820004d180c9406d10204811011110114411641c400e02c80c1078203448071900c8580c0350101c211000c40000c3ca00119112500454040400b1300c58414801072441494082001c11410308010404006040c20507803044003100c04804900060740110b02d495010b508400c035220001030a0400500710310611031081203c1c0556600804c5030b98109543c10300600310b801e8104144d4400070b0070300c8202d4005031400303440050301030044007681e40b50a12480300c26102030b10104d8601602408540307507a0034520390802103600850a40710508000c038100d0301800c1102c07035a041010707a517180a9100c0494806190420600080c20401e0010400035507814420140441d0700640e07540351000074541007143c0641c04e4010000c482c00d50540300d10240c1e0300031 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 268149361 1250 268148111 268148149
    0xb18060108011401031e1a06070c06080903072a080a2d0206040803031503070b0f07111009060306060306080613020109030b070801090501090203010b12060415170606 73
    0x10b90a0201520705085405215410541c40b00b071441c07495848840401d00901c5400c8000c6a1012141c085646072951200c04501035181840b101010841480800f01158810f080211894441040c02c17802e52155010103003c822404410880d010140703800c403409071800307101d04454140c60f4609242c1313820103090054484901c03600300c050172800503803010303c0800000a00140079070751580801d0746a046a4440c01c0c0d03542011080150380c40c0d040740013822514044001c2e000031401c201c3c5248580c081c01c20820540788005c107040041280050200b41004001810343e4225080382c44001c3c5841005d024950019081c0032000410364004d0080344141c2d0f4842e405807542e0742d140d50a5903c1c0030f8285809130304121541e980040410540d0f0244c0c0d00407002079031014115030405105030107840c010380c81407180b9032040004201442c0c1850558045101250805500d13498010006001d800ba583e80590600306044000a110600001300141c65a00030195401c6584035400c0084015203041381280c1 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 268150611 1250 268149361 268149377
    0x304020109051008061005161103060c0c03040e0a0204030f080a030c030b0a0501051309150f051005030a09050106090c020c0f04060e04080c010204121103160b040b09040e010f0b180601 81
    0x5914214201040302c40041c40c0c01f6007816142c1040c0c801071425400c080e0340401c0043c5285c09142024021154005c00380c001c41c92520840c0003031a07949110311705c0b0750003054041401191904840c0d404443c001c0d50442c5580c16401d45909103010168080d07403c40b000b00e854441c1035010307a402070086101a01d401403202c0e810524140040d1140d0f0b00040700052620117049000c0740f20303040c0b8418800e5441c4d5070b000b0849a503041c02880541a2126040148103201124a502d601e0f0b6010301140d03070042903580c012541844520740303d4090000303900320500c3c980c140355000962660009031000d14400441c0d003203c2d199482424802290390a000303100341c050306100044e012903038100041000050f4071000601e01680c9441e809000b00d070101c422140308941e4120150346103401c05ca111f202a2501100298203460b11100c43c10505c0341e4451148151404110305500340d807180c0c007030119180f00c00c00911000382d205955200130030138070801510451b8003c103010201690b4155240c801c0c3d9040e121852 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 268151861 1250 268150611 268150621
    0x301140f0a18090204020c01230c0d020a1e0201050a0b041103010504020c0f070b09130506010c0615050d0b1602150f04020f130906050105100c08090d080f0304020109051008 76
    0x345201c42c142645115075214445980183c0780d620042880344011000002c04100c00c2c101c00c0c8010001210190011881e141840013165500040710b1500098900040c3e481d0440c0c401036070003880c0d5820030b10080c1403010a900d12181c06401a51040203450020000c1c032001000300800c50300440c0406c060184240018481030415a005096000e082003c4600c0e950120072202d03e480c00035002155001000308010040b4280000c64502a004158060000703140010000f484c0c05070416024190303d84a0352880d01040007608007002826000d80003044208042c100880c040d1000e031a01e9440050071a0705c3c0e00f0003032001c00c280c10b42010340036880c030043d100e01d0312501d40048094410780c0d001c00140d404c0c02c11540c66624040c150b070311401c1c001c2001c2c0c1071418864212101644001c0c01898404200c407009540101045e00c1264002c00341501c850013080810210103904200a015820000c1d1040036420780034055407181d4400da0f150b480107502c41e01031210119400c5652000b142113500860 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 268153111 1250 268151861 268151879
    0x507030e030f042d0b0915070b040b070306080106120510090213090804050405180609060c0f181c0b070507350d0608060c0403050319030612080301140f0a 68
    0x41d03005140464204440301038a4011542d041007a0310030b00d082000024036050605201c7c01101424407982590b03402c00e00709445000c201500200002d180c00300010010b20058001d50080010b083c4090080124a444040f124034509001909030751070701c11140b6884038403855014200c004c45d4042c2c21681d01d21309441030f10003d000e01c800225490070007800080740648648c0300f074a1144401a044050759003c16500f10304080018006028503000081000741d800c9603042118442070021100580c0c50281c00500c64004102c2111280c1c803807030002012043c405a00d40301d04441d4014100710685840c3e180d0295802d05c84c00500a00607072140249191700484d160f60040c03001d21440c0b40701e594032410300714405c1a80c003401d0f02c03564090b45c540c800d1040348001c010142d4012107020b10540b0306800c6461b92980da0140e0401c4015061400d019600315034400d80006000341590f00b00e0301c500442501d014000e030b400901841d10001500d40188506291a002c0c500015102402c401c4445051a04030 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 268154361 1250 268153111 268153139
    0x20307090b130305120a0314010b090d03050921060703061809020f280909020f09070c05060f070e030a0309050f03030f04170607050304030905220f0507030e030f04 72
    0x2182140000c0c9000004a2020310811072404001c000c03081e80d46140013401f400702c0b5502181c00b51035203400001802800c946004035282072104440c1d0348803007035503172800311458801c0d20001e0f0341207800041d5510505982d041c40004c1c0000380b005907103855031108000c0b002c4070713004d100d11001e03600307920401c40c580000e81d0f1101d44d1003030000e045c0c80c2a0f01031003800300c2e0f105a501001103030424281580c04500c0715400380591301604549500340240091900001c1051283c03030083c0d031140e42c1c90030100704101c2c0515110a40707a035101098800c10b2404014418070183d04450041c0071554030819800360380380100b542846103505444440455040c42c0c180142c8291000c1e6154040c84104640b0a2400551001c1c0004020f00c2d201040b04800e02c1d4003031070900303202500c2c91081c441d041c410300c00001e821031004000c0d00c8040d94500c500300c07080c903203a408101c891301d6040882d514280d049501d40040342c0115200f040d080c1c80038003011503880c629aa40303125542e80d0700034003d800d010070301404c00008030b6 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 268155611 1250 268154361 268154377
    0x3140f15010c0b09060a0f0603052503170702040b090603060a1113140a050117190204090c05030403030608030f1e040b0c030301140a030c0909030225030b010504020307090b 76
    0x4441d4600940e83c2d001c0100c0d0540d201d039400e41c040802c00c10060103900689140c007910180502c6007919547d41c40b0350300c54203100c002028802102c9580c520341e66542007807000f541c003c80b44010982d141c21601c000390b8440c41c001d03805141086d03020146070802100c0b941c003408021b80207101a84d48d15000100601304092040400310040283c0072004440507015800342c95203987c0d8001030000380c1d00304021200903511aa0502080b008000d0090000f180d80d541d121501c424031740c0c2c0320111000c900000384103c3c2c2180d900640780c1105034504c0b550140103940700c1d92080d1020802c903034440e00d0450303032400b48101052250030104500444580040711880c200200100c0040c01d00d40ca8207002801508002032030b11140e8070120040001961852103880441e8058400402960940c0c5600100d1007a500580c140715403074140744402c140c4204000050000c3c0b600100000084490b40e1114140143c4000d0716542420000032a0030300d05031003141e000e003d094444400c028900700078015543c024bd40 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 268156861 1250 268155611 268155617
    0x90105090d0203011508102c0c04050a091a09120a030603050f06091005070203040e070c0b040b15060f070308070c060608010606080c0901080a1d0f06010603140f1501 73
    0x681500103032000d005e44200b40003510100d280b0070f401d0a070700c640781c8030b02d240303800810508081c0b15401c680030041144004080b00d03290351030703610101001940350034452984c10350860700d06810092512480d6200c4841ca511500307802061400030b0403034942d194402c1d20015502d42111984d90000c41d602401402c8442480c100450718a56a4440504209100915010b1600400200b1148860902c50310341102c04c080b404001030300300460000e680f4002d901982c902c400405e0302080d403035030003a034855810980c809542e201074503041c80d00c0840039a0650b00325096041204e0b0340e808900e044410354508a10700e1300984c2c203006098504443c0500c010b4407000a01100240c044045a11400b44102500030744001151071071074090000d241101c020400d01c4000c0d004d226424050303138081200c0e13030001d5045001252090866028161819520b0b140200e82e116001541200c03800104901e8101c85d800d07102000f07080d0607403d80030f404010072036a410a60804500054048119120070501b0040605d = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 268158111 1250 268156861 268156879
    0x3090b0c0a0210081e1305010e01020a02190b010501030f0e1b1005040612020307200604030e0f130f02040b0a03090c09021306030e1207050c090106021b01110c0307030c031e0809010509 81
    0x511070718211340009c0350404469400184d000b07000e81c0c0400c03980200c80c05281c107890864006484401c41010180901c50415440d08098050030445030070151180480d44282c4000c103051242c4480c03c0100c02000a0242c0403e0440704800c038019001d42e8200c640c0d588901d00e485803007241601c001d5000030090380c140103580e0000b07280b03289400e0f12000008190401812141461300300a05070007a602c0722544203d100e000c586501361902686600d011200d03200100300c8400f4560a00003901554001d07114042001c11442d84269054000074403050007001600e07034068a40409100340d220302c070300402c40d200407440c08210440c8a03900807540000c0e19000c0e02c41c403203010340003c91300341e02510055609a200401b40351091400f0004140101150f00081c0a0030390f0a00505000b80c41044c00316050000480c56802560b0040c400494000401001c0d55881600d0f031514032a2003029000548541117150b80b95a100f04c9141c04003601c40b0f030000f1040c2d0605a07071400442c0d403544010310729a00b0200c04 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 268159361 1250 268158111 268158113
    0x901031806050f10080a02010509040c020109150614030a11061804050c070501050a0510090b0105090307090c09080c030a1217100611031e030403090b0c0a0210081e13 73
    0x2c1c412203000f622841c0308440309042c4140c0100582c660358000741d00790b411004143c00142e8100b01151403580064030082003008951030242d00600c801c41024158a68001d0036038800c4085a200401b0b40e4402e006003161806c40307a0030306664805070b000041c10b03803543d40b50300d485515001000e480c3d184003841c2c4102c0c0c000c07000f10200701901c3c801e607048280b000c80800d60204000c070a00038290300505c0400c0c20806450170005804131b40280384104c400701c990780c040320902c6900c01c070112103020ba40a0220360100d41d0b40c60b059002441c20100d10000140040404600440007107665080004010010800740d00c8507196402514003c401d81e006004100a64500001c13481c0c0000e4440c10219204500d002c8c68402d01078200c0b0990b030a00e8500d030704104201c400801d0412100d51445d8030855200e6100c0d40c0c0c2c0c3c6001c0c0d403003090580048071250f5010419030a050400208218000d00c00e83c1c01c0106d2040c50384061b1404581035440c080c086004c03004100415201040c00b41d0b0180403440145522039130b03 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 268160611 1250 268159361 268159373
    0xc010c15020a0903060f0c09031113020319150b191e0804031b0c0e0a020c1911010c1101030c0201063209060102030304060e010f110702090114030309010318 69
    0x442201c02d00401c0c0300c1c581c100244905403080030300d000c800d68802c1c443c513001d40303200402888107070000070110010718520340e6140d00c0da071489100c0b030181c0e00011566414034505881d5204840310b0a01c1d02241000d901d155420f0128020328100d801c1030483d10305220098a8004090000040c440208104014500c0b412400c0c47c1952078006941d445000d240e00b0242401009803158401102502110f41d2100d0001041514a5400c40d07551220546079501d41c1c00da48006803044c51382e030348000e100f001454106003600c0c1d406000c529200347da0540c1103600c40401510340e024a200050200b146580e251009540690821100f101c030a100000c1c03c203489000c02a0b4a2240c0d03800e080076246a91000e1040107903000c0c0761950108100ca0880d070b0f5242c1300000031340c3c80c440144000c1000740c45000452080320709420603001007070700f64014400c400c503c200e441080d400004003079100b50440400000e035001c0c030286030b200f81100900954130b4940b48000550140078149400c00d00700800349a1100481d00d = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 268161861 1250 268160611 268160617
    0x3200418061d060121061404120215060105090f031204080d030b040e2113030305031e0105010e0d050a0b070c03020706020309090a0e0a0501050a0b01020f07080c010c1502 75
    0x2214180008210a81c0c004050244007002d500948581c440001407190751240c80d07aa14408091100380b404150562a107a4064840c80080064004040d07040c00208101600c813103039500e0081c2c0c200d90504c3c81c207440021001000f03880160105900700204145070a254804810034100503007100c03c00c555000d1400184e502c00c0e807020005230000d00c1c1261000d90706008000064600f110140304010208040e55140c40440c00c402e1054949407400300e0703c40700340d80c060303a4004482c412040515503503800c019207986d200b150000c0385409030204050700a0000c01e1140e058403070681d1928888034041c824000d030385000000568043c418040c0030000902140d80b81c80c4105c3c8550b4500c0c108410924010b890304000c0c0d0084801e5420902450b02c194407040200c0364004000000072441c034050122650800741241ca018005500300000c02210b960b4540001034000d4003a401c5544040d031a00282c0e849001170b002d20b40340e0746c220501d0007405612174410801c0e504e000304c1003a650141e01e000514102e0b4 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 268163111 1250 268161861 268161863
    0x30f0414100f0c021c181a0310051804030e010c050109120e090415110d051f140114070305121504050121032724030603200418 56
    0x40d10307404082e803440514010282041d2803400100700c41d1080303003200200c0c3c16034107280008009200ea20090040c4500131440000c10003402d0100029040303000c14443c5500031078805105680c03403900000c40d070034580514000d080410040c103509480350740c2d0488040da4020380e06810004120b4080012603402e01c50780440a210b480e009c000104441009400f90724443e0141d80318583c200d0400000c14442c00c49003156506030800080c81c20880206c889160041a4075011080c0c43c10f030820100b115445451486140c50080049000b641c565902a9100c2c0e031022180c0000c0d10401002d10000d030290107040c61501c00d003803107800c1901d120304041c400c030000c1340c0300c101284007080c00448a040078413566003d00300780002080040008451841d00c00c0200c14001c0030426041080011040010f805070150b80c4034021f400c81c456500c19611904040c092841521240748250f0f0300080e9000344901d10840b644a020703011a1404c96042c0b6078050401e580513500562500e024840358101407420000407 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 268164361 1250 268163111 268163143
    0x1806051e1c0b1c0201050406030e1501030b060906040b01090909020d1b06030c0207030c12030320070204060f0e040209041511071208040308010b1b030a02031b0303010308030f0414 79
    0xa110b50742c100072140e08000b2540301c203030030a000103e0260340d1107021a802c2c1d60003424082110403c0c00c02451400b0214808040c90500000c0003000700402c240301035005d0f45007200d0006043d1240310420088948800b082404a02d80910801c2840f005d9046035445600080a40410318000c1d00c82420010f01245d4100407800c0d100d03400c0c0201d5805210300269002d1701c0c402010010b044d80d8840d4032101c1d40b40134a0300c0c41250b00440008040c400c0d00440741720400d0040c0d00c41c02e29036041d0307400c1c0c1e25004032a040f071245091080c00700d0700510f00782c0d481c4102c4404000c2840c96448a400303005ca843c101400684140011440000c0000c0c201d01400c5a400c00f0102196612107181c00c01503500d2010120200401c03605030140400b00781d10200c2c59046d5416004c4560f514201148039034a03240c00b02c04201c0b000c0c0004a04a40019004809801990301880f19945505032095010344c8a11007400010440141840410075204620001d294011700c2402101402000000954a00401304c01a41d8070 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 268165467 1106 268164361 268164371
    0x20c0309041a030c0306040b06040e030d0504030c030809010b0d0803070306050a0305032d0d11070501050f0103060b01030608120306030a140d1806051e1c 68
    0x1103000080040021a000c1d084a808400d494088079102c0e024013001c0c0181070030085210b42c411a030251a807440c80c0ea6040400006101c0d040303a00585100500000001603100d104643c02117019807100020103509140041440c507006080b04056410b00d01c0c04d5500340c07076400101c0300c4607920a40c403d8880c0e655501c110010f00f141c1d88219448445502c0c00801d001c5c0100080c106c04801d0710720710310441d0310b100c504801e410742c01e82c00b50a001c008221354448015281c0c0400740c502c0c22001c07403520708103950b11403a003901d10a4848400550407c1d00420030080c4511980004c0c1ca402e007010b000d1603240800341ca48460b00084000c0480a001000800c43d82d001d100039035003198441140a4091110303401c00e80d0303c2c0e00400e00d50740801c004036012900c440003031307a24004640456075070514010328904860020799196140d40b082000a12090301c0c08090040014041c0d03c0c0d020703000907 = true := by decide +kernel

theorem cover : BRFrame.Cov 267985611 268165467 := by
  have h0 := BRFrame.cov_init 267985611
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 267985611 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 267985611 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 267985611 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 267985611 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 267985611 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 267985611 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 267985611 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 267985611 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 267985611 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 267985611 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 267985611 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 267985611 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 267985611 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 267985611 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 267985611 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 267985611 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 267985611 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 267985611 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 267985611 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 267985611 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 267985611 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 267985611 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 267985611 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 267985611 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 267985611 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 267985611 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 267985611 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 267985611 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 267985611 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 267985611 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 267985611 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 267985611 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 267985611 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 267985611 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 267985611 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 267985611 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 267985611 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 267985611 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 267985611 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 267985611 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 267985611 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 267985611 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 267985611 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 267985611 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 267985611 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 267985611 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 267985611 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 267985611 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 267985611 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 267985611 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 267985611 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 267985611 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 267985611 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 267985611 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 267985611 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 267985611 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 267985611 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 267985611 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 267985611 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 267985611 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 267985611 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 267985611 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 267985611 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 267985611 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 267985611 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 267985611 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 267985611 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 267985611 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 267985611 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 267985611 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 267985611 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 267985611 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 267985611 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 267985611 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 267985611 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 267985611 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 267985611 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 267985611 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 267985611 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 267985611 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 267985611 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 267985611 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 267985611 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 267985611 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 267985611 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 267985611 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 267985611 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 267985611 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 267985611 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 267985611 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 267985611 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 267985611 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 267985611 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 267985611 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 267985611 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 267985611 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 267985611 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 267985611 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 267985611 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 267985611 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 267985611 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 267985611 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 267985611 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 267985611 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 267985611 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 267985611 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 267985611 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 267985611 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 267985611 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 267985611 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 267985611 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 267985611 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 267985611 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 267985611 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 267985611 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 267985611 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 267985611 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 267985611 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 267985611 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 267985611 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 267985611 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 267985611 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 267985611 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 267985611 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 267985611 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 267985611 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 267985611 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 267985611 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 267985611 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 267985611 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 267985611 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 267985611 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 267985611 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 267985611 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 267985611 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 267985611 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 267985611 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 267985611 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 267985611 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 267985611 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 267985611 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 267985611 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 267985611 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 267985611 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 267985611 ≤ n) (h2 : n < 268165467) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
