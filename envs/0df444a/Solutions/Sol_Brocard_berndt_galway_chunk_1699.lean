-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_1699
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T04:21:18.600998+00:00
-- url     : https://prove2.me/submissions/c5b9c425-bb23-4806-ba93-5d5537041e88

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 305395683 ≤ n < 305575539 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 305396933 1250 305395683 305395687
    0x92901030209040f090c0806041a040204020d090f0213020a09061803020307030b090f0102070308070c24140c0a0509010507260405011d010905120a060608070e090c060f07110901060302 81
    0xc0c06000c5070300d02c00800e0010b000b4401071405545100f521000d0ac40298543c08001020608569864041c0e64840d80f101c801000029480c1c106513607009658401a8026440c00c0c6040075030140764001c803100d42406455100388246070030400c441c4100310201c013a1500b0080c81010005036414050f00009600454400c107240c2000d52442c0d040000c40386038011a07a10402c02140000d40144c00c0941c80106420100b243c3c0701c0d02d051140080044101511681a070005401000f05050380100341fa031b400b280c2078000941d900e00c150314483c401e40e0701c4c00c40031032030500a03454950301c100024801144030702d9034203007000130703150301800640c0022448455441d00402c0078007103540c1c40301155141c900d24074400d0b5492450000080d0840ca450b0280c20f0003140210760781680a00100030b0184c1d000d0b40203404004165580000c1c03070726031656004180300d00c0e0314000410406400000c45452703001c0c0060109142504050200e007540d0b114007002c440220040300442d5056880900f506e00030900d80c3c4000d6 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 305398183 1250 305396933 305396951
    0x901061d0103050703060e2d0d020a080d090305040b0705070e0c18130b19030314040b180d0f051605040e030306060901031e090c092901030209040f 65
    0x40d214600000140300d0058080300400100f07500050010440e508031a0015412105a032040d0030807500912050034240302004005a0b0604400e181803000d524a058548050320490b04070303103c040c402006011004148001300d15101e0a0b804144258400d04083d40f406507160100b15940c0c11400003502e06411051080061a0003c0d00c01c0da803001210f040203140c5038603560001800b140403102c1a015521120100c142c22100341d101c0380c10100014007000503611200f102800185107408200e00041070340e00e050020b06045801e503001e841d40c0e0307104a801e042c440099001000c0504018540c041c2140c4001d2010a0a14020f5201540241e02070a104104503045402c10410f55003d03d0007140360480c64034a55002005598000c2022911155110000070040300502800a0143c1807035003441c080d88180c04090b07120360349043c0700d844001411956201d0081c215480c1e1032240110350710461191000114040400111002c14140141007107070341008181150781c0c3e914071100c255a2a0821 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 305399433 1250 305398183 305398199
    0x60c0d030605060f070809121b1e01080a1a180103050d0c0f080a020703020907111203060303090108060a0b030f04051b06090415090e010c0912050c091918030e0306270a0605090106 79
    0x248ad140c0a40c00c419407103900900000800c040c0d80204820503141d910b121076038401001903a501076558004080c031104001900700c18a5055007031000f2201031107404460815a406130480507440c1e908500880c0042c146910740a40b281e104040304d50031070107166008801607a0320300340d5500034585907541648244c0014655890854002d080c1034032040c05008002482e03074008111582d030b003020329091400341c882c0c9022419880b020340000b4800c1902001300314000301c54240e0135200d00d0241045070044015010b851a014881c1d05816400072001c0105000c582007940040c1104031060320540441e030350382c1c00030704c0c1181c076600740d500c00ca40d454600c0040010762041801d405090482080c42840d28107588007607880a5050b03020380a03a07011000541d00d030010240b00c0d150008038941c03d01002c0100c41c614281c03800400c038100d011400200d003d003002d09000170110320488442e40d1180340d680e0102203601c000340309450090003502c11800001c00103580d60007814010b66081001165090510700c02e = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 305400683 1250 305399433 305399449
    0x60c07030e0a0b0901180509130318050a090b011e0f090f050603010317070c090603020a091404060b0d020a030b04030e1f12020405060c0d030605060f070809121b 71
    0x340701d9550220103101074600390701110043c0c40c09082000044841c4803103002c910f5216402103910441c8c0c13504010280400d151071503a081e00c242d4a8064811211001043c0ea8083d80075280d000607121006101c8904070307601c080104201418070712591401d00401c1300781c0c14040300512001072807090030410100c1d04680388502400140c005407460b9410200801c0031400148005008505080c102b4040d00000350300b1034104a800030144d2030700340d48171030360711000d01910712049004125080c00054010100d10480c10070503e1654201010b45413502c0d90390180001d2075a140c3d02c1005580140c0060b924060701000071403140b80c100046103820304011701026001050580500980301e44604044c10700c458040c403c4405050c000800c400940d007090083c0540d4000d141c0009000450009082c00010080152a003554007405002c0d218818480e40b8040c82180e001b082205020f05000200c00c40c0251140c0100540746000301d40c16410698908402001c0c3d034800c0700c0d0150540940c605150314 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 305401933 1250 305400683 305400707
    0x313020f040b0904150b0d05030301060e0a030f02010c03350702010203160f091205100509010204050f04020f0c0607051222080304020a0308040f080f0a0314070c0305060c0703 77
    0x50100044100c51010034a032140084c0300034400802043c140c1c500150a45c4880c000b040090142a030030115440c00e19070340d6000b2701030113000c11a035503907840040c80d04d4480107040d00d40c0415006810821350340151001c00603000210180b101078407110b041500c03007032040030b40022084200c00041c0b016000340215410043c010000b1640100200b2241c5100c0364144e40b22903a051070040c50031000c1510440701d02c0215004000c6a4501c25215018444000780c8400400352005d41041140c441d51401d900302d2046205081d00080329140903c12490240d019107106540368401528140c0c0d440da84a041c408204c4202000c02d40201d001720815151400841d41310391840c00907107610314210310319040d40310716101c020446040080000c0440d2520b0244000840d44021082d03216500c641c03a00740901140d01800e1803030310442900004000001848402c0e1a8140c0ca03482d088541c580031041d0264402c0301c040e598006980c500000003041041498800c6006104494a8616626000b014206080 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 305403183 1250 305401933 305401939
    0x605030307110907030212040804030b0708070f110f240f1306020703050d060602211e1e0304081c05090c10090503060c071703150402070312020313020f 67
    0x710105000030345108056518410490f032442c059941c101e802c40191144c040a108441d0031001030100700032074080603000b5207200c0c120001540c0ea035a10100c0d90943c04480040004607400060503056009615a603106005032040d15600038034294400d14080787e40491401003000c01c1a842002031080f1007164000b202c945007030405040c1001c01110072028908064100c90740000d103801014010300c00c40c1da0b241c808a006015903503a490307010307403a01c14581d100d508403682c4907a02580807008004803500710240c003040948045504900509030b800c900c000340000132584004ca41e5503c01203000d5440780d0b00c0351804590750404405040d460085000c11403610318108003c2c8420340d107020903101a021019101c10740508003a03d0110b910701c0841e4045030b014001e41e01480380d01c40285009215060080020b11551112044010350700d200450b10fc40d00c3c00700c15004481c2c1440c154006220450091400038180d44052403e03030200c0e4015204460701e40c9500e8031079000c500303103c000301401003070403 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 305404433 1250 305403183 305403187
    0xa0308130c0605030c0409051609080d020304090e0312010f0602070b04030209040f0204020904060e01030b0609061c030207030c090e0111190804081201060804060b03060c0d1e0c030b0406050303 85
    0x2591601d20340c10361406240103200c004000182103150780710640c0c0040181d9602130105040c01b0f1001c4185200b4408820b00240e02000c004c540d0000008607208069055030013940782524222504008090301c0001c0340517400704001d981c0c5980b00302030b41e19001c1c00000c405601700525046018dc41d1003965404000a40014401003001d41d8414043c50350041d08a8031219441703506100042c000e100340c0302e11580c800e02d420342c0411800850818a81a20301c110403522035611900100144603c0c11200e09034029019100649800203040c03080d0401c0c0d10030700407595502c3e12a44c031865030310070ba50000145030ba510743d44451000c400b40941d0a10746103d01c082c03071906030b001c0c0b0780d0540103000b20550030601c60040e012404016486085a03444a000c0032002d0301561104070040040d04260b60648040b400c0c040d1600491601185e45801151907070649031500c1c51010070040a03000d1242d446c020b6644240e920034442d0a03d000c2c00c544011250740024142041004200450318203400c024001d61003 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 305405683 1250 305404433 305404471
    0x30d1406010915021002040f0504141317251506080303070f11010e210c03030103060513020d08090a08010b0f0f0307090207080d050105010e0328140a0308 68
    0x1800c1c094a07a03c01402581c14680c40b4203078a0402e0400742e1071105480003c00044101116140d0820f80324103d4052000c0720b40720315100c0c2c80860030346050451100b2040c0400000302c14400e054400c001031810b150504d80e849100b041c03148101d0261901e1300038405900b0b0700308540700c00d0032800d10103c4482041041d042c042c52603580d0100509203418040304082c47c00da4140030b486005007000c14140240701e01c00800c0707115910741c1c22541c10040c0303142c2c481d030132541c241e0b2036241034400316100c01c0e0080d42540e01c0d5442e15000703084040c0c200a428000460030b42c01603180c059207824141c0c010340c0b003281d40740321200501c00c1142050340020b04592400604c03c10a039903040041d5210b04007104d0500030b062021b00081d00b03110b43d6600002003584000303148800c10040f14050220901241c07c00c11031681c0c2d400040d94842c000351000396060700000d600701100b00540310881030041241180c1c0803040306a41d14020000c103a008840700e55803044045804242c0c0c40f00d03040b50711010b920401004925 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 305406933 1250 305405683 305405687
    0x11a0304151e240e100306050a0c111b0105030c040e0906090c010c0f110a150206060f010e030a0605040c050303120a0c03090206072a0312030e160e1801090302030d140601 75
    0x75041c0034240351007100c1001700e01440708000701a00070310f4002c0010406410301d0907100c401001d44242c640b01249019980414200c00032480980e0224000741010908046600441d001c0e80010b06940f0751075014000402d040b581e10b41c0b00c82c41852403d0040a442c00d001c041035251000d0b6010050402032038005400008441400c003414542c0e200560b0405a0720307140025840110036000382ca00200d0300301e60380b0101940010058065601558811f20030304940c4011030f46d482c881c0003025055440b1a0360310001911076406654042e009070355140006482c3c400090440e800025880500020302d814011100d01a00c6914840501c60908000a6141d81e0119a4038014100054001014203620341c12a0010101651406000c882d075094095280c1c0380c200051144043d0b0800003030b01d4013017a18684940001d0441d001c03802013503505031444c0345c610440c0488800800c016021581094006003402090080d2000301e0b00c250091038940c2c0c880504881104e0000c00c2041d1421500001c0c012640d03 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 305408183 1250 305406933 305407001
    0x4171b150708070204110a021e0a0b0609130602030a02041403032107050c06010608070305070e0306160c08040909150b0d03030507020a1506060e09011a0304151e 71
    0x190307000c1da0143c0c860280f400068000e00003c031601ca80c0c0c01c00003641c202100e42c0850141052543c000000903808481d42c84555104c90141d0300406810b01840810703140d280c1a121203500c2080f503070800500c0025640d60300c00341c3c2c1060700c1e510052600414140b0484441c10080008140142c0c015170500420501d4010a400604219840201a170000c140114400c40031100c1002d40700e8100d411550b0b40303941c0101000070441c1e01d50006454000441c0410388192640304801400030300810058849025141c0803030640c1c154442882890401003000448c098050001000701c6007000801d0742160a1508040e804a610455402d2412400c180c0c1c907511111130110554041c0b400081ca039603064001e0f460b044c0c51643c054802606480087c052002c0e40c1c010205484540c0d6407010b101598406100d5251070030702a43c940b07010380c01f0a02c0e54030341a08000e1035220380106444c00c1c800d0261081041100d40fa90380c1c5c182145481310455098000e00e0080b43c1c0c8905030010a543e01098040000b502c407 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 305409433 1250 305408183 305408197
    0x180a1e0f0b151914150a0206060f061e0a051b0c15030403050a03052224140a150e16090b070305030f0603010b130b09090a08030103140304171b15 64
    0x22038130180302070910340c80d041c02050502d854200001d80c0c6508014000e559103408840c514840c0030140001ea030f0307a00b40002928a8100c84041c01e075048007a9014000c0c1d1a04800c00709001c00c0408d0001e0a440112071405141c1009a070000e00103140102c420f00444220826000411000410520001035402403c0f1081c004203494002419286c104049400040380700d0500d01800c10850044248210f400f89000c42c55044904940c60600c040540f4098501d0401c1f5280001c00b4000020b586581c10782003802e1011132440513032551a00c030010340040d43c1c070a46d070f010030000308000441d0803513401000b0700307001c5c025000405092100e0f9503001803e40c44001c2c101e0300c250460101181258030300750000c1c83c0c448002862100c032044542c1600c0c009000002001e40300e0050a0041081d440c0c0104407032102540043e120383c91a802d685400c20b405040038140002031108110000310b4111036007041c0036080400d400390840b4011400d15242c0000044605031180b114844007004a41074031044800d0 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 305410683 1250 305409433 305409449
    0x103140604200d0b07270f0b030402040213080706030f0b06030103140120091f050702010522030305070605100503100902150c03030609180a1e0f0b1519 67
    0x15410410220300e0b00c1a0f43c034001410f00703035070606001c0c0c029005000c140030007401e21420074030641042103840a40e802849410107191050009020f40740f980401161301900260016203031000c54100109080c245900c5aa61500b00001c02d0003e154540512034980812b1003040c070a000201c000180c1c0c5102c18030000303002550a0043c00c00d03c44082d0098140602c880c0d850105803111030106c0d44140e0f004603822407044000d91081210300703c00d040e01c510507403565a502030034400c05900550f03041c1d001500040148284401140d98a00b01c031100130003840c03099540648030f00d1103107001415a040a481c1c03d121001c2eaa1081c8041e480c0050403003503602c4c0d424004540c06e042800421a00b0803141005054501b00040d442180240000107500504d0140d510307000300d660b100c00c045102c4a5508500c00daa03040b59485801154008400c1c284824248400d03020425566590780e400715040b0380308940b214426010031a41c1c12202c0964420b40c0c2003078078030844c0010024042c20112200f4014008 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 305411933 1250 305410683 305410733
    0xf08060328050111040f050303030f040602070507030807060f050109231005040203010f0e130f0609020a05040e06070206010f0305120c21180d15050703150e0103140604 74
    0x707601c81c40d690091481c5030401c00070003041600102e01d0a0513400380c00b440c020341100100c0001c890070000300b103d00c200b0f40105840601c1d11141d84a01c0030394840e0703409890034071030100d003c000b052881000700100c5e44100720000300501c0001e400410b80303405912408440d4640505201e54105032041480d02d0300102100c0c00c1c540d0f030b4031204054400c08a400590b00035102000104400010410400542d0303000d201091103650384180c0340c101c087d4001401400182207910308400a08540c00c11200039100038070b01c24495440340702043c1220000350083c00715611603000e01038125010310205025040c14454a002c45085483d01e03075079810002c05a0025010011301c1c2000300005100c035180020200c8001101c18121203c204616000f0708115103900c0c0b074152a0907024580311311a042d41a6002c1c101000c010b81c00c0d03c10400403c0014061014903440b001c030800d80210318140c280140c00c1c04101c00700c0039411400c026810106210380301c004c80d0300c00e4082c030000c00da109403140b000300400ea200c04 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 305413183 1250 305411933 305411983
    0x1d0120070f1e08030901020a08070602071707060e070501021f061a07050613170703090512030d0e01090c26030d02041401090509011404090b0411010f080603 69
    0x5403030030303000394021081c04074a074002007001c00080c001600d814482c0a03200110948540c850b588a118950441d03025a01c113030034040c00180380d0030142408600072100141421a291141d0065810000c0c040f80d20310300000d1320700100300c024880c10040c0c5400300004e2208504010000c0e42c2e0708400032852485c011420540840e08450790080800350011100c1220128035016030301c40c26800a840c210340d940200d000207680d42c814074600c040d00642080d000c07500f04180403000005644001c009804212403c00086001d444980c4045803417410040103655400300c1c000c2c071500302c810040d8844c44a034103110f8104045462182e0040c01c0d140c802d40c4590b0103041c18104c20f00c111204810481040c0008915244800341750390240080760202d40c0c440030f2281040004482103182da02400d40c0c010014801400455101c3c0018080001e016100181c0c08006446000016000701e0f012600400b020404560030350744081c80c040000304900b03081c10107092203000241c40d00c03804100840b0f80d400f103201c12 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 305414433 1250 305413183 305413247
    0x3021c2328061211010f03050f010b21070207180203040215030c0403060908130816030b07120204090506010e010c050c011b060903031401060c0c141f080105011d01 72
    0x30080416010071111443d440c82c0c010b040202c2400b039a0b0100310304802d442e03001c0b8024081c042c8219980400d105407a03090024900c030a810101c2d130004207400c200326285a0705081a070050294071550000d148051508414010700f01c80e2480700d4030380d940103106010058a8a0065481d02c00188000300d031a039071551318200c1d90340920b520251802e800d0002c0002401240c2000b05010408c40820b01100d03501e0f950b905030394146c989000c0358820780401c0200040307100c54806507007010580c80c01220603041203140c0c0341640c01c01d400940c40c26944406002042d0b07004500542109401e08284807244440d03110280c480b0035001109042c0540e103601031844a103024016002d1690010041003c00c1141c20300400070680392510040c0d550030341001007041d90080030701e058043d0380103a03e40c00c0c0354109801d900f04154030510017030700550320b413011405000d00104910b17100c00c035035502c840072580360600040405011003d41289c8174055101030b0442d9078000c66a02e00d030380e84030341c0503c1c0d880150485 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 305415683 1250 305414433 305414441
    0x5090d02070933090b0108040f02240d0e0d030513120c0b090c0a05031603110d0204061d0109021804153206040602150703021c2328 58
    0x101800c54200103080f4500c103a152504503080c0c80440a042002c2d00c4540d00548160000340c90150104d9041c0645100510340300401060007020380e00c002c01d03144115886100303540c002c0400c1c032407e1503c0761501c03141504104880f0503054680e1906002c60300301a05d00c034000c04100c85000c0c0041e80b480704c01110a038059202406007a52101314500035107886600191039002c9004a284581007802c2c0c0080c0310700d400640d15490912a00000d40030310300d9580c80703004405558640d19009000410018056906c51245070000d104a1030682007541051695040740841600000d01c51032041c0030070340046098030340c07003a0030050070f86002400701d801c11501014001c803544106010004002e04960f4a140c8003481040c6002c00034004100c00c03858410020140224020b01c00164006d00400c010b4044c10342805400803c40e06006241060b80c0c5260f00706600c0c1c080320031f10082d854030843c00c00700458a83c81065069114462002400c0c100b241c100113004524200b9040d21400728445000807080c0c0c0 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 305416933 1250 305415683 305415731
    0xc1b01080c0d022701020105130c152a05062a0a0e120309031b10050703050c03070b0f060303070b150a050406140f0303030403050a1b1202060a05090d020709 69
    0x2c4c001e40070f100e85032a41c0c0500d450103500d9030065080c10041030712000d04080c6040020382c0708203011210340c28407207108600680d14070707120204009031003100001c00b04000541c05400101588005111180c186a0300d800c0000d1309004420601051511a250340c1c2540c40e0300e54003030303503501c036640b2030420300102c801c0c000f10302c4517035070100d47d41003039240001c00040103000562084c1e00380d8800c0380030240c050300c101d80f240084079004294400c08825240c03050008180007032107801c0140c00e00101e1030460386180c01500e4200d07008454041403022002c6501c0302903a0001003200110300c4c10503256518001c51502801140564991501182881d0b5400030750303d001d800042c0c010030040b6034600e6003e20003507411301094041d4000714112005d5007400b000f264411501502d07040e2500460b6070080780c0015581810b0000c500080b002c1c1400500c0203404080000003d41c01401c00d41060407640c021100050f05600b0958003800007010441d0f00410302104994141d2800560f24090301012445104092 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 305418183 1250 305416933 305416957
    0x1030515091006030609060f120204090f08250818030c030a0605060907030603050d050d02120705090f010329190f0303020f120405040e010e120c1b01080c0d02 70
    0x1c0c10031002ca00e00a2840c8200e901c0365500740016580c80001d0f008940550048503e10210b4000901440071043c104440c005e102800c0000e13041d07180c2e01c500214010440701101c50250000310b104c6401c01780c005285440000054403201034005507203002003449401c880e00700b006030751885844255814009400c0ca0103001d02a11100380280c0341a4008101c1100e034117104555000215003440d110384103001c2940e6100d0001c1c10607030070342c070f609880c02d0300682d0000f1200d68082180030400d4050400300342c0282c3c4240c40e02501c5a80c60b408000a00040340c481070704142c9007200c56a10840803030000b0051040c3c001007031a0b00115100030070610200d4071031029008800c0c0d0800604185031a0304401141d0090b401d441c0401d07001007401d6241c82d0a21000483c059007404188818135050f80100706910442d0300008282c0400012542401c90880742c0d02c00078000418602c40c06402440010001000c07002c41c03103459131500c0000303000030390007400355009000c0101d40101012003503030489038680090 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 305419433 1250 305418183 305418199
    0x150308030a0c0809151b040b0d0b13050408040b07020d0b09150903030c04170f0604030e040e010b0307090209120601031b2102060a020c090c1305010908060601030515 73
    0x1c4140d2801a01200c02200001080600002c025141c0810010070072480101814501d0b00c46e00005081c204a4100151081e50204000561030702c3c2075008000c1085850004202ca40b000c0741000860401c05c100d105202c2c0c2042e00700400110030f0401c4a040e10401c4050341d031141443d0000c140a0358280e10b00030240740c004420b021098000164143c08484208029540d65440c003000640b40d01080d2403d544400040c0410b100d0340d42400d01079099412803100315007040d0280e050803885e2007025030701600480d180f414242941d00b014024108000e0322174001f80280407180c00440d80d2400e40c2d00c03d010035640c1c003080d1011113139604100a809032031540b0807aa02d0356183e0034900308180c800391000030700740b18801d00020660500c1c0da130311007900400312890070744407215020701c4040d9100c0140ea03000c600900e0100221541e4114469000e17102020340303d03488006140c40b2080f21401d5402a505000113140d04218a410016626600403007e1902180e551a8a5038006c1480c4501100652003844 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 305420683 1250 305419433 305419441
    0x151f021e0606031c020d08040305090d0605062d1c0503030103030e0907030c0206060d170f04030c080708030418090b1608060a051305040503040e010b180a0e060415030803 75
    0x26030324000d240c2102943c1c031301424003100800b9480e02d4000310740940c102071303600d40607036000f040c140354454084d040841c1b61000e280c0c001000780c1c0021008443c004d17500c6083c0405c900b042c180306c461110601001c408400040a04181c202c3c3c2d8100082c1c0c440c6016005c6005144802c83c0705d07240c4c0c5903000c0b080341e07201d503100d14000c1c10941440e1100d5004074510ba001644440c42402000607400b160b0b0082e00316a2038090138801d182d0300d14582035949181c00d070165042d0004e490700034400d4184d144a042e440e0750441c6407802c00f6050302c0e400240700394440d074024010400c010084604035070004240c11400404c501500010b0202e418020f404143d20504025036101d02581315900c11100d40d8440001e50f46d03041c20440101c03020b00510760003009200c810a22003089030b00c0740e41c029000e0001ca80c00c05a8442c403042e00c80e8426080008003600120300c0511140107407043d00e282e201d0407640c0700c05d0203090030721881b00f010004081c0e40c1302d1900d0702c0c1c1c40c0c600402004002c80145400c043c0c0b459892038 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 305421933 1250 305420683 305420743
    0x11b06051b040e0912040509060f0d0c09060f080303010e07120b03010c0e01230f0a0e0a060e0102120406020a0f1b06030506030d020c060306040c11060109050f151f02 73
    0xc800c4804814034024141c03005d50f40340b81e04088030142c2d00b0041580716541c4648040c0802802c6000c20142c20044440c44034000c9500440c03c4001000345807c080380d12420a28003031006215a40308802076803050005008040c280c1070155840718041c5802000700c608150f045000e80f40410045e5059407a01c0b400070703545079012505103c0d044081c0c80340c0c2c490159440348130070200c03445214480405400e114075a0b4107042140202020350349443c0881c01d10962500080b401b00c0b9a0f44110042a0606c00202103560144400110652020304403410b1034601000a900ca8204a034003c10400798200d1600030003803a903224101103c007a0381020f4a55454040140042c2019241a4801c1c0318812608628520000704032141c036001401d51741c1582c59200c10f0001600070242c9140521442c5107818039032103000c0150500820044c031000c41c182c2040d52140102031009481c0b1441d0b82140e03000e5a8840c0c44110400c0d01ca00311035050100419040d1000728104005410344289643e100c4c2e006c400045 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 305423183 1250 305421933 305421959
    0x60412021006080c09010518041e08040b0403300e01090e07200718020f0c031c0621140c03030412021302160b0702010902210606011b06051b04 63
    0x3c01175a1012003a601c500070482183d10329468001c114013030780000781c0011940c520240700b002a092809010a6140d82c401007950803031382050204e1003022030104140410782206802035200c12061000d804c00c0055041103aa82901c041824040c146510040592044c400080140516100e801d15420401401009500d4110888465600340c2c401c5800d0303240d0101c0d81c84100e81d207451800158401c20b0b0b6066000e50442c0c011140070010a0047d11058442840104082c090758960030800d4a84514601d044801c40c0d044204e07413418000480004c540c0c01c01e0b406280c06d42224064540080c041c20365031400c200c0b401a642c0500010a000415038000e86001d0030452088a24102000d1085400340480c0150254039285040080c40400800e240b0341c01d0540100c4680700101e0503107016004914140900d0109a03401650111603400b105010301c178050304488240703081c64a04059044501800251120140620b80c1c0c2d0400702d001003504a16000ca107400c0700c245e942d211696505d43c28040 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 305424433 1250 305423183 305423203
    0x1e0804020108010801110d09060b06070503280503060103020702030a1b0501021e03040302130f14150405010602280f0f0c0b0403120503190509070602010b01030e06041202100608 78
    0xb0645900001c80d59035418040c10000038a001ca0160808407030500f55000341c00c40388400d071038840c1d80d2019072800307468070030040c07861a0140000310f0382c40e80d00400e42840e070703000b842215000c01005004842200d41c040203ca07045942482d002d40c44d68580e000080c02d10303612640c01050710301c0c840440030000b803488200d1300c100c88098090324087e440c004201441d03103d03030003a072640c83c0d0001c000c03d00051030080d04100d4400a02e02000621112464003107007101c0c0982103812014094404001c1000c461000080c1a24070644044c0419450001b000e5603801c01e82e003804105200c80b000082c0b045181e054182c01054102258a040d44103038141424038910b840d0003555020f174140c1001c181c1c0e0086030110703811243d200043e04510081c0800403030308c030380000d0880034082c039030500d11004600c41406030034010b600300e60203000c501e07240145c00783c2107810401e485c0d07040c5410042100507802002c602580c2c01500b081c03038007a0303608030841d049007028040c600c4400b200e49414070100e501440080c9481d09 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 305425683 1250 305424433 305424437
    0xd0f0506040e030c0d0f050d05010902030109060b0a09030602030622050a05101406070618030905030705150d1104080604060906050709230301020d02040b120105040b030304060503071e08040201 85
    0x359804248203d889105042040c409540041c0e4014a0309104070b924841c41403852900b107003040790fa0880300d0250352080e4030101d4816004401481140705504c107800041c03885c510183d281420216024180084a2001030140b640c0400060250746424902c5080c120500001215132000c03c0340c044000c2606403101d0a10070300d42400101c4100c0c03030a10380c00c181c1d9810f955902100c240c5404014607a4040d03401140c0700b03602c0703541c111500c0750070b250b00d045d001c2c1c4130703071600718000d42003c050515048075903100d00d20a007810b04002060412120858109110080c0d02050990908040120764401c56100c0380b00d80c4070b83c604001c1072100648c0921103180c400d030418052500e5079a002c0391403121a010702c100c07610b40c20951407035203003048400c407900b240e01030005420003000f01d40ba841242c11a0713004171800d20000400b17510030102c95402c1800b410088404124003898940070a44c0d900980c01240207020000001c41c0b0111b008d4040102c140c1014402c030200c001107820700501001c0d05031001c0780 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 305426933 1250 305425683 305425691
    0x140a051e010915151d0f07050a200a0209190e03040e0604050a06080d0f0e09100e0405100504060609050a0e0607030c2f0607020109030c02150d0f050604 67
    0x1900c5030041c090302c411075400000d20b0a5040c0b0718410040101441808070703481505140e000196540d01820200c039804c0321140c1040313540f030000500d41000400505040804c031781048000d60042e088410000c40d5860b4000c0800318190050f1704901c2c00a2118019600a64450400103001340c003c0c082c5108c86d00c1c000c41800450103c441040c0d5a01903401002d07480380254001603900d0030142c0c400765116400000101311940d860719514180031004000c00000f44004840e0309025800c00d200c1e80c100c0300e00b540c50051610304034441ca41d050b10f560089001c4110310801117030030710800304010356503a004400100aa8101071030301c0c0c0001c00791885803403140c50600001903a01c895a1141601440541c0080c0800b951400002c400501545804d0001d00031000d8009018034001220070b6070180062014107800803442d900c0e2031521400420020071a03060403414400240c1c000310202101d58140c0d4010b4a0901054940ae81c601490145801c101c1c64004822007007421174101e03a004484c2036034200 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 305428183 1250 305426933 305426983
    0xa18063804030f02040b03010f06170d0c051c021c0207090506010c11060307090e270708030a050d0b040e0c01030614030309060a0c0c0f050a05060a1b140a05 69
    0x15540c0600c2c07001520a8085103840005800c00340c0242440502c001d000040e1001d02c070301d4031801c842e1a600304408101c5d9600940b1110b20040100d800a40c0043c10140081c04882d074500380d6030740c00c41201e90392072200221072140030b60013004120040c0c801003518000c5900d0400c0000c2d42c80d4150300c01e0209143c109800308500354007070000151403a030040041524008440c00f44030fa01d80c07010b0300e144100a068000000c5441049140038001c020398440d00c4004c5ca07901203100184508169101c0c4030340c104180401451600204442c0c0766806801e0050b1181103409880c0010184120455085800d2032800720405c24080b884030700040007600c0400c800c58461407100d5072700418a0342039405034010000c00c005840c0c10000b802c442d1a4070710f4143c101304200d580d503a0855200e41d10040c00c004035508140030516250a20001a06c0c050300c10074244503030017000401c00488540002c01d0050a040580180004c512003894001481422514009441e2070070668920740b1804c1c5000014600c4040 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 305429433 1250 305428183 305428289
    0x6080a050f06130c1101020417010b0406080d0f03140906160206060d0b06060d02070503040e0c09130b0d061508061006080f070504051522050a1806 65
    0x34061080940281d00b41142241614004d00c0c164403007005211310040105071900003400100081c0100d220700042c905007042d9403500b5111000c2d0030728400e9007810b034140702d9580c00203909500c0503550301d440c0a060990141c1640103001c40300114012200c2d000030400600c80c006246801042d00c910840302c0c0c1c101d4054101d845807001d5460a5014426900c03075400700c1c02403842a83c0180d8001d048038a0103043c0c0341c18100304c0c1d000c080c007210581c0001c50100010015034548640c000c0041002502d001e0300c403800903504408065004024642d00c504440403a261225011100c941c880d40800100e1800b00d210045070030640b20f010510f108000c00100543c0240c1301e0101100c1d0729440f00e40c11500c50b41c440c0380b801c9a0051048003081400e2000081c1552140100c0006c4102321110382c0e500c030540c11995400c25140d8400001880035101d0030883c3e0b454482031036040783c5199071414290380b074030340030705c4054800741d401800b460615490b0303c00f260700e40600d50300e160b840e80786034181c0c00b14140d400 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 305430683 1250 305429433 305429461
    0x1b0a12020c030a05060105010309030318030207030309081209151b010f11040e010b09121006030317060d1401020f12010620100209040902030109050c010e040b0913020a0f06080a05 79
    0x8002c0217900050010031541d400b9410441005100303080c0401d21411144a1081c131030107405094006070b0181c1307810004d05800000700c00190203841e0140400c00503074401405544a6143c559014a8445c25030001c42c0c1301c1202540c4a1000326580800c15070401414117000e0451080007070050b81c41c18044002c2d608030b0408860890700301c03c42204050b843d024005d02c01d60080c6002c283c000ca201d411000c820041881003c803590a14034001031910305504008240019032005210040e882405000c070b41d58603a00706a0404e644096210708150181160324064068628176081c0340d40b003c40c0c4c202e85070314040d04c410f050380d6040d500c0c10541356a4214412140041c00346001132600302260510f040c8600b5001010311580113407004c02c03200041c0d80400d08440640c40144c07550742082032244e8141d07170b02029450030a98219400e11003262080006402540007500b00320800000702140c50442d280c1c101c8060050041d030507268282a540d1902a00d900c90488120140524240020707001c01e8602c0c80d = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 305431933 1250 305430683 305430703
    0x60b030c03010c08060409050a0b040503180409080702040c020102040f08010b0f01080f0a050408070804230a05130207020a0b0a020717010218060d06030b01080f0f060c09061b0a12020c03 82
    0xd1404d469403540001c0c080200101c0405440c1c90003a200005d002c1804510306500451080004583c2c40604c2c81160384207524500300107102d18189098400851408401d4911450b0112400190800d1410081c0d0083c403c40e07018010400354004005252030341036101c2441548140c882105a1690034011216403404072816420040034002040300400d550780f060360701c184039904184c90a0800d40343d400799034000e68402481030704d88010101440b0407046103207100110594800314680c1c1404d0004404580821518003002d502041c420299543d1503c1c1074000d00003502180e44d80d07004c0e040025180c56403030003110305610301071100c00e4604c81d0501c00c90307540300361110300290280703008070412402d84d0000540582a5407903103004404601c10740d080b24000c259000060541c001005202c0f03003040e4040c403014181d900035008206203115420200e401d115401c44015640c3c4042c3e6078204084a202c0f06440d1030b5204078505501040401100b2003000340058013221503007400b400806950f440342e90 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 305433183 1250 305431933 305431937
    0xf0b0a090506220b030a0c0602010b03060c0307030b0a1503051608090a0201050307050d0e0105010510020a0c050402090111010e15010b07030f050d200702010f140720040504060b030c03010c 83
    0x20725500060b00f240303441d044080703074100441e06404400000b440d184d10080c050324002d0302c240003003080d15024071410703407031920036400f4124915001c08107c0b40d60000400780414580c696035110155038980f1000b601801149a07080d41c8180c400d00002c004180490b01c1400301c2801e0706031440098040d203459413141e890304000300000c000c80da0044070305801c0904103000748041400403006080050048901d40c00044000041d036603d04002c000304807003404813000a5410044154000c90721031760107401681d03426140507985044020040760362900e0b1003003014541d468451004010741c004103980b06440300d01e000e40d000c1c59807142c080039214032401c00300901144680c143c0034a01c500900150100f00d001050005120000c81c903411256001c48202d50841c00000030b0140c00c5682040c41c8084081c02c03468a0316008150304070603500c13446030b44400341450a040e0495025410742c14040c4111f6000a00148901d080c03516141c4003030007012a103a842801007414040060505100d6a401a9416 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 305434433 1250 305433183 305433199
    0x3040e100e13020609040b060c060a0c0302091f090302061306020c1f08042609150301060903080d1b030e0f0f07030b04050f010c0c0b090109080a03020307120f0b0a090506 75
    0x540d00b00120340e17202d840f40030b40140e1104140c120550f80c0402420304443e03070202030a020725020b541c0d80219404100700030245841880500c0d0b4984400480c0a800349144162a80c001c2c80c2002c20740c0d15000c0f940c13000b035002d140001d01d02e0064282d40402000c4401680850392160203400402407002004400c80382040e100b14400070b0400d03c90602c3d5a0028001c0d5420014544000344640e03403990300350700d85450002c00050b00d81c0c1c141040002c1480850b9a5240740d4107550400c0d030010940e41b41488050110000810308100c4080568000c102c000d900c89140c02c80143e8000c00540601188911a07405000d0402050fa0528000c00e884941d200540f0280007240e0031580c40c4426508003410030f540e20320480700c0c0105060070904c112511142d06884413512410b0350b140048440c0001484000aa410245008001142001a1000d00c006400c000d6240c0d60382c500f040700c0003800704c201e10007007504100000a83d4991f9070710410200005a8600744982d440c0c214502c1a03030300540b600303600800c038 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 305435683 1250 305434433 305434471
    0x61a0703050313050d02030715050108150a0b040c0e030c0a08030a03020c15010305062505030f0604021e1c0b0a090216050a060f050702340803040e100e 67
    0x1040000b1588200f1218a402500445855035480c0625000100000d60310000703844081c00420600e45090800278107045c0328960401b02d034103498900c40105105038036280008034100350038070307045a041d105024208100c41601d40ca030052628001101590207401408010440e0382000b0801100387d40c0380100031403400b00d280c541203000f54801040303031195018001d60f8400000301d441d0158000c500070710040103a800d010b40011454040c144d04038800d1034800301240313003050b002816aa403000016000d07681503610180481d01a108015004105400d40440e00e01c0380c0401c20003800c4140351045609901810003140801101c601140b440d40c00441283d04004203601c9030003c26000909280d204400d0398959607007860004040c030121015a103c1101c1913803c1c805d4410740b031f8801c40d03c0c40201303032001c4107115407403600c4210111016150028070b419500c80030710f9000070008014001c110307580d49503501011481e20000380c40021140101810001d040c810641c00240620382104010081d214 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 305436933 1250 305435683 305435687
    0x10305040f02010815150c0601151202090d02060705010903120c0206150d121d0906060d110c03040602030c0c090907181515020609010513140a050a05030706061a0703 73
    0x2a0041c542c20300382c07681c160300c214262244e0308034846c07107424a58400d0b01c498900110a05000050b00725903108044075520010072940408a0000002c05003001603481e40d100e008251001c3e030000c0040e4102c500081c410b0100101540100042c90180c0d880008008910b403e040981e0714140c6401c00503400343c40400c5e07050101812010341610000d0808401d501299244015000000c40402c040303001e0340c0d005408a224003c02041c00c440856000b45240350840026050b8014500301004040d40c4078441d401450700380e0708540d1300280e1407040320b40341e5a03100e40c025a00e600c070412300c4840307024060b020409400c2034500d42e8003e400c9400540a00d0342054190426010056245000300e502c4c2c4005843c4805071540d850054500d070000710802466880d00a881c00c07102401080c03040c0c0c900020403c0741081c1d100c03040c04650340b0035146504018850401803400c001e0407800342040c0685500881007000005c0102180c0c0e1003440305000c540c1d61907490030405911900c020800802c100010070001e4 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 305438183 1250 305436933 305436947
    0xd090e270c040504050a050d0302071509020103062106240506071b0b22050f0402131a12010801090203191a0c04090b04060f031103031608030103060b010305040f0201 73
    0x40d140821544030780041c00009054a00aa0701550140c00c15054071003400010710203e110800c807400c1c1586014070682e2490440d00d07000c911403500c15070b00c04400045a00c40d402c8003004040b040035007915442078000c440e0b070781d00b04032038100c8400d803424a0641c03c810050544003120240c0f0032100307010074602000d200440e486488201c500c8541c5603020500c0b041042c11140140030081404c40d141c06503004540503400510f5041011482078800c05c10a40c1e84400d044140d40106460240e100c1c00380059440c54800075401c000380c61140110841900017900000d0008035002c0c5c0380180542e60381d8a601d500701c4001c058042c3d010307006a41080d04110032900300e043e24902c904080420503820000c2c0d46090340c0d0907182c5410a00c80050104034601c1079002e0510420303800c6a00300003061500c032442548060f94840246194082e981482c000c2d0350074001d6443c40199032902d01181201890244040da000b400210341185c58101c007502554424492548181ea01c01c0c500703c0900b0042c3c005441c0c003 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 305439433 1250 305438183 305438251
    0x10b070219060e010806011704020127080303040320061b04120b1005151c022701020d03050c1218030a181a03150604050d050d090e 58
    0x30511600c40e6001011801d44410000d20142d0303a03180b108030702400010110000601280d040051404001c01892085c110310f0390010780c2401c10304041c03051151411450400348114800b0326504000c001003609000c80118800d901c2981c0740b28240d4440c411445440300c0b8010b031282c0f90ba00c0840020a01080108404100c00e0044440350a1a42e2400c409801c0c0c0300d00c1c601117990010b0b2006000100e1650711041e8060001150f6601100c03101801c0c140c0d95016140c04110500e02250444642c0400d513412a400d04202c805101c030044030311159018590f04290b100c90061089000640c010741c42403003414003c40d442c40d126481d00b0340c00140d0000254001d8080b05800711100e075007140c590b00800003003030f03109916200c900b00b91140107840342d5040328550280c1d500f60801a0060b4003c4210801c81c0d41c0311003104035005000b00c034800810715a001e40c4d0041d5400ca102200341d1028040000380c50300b40340d0820360b42c01c81d00c079455a4a004c6039007420344100300302c0704d1000380b101640201000f0350044 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 305440683 1250 305439433 305439439
    0x3070302060a090309170102090108010906080c06030414120a0207080601050a1715010f1703031b03040f0506010b04031b0f2702040f150206151215040303020a02070503070b03010b0702 81
    0x100350341b50182c507040d11110b21000945a98000703107418140d6013094400380180795080d010042e1602d0010f9041e05c82c00740104180c8540d0000002504100c0040c0189400c0e0b40301c141200c1603060007002c001e10070f030f1005991502600c00c02c040007403012030010f1183c2c10303920050700007051180340040c00903046004480f071503442d02950f84c0c0171025a1010301c44500a0108101c2c001e0381e20b107400841d030f100c000c00e00440c40103034000f0000c010710015800d070000ca80000030703001640d0340e507aa400c011a000c0d0954000400601420300002500c0200c100600281c0b0301854881c2080c800388248102e00f029603108203c0318003d089020401c401c075020710b00d0750003881b00c03ca20464800c104000e0040b603000d0742000d54200c0ea03c4002344092302d240a080002040c00740001c14983c1040380319220074001c00002a4407451481011000f505420700080420001804144255080600e0050083e4000e050a01d0051041420001d07942c50b000905108945c1543d07401c51540c0d0802025080950004a082c0c0e0 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 305441933 1250 305440683 305440697
    0x1804020105190e100810050d1509031701050103090506040204050712060902130f0e1b040801140615040303051905160c0509010e0f071d0406080a0b070203070302060a0903 75
    0x710102c4900301d1003008054968444002c880305030200805404800b182000300311044081045101448549005440040f5000c09401c47e642c0780c01e1000c0d4030001c1440c003803682410703512810143c00119042e080d440c1182a090241c2c0c8600046003224038850000d015584900d0228000d82050361103541c2040c190300e80016074120904643c400d850040c0d01417050b003980001c204900c4120719503900c001d4103000044c412503c1c40d02810401c86540900703030348062a50340d01a80340e4010500110703401000e8520090040341400c07001d50f0517851301142c0d002c0c007609400d045000060b20010880301560740c140c49040c14007182c80d4143c441244144104028031a0810103981c1c07412910409040e01d078801c0d00c6010185007840d06122050318180d0004056a0840041c450813012421441c2d5202c121450128603100b414494141150740240416400910f002c0020940f080d0101d030001e003050003100c01c1c1d4075030344488a080380e27684908100940143c0250300030411002c81c903081982401d002e407400300 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 305443183 1250 305441933 305441947
    0x1e080f04021f0801030620270a0303080f010e070f03020c0c301b010302070501060b0c071715061504090204060915020c0901060c03030e01050414060f061804020105 72
    0x4807084085080b80020651000040081001600502c3e201071180101c0384212101d0300160b0005001d405140ca902503074030760a000e1150983c4040505252005011000031940ea04000e8550001600c1210701d0060003400400d0903043c203104640110070726030380c00e02001c402950071002900089000852406004103180701580e61040d1003030112200e07001030030b0000155284000c1494280e8131000f00b90451081d0b070100840b00443c2c8136074041d0030b09016070355101c2494154014540c0f82c0101032528004520030603013000008100007074410740d201074101070b00c1b4130031480d82e2020707001801d1190466003070000b085401c000440701a50021503880505180e02c840d2a007050740c20076008240000d105000c10418803181d050107482402240c0040d00b0449a00004503004c6601400f030242440103220b280c108140c8603502418014200000800c114109460a845d10401e01b40005503c2d1180c0d07800704001241402c4518040c9000920112001c85070f1301404410b078500600c10ba0610200348003003 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 305444433 1250 305443183 305443219
    0x905030325021302130f0510030504031e020d0e030c090a020c070e1e060105160b060f030304030b07170f0105010f1103120105030d051e03061906030c1e080f0402 71
    0x202410320300188000da202d40d101c5008501c0e82c0102d42c80030702c1c4291b0a580410854a0b000700d0b80d6151116860042680c2d40ca07401e09680c002c00c140841c59210050514410741d484c4c0c00f01d440240403c565403031a00c010920800c26650780c5101c162107900050003008070f0520f52080d4014a003100444041d14040c5965110454107440200c802041201c4c2c0d11071200320701c000f0380031a968880402d08202d030078040f41030301128240c5000400104825201c1e408180380d036441000d029184800142100e907540d0302d0b8501940c0c408801c0d00c5c04000308020316041c500030041c103a8003501c03c3c04c03840d03042c3c050f50b0318120045801d5108040d00e64240070703084105802090701880104002848420740200a51601041c585482c83d0a03081c03c041000070f03c4018041c507040000790a0310540401d83c0f03601d039295080045c00c0381010144104520302000c600060143e01a0080c001e04400d58880d011250004965407010104281840000a0050000449154111003d00d800c540040c20030050341030b40c5154 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 305445683 1250 305444433 305444449
    0x2003090d02030f100b03060705040e06010c0c180f0e010b031b010c0204020408010213090b060d23090d0f1d0607170f2503020a0209070507080409050a0b01090503032502 74
    0x12a490917921160b984407141001c10805810041a03d00185810315000c0a000c171004080d118904002c0c00d0b886940600030300100e001c020740f241c046034144e26420f003210400144034400e080c42040d402d064100c02011018447c014260380050040c0489503038a04090343c1c030240d40c03040c0b1418032084080b8440940c68520113040900300c041e0005a850b85400c009031280c141c40c0d44080340c91814803d8803d05070711204191400c0c02500c94000c2001c8000d04121850042c810f4801c8454111403001c111000600103000712088030261207004410001540807070306100e24420164030641450b490b042c490410b403004011050184003e01d4890885002d0b1001681c4021000c0210341400710752130541810411110f030301803172180036520590314280c2c0d01079211495190040c3c8104480b90004040740d0088084400269102c0310f00c07580c49031900c03035403c000c00d82680d0035800e20313140c46a12070103540124141802e031240100114100105100e0f155002647c0546030103030760210056910050700c801d02c0c = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 305446933 1250 305445683 305445703
    0x525080403021908010204180e0d1e02030f030a06170a0308360120120c250b0103170a080a0f060302180a0b1c1704031a01062003090d02030f 62
    0x21440d4008c0380303003200380c000b0384004c06d8448030580c01c070b902d0603080c2e42c1e00700426039000701721041d0560854120700016800d50103104459103000c40000f04000780f03801203601c1036058820320300c500d192098182002d00e9664817823001c000c007c102000007066426002a1040c0080407555110b0800074080080d0030115103071088100c0c1080e07441e413460b010441c2c81c802d41008908810030100b4184000b1010032448230b42c010b00f05550080c0001030000204001001884a480d121109508031803c20700d0443c0d0006c10920054038440f0885000c05003004a440481d007900b03241b9912a4459210200390303030001c204a07092400602e655050001c010f8070350a01d540d2070341d8809614190207161018070403040d50b4034510303081c0c4504008000071102d0084e80f8a40000c66403c951100e807003562a0728003102603c82d64001605400140304c0510b5280c1c20541d020b41a942a0b81c3c800401c81042c0d640303808600359880c40c034082a007007400341c06400c1c2840220411698002421900d800f0a98050203041030b013500 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 305448183 1250 305446933 305446949
    0x1321081b15040b010605070f060f0204030b0c0d0f0207080304140c27010909080f0a0c020a092301120807050721120c02010806010c050114070525080403021908010204 73
    0x50108420f200000340075500500c4c1c10f007007407441e0140640d035944101118081c01000745507110041a01c03d0b96680c1524061035004840385140c0c1085101c00160f0f80105100844c800d080581c2d500c900001c500a8800700c0740c0c405680da05685442d40d4040301c0c04105807075001c051081e10b4000c00c1c0b40d55051003452040c7e100401c0074140c1d00d290949090b00f01c40580150750840d081c014841e000030020000c0380e030700285039540c0c25120700c40100d046440f250310141c045e5004080c40b1020903075201d164071003002c581d00041c4001181c1031000c0b003102610001d100b8800d800c1065907026002c02c1d6004018081d581c07148055808445d00c0e0ba02824100c0c0c4030414a04505940752a024100110352840c007078081c10320304245482c60101d0b800203007420f40c018152410884038600c42003c02800b508540d25286100d51207a18034606600c0c000c009420510b1031308407400b801d95500880b923242c00780a000c4250814015403500742141c090010801101104140010309900009611182072000d80f020340001c07 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 305449433 1250 305448183 305448223
    0xc060213050102250e0711010c030212060f060a0c050c0909070819080406052b0b1504050306040609150e0d140a0e011d0a03081321081b 60
    0x4140028507213980760a031500e910900400401c5030002090410f421500d0b00c1c040c0d2502035032854004c48164141800b03024a82d07003040800d0b1000f64145e005040c030346000010700c3d041d03903030741404100300c4002040ca1305410440800000c1200303841010007912590041c000c4810504810300481c005070011910700249400428051058010134450391604c03112134400d401180840d520340c0c0350284100d12401c07060100026020f10170038011300f00c1d44240382003a410010000c2002401e0000380985125051050000d01071109006e070940c02035400341e0324050020007a6544a60314000103084001e001d6580e154044840030180f15507014035811409250080e0003a0700c91000040c01030440d141c2082c0300400c0501c400105294010a8141d20500c00d2a00e100c415542c4450800100400c1c03024540020403924007106012440000703111090700c0826610006903102003910074807185074070000445040603c07030800310303074000701406654070880f1140a0b80e40b0320740c803218680f00c40700041a080d0304c51 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 305450683 1250 305449433 305449439
    0x12021216031107030509010e0a0b070308010e090a0b0c180d050705030c040501210309090c081506070c06080603030409061202100201050912071b0b040806010501030b010815010c060213 81
    0x4980100003000003503103090b500304840c69802500c1402014011410850250b02048140d90b0b1103003550010a540e004480d0740c0e900d14140140010b41c00d000340002105883c011070300c4807000107014000660401c0c01d001c0704d0340b50341d41da0904c0c0e584044140d0703080c00307540810304055036a401b0070060a241b044000f8591a13181c82c0a1500305414040110721461608004001c07200800502240d91042c0d030344204c0340107503549001d0382c402945070080304155241241500d041500003d400b03004408009010b0a113196030b908210f5940f20b00c6000400101c269a02042114014030169803c200020243c908083e01c414104003159000e80c000c4000250941621040d420181d01c400324140292000303120614204a0305680c418608078003030b4400e04001103600901806d003e82048040078590105e481c03070b0351980400f0707540d00580142142805242c4c0001440d6010b8410380c1540501a181d1010301d946890703500200c0103110800c503040c4a0515a88030005c0d1851008008091405124860140c1 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 305451933 1250 305450683 305450687
    0x6080715030c0c02090601110f030301120308010e1006120b1c0b09120313081209030301030507080114130312050a020429070b07021c030518030a0c0312021216 70
    0x205015254180803030443d89001584400701c200754462428208200b640a00e11041464070001c00607055083c0008800400d00b6000c000d2250b070741d1400303aa10310000740d880c0c1c618091041c3d0b080e41c4400c1000b620070001c202d03250103007141950b20414580001038410302c0c0d074040f0b00180c2043d0604010030030242c40000c20404c40000b0b268210620a009200110006c0002c00c12480003901e002d409115081c403200070010301d14201c810038103641c00c040349141806000c80d5601d80080c00203c8550054450201300032078144a01e00c00000703102c6640d0056111a004000e011690203403d07410402c0c0c8018000400c40240641c0b03014040c2060016a501d280081481805c0304802e044039140100010441700821580d0503a00c1282d0001f2020f6010b44880c8030580c0b504010f2a0144400180341b641803201d40e405501161003458002d100401c00310701c042c80151079100302c110b0313203000c1003c820392840400e2085078003513401c0707100400043c03811072000141d5052050403108200a03490464071280712503 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 305453183 1250 305451933 305451941
    0x603140901090209070513090905010615020a0c05090601050c0d12060603090b1801020c07030501050a0c0311120703060503011a030f0705060301090207080910030b0a081f0f0608071503 81
    0x900910000c000b240280e600160f05014050034440802c00007040c041c0030001602e40250040018a400b00818111407030014013070801ca10544c003040c42d08900030b140e1103002007100481d0340d500564a0340703128204410020a03c0d0041c00241c10004280102c0308002001c00403122025459240c450701108802513900c01d448264004104250400c0451000502c22580e081d412040362800ca07200640041000c0f4028040d00c100390f041807141030b00001c140030040d40001d0040d80529018040b08007564804c1d8180c6d1940301e41e05455620402108180407800c0d02c0b0131740c0001d035910300030035010f540c0e01c0080c0c00e650300a0840301084a401504080c9840c0810501401c1351000d80541115841e203000104c0a020510900c00e0450700060554204000e12044810510300100b03402e90010000500400a0000e007103510f0040f0324a00700460b000b91b0026040984e4011303c412a40400060750040b0082d1140c480b00b8940c6c20b8984030301240f0184103015040c050010410b6a90034000b04e5003008081e5 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 305454433 1250 305453183 305453191
    0x705011b022802030a050604030c0c0b04060c03030903020c03011b03050f28020f120a050a05010e1f0b07060c140c0a020607081303080d0c05090603070e0604030c060314 74
    0x141d804080c101080b5064444540d62490101018504800d043e001003030900030b48000040260056204120826402404401c21103004840e04004180c4072488141584114080c01005c290700d6681240085d2180d040300010600c203105640481280a0200e8251105220188510204000504003483d0316200700ca81c8044242051041030034100c2d07040c0c0c030100c0c2903140300e450082900003100d20184590101c4144403001385003da83c5080c003603c90461031400b41c07030320721b0854140008907200d404103001d828140c2e00c3c420009003541e02c9400300401c065000a0348a83c500040c0341000840c08000c0020f8050035000c3c041c0800e40580f4004004c0002c51b04060b035094a42c4107102a000300e04c00040c060500940c1034415550f21402c0d410100780707900402002100340710789060044104000366000c1d00307c2c00b001e21800e200320b5074150720135130307007405450a00340c3c1003501803000817100340c0b00310309030300260038007403d070b14945030316511341e00c1e9842404c0e001180880d403282d4120300107103e1118800c0d84 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 305455683 1250 305454433 305454437
    0xc05040e0604260705070b04030303060b190509030f06010b03060906090403050a2f07030302060604270204060b07050705090f010503031c270510050906010b0c0307080705011b 77
    0x2162a00360f4500000744001da9207080c40701044520809182030300f404980305150002d0032140801c3d03640e8002c00030340d40240011030009080c980005407604104c4141d58a03030f43d03c2c501414480060403000ca4450b006540703601e50600c5000c069600184040c010b030b074080d10011140b9603603850a04144000000c01410090180e001a01003002080d482400d40341c422010b4a004000d00c101e54095403400c044030300310040041010f1510705103c030300001e0b407001182d1007602900d0a9940307c80400044507a03500450004400174144620701c41c401c03000c5000340510040002034030648418840c01c1c00d4014600c11100340d031200c4818452450304090642d44181840300702070040d8100f401007030f200d0041080c038801481e9161500100d080300e50f0010950080c240010449080840e030024000004100003034882e0700440015031603007030890180340d01c603119010080034140d18007034102e02203178860400c010a5020501c00d80c80010501801005001d01030000030420035408590641050b40000500341 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 305456933 1250 305455683 305455693
    0x10050322051002030402131a010306080313060e0411030c07140c0f060304110909011e0c090501080a110d0c0f030b0306060d050705030105040503130902070b0a0b060c06040c05040e 79
    0x30014000155000c00c100d01d2801c0540c6035100c80c804500c0a08022032110900d50521031641c41742c12101c091100c001409a03000e0041030740d6101840d450b8030130104280c12030240140140a801e008110135410390700050000035070240e0442c0001c055030010b66261030344c40800038051003404218075010102e2081c40b000f0f011144107000001e0349107240d64241c580030301408000642440404d605480d280400501410000e16100380340f10300038014400c40418001c02c488103200441a9880344515251321078440e2482d507030810005480c0d2900080080030b0445c0c0b214121141128042c010313101140c10a000815101d0500402500b0745400e00380420800d4a01012070490b9940080d9040e0803407019141c8801c2003180d07003031142c1440c099400c07603a050740c00d020901041050010007081514490700c050007100c1c1e02c072001d40d020792281001c0504107844a00200b102c059081e0700c5207440c41c1000340318604d00301d01d900e80e2506052040f02e00380d51003003000c0000c010710305250180300c4604801c04054a = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 305458183 1250 305456933 305457001
    0x90209120d0207060e0f030f0f0706030504020906044709040f0209070504080115080d02030301061706060d090f062f0702120f071404020705061f05100503 68
    0x80d80c035015885140200429469801d020b92070349801c20000000180689404541c6040b0f4549d90f01c0e0000000030441c4030307011000448a1003441038a018950003802c43c40180c49510801014003540c6c0a0001c44e01080c2007250600e001585c0500441410141032601c1c0f8103000c1c2c2d809000f0070400e60b1340d601803c200c100b040b0014a0382030b40325615030f034120b440c240710f92540802201c050080303810a0104d90303e01a080f00e500703040145075008403a02002100d0009070307000c004985070f000c00c2c82003402042c0c0c1c1da1302c1000103282201403580d005c0d001400d828145200c0101c81800c0e6240c08a05886841100c0c050000f07200f2140548207802c821859803100082c2824900e20744110b9400c070741750396004c0108a803821552201c0e14201031106002c102c5440300c00540000d52204645e11403140001010b20b09044103041a0007655802c54200000d04a247e5070080d03140c0441070300ea107680d14007146030000171902d41e440000003801400c0554441e07803a46015045c03941e04810600c00d5201c20b0300f101c8529 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 305459433 1250 305458183 305458187
    0xc0903030304020d080d110c0709090314030403030908031905010905090d05131e0f0501020a0201270906060207140a030507051c060212090c0a0f14011404090209120d 73
    0x202e81065055440e040300a106042c54038650240d4070385000b10a050021900340605584041d1000c1807840c02510380d61543c1d00400c0b4120f5072441d40081c085006d50184004440717044024607071044c02820b011405011030ba4800d00380d43e204407400d2440c4cc04030f410b8480d045003188200ca01500a82108002d03034106000010b03560343c07090b0241010494000b4001103c174000d140c42c94020306e001c42034004030045031920701d0104145406812800c000c1c0c9880054190310010707641060b80d8068484070a0a07143c003402c030b400589004818400c41240d91400210440148180d2000b0f040650140c25881d00b03102008090009903550390344102501c070300030b10100700c012030400d0807220116400715400000d002c1e505055030f200c030030141c80e062000c181c000100b99405081e0788240741d400c041d03d5440c4203410030050103400c0c90091080014008005005e800e460704e54101501703805043c40070007150000d02c084215841500b00e140550b80200c5c0f07034410f60806903041d8003c0c805080c0a030411080c99080 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 305460683 1250 305459433 305459437
    0xb0a050705191701030c030203061509011a070210110c0607021806010c0804030516050103050f0106110c040f0e06071418040902030f060f0a06060e10170412080c090303 74
    0x1001c03502050901d0b02103407070051200c5a0110f25503a2070466a40c0d40c0d00309400a000544410b07400f0703000d014006610052104e01103921030350000d000c10351903400c2c141a00c100400400080040840401022025070389042e140310b4191015656002d103451001c40a81c108000c00c1e4085014000c11301139000141d84407451108124118540d40280742d030350400480b41110070700c2c0c1c058003ca40000d000f1091000100d12110f0294440202961455948004504032502180d0100305408003000510201d803140004002007208034003154044a0403600240480e029244442422540c0d80301c114002e110a000d0f159208070b00b4284404001401c4a044043d40b01e0031841c100c200a403188461441e61b01c1d5440500c1264025007103400407071104884503a2190b080e1060020308500d100001c5031000107000300c20a6071322640d00c0e00c02c5030440c1d100340170060903210301c144144585800801c420400c61803801d4070030707405803050084400c1c0c1580c0107043c200c800b0b01540d28882d0b0400c02d844080d180001 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 305461933 1250 305460683 305460697
    0x51009051809190f0b010609080307060f02130e1e061e03070308030423010b03030f0304020f0303071208131212140106030f06090c0801032013090b0a050705 69
    0x7582292551800c024504020a001400c800d110a84801d441406024029442c0661040180d2031141c1d8840205560340d00242c801e100d0380313a10400420001070426080502c008010b40405414600d42d490800d0340c1000a40145180070b100c3d030300b004000c2c2c3c003802c81f2020a040c60201c140060a0010120314072000d0641c0e00b10081d104062241890346080044000840d007040015850b420285015410000c12803000604008111441c00c803815061040180c1340700018010341c070b4640070800c04c0070b854000510036a402106810140c0c01920240002c000d1070744150401c14031620341040240003000c002e030a8040310204d5202d00d2000410704400300d458100c484c1055040301c800c150500e0042e0a141e074a150360003044900014440f0f8040d008864ae0f41d501c20424888541c407026050101c4040b03100101c00510800f0042020860010122071500d200741c07109013581104070003107508000c1c06039200800607038506004091009104d082500426221424015428103000040c65401201 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 305463183 1250 305461933 305461969
    0x908061914010e0c0c0703020402030703020c010c140415110d0e13021305130902040c0f020c040e0c01050304030507050a1b05060901021f0603410304060309020f030a0b0105100905 79
    0x140717408803814200503440007150b00a0082d540c030b24004800401940000d0b042e401203600b406000744d0307440e01801c21032403c1c03441458080d007060b18082144e10903180113072040c414050034110303507905030b4814440d4075094011501c90188000300712040c00707151418142c03107180192060104500704c0e6220543e000854401f220600c912183e00b0b0340640003130060f080002d5100d40351810541c8165000710950500301d207540c027a62049407c680500c41660041e480003103c0341c12641074070703e141d03000c1c00142d41c000b8000c2c902542068280da40d0743e445c020014005a07103003011041d2000703081001310700244c054403040d1556410b0aa40c400040c1d520350f41c0d580b10080700700c0360361b8001c18141800d0380a14025504460a010344040524003150448030043c0700303411000200644651030722a0315408c0a040c1c0e1000011454a03103045000c07401072841c00f0341203a0120040455280310340d0100700c4422510300583c0344c18005e501d81010821401c0c4000c030000248507040d101008a40e0b00d810304ca4940904070 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 305464433 1250 305463183 305463187
    0x9040504020a12050105090616080a0509031306110c061204020409080f070305040503010c090e1909060e0105270304031707140303040c09060b0d0c0908061914010e0c 73
    0x141c030016030740d0102508100c4124030000320358820701c80c0542215011340018000c0d1802500c40340e100c64a1040011684070101390481c02080010303600740d21190340035031198142da003429200847c0842d0084c880c0c0c08400007038001da8586002101c14000c0d000c1d2000c0458005140025208007403c2d03000d0300400181c8155a80c1c900c2c60113103d40c3c48120b1354220100ca640c00d90b91040d0307150150481c0c000340917040c001d6207402c081804a50140d40c040054a0104414040360b50720a041880304a0713035100411507080e02c84200074009421070140500b00324540e4000b240c0c0b454015140c0144a0303085201d000302c003440d0030780080160008011542661b400810710305140f1240c17a50417801c0d202c0d6106c002d11740070110150b40303460a00800070314011441103002e0b6030104c2c1e031030304203000b41e841601130081c881101700440d01d0380385030325403048200280c4c2c2d041800040e42d0381c03420241829402c41e80d9041900c8100c0d003485c010050b0740304404482c0e440c80501041c43d41088040f070360340707040108864014500 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 305465683 1250 305464433 305464441
    0x106080304032102101113050603101205030f0310081c080703020702060c0a0507050a12020f010c02010201140c091809030910051312120e0d081b0a0501020a09050a0b090405 76
    0x200340540024000d01840030303c060498a0100c41487c1d00400b0408140d0f911000c0c041407900d07100041340d004505102c1c0d8038981c14100102d405039560740c08812680ca200070041c00d610180110007452140e00300c41c4211000b40e2810701c0c56410702c11a1401030703102c4d09000c054a00b199822924482e007060305480c0c0161600014404110355103d12020306100f031040044840411400181c07072700c03d6034020740740d10400a03903c8610607200c1d00510802076000c2e42101440a081d4818000c01280d1401480041058420460070150350314064409009007500001e14a0705404c01b400807001c6c000700c8041d0a02586000c80e56141c40b07001c1c00d08900e20407004000700500d402c0c80340007940c04590880f010000703159a2068007800b8812800780494490b400100c5002c0e5490140c5e8507a176a8407400b6050401c0c8134120b0f5601181588020b4a80d0215a158031003040c0d0f80f00d0401241d40c07514403a1000603558900050054103101c0290f0000744245003031001804140900015100b852106460205a5441d = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 305466933 1250 305465683 305465687
    0xa021611030c0a24110d05030601030f09050607080c18150c060906010f0b030f06040e0f0a030e0a24050319110d1b091a07210201060803040321 63
    0x69020b00d1103600840c940070200741c1c5070f0003034440b4071035109003030300044501e04440c826100703180014141d640e142c000d4108101d003a070261000b1540000140344c001440c81d04400781a046904103881907600b6808001004821a04080d01d2500101d21618003400c00560590301070303110419030141d600070444c1000200c4041001400c0e030708a82d215034188c0745035290041d85103541e01000d11903030806080d40d50002035035140e2a011280039a02032080c42000f9034034002840060106a10040d15074440c4184485042400380000d48240c1e201f503030340f20304201e43c40e820030010107840d0f000309400e05156449003070f504501001048110545007071180c0c50381c0e00e180d543c200c196183c0d41e00c2c003126410301509000341840c0c0310082550a00750741042041010385201c0b4600d1011a9a12802050a21400f80010002c010882c90090300130304050b442c0c1602541d170603900c1440c1c0b0b4981c0782d0058164094146064080c02540c1c0074109840086041519640b5038107140030003000300780c150f20204910100014 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 305468183 1250 305466933 305466943
    0x18020c2a0105370206010e010b04090513060c05070b010504180b040305130f05040e010e03042108040603060312110307060203181501170705030a03030203130c09140a02161103 77
    0x35462501c084480030f501d9800300703142c0101c02160050003140300214448007a91807d038103980c0b603d820141018144005400105000307030484940f00d43e26041380000400500442c81948455035807261640b00d5407500d00d22504041e040540300b20304001004007441c509401d50324019411030b8400c0c0c21601d032810180c3e058411101ca4600ca1038441c071022940c11206060b950840380152403c00220111411060880b000c83d00c28031010f42003008100b0a90024014001019595801c1014505074694900415034800d51004010039100c02041050007012400b69000b064542400d5185c10075280c603070b6883c4c4c40381e40c100600d410741c04000b04072603489220480703030000d100e18111050034114180641c82c6d410248104030794901d00d5014101015004a0000211440a8010400300d512030b0f500740d02030740004040c40209610304500c1802f0502122000b030081c01d81c04400600860401c039072252103c3c0040000c4e903142d0041100410140d0711031244051250002c13040b102070684440068142 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 305469433 1250 305468183 305468227
    0x19051c03050f04090501150c050d140c0303130606050d080403020d1a070c02030105150102030f0a0e060d0902090f04080306091008030d0e0d0e03070b0f0418020c2a0105 74
    0x200d07400301c1c01040d132200d140c0c09107050300c410701d01c141c0a2103c8100c003141c50030b406900c014026004144d05014550040129407041c400d981c00c854100102c03080d0b8280f45401c115601c8600119070074003081400540d114000150038140c2d58034052055984507040b01e40301c2c1e844024015102c55000e1400e000d0f0300f0041c026541e412100d00a824282040300400b49011240d00ba8469483c00000c120781d481015901e04c01c0d0749041c1c0185080580070710244400f03403c0402c90605009189056600690314080106400494141c00003100307845030041c0801101b0040c09405003c20340010711005c11002400e0769400041150a940c01d0b540784a078680e0703c08030795480102c10384000f0401c90003040f029000300110030f051104881c40c4106209048500260101a2903010307001460309020740030202005140c51042032000c1c03071416603074400698000307044086400c02c1503408144041c54200070b2104801c1311250f40c0c3d10004901544440143c1102808502070520000007001100007254841603900 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 305470683 1250 305469433 305469457
    0x80604090c03051b060306010e120102090a030804080114010b030114010207050301022706120c07031e0309030210061427151008070e150c0f0c19051c0305 68
    0x4076554903c0c0c0540d61301a81600300214001c41c0c8086540ca0510340203980c4269416982c2081c041041d4050003c000c103240d881003000e5408101080f0305840395800c030300055128000c2035a80310701c3c2004d050308480b08006400ca46070894001082007820b09415281503a82842d2040c2d040c080b1f010040c0e00e0300c0e005510842e010350011504032401441c1c40e48689410038a03a028110003c0007100f0807415104502223401c0d4004020003040d1000c5640014041d41d610a050803100d8000c808000a65039019110840020340c07107458100c01c256040c4014003c500036140b06000f12400c0202c82040204820341c207a024005d4480401d90310307040e1510120740c154407602c00f1060340c10440985daa400d908507214a01524520508001e010310600c006441600c840d130ba01518240807004001004038885440423540c0000d10011550072010b2041c002c034000c0300401480b10700c0040c014040b01404955409040c11050380b001c00a0351a01103c9401d83e0303000700348068045000b0300e0155164000e0501c00d0344e0b = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 305471933 1250 305470683 305470703
    0x4051e030f010f0605030c0a080a060504020613090c091517150d060b03060c04030b0103020409020117090604051905061b040f0b04030203060606190f020f15060901060306080d08060409 81
    0xc003e501648880d0a440b0150259040201c1c0d820a00c50180880d10503840154032401001c8085805940042d030858401003100307117009451501e212640e603c0d0340040f030840350350302c074000003081d002818003004003401c00b0070004011501e40060301040000b084800007800da03d00207070f00f0b940540200d0041e181e00030140c0b5202c04060070403e009109620105009104840100701d090b8443c20a9804032a03105400c910707142e0a69003400b0140040c208201c0c10703c29000d01d0b248800d2500101c032441803040000030040e5140034203126140c0101030149200c607140000d41d200100b100810348036840301014941c1000800c040e20280f0300e6100384d46c03150b00c00e41c1c02c41c240400c080b01104000c1040ba03000300d0480c2c1c4940c6880c1c00b0040103215400d5418030081d2035020201c03400f405002e0b642d6a0345114015910030b400c0e0140b2441c105801081d00460000340b000810102e45820035010307000d85080d24042021a0401a500ea9142000740300354090150300340000300f6a584903000001d0741c1d0f5002034450 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 305473183 1250 305471933 305471951
    0x40203030c0f151e07032318060705030702030a0c020a0302030d080f0a1b030905010915140a0b0102060708040804080d0e13110406050a0509030303070c031404051e030f01 75
    0x19182c40b615043c120003840d000010605103680180d00f41380c103404209022925884003003098000f040882c03024140304040c01c071303510a0035160032071030b511644080c0c011283c3d00c030020200c1d0b8101280200701d003081c04400c0c03080c003078203d42c000b040c0c2e00850300c03030b051041141801d030001039060440c5900082d0b25109a012500015074009440342c045e4510701c00c520000e440f0a09810165807649548a4400c2140741c0c5400c2072904ca41c000c444080d00420000a21008039250f001800b4449091102201e4035805060100318449141d80c1e8401120b5004200000031500001d4650802502c00d404200d6007001040c01c1c440c01000b100e00a025450450340354040404014040c01072004000b449051191521080d40b0781e40e001d00130b40001c55510191500e42080815142908864510820005c061091340c4060710100001e6010792583c4e124081e82081615000b42006044421048210f1040c0000c104940350750b80c41030b28244100f003001d20924520700c0464078007480404140e01d5982070081d80 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 305474433 1250 305473183 305473213
    0x203010305011d2118041104050a0504050c071101022a010f0e010915020109050a08090f060c0304141c060c20150703020705030708030a0b100f0305040203030c 70
    0x220110210080eaa1aa07041a00d40d110784a1100d20942685902c40d0002d07a000c680450000b010f075aa81c071449490680c1105c400300c2c0850721502a03101c610f1500040c1480b49282c11140c15008250884041c412464400507244481c041c915004003041d2040c0540702c002e030b00901454400c824580c08030b42d90b110041455048600d21441c1070342c0480c035820141e080d81e520864a949100f101a1031b01c4640600d08420040d040c0d00c6c1058040455580744407801c0010001e00c5000716841c0100c01040e255100c400401c4404030081404a05c980001c02c4148110340020058508071559450300301c08180c5090085200c8900020309104200c81956903241013040316030000301141599912107440031440c0300c4403011300b800020340c0300d540c0d0b2180b4104840c3d80c8880890980c458010b1030054101441561014650340007000c0443d0019004000c001c1c000e1100d10031a5400d81c0111112031003082010006803030046121100020103844d44001003d548080007203400e050143e0003200c10a114403040 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 305475683 1250 305474433 305474441
    0xf0409170403060f0b100c030915050c07080a050d0c030201020913150e07050702041104031410150b090d0f12020109050c0607051f060e1005130606050d0b0301090501020301030501 79
    0x81141d040d4980b81081c1500c50a80c41010311740100034160600403603081a00b5100809080d404608024015201060744104110786040807420b9803601ca8588114254450400305070340c02c0018641e00115140010520000700000101540e05101d40d841c1e24608040b0b019115890050b50045200740c049103005030f19601c5003049041c1e505815040548601e0070003081c584c1903401c1000601c05200c0c1401603c0c10f0341c0103418000242607220314250382c940c0c8009034101c0079041c0351015008601e00164141046c01a001d12402d9031410045242c10721011a40794014070f45101d000d080345560701c000304401d010114510325000204490500c0500e00001d010b841d503120112514091041440304604001d001d03115025071207409024840300d18500301c04107880d80105500c030f03980c0707a84002410101c0014550700802800d000061402d0506003807100c8142034208804040740341c1141041030301d600c44142c402c0074419800100780c4101e03510020b80901213020024055500c000000401c0010543c0 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 305476933 1250 305475683 305475689
    0x304060507201f1205090705090f09030a0f051b030c160b030a0b0310050f0f09160504020a0c02060c01060e01080304060f050f12040f2604050f04091704 67
    0xc0308901d12610030007101c4000b040d20a0307070700241c11401d80481143c40c1c0311a030140c11010300c0c104218190540f14101a1030040d1900708954018200601040c181088507590149036903031413000c01d04204040682e0b074402e4000c640300b00a440d1203034414580c810000c440c4420000c2c0d00100c0f5000d01c0312469522503020a003051098400d55038040c0000308000314400c11205020780785402c5984208260020341000051260315001d00000c0b442c0c03501076480b0380d50041c900e030010f01a080c03902035080500e00c0b00191000321f60f80d03c210003000c81003072040c00d543c003940c105880250b1100410041038819600c0a00003d601c6100400e00002c26581548801c01b1a4041022252141d0365005d0a5840384218015030b0001140d084084414500940060a207880f0703020140d468003240301c0340200800740654046038041c030700e14003210074030514120f070b29021101580130807560f14041c01e000000c0c0c070a511445005a090310030f0100144d4841e0320010b1020740140500350f0b504081102d5009940c0b180c0 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 305478183 1250 305476933 305476943
    0x106021009320f120d05090118110a050904111018080303060306060604060503040f03350f13030c02030f03030f04060c08041509020f13020d061212050c010e0304060507 74
    0x292004003d4403000412420100841030414581040000c840d400381c0340003081c02c1541d43d02d6a00c803e80003081c465505003c14000c4118010301461502040324003c55940001d10800e880301c02d00c00841c18086d00e40b46184e00440e080c03420032004c00e03401d80d645145800c08460a2290100c009501d070070120046121302d10450a5812035a15002001140c0c0141d0040d800000c8080c8001800650801d11408400d8042c4c2000881e05140c1140c520705804a5244041940407008c03d508141c110704110581102410b04103400502e07003058010490958080040c0400120000000c1991010301c0100c40d01454102030703956901d480b00030010028010385040748e0041c50840c2d541503546c452a2094042d40e4801c2c4104084101e03d80a44040c2c81c8609081c0c1c0c0c4a00210340310010303503480481100e04080c0402002d0b0b00c800044090808071079807a80400c0c2a071801d1070a81000030440d008092642065081182d100c400b00152940105018070101400d4400080c02007001c076001009405118420 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 305479433 1250 305478183 305478193
    0x9090703023d0c051f0c03060510050f0904061e060c0c06051c060905010f1e0b2a0627061519170d0503010602100932 52
    0x820220301207500c01e061428103074192a09015506a4880b4240103420003464420b0107105603031038003420108600b025604c01c10b80e00140c08100000d074080e20010340d4490034104811403612011440701c5000c1117070401081000160213101c40c90150551300301e0000a4030070001d083d1945030148054010035003003040100c4821002452901c10401c032307401164000904c2d0784a5203041401e940540147c000803003003183c40b070f886200d01a0b032489800c00400240c00c0100c2c06500d040c2c0b00017107040403a04440c0c680751291180741080100700c240071084a103003c122958483d48284407001003031882407814042100d84102c1e5090590020303140d401035456588060440e10f40a0b14241044845105403031660000c030001441c088500701404020351020f1f1284001d6a0381c0c0c200c2d4410148680c1102555040c1c80e1104664128108202c2601019905055241d941440000383d078420090240c1603181d82c503448820204022812a0000030b040000d01c03180c28a204510034960741c8003455062a14482d0b = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 305480683 1250 305479433 305479459
    0x203090604232503020301052a2d04080a12030f06060e0d020604090c08011401050703080a0504050307080d0b040b01091d04050309150a0f020102030105130c030b0909070302 76
    0x6101e842c450a1080c8001c1011120b036011200001c0d04840d162203030607100c8080080561005e0059600c58040400d49580d48600c8001c400c0d114448902800405001446001c04020b88480321000c0d00403104409158600c9401100c000381c4541d8100300164004e9280540800114140c509040c0c451a1414480030110044200031542184200c0c0e0006084e0300f00c0c0c42e03aa0502c4414945c0f004d0002e05080d15181d00d5400c03c5041e0b410803183e080000394200f004000070502c0f841014400803003440d0140c41c15405440c001c001000180c80c01554558800204080240400c11600e02960228109031600050804c80f402041101c0d0a20f0056041499211700e561044010109490940000011034440010a001c42180040c800c03509403200f0421503803d42c1c1c6400340452000c034500d0101ea62800503800c002c0c0900310031404074056a0060006110607035550350000c5400c0d4800c0c1c8009161f6940c444114040e1000c4814140c101e4a03080610115180104070760041c2d900990340c218440c24 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 305481933 1250 305480683 305480723
    0x204140115080c0304150f18030e030d27120605070815030601090c0306030f0c030210090b041a070c1815120201180e09010c080c090a090c0c060203090604 68
    0x81118484040740041000500003418551071505410b910000000c00454247c8aa01100c440707000e14141c41c000f42500408051b40020f101d00f209100780c0213018000e0700540003529101b4071548101d244200c182018080a102c100e5650041107000140011842c0c43e08100008040565100c8001041c010009031698280002d080f030010300a4010308480e0f103020003120040c840e843d401c0c0205904c81c5400408035050041145519009405800c84103145104004034105400f110f41c4c24001031034800c0000c00d090f5000e03642100c1c41200740d510b1100b40b14501c00014410250011725a000303445000c60700a4a9094490701030313201a04c01c0108044c1070b000d680320261503105640c4203010b24440e04005511070b0b1006204a041e860500c0501d0303465101c03030300305d07144202c030f0869003030f0b41d1500400646584001041c0e00a24100441440c010000001c51891056070045105032501c90003c1c001c21032082040301d03a482d4012034210340340c2c10060203103900d400d01590150b542d100c08108103422a2 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 305483183 1250 305481933 305481947
    0x150612010b18030d0c0303111b0c0f03060f0f0a0e0d0c02040c05040b04091a120a060c0801030b0601140c0d0201060305060c12011719150c090f210204140115 69
    0x140181c2c8131440c1c03105c03072940c048014141307040621401c880b0502460181182c0408090400111000549131400c4071005218943c0150030070b80f8403c0c1e0106052040c0f00480c50f00080c0c0020715241c07101401d60781c400c0620007a000725803115070b0500c260002a01c0741640115001041442240c080c0019031040c501100e0f607000d035020b00d201c007403003c1004011a0380c0326444a41c0d1181d02025440060a1000002d20f66154001040b10740c3c2d000200700700200080c510400300a5201030034618055411500e6004a40c03600138a00c505200c040030342e40d0900c0d000341f0181d407196002041103a278034103941c0b900240a0075691208848034410300002c20824442c2d881501c00204c00005200803507032803c08843c000300c0c050240c3c4443c2d0f00540707181400c10030904401b0b885050003158040e11b4040285c1e0307014116100381540c8820010700850a001207621401c40004451b1030181540b0f80c145080e0400021200000000750b00c1440c04c84c00390400100b07403800e44e048412001c004070f07003d124400151074032 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 305484433 1250 305483183 305483203
    0xb090f040516080c09130c124b0501060f061d060304030c0807020402180f010c03052a060f100801021c0903030212040506010f0b090603150612010b1803 67
    0x40c3c01881804006040c008005903206c02d003505900002800c40d01c5419404d0125003000383c0000072a0055000d121400080310068a55020032178a040844200074988054180403103200e014500700400d500c518105040d011550010001c010306551100c11910315103492080c0c20208503141c50000100340584104844400c0280401e89981c5d15503501319507140ca10001101d0b100390910055000d030326148042e00a503144200403030310380501c039410400300d00303107200806e4100694207140b200002d6201081d61460020b000101c4400782500e0400908240c0d1031006c580544114420405010000312455001d002c0e0b001c4441411500c6d004001e09030300ca0310090903214541d14404141e40d050950188010900a01c1e006040810302000041c69540a03a419a02a4425030050050170355118105009020000038585000c01d420081010750200401040121009621030480c80e150346080780e11040c58000036115540c0c4600c9000d105402203036402c440305014040d03500e49424002079090744 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 305485683 1250 305484433 305484449
    0x12020717161202010519020c0f030a03120509030f1204350f0f0a030e060109090c18110708030f0114030604120e03010603111009050a031101030b090f040516 69
    0xc0c1c9040005140d580d0b034868204030304020341000900701480c00a8401480300307013541c0c0500000c80400c0100071050341406540d5120f41c102130400e60010b60483c0f0f8038000480000d1001c200d036900c01c0c4449042d400381000a060140d00000c2e400f0600041500341d620891040e08522130840c103503040000580c840c18400200c0400840e544a08400c409003e000d00602d0345c202d003490040b0058004034182c020203118404282c44626940340c0d49000c1c00120b0241503000c1c02000702d107605858401010001e48608004442504402c0f0941c040303a40040301c44007400c0d031680e680d0b07100134071308004142d00440300b0b01c003103100080012988020207a1000f035500002002040c06441e15200da136440303840c0e00e13840c205000051800d00225142030003040000c0d80202c028003420700d800c03800c0c0100488004a0802042005141030140781d0751800c0c40c2c02503c1c0c2204200d12a0003003040182d005080c1c2e441c003030f82d00c240004108140d80c0d80386a20030344207902c00e4080c3c0762418000f5907442c03250500b03030042142c = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 305486933 1250 305485683 305485723
    0x70809091803270a030809090109020307021f0e06010e0f060607080d0b010207030c0b0a03180c060c080f0304062c07090905120c060f2d0c0712020717 66
    0x5544031019210815140c4243c40c42c10340403400e0300004020802c071354004c54142e0300200310003c1c6442c000e8407050043c2a2240194078500d00107400035150303000ca019820315003480101d480c0140100c1d501c800c0c040d8010000301c400a50311340041103a4160201c505808094140c80062880c3c18030b80e0070f0307501d900e40c000880c41c10240710040e0340c005044443c0c2200d04511038088c00101060718006101c005054000c2400e03924109440d000342134880480a50070312070305040b410000180500300c8141140c038640b4003500c020105151040a901c1541c2d4600c0d03c00d4000b0007072006120060b4000f404094291b280060000412900281c00c0305d4100d100313500d0b54210007410411200780b60000d413107a0744128182c510a03010f003820f413071071900300c002c4408042d13014204210142c180c50040b00d400803640d50076000c1003141c0c001d402c40c0d8104501c98100028040c48003080d84a810082603800480d401a004400c00e400403c001396185404d1041d120b003019903c21290523080301003100340d8003404024030700c2c0c = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 305488183 1250 305486933 305486947
    0xe0c130b0a0303050702030109150b010f020111040504230a15090c2a06050907090e0304030b041506050d0f02040f02130308070302150702070806061203031501050906070809091803 79
    0x2607141d405c4680b003a03801d0b5403114203000003d101c03040040a030300507103800001c2d403030510000100030008030220722741560314101003c01400b000e03202365406c8600c112408a0780d4240c5641100c1240c40f04105400100c1c418002e01040c1e0031a5000301865440360500d0b10542c9540d034507800c00781c81203240d104000c25101a01035407051500407805101040c0c0c0985500421078a075a1001215022640311006070080b100a002070405070007810b154507844002142850b045444041c221007002e040140415100c19082e0041252500020700914004003080f414000504044e995035202c8039040340328038a0040303648840c4140e0b10945c1c1c4480340341062a1062400c1d40c2e85c1451035403040c0d005405500c1600032005440310744000d00e6104181b0343d1b003d0311000e0301c3c103201c00e8500100a00054840c039100303444050108000400c0c0c0c3e5000c18554001402d0b00c01000068410f4072800c940780350032420016019060002400092050510955007200590b440c03501c41c0306a034039014038184c13194008115030 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 305489433 1250 305488183 305488187
    0x120c160204090c05030703060f050603010c05030a090507030f03030c080604060b0d0e0c0913051911010305191d1603030e0d0615090905060604092111010e0c130b0a0303 74
    0x1d100d803038810018015800e8944d000280780104950040360b445032158200c5240400600815810840c194002d102ca40241c0f030001d4020301004022502581d552413401c4d040c41000c0002a00454010411a09003811401c00902400702003001e0720108041034003090560800d4480c10040300d00c0102c8403070030882c17220340040103010307aa9a40c8107607105a0050300481d948e0354010601079000000f01d0450b401c040c0c0350043c285500d0290089400090b41c4103c03011440700c1e50829211a070034a400200d66968141480100780c0c1c4500c02003c03546091090100300c1f0087c200d112440000004503165074203c0a80d186000302036020050000d0895180320351141005101e0304c82051003004046941d00d200c04441284480c154014017240d9150040740051100600c4400c0c0c00c0001507400380154802500c4404208420311500c20000200201a04200d8480c003082c100c241e202500900c10b10a080002560341d90311800f20522403441020a0010611503102d00c41c0418006420b43c08601d10355201 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 305490683 1250 305489433 305489441
    0x601030c06030e0708030a1115190b1305040305130509010b040b0c03070503070f0c09050f060909010f050a05060a0509010f121a070c030e030a032c0a0b120c160204 72
    0x10f29003903200f20000400d240030140064a0050340d151355262074900901c00039481c00071110385c80c030f550030400f00034050140b0503031050500c483e1022101044003200b1704080b40c04106140c0a400396145040c091008140c0d00c40010b00c0c6444200080e9051240c6070360801c44548800e00c28184285070402c020400404402d002e8801d5528480540c1e08044144e00ca0078150303401800115064000c180c140000c006104441d24090454250100305038074000144042e451405009548180b4043e030019401d180d00b500848180c4403455001e2140f800d2640c20403001e0481079a0203441619083c0c004110307400d00c1982d0724101c03401c42582c0788ae0781d45880b004418440084406481100081da001101600c07805e504c0c40c0a0b000a0361000b88203229810300410305d0140071916071003500450100c002196200120304041c58421030640d41361009110403440118540380300c140c0104142000058640160001e04400450101d55400304d64841c0c00950040c82030120030b00e81e552031080080054240340e44 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 305491933 1250 305490683 305490701
    0xf040219050f270405010606080c0306061803121c050a050402090a2a050a0f11120f070c0b0c10050103021f0309140a060f0504030203030403180b030708090c030601030c0603 76
    0x45008107100910f00d4000e072410b00712410f8802da9181c3c0400c00010740d0207a2140d61200c01009501c0c00d5042940c0001d00502c141d43d80f05070984400c1c0c1c1500b071240e8081c04420910181c00541542e54030b03000da61500b420700c844a0414400b89000e0014107210349074043c05224aa004044040329515448200014584040c40c544000c488484182050700080140003a4071640c0c1c0f10246c8441c5102c0c00101089103c0c0d00305002c01214050140648800290100010f07040d0304c14170391560080d15a03a500c50088542c05440040840000140c940c034136070040000d04201010380726101155540c1c00c098400a10000b508080361030020b603c000c080e80d1441c007901246203404158080140c44078002c411b00600d480c4e0319600851402d60420000c0d100e00780800005080c20b20480c03a1946020f912400005c202400340000801c1501c1c0d0401101c0310301c0c0140510000040d08ca04203103900408220044411000a11411005801528001072258122584000c8030240315003000c80c00c90203414092 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 305493183 1250 305491933 305491969
    0x804120e040c030e240714090402040f081002030f0a0515030706020105070f0207030b0c03090a1407090608010209030615180f0402180f060f06070501050f040219050f 73
    0x41104815540c60041c403002ca55030356000701d9041004201e4500b00f0000c1040036003041c0050055100da4a1813403140355205640b82003520540104480b441198806c00c42c00d5684540700080205080e0403d60b1000240c032503110840304601ca007116880100e210640c2d100c02c1c9041e1600000e41c40e40801e801c0350f5807040c040003007030300d218070b00d403011a00e41400750b004440580d440d0004c020349507901c940441c168000d00c0c4000c0580c0c3d49140c982407024140a003e010101200000041208008100e1100200c0e0300111100b08881d40e50541501c44080307000e1801c0c1c1d1401c0890004020405009841c03050070001c02401d1507440f00324210344980410202650410702c09140c215800d03810090041c4a111011144a15440d00788100304ca0350400211010320300c01400180701d0b8000c00051a151310400640b030503e1a180d00b05c000841301d000b072940041882d0308080c200604a48010801800f4510a5070340c1c0c4030f184550301c019002c21070755002e12900106000440ea18620785012620310004100f = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 305494433 1250 305493183 305493197
    0x902070f06050a060305010507021212060a0312050d06060e0f210318152104030314150102012d0203060a03061b120b150309070b03130309120201080412 67
    0x2540d07484042e51000c03070300000a259920000c1003809004c1c000c144c3c4c426550700c00381885041c1d2404030030460140100102d0046180000115281c40d28800c0c000a1500194003503000ca0780210014540d070320440c0c0340001c0078140b04001603094040e445030070302640002d00d03410040d103420003030003a5255500f40c800070726640c1c81d032091001e550520040500c054105152104400745100348101010703220100c2c2b50120b000c029541020035100b500380e0b600100130541004d030b622141000c50103058000d4414038200100010300c03a100a10034a081e40003002a00280040940d000742d018800d030080d0780d03008841d02c81071007232200b01010768000c1d60b10030001092020003a80305e8a40c0c00032540c408050050091600d00344400d02d03a000070800402412601080c0002400c19012903000325074280c0901c046000800400e85403071080c01114080c0220301c40741a203901d00495289042191041c0c168041800c221000c03030240c05454500c1e4003250103031a035a45903121b03640c1e00e640109041c80031000700509 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 305495683 1250 305494433 305494463
    0xa26030114040f0e071d13021003020c060f060315011505130b040603020715271a09030a11030c030a0c140109111f020c04020a020a1b03060b0a060207090207 69
    0x118407030303900c20356003034801422080c2c100a1103103010b506041242c07480700c46d0350301080002c49095100b08071603581078070760f0407200750a82e1098000e800b4800c03080c1c005000e40d504201003070300c440050510850701103040312030690003403603a0b0182c2e84c0f082c012440b01805080085682d03900030402001100c11040c001249640c0d52040904160841e0f003002001030740026010023071005030080904c1031034011303200f04100c0724800e810013460140030f189140300e0400005003800348498400017419510604a00202e05d281125400361254880f00003a400300340c00f2044d4002407007002059400d0349905000852a0101901089d1f505c03c0c2c08000480d40c452074500580c400907001c1c0140401c50340300d4500c0500351190030041002c006044460400c1a010020901041c0c550005030340d407450000703031801aa1040c62070b03803c038140140e00d01c0142000c224500d1007220510031803840412030740501420441c4c0d42c000010018188154401c80c130050b48015010f0101c2042640100304140c802c1042e00c1803650 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 305496933 1250 305495683 305495711
    0xb16060b0a08030d02040501030b031902040902040b060c06310b060d1401020c01110a08060114130e040b0906040209180c0405010305010902192304060305030304050a2603011404 78
    0x440b4442c0d135120130743c01090030082960180988603034280e00314050158192404150b0098800500000c4c1c417494840341141c2c25500e41b54010486450050710b03059980c600e00081907990b0314117440c1041000700d21811102c1510710300d0f0011a5800044a520700a0a02515148180480981780d25441603010031700d031001455480020507615101c100150f15400c9040380a82104e290150041c0b01d2181040107091150340002210343c000800d0a1a010712800d000880350785008540c14440c2180c80464041800d111013a10144100d01c00d0211064a81c0e681e04110788501056400a400240d04000700f4200a074400c825800310443c58100c0c0c444407400c0c2d0000b002c3c4d030020390007910940d5540f81d17100e045d800c210515003504280d00032181c10461512260800641c08003484e0140641451201680741e500ca030040f0008540003401c072501e038101410f0081d2907408a880860303a14108007014001d000c81814200000028189090309588c68a0480e028201740402c0d01984107549442d02e41d1011 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 305498183 1250 305496933 305496937
    0x90d0218160f02011104051011010c090905100b1b0a050105040803010504050f06030c040c05073908060c07020301090203072c06060417030d060902130b16060b0a0803 73
    0x34100c20191081c200360503400340c07100702c40e212a601164140041203062030b0004007100c0440e5820354400c000b030039002000b201c0c82d14110382007000b69400c2060000c800d95002c82e502c1c0035200224001c01031030f2a0b80c440780740c02040c5440f801c148640e0500a54100011202508005c0d11784c03042510207403140d0755a614219403003240c0487e138500c40400140003d080922501d0790204103900002d201f4146100065941c0312225140c5214603110900765a40901c0303907042d02c001c07903401801858070108100c81e44100700810001107044c1160500c0d04041c06528500860494a0890180140f030700d0384074449032141d100c40d0050340c16640740c18070000162801c1000c800103116896803044800d03001c01042c51340d0081c3d581d441c1540f80800302800500d940c0c0100710380859524903120040c800c61241041c0c19030003000302401c0c1e15850007a0018004906030020035420004c00320182107951105014030543c0114039401d000d080380c00305904001842540b0400f4003160082200c0a99699242818515 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 305499433 1250 305498183 305498191
    0x602220303090314010537020408030c010b01091811041214010f060b0301180605060a0e03010f020a0e1003020c0d0c0212150a0213090207080316050f090d0218 70
    0x2c151080400902814010705499901c85000900241c1020b050a580540039075001c02e8071003a1540c4920504940a00c030314540241200c0203546960f92544451b0700d0b60031800e01c047c07041d4200200101250310441184c41964100221110204e64001c8014014444c030b005039084803c003048013051000c81440c559251a200320030044512441f40b21290035a03480c50403280705141424000d20520116800340d1b81500d030b2944085d11494400c101000c00f901850f40300c41d4101c0b400003035490000c0d600c100d0719030b001c9100b90300070721500c01c0b180b020104902c902500c00000505607805c403903840c5491441c10005c6a51071401609045008510a080a00d030300e412102241542c1118821420050990350800c3c5010015100e41040c1d80d03000400c0303840c001d1000c3c04845c0e0004c0c00e41511030a04c0c160b00003a011440302103444420783d00e06400c81e03900030741d000c60184616103048000b0300d114604480f803d000020384142002542d40c28040c01050011041340d1181400b050400407a0304070a0082c0b007 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 305500683 1250 305499433 305499437
    0x10302120c13150504030201081e0103050304091a100507020d02030d0509040609050403140d090f0f03180612090218090c0111060702030405120a02180a1a0a030602220303 75
    0x34070324045400c04070100e400e0b40040f4a0f00d40c88004800803580280580f001c407602828007a14668603001c1c0e6000b2903090250611344c03902110000b1003845400070142060740c45006080051138090400101800d011034a0190700244124011107028419005410003610141c40070f24082901c0c0d0009042000c3c45a6200001d6008282d0000902c0c3c0743c000d000c014906000c0821030782c242620b00030030302c0d4161181685802c000140d48603281030720351300580440d500054105040503843ca4112541d240800e01500091401e05d400280c104411456030125180c0c2d80300c0448820049a1b642c024065015050380c3c40a000e0200c0c41c0f1029803e8006031042c0f131040c000c1c008501492002412070700c500e5482d00e08070360100c0100019680c000003101d080d684100c8030017801c0a1403c0000e0303e0040a560000d40044028904842c0c02d61498800d9000f40f0b0b26000511003050307440303445080f03107450b0180294001d00b901e0003080400c201e940100070a030320b8030501c1c910200d10358451550151180d1b0080700 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 305501933 1250 305500683 305500687
    0x4141218220c021609050c09010507050709020412150506010c02130f020d062d05040506060c030726090607060b0a03020a03050a0203060105120318040e0f060103110102010c0f0e010302120c 83
    0x6021385102d201800f41503000010480ca0803c404004c02c50b0084070400d905021000401400303004013000454020984070100790755840e150650f030042045480030450304100140318540031070844d4001c252049030306a58400c009050342c0c003040000401c080710038088607034030903070321f070426895000a04180320b91a6010660601e0020310028565608509101c20801c0d1044210b44102000071a42266170480c0c0c041040d07100d110000b8002e105940c0c00310454031000480d1010000011954014032a00d448a410913558003038200c07459128030320505501600c10060079000540c0f80d80003001c03c00c000380405c2031603030b100d82c04274000c1ca0140d04141d5a81c1c0c800d2051004524003040820301509094a0f030080c40d180d800c152590b0f038016804001d107007e0214504024235140c030b40c0b1801801000c0030442d0803000c00307640c420f92100803c0c0020b441407240c00c41003c12035401400740d614014482c2e0380d80c05a550170840c088400304040d045d1141055000c01501840d00201d2240c140030b4080b601020ba = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 305503183 1250 305501933 305501953
    0x50622050421051c0e060403121407080610091508090a0c0803040806010f0501050f1608030a230f24030a06020a0305090c1c0807020904141218220c02 66
    0x320030b0000a1301242c000350500403040820030303000c141140c203d945410f106620803605140754000c1c14051144072000d608140410150980c003616080c000c49003950014404803c6c1801203030508114050709206190f074460349283c8a11035401d00e5400341d11281a00c00c5441035a0701c0c12000600d5521400031381d80007140501c00d03540c081c44481d00410032048820582460500044d00328042d0510b0480b1303004d00803c500901002d50b0b82404d00040d80b0040803503682c0303040d81640c030003400340345807401600b982441d507507855501c40003581740110595104060950340d502a041c10340d13880303941a03c0300c040071300c608140c090303e0800a04001c80d11a000260321288a414000e00b101e80050811745171303030300015813200a0707191840183c414a1940200c04108141814402d00c00d105000000790400b180204010074888010070780ca81c0d10381c40c2019a1210080c1034400e0310580101c110100e0f402500218605a92804480e210302130301c41066400c01c0103984c101c85100301c03003c04c2c1d03203940540c200c82100 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 305504433 1250 305503183 305503207
    0xd180315050709061d040c170103060c18050f040c0207080105070203030402011b024c0314040803010603180818120102042108190c020405062205042105 67
    0x14001506251a205c5110751800e001c1c0003030030300003640701d034000d5079500000401d551017050307039081150303220403001d900b5650703031822900402d4a4005040000d04002807000c407424150203403021a03a00400c0680c003110103004000040031900001c0c025441481400104080c00380241c0d44211515009140c803481d06000260101d4180c4050803c1c1940c80c414000040e03555241c80707422885100780c0301d0303810103070703114070900d600c10127046280340d084049089006140a4545810707040c1141c2d905100107441441140758010003980c00400303030502800140322082c0320f94002c502550f144030388450700ca42261200c006540c815051900c0740d510700c1c0081180e6040004a103020052150001c61030107181c865074400400140d0300c1400021076a074a030006109105080e240c000d0702c0e0011074a641101001c0c00b801014401800f240a54140310001e400c600c4c20a840030900703d01003654400d6403003451000c60007043c000700119003068140c0d108a00c0d5488104129214982e41e80300c50b566005042c201e = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 305505683 1250 305504433 305504447
    0x20f042d0506030930040f090b0102060105100c02030703020d080d0e03031306110403051c0305130f230327060705070521010c09031506080d1803150507 67
    0xc0315009070410000e0110b50200014401d11042080101e0060711140c10b52141c07117030130341c05101d81040744003140c003103079603c0415403042c03c1703640802c020010703600d0300801682c507100d0034854682d0040390380c41c0a0805501500f429100944010141c80003141c5940c0000e5640e031b8404016100c0840100e0b510708038034880e120b4448110f0b6004001d504628040e9900c00f031000320400d0041280c2e03218074080d02100c08880a07903018607445010307030341c0e000c10181c8280d044401031a03e2800203414070020503541d00389410100c0580350010a00740b842001074481c22115200806981d500c400006d010001f050014005003210b10001c041c5041c12a0300c0c040000c00340243c1c03401840c403400302081060000f510006503181100c03004c0d2140c0e0288000020408042d03a05a444d2100550074481c0c4010340c540d20280e08010f0303d2140c080c010180488880003011a501c1d40209801a0310260300315405601402803401114a41000342d024541c40b0f680c0c50014204038200c1c80c807050744800038400031540000d8 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 305506933 1250 305505683 305505689
    0x204050f1905120c0418020307141f020f07060906120b0f0405040203030705010606180b0c0c06130803040807091b0503040b07090302120c090a0b010909020f042d 71
    0x604a541842035400040700700c019204503845407401181d0030030384002c14403614541001c0100700b00864141c0048039858100c030a5000c03403090043c00001328180f043e6040c1d01e601064090079103814181e110700300ea401c4c40842d400050079845003c1415603800d001b00320a0010703001c5503039070950051030940080c00781100f0701c0351007851504042809007a51201c103a0540848800c584c0480e40b520396002103030030751040b280090300d0f950819001003482904840d903800d1598954403910911652550165170b113008410b07545034039822030404120240781c0300c03020b080441c0720b0300c0c030401c2459580c03060103107142c1c840d03070010036181c00a240400060000e0701c54400f486d100b2018001840b001c1f010018036a00c00104000c210b200580c1c007141e030b0746215618035800b940e8041c003580540443c5503d02d0340d40d0042580114403c000340c400085480c1424040d03002851410703116000018140b031049000b0350041481032161035014040020560b000c0200e0079121022b6014031842d40b081d081020015203a650 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 305508183 1250 305506933 305506939
    0xc06050105151206010c0b040b0103030f0314060904050708010f0f110c030d09110a03060b19050109030201051605030f0c0111070b0c031504060627150f170a0204050f 73
    0x9089800409540701100c60010303821001003c20364809005031200984030101070403180309030f001c0004200c00000035070305880c080e4507603001103082520300b01d00360380b25400c1400c2c0c1192a00082042e41c1480017550390491300c0741d03081d81c031003540303c2461500f1995a001c40c6140e26450f8000710f01ca4024620034204d008081040351450150400d0b4010390324420003190401e140d0340d40c13005c4c1c4240208004080e000d100c00403c140c00c80d540d2030500c0006010390805c400d00c2000e1004c0003a00441241108004582d0180c540d80181480c6400541e040e07001841550b80004125004000080c000d2005119040c2000056034440c10400c02086c01c40c4c1c05000e104400a0b030811200c1e0100d0300e004611a0300c0400340907801c0d9a5075641208000a51032078038600d400c01d05040b40850500e4211109a16488031450035107514400008641c3d84007049102c1c2e00041707994030070340081091142607400101481410400c00100c000f41d4400c003080001ca480300403041d0302040600c03d43c60301320341a01c0b00d12000c03 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 305509433 1250 305508183 305508199
    0x24090f090714030a0605130203060102010b0f09220f05150a0608120c0c03011a011b0f0204020a05040305150103120f02101505060304060203040c0614160609050d0c06050105 76
    0x7002814401d412014002100000300c00601141080d0300180090140503020f15907440d001c0074003074040d410941c0d0550140d42401c2d04100a0f0a0005203101c04d07010040061002e521410582c0f01503810500a2000e48440d80071000c001c00d03901c000126801d40304400070180030ba140303112801000009070031200c089007441d40130084001300280400b04003070a01c103070380d80d01c1c0e250518071442e080c6203030f41e05138140d420480e801103114003028072142032032400c0e215071031400305040d5000d0b03050f951048010000c0b07504900300f0000d4100341e800f805501e0a80c0c01c040e4a042d07200c0d110286044542d038180d459140c440001402008602025095800c0b01410101400d4841c0130b03000e174a40300880c2580189a9464488100d10140d08000e00020180038140c030f0356a042c41d06141019500807502680d1040b100d4200182c01440303031036295515040902c035a410700c22482c2285103245074090050310001d807690350b400003050062001c10040d624a44940d550040c00785007d40903107005900443c491594 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 305510683 1250 305509433 305509441
    0xe0c0906030316060506270916030302060f0c0f0c010203010317090d12120212041b051c0c03060c020a02030706030e07060302030405070b030106020d090905130b040224090f09 77
    0x41d00c03450f0f60ba480e074400804142ca66072140480c0745d1242c854081e03104000d14010007110000c4050724280110181d8040e15401405000d60410141c3c00d40700040051340030b000000e5040540700e010642003450b5009484c030b4116803802c2d03e40c0a400003607650000340d500000400400c0392800803c15540d0290705240c1c1001e01e0100002e04510400c50003a060b00e081c030500303d0b62503100700603031305c0d01e0011448115142e002c80c0c013000d0003a50044604440e0b8030b80c42000c440c0d60204500e91001291001020f0100140826121000040e1251011607103514941c0001c80096054041e44010b005a039000304182c211500415142c2036150780540b041c5480c0403004019048081a544151901828007580e030b03488610f0807614040b2550b0010b41018004000420082ea02042c1000300204550302c20320010344031032070312007140c3c403d4882c1000ca500b02040140011259503040c0c0d80a80020460b0181031400210359410341483c408048004900080d9443c4074039040480002556050b9948022490 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 305511933 1250 305510683 305510707
    0x1d011406063f090d1d120a080a0e12010228030b180403120905061f0302150306030714030304091e050a0203010f060c1208090a1a070905100903030e010509040e0c09060303 75
    0x100049500480030355005602c003003000c1020007242035101c190032741d0703e8244500c000c2104441a1846119000301d1081c00b42000050090f1400175500d1103521500c080f1380210103c0045440500ca000e0603111144e6100c5a0fa80340210150170011004001c001c0c07606150041c000c0c3e03015110303184618680403032900881c0e40068115403150744603002d80c410110200210181503880c5d40020751100708102c2c043c09681079000554025801030301120300b0365884100f9020041e881602086c2c0544c0305200801000c0300540110b1103420b003881f41440d44000100c15041901d2003183c00d0b002c3c41340c0000041001d420b0b80108100103224601e05041003040d41e907203084440a0041c45c440030440400040b410401c0c0c280818a041648004692140b4510321411035005208441c0440480c0101c00c0c000365138101095816064507403955034050260559030103a404500f80c2d0001810040103010001054450384182220205a03a005010000c009820042211001041d03540079420034012503507885 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 305513183 1250 305511933 305511977
    0x703110c0601060e0a09050408210103031e11060f01060e011404050405041110180e06030d0807050c10061802090603010b09010507061d011406063f090d 67
    0x7860b510f40006003800348000514041700750f400440000c0d00d054180010080c07040300402a6680480500c01001a00150303040200340922001c0c0200e4804200200000c41200c21031f60b6148140c01c218082620a060311446c0060489900c00a18100c2005000a03904000920400d00007460000c04480070a100440d850141d407044900070380d194804a410809407091822030124080c210308142d882d11900109403409012584510020780d100100d10041c0c2032075600d1003210068007c003401c4655100403a60350500400f1f90040010520060208803000e00c04903010136003030400030031640d0600c0260358540381d0a242007515a441005008a2502c5010540c0c0c1100d44400c000d41e118819000180c0b00e6200d0410300510551421001070040c101204804001500703000081000007001410045024401e0720f00e640e10241c14014085814a0000380e050060040b4250000404211030b045000500d03040d442c51520541d482044130390b41040226400d01b60091403d0400a420089990142d03 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 305514433 1250 305513183 305513189
    0x501061d10050d05090c030d0f031b0c0f02010903050607020a0201110304050d03050d060306090b010801051b0906091801081c02010c0c120507141c18120f06060902030703110c0601 79
    0x75034448000900320b4030140304108025070040e003600c08d1607501040c01098011201c010b40c01003131074040800704003184203111043d40c070348a488801ca5001c0d03a0721005100255613004034100155123201000095007804664041c4034590000c102180e802c1c80098000c0315800230b10340c2a0f500c18401000143d880d89200c0035160340509010f507030341c0b9034a00c111003d49419040541810309260b4410304021909170741c2e82c1280e454100030005500c42d98160107076005e40c981401d41d0f4100c18010f800351444d05000801c1b654078020a80c851041242c480c0102c0c56100764090451a0010081c446401c201030b0038180d000c950714802080030300d00c083e40103800714182a002030320014103110040714090280b02205c81c080e0301b00031440c40b29107030491080d6890201001018140f401110b40038081406003030300c09001c2d24404941c0d1034040c20710042d1030700c09032001d5040d10200030005401c400300310580701d0240a042c0c0d00b4005680d0740f80020014064540303556011800440401c4103400208000c9052415 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 305515683 1250 305514433 305514457
    0x4091413020906130513120503091509010b1f030b091006031a030f070906060201180b07020c090c0705121611060d0c05030a1103010807031104020d0501061d1005 71
    0x310740711107002c2240c0340004c040514120303242c0018811341070500f83c81900c80340d12071019000034105208045810380015109076089510007120000c5007620882c0d01070340901224000295696464001106842c96406101501600ca00d0803101598180162001c0c200c013078804280c5401c00d801400400c0c0003900c501c4d03040507942c1603c03d40c2d201b003449000300f0210006044803072044c10b5210003a100c4c00c41e8131070080003a20300b8074001001030040c00341d03558601e90311000800032581d40d1608180c0d07950041040003140076844007900150340d0000d9042c00b078054158645d840c0d18141c54120319024034510486249a0140000e00b902c01c241003040242c80d07440300c00b4034405000b04002c90602c1c0640c11510070840e0070035414045072a4418081e5100b80188801844446150701004080d44000c0c01a07c1c140d410001382440130a049007402030150310003030001450708400042c11011a8003c1c2c00450009003c0c204144c501e40c00c07003c0b08030f600b50046908104051101d40c0c043c203584030385040d2000d = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 305516933 1250 305515683 305515699
    0x30207020406090c0f0201050a050702030a0507020a05030106170f150a02071b15020c0a08070e040f0605160f020c1c050a170a12060501080604020d0209030708030409141302 76
    0x411901d441c0c121000038000d040d401c0c0030040e0b0341030014241040380200000190318040c0050114206130140500546481e0080c43c0750402d10f180840710750340312070310980e0070a14191001650382c03000d10130040140901900018030402c11584903043c003094490a05031941b2050300e40c036140609803039158110000140059072441c080c90b0161281c500000c0354030f20403c92003000550103082ea0f640c3d0385201e030180e09607120103040c5020002da1741c3c45401000c800364064a0240310b080e009042d25500b040c0950720f024100071803540e400c2c2c10f8560807103e100c880e02c1206104001c0c1c940004180c01b003044c843c0064001740b80484045160815203000c807991000002004509204081c0008801c10360425400200e1408140c25a030035039110100031800900200f03c103402d0718101e4400c038015241d05a40d620704039200c000410000c0c0d02b00325070350302d1074a608000c1402c2566017003082c94010301021000d103403642e1038880510304451000840c0303400d4502650410611036000c4003400e0703106a049545007 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 305518183 1250 305516933 305516947
    0xb0a2607120902040c0201020a03062103050a120e010b10031a0603070c060509210c0a0803060f0d1b0f050901090c1e0e100c0b070309240209040f0b060a0302 69
    0x1074050985907602035003151601c131000b0f0140f41c1c103400411550000b500c081c40015a500e82c1007505000312a5000c1d84841007035424000a4421801084190703014175102c21009604050b030b0046410100c0104460ba541d481800e20a0810003101071400c1085d040820040c0d100d98182c444000710256094840c100c00000208414005c00c44040d0301130b00b041e400c20140c646a4003960351050310a1420000701041d205880c1a000c0840c110f0344140c00c01d00144c014800150b80f41c0724a40c1000d00b0090703100400000817282629404064134115008076000c01c2c0001c54400049030321841c44d000350394490740d000b5040c07290391a143c582e00c1c1100c0b00b00301d000804103082c1c00210b031030044a109501405541d020b402e0041540b104080500c0c036012160400c10002016080d01c0c80b90140500030007484094002403040d0307010b0391100c149580510341003401046001c2d44641e4100442004070105a808148980942803e11032603a103240c00402c20041074507040001017460041484d6141010f400103802 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 305519433 1250 305518183 305518217
    0x70c1a190212161109010510110c12060a0b031207152d0e010213120201020f03130807050d0f0b100918051917070c0f0b0a2607 56
    0x8070902d44030003042c540d01e038007800050303d07624100f040080c0c0b000030f0b000101c6036aa241c480f450390704a4000078040c030500361416034187c41d0811101d51244c0580150800790032942c4841e03200500c0041c0860103410145446810501120071203000180030342d0050840210b1000410101e0360010741061a00c140480c0e071301e00311000761a0007000e06c100d0040034254110321000151186810406050b811f02584124490071400c0307010781a0346200c22030110004200803c10703810b400c4811401031044c0e81080d9181c034651031440e40401082d0002d511400d0080000d03003000e00591001d000300304c6401180b4202e0b910b48404c10b21016101505920260021908079400384200034002c2c80c0c000300502410740c8a0000800c42c23a0010410381e0700e8055500b00302c14003004100d1040400e6030008840088001d0b202d180f404c1c0b038210135400c88400c00f414501050000c000f40e40c4600519540c040766540d0074810000501003200d21221081c0500a4828000a8015014156404041860140c103038160625034 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 305520683 1250 305519433 305519443
    0x3060c1205072c06070606030215070209060904030512040c0f06020f030a0f1e021506040213090b01030b03010e0f07060f0504090906021909030b0603070303020309100c0215070c1a1902 81
    0x425135020700000703400d81c10071880341c0111f011070380211912458038200f1070070342c0c1e5244946403009500050380ca001525501c0c10140103500a4003034541303942005180107807842d0082d0243d03000d981b841c0b541d083c100007002130084204013800d0b10744043e2200300c120002d000d540b40110f0703440d4000d210402c0168981746103d00c0900203400e2140680d25908034008030080e40b502d104a4100300043c901500050322800c00c0e008032507510204003a4942d41c1c030310301351602005002c40400d20b410540c446074a0400d0344d82c240110028001d6800103030220300705000d003940c50100c0d00d40c8100c0038080c0c0c40b007801507031a07080380540781101d1100c007011030818143d140000080c490498441c4900460241c051411980840d2140c02d40b8410469032105032900401c241e5108814800100164800c200d034840070705003412681a48041810108608000c990000303480092104800c40b0b42040401d0460510848080090083c10040ca21700c2c10204101e0654656100c3c20b444c000c3c82c40d442c40680d1315a5882044 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 305521933 1250 305520683 305520767
    0x30902090a05060f121e010b0310020301091404030e012a0b01080106050907170402060d021b0106050105181504120f060b040507080f061504120c1d07110304080703060c120507 77
    0x9650400040342c22b0b05000b0b4000b0300911040030700d0301c002030600d02c507403030600c038012600342c1c596150302004c1c074004440386500180180740401141076120551702906c80e03884040361003810480b03010f40c1020601030841d115070f800786100e154540148014030360050a01a0b142d0104010400303556554000f084040c458130100224071440055100303a04e83c9019040840c1508080c02484225170f00c5c001103c1c180501d2200f00c03003140380600c0e042d002d4a0700c40e64186d0350f8510b100020342859510016506103201800e000d5591804240f410410400c0030711030901c2c2d01c41c0c201c50400c01400d241c60001c1c4403040c0100080590780114003c01d4250360340130040312a860b2240c0e90203a9468031980300b540d41114420044074400a086404501c00340f48078044107001a181e040088695070ba20403c49080f00703002c1d01980709000c10080030442840a000c400040c50203904040b40100008000400110a04424041581c50401070086860744410b001c4107002c003040300d00c1c1d212168600080d141c0805e1038 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 305523183 1250 305521933 305521939
    0xa03060305100903180506030c130b0d090302240708040206090d110a121523070e18060a030b091501030b07022119030902090a05060f121e010b 63
    0x40160700311007500703422200f070300ca22a5442c134502103001c00c10894105020301805600907000d01c0060819601c00015000c2d2560259030910a140e4070b100d2031601d907020148080b40f1685500d8280203068040154042e100340e8403246081024182042d00c500103400381842040111900100742555a80c60070303589205c40040c03c001c000041c618025a240c0c0c4805034490003642c00c000c0005900d20350940000b01682c01c40005001450341007444c50041c8400c01c40c00c01c0c0e07850002c4560350000c3c40c1c2c9428602c681e1450321120359021210f4100182480c003149100303801d00004003008519120204990201c030b40c0030188101a07101c00ca00c040c01c1160440d00c542d411580d0714000411b00c031a07084840e0003107900390203032100d80504124282c2e0700b400b10740340f48041a0b410803202d01500d08109203102c900c01c50b0300c1d0000b48820300741c0c002200708000b40e60b00d54406840b40306000d01780c54203c000350500401107410310744060801e0f0a164482c00c544c0c0100680341c0300c401100d401c0400039003204107014402 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 305524433 1250 305523183 305523193
    0x20d140a060e01050d020105030109050c13172109090a0b130b100203090a030803190507020d0f0f020c1e04020c1608061009150e0112051005040b04080a03060305 71
    0x5034404000c001c640705405042d051140002004d003811880021080d03010781d80d40c1d1441c0c2c00e1040c5540540009422075030040010004080d6919540250001800c0540d40901031451084155494a901c40400c05010001d681c142c19041d0b0140b0112501d030f20054940c994165920441e4800400c00c070400d464110012001201d1040c50035407100d0b804882c211221031446000f094101da4034090000c0d40c503080100401c0c1440840c0c8081c000c1d551190603c1c94100c20a8030a1328054141c40041d0f03400405640911100d0840581043e201c80c581000c40c030b40000104062074009548004c900d101d0380c000d100c81c68a900c84254559031b40014110050b00c155a40c40c610303200341e0b41d43c183d00f00d0007505410002c0030114510300c010909900a0100c8447c06010320700f8810368000402800d440b900c0c44581c0000002044020b04200780d008154007086e940c503d402c0740c100b580c188010b040013510510b19000801000a401801e10f507001508000c2954170303000c1c1c2450540003801141c101030021312032 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 305525683 1250 305524433 305524441
    0x705030115032409050112050705060d0e03040e0f07170601030b0102010b06030403091e0b120702031b070513060812210103061b05030411132706051003030207050103020d14 76
    0x99100120202e410f00401042542e0fa2529451f0300600005001451508190410070852502d04060422100007c00000e060324000308014a10ba000f80e1001103081d1481c001c10043c1c9400d04c21560b400800c500b0200f89041480701000300f0791000604a40c10300d951054a81e8999100b503110044808010344225641d007000d0602414621051051282c070b501070003c00d41e2001c5079004602c003121403c641d401c0c00c10004042c00b400540c0020580400c510041c491046002da80808400300180d60502500aa60a140600840910035110071981c00e007010010054404006268490505100300c0186c07514844100c2400400004000f14041400380c1e002005001880d400030000c00802c103040440494498000d6629000880d00580540d00141c080d00080c11b200030a20f0054408480000308a41c0d007241002e8a141d44907802c4c3d03e1a0a000307945010001035220782a000041c4500c08050b0134590b40d030007903075000035006c2c081c101500400d00c0111074130755400103803031581c401e01c4036202454 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 305526933 1250 305525683 305525741
    0x30103080415020307050c21010213030b06040c021f090b160e010801030f03030506030f0a140601080a080f0d020412050d140a14130b07051006060503070503011503 72
    0x11900664864070641c480000e01c0070f00010440b802660300c140034000354007404081244454429410340b07600414100e04d162002820310080c440a4180000d100245095042502d01990002c0115000d0b03440d0454a003052070700051129980940f500000103580034118402d000350100780300040c50f007110001481170a00d00028410a01c5000d640c40c01100ca004000446442a0a100203048008552242c1002c01d00c20381015500003030203403c0781c40f000b49418034249004507035881926000301122506a11070410b20003180100000c400401003030003d5114a54507101c1c0c6605c0c1e4004240008800780030f480c6c00d030103880040850b0302d02450856081c0c1042e07612000384c1246680050700160b07100420010381d006031034810401d07680e400c0030815890445500799010b401c420310161741901d4005564070045005242140c858006040004103104100c026a0340c0c54000344213001c0280100f080040d84102541d04540080240108032100880141c00804001c60107101e40e44081d0000c4585907 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 305528183 1250 305526933 305526937
    0x120309041b0806012d090b0414010809060103050c0d05010f091a0a1b0e01020c03030a0509100c0201020c06071a0103080a090e04050c090714190e010e031018060203010308 75
    0x40a1912051055501d50f03004403551244140e42c94004100401d10003010b03c0702c1c900350700441c0030340c3c18011a155242c00342130310250490b6025400d21044c15804084559000c880c5540261352400140341725411591000c0c1c4403074907810003030700600b04c03911342d90f0500c6800d421545071004100342c00c1241c0c0c640b034241000041c0900040080702000403002c50311481c4180329400d01040d404401c1c00340000c10400031034030380c10325203c881d0452007804010f83e6507a500340014019140203445075907540c0ca801c3c0078450316080000d0b800703051101c00141000541d0300070038060510b1204a940c10350344c010510341260a00300c08650b032502c02c01600d0022040141304401032013440c0c6151510558140d85d01c22142100c0f008880040090304043d40f002c0c8141440094990403080c20f0420701c00c1400c001d10000c1b2250000c0100346100101107a001d072a9541088526400c0f078805c3c85c0010b00c4441d0700c00481d0340e1b128900e4409003242d9548407011504c03210b0030941c20403203900c40b0045d5582d5959007084007485d = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 305529433 1250 305528183 305528231
    0x51f05071a0609061918020c060109020309010c0c03050a082d06040e0f0a06020a050c030a0302070303060b2104020a090c030525080103060b0d06090b150109050a0512030904 76
    0x15035040002c51075528004c07070002585c1d01d1074900d0489040c01c0000c03100c41c500c0c1801c0d005411a8080c0320200c076810007400002e000c0c01a0101c0180c0b0380c6883e229890945900420040070b02c120074440502080d071000440d80700047c2400d000310380391941a040041c01c04511605e4002d00072108404e03a00c0d01100407114090201210207001c101c0041c082d013a201e43c4d400c1110009c96200e4451080001c070180c01401021a0500f41141403080203481142141d0104905c0d600196002901d03004050b01481843d000d01105100d00c0c3c200810761000e4402c84080d900d4104201000c480010304550b00e01d8a050003801880d1002d20081c0355001c009406050207548002c5014080003604a2aa0036000070076030f00801665482c07903a929503203c0100034025a142250080e0210b59102e01184483c0251007146200f003031070540914020f40414803050702c080140b41081403810003000070b80d130362007a520f0985004503950415000140d070715502d14417440c07007500d411070b0420300903e90f00004a1300415007 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 305530683 1250 305529433 305529439
    0x3040e060d150207141204060305191404140303070c0f02030f1006090605030a030e01050a020c10050a030f050108030a120f0e0a0302070b090603010621060b0901030c09051f05071a06 80
    0x1c88103611710341340c0310051a96002c1103800c0c0810480a44a50080341e0003105c0b0210f02000b170311804140b1010744100301a2003c147d40703c68140420825402c424a80a440040145042d810034040080c81d2b003461010243c040c10300c200b00d020a40d0b6060000d1141000f0340000c8a121080c040c0b040e00140419114240c00c80c0c0c58140300160a00340460320700400c1d0b515944000c080e82200300103540c0c3d90403101c10131085100382034107448151140d00e01d80ca48000745481c4d080d1074804401c8004d003601c0740190580156810b0000400c00081d001058070721071082400c11003106100c2550000c01042207402140b8a1410406590b040441c0840c03400d140d00e01903426142c0e8035450303400c2440603100e0310b001c41d900440208010825240324101114082c0c01c810030080540e661940f840302074541d25004120700b0400010407143c250303014410052032004608260b44600d15000020f018003103003840c1558000210a6030707442c1280300c3c10480e2040c41d401030011089500c80c0020381319404040b40c6140c0 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 305531933 1250 305530683 305530703
    0x321090c030303100e0405030f0a030f0605040b0306010315180f021903030804020d03051c06052b080c030903120405040501090e0d0f021f090213090503040e060d150207 74
    0x54141000b10407a44500d0303841205490305440e0240850302400c0050040d80c4c58003003442526030354844000141080c5040c1d540c0402c0d060b42a9000d1000c035030039075100901c21440d0049024031a14041403190440f40c00c500072841140030700072207001500b54203c03080340c40c41c2580070741c0c030400142c0c080c510380c0a0700030f0b9017940e98100c0c000f5240d0750814941c003014000c2000740001600528100384200e451610900c2d000741000240040890031808160343e403882c42d03403104400e200504050184181003140d9140300d451100303d000b40e000d01840d800001400c4800001100150340c6c0081048461a40c805800c480b441d60000600d0041078100d4000ca5106034180000050500c1e141e00480c407000c005100a055145540203080c1d83c2104200303030369801c2d800b45080b461040c00c00820740300800c1c4282100403130f001280388100072946040c0501003002e5840e103541c0b02d01180000041d207007901c0a40c04804481d440d140c0025911008007680100581844840703200c82100c3e540241440600c0340034003413 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 305533183 1250 305531933 305531953
    0x1005030a0f120512010918020a06080a05090c060702040b1813121d04050a0b090109020702030f030310050d03050c0304030c0e1315020a110106030501050601081311090405032109 78
    0x3c910340320b00340d0b0302072001e102c400040c00b407500c1c0f681c090710705020200304500000c55160701103058403401e0750114000c0340541d000c00082c042a40940340e808401b940241c0503466a4000144050160305000f90195a880b007512406895880e104000d00c04c0741801c00c941c5240004c0c4070f01c181d0443c640101d9404050800020390036004600c3c081460041d001c001c0b23440d455500506c80103000c0100114100f58903080510303030340d895141c4803034064040040056035440d00c43c0103140c5840028029030350742c2e40c420000c1141d0305151401c42d2098401c110f07541d0304101900e04044a05010345103074a5880d000001d030020800c5800201441283c015000019942d03a403860580310040c1c5070a40501501a998210320f8003860981c02818901c41d141044000309030b01064a030308654058001b00d940780c2d500e0051000355a00907039219071003180c909104000e0782055403650142805840401c1c003a4662030301040400c00c051042d2008002210940140503c0c0c40760303a0340e03010382e00351040e0540703005242c000 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 305534433 1250 305533183 305533187
    0xc020c301c0f08010602030418140a0c0e011d060309120c030316020d020d05032e0504200d020702040207080c0a1403070309050d0503210a0b040204080c01081005030a0f12 75
    0xb4101d60403074000c0e50502d86058130207024075408089c0b800c02160340b590000420380001c500da500840c03200d40001821a074551025100c0c4981c1086203051125410681295520400700664202002e4403000d407661603200d1541d16048041102c0d031644000856000d1414000001440c4104412041c075200da04c00d61100b0781e29815007140c0000180c104035800c004140c012402583c00680800c1e2030545c0250340000301400b01c02045014001e444410030402040c0f80078056100301002c080f05000302080007054142e944e110740602034408a070003052040c155516607040c2d41c00070307402c540361035950360401c403860344c031480c20070822143d141d0201d000300340111002003540c1203e5410b0311640005810582008605211600c0459243c4403c10100501402c000c4a0a075001c1680c000141d40c0e08094600806450125070341c540541c0c0705000400140400290243c440a0207007024240e940f200c00304029841b100d40c00007601480b4006007c410401c403004507894180c000c0304040e00b911039070141 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 305535683 1250 305534433 305534447
    0x206160c060503160815030d0306140406120f06090c0b070201020708010b0f0909102313020d0b061311090301180b0439090c020c301c0f 60
    0x101d10131a203411000120554017407102940c00c04002000748040d000b01e000020326000d21840103000187c0c0b00d800800811016905614004108950074085141041040380c62081d10580181100710700c411035000b40700c615405001d915030040220300085450360310030324450b0310400c0128014400c80c1d00000c0e44900c1803007101c0443c0c10045c015841d032410041006401180680b240600e4012452075003010101c41c400c1c4010301c5410a032001c9801c090036080d036441f40009161404214003450312a00580d00c0b1000c00d42402e034000c50584a030340b00d440214000502440c0c0031400d480c549603440d100030b240540500b1080f20103c00a0040c2ca9a0910b403199220207110014010402180400d001502020340025440708070340c1310f90a600c51061740c0c4001078101c680e0600c40b82d020204140f000d400f86024820140485000500c08401c850740803c80844255142c10f41600301c00c02120064000700b0210f10050314801c0c01c54907903040313002048246d0f40714240e4030b03c00320314802d01241c08a401506 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 305536933 1250 305535683 305535691
    0x1091416120504110f0d020f061305030f01060302090c0c030703030f1d0c210a030305090a0501050a05010609080f0d080702011e0c18030308060907110105040c05090a1104051504030206160c060503 86
    0x12101008d00720043c2440340c25000300c6010341c0c1c608c410f408041004e031402c00140146440c0000003017103882c0703140103001c46060b001e409510b01c8501080050340000d4008202c801c180c0e454a400107908031011a460010034600c0c91b0705504e0304140002c0e10a104d00015140301c0981d0031241070080000b1342d04410300c01c45030030010490a400030982c04012900a42c061a442015101614120211903890a003116000c541940f40c0c207070b441005121071680205607001901042005204002e112000310b9510f801c8600300104005614001640070340c0300303400005002c441011070560f0324560400c1040540010f0240d4400141008400942841d20b0100c4400b200d8250700c40400c80e84541c02800307019880101004c05100c484100032603488000d03c55644075500034007038120320a08050070000300758006802c000a445c185238409104010354000c440c201c450480d0380580641c90702541d40c140380100c1e0300c0a0b51000000c41d80200b604480c141c0c0c04403031032240e012042c009890ba80c045d83c650005803 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 305538183 1250 305536933 305536939
    0x10507021204060c0b0a11070506091b010c1b0b070b0a0c091a03070c080304050d08060604050102150405010e030c030d060b0403110f0a03020604120b01091416120504110f0d02 77
    0x4900d00100711104401e0750402d618080110301484011000b40b048d91013040d04032070a901480402a03d2003040c085440c669030141000d8604110360000241080b139071050151803602550f41500c41c0e5203500b0900d81c002c01ca02c61110741c4861072401c081030300400403544c41991505041c20181c841c0d1203a0000d4050b1384c107965840910032403859030340050303030001840030041c00300010740d18010a12400185108500c100014000c51007110f400605851019040034040c4c4020f00081c0039585e00810307080b1804418110082c0b01d50b44074100301740074020747c443e0380300796000000300401c0d900804001800008410714043c0149503440c2c0d650003551003148006001c005012458009510700144000e00c0071100400a5010540741d40000b6003507805940000308020264084604000312002c0c107038018009400304100d503803c0001d886490f0356005101104e4200000c1d001e00f0045d004020003d00045d440c54100300324a407a01c0c004034035081c10008a4031075103c03400041c440d4900441c103444010b40c05 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 305539433 1250 305538183 305538197
    0x40b09100e0702010b0a0308030402010f080103110609010c0209012402060408030f0901020d1a1903080f03090709061d0108010b0a03060c110a0f1115090105130302090901050702120406 81
    0x781c9800705040060107080444d520385040c00c4a940c0c482d07010b000618064500950707a41004d20000d80317425400500041400380200c010008140f2200911407a9802130710b0b0140d8801c1c4000c01264000c641ca0002948400185c0000c641c007000800109040500882185800030508405981d601ca0444000b01a64410800100381c240d14100302d42c0c102410a00150420030f510104a00f41c2da2803c1c84640c044507000d8510400745401d21490f100c000d21800e6502c4030606589440c070062080c01201803e03400d000000c514020010445c6c0030081c004407904000c0962076201c0108500c0010b14092601c00114001140b014018071a4190081000f080c40815600d50f5a601001d44001e00c0d810060210040d00b580100c0004e100c980c1145104141d4508244030600d4101d880c07101c8200c1c1980144004d5104401c441038441c22a00401c07800d00b40349850b0305075a0440c40c0f104a035500000d41086a40c4240450074905402841c00b540c0da54081d980000010320340041d03d0b0007144100c00009000e = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 305540683 1250 305539433 305539439
    0x61d01061404080d020d1824050405090405010f0531020a230a090c0c0312180b100603110d090c0801020a0c0302010605010503061e011e0c02040b0910 66
    0x40c0c0c000c1e1041c0e8034141c1603904142d0b071500303410b0500c01c500d0084400b603009000320b20303200c950040c400c0314240d01c0401c50150b4141044020f1048500b81002841c100e1f0907004c200e50241c1c041c80a0714020203008010204a14051400728043c2600c86004030301e01e03092001080030714521014000c042075218441900550281c2032030103900704c0032101642c1200301c440c3c010800c280002e4075a50080da9446100000801350424011542440e03480a11040e00c1d042c0c003103481315800700e041c0c2c3e07002e5090324140040384840d01104000f40032002c0058101c107141c215403003c2140100710207108103001041c50388410307501e2000f83c05850310500c04441701d040c2041844102007140c3e200401c102c0c080d0024034241500c1b0100c0d1801c80c5e004030501d0300469803548191082503824012000602020301c1d0140c00d43c01d01c1c2c070208521910b03070201c510300c0740108100d595050b44100b0380307141181d01852100e081c003200071a01804121281d0001d81c06a42040401d0f03040d400c05400300780c0600d1150081c0c500e1649 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 305541933 1250 305540683 305540687
    0x20f04061d040612030f2106050102070e010803090105030417070b0f090a03270510020c10030b0108071103070b1009060503010608030307080702122709040c05040b040f0e030d061d0106 81
    0x22440c515409100801c8040c9100401082c3d519000c00500100007818600389000a881c040a41d07005800003291840140b000cfc50b00030003550513100b42030916507240c1e00c0d145007944490300400c004070344080010400310144107200c1c800c14052400c000280100791106841c0e0b9031142a5032130041c01003074801c0080c1c4135980c24429903a54051041060414a90720381c40020798510305612458010303809509041d032145050191442c0c3e0000030b0a00700324169030400040c4c09060010241024030048105590224a00340121a081039124401c12902d18101c6000008034a06016000e02c4030300d402800b10f25802e052203200c041d105014019401c5a40d1003900301c0b0a00001840481180105203900d082c0c1c04401002c0c042800141c20748407807185015180356640b0660f5454103218a2140f8140300200e0301d900d8160040d10710580300410b510062102003400343c450219080c02c000c0c0340108060880c01d011001d00512012400b01380541960f84010740041003048038141c0c0034120040c010010a4 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 305543183 1250 305541933 305541947
    0x70506030a0b0603011508310305040315060801150f0e0c090a03050f0c0409020607060e1c031d01060609090e010603060c020d020f0601121401020f04061d04061203 72
    0x4491070001046141480c00403420f5504283d01c9010079911640d0262a5160020143e5501c0f0000c180c103040e001c200944d80c0d44889110405010000609440c1c001c01d140c8210101c901454100001141c40351058918800509043c840d01e44e203940b804a11b400d2004610095100300c03614100400040c0341410483d0082d12006040c0000840040004c04129252441d0040080d40507101400d031501c002c0d5100380c140460845d0843c40303140b500d9110001a5103139800e51713444da40c02400c0041c03400360420740365152225807100c2500fa501e46210684005916401c4001c0002c4002030700c42d441020f111019003619003500584011407810032050140751507680c44280700002c03d0002040d1181e42c0c0c0c030b5900c1151820200381d401604003004000c89907404200b03081c2c980c00981f0044c41198505540802140408800100b2004540081d0000c103402501501c641021301c90985984907070751800a040502d800c80120703102d8801781c505030f5880ca0300d40710b8401261004c018030416808a540c0444d588 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 305544433 1250 305543183 305543191
    0x40611010212010806041e1e05010f110702040e0c1c03030f0603060e0f06060102030f0c01060816060f020c06071403070f06150803070503040603110c060a0c0e030c0307050603 77
    0x50341d401d0104003034032500344101c035000308401409003610b410a8201404c1080e025011000303030080200740d81c0300044e0203101951311400f500120012004003840c01e42e003d003003030320f00e0b0390020380c20050310310340100d02c200040126034401c440400001e860300b20701ca40c41c0c00201c00900d61106151241c02460341d40c0c0d01fa80c02082c0e00c245000076191400c80c4144040fa0380c01d41003505d0f455600d9a0303480302c801741000301c80c24410100008050f50f1604000003560f82c0325203000302e15190008280c00b54114000d4201e48040c00382001035484c0202910300031212030031a80704600014001e507840301030490000c24680400301024041525103c200e442e00300f0a00c60701c51640c500c501c820064540818140c22016441510a01010600d01182d000ca80c404280f29042007845420420812001801c00002c94040343c03512700b800f280c050010020013071b0500644a81c150140160700420148215982c40032944a036140c0700c0e50141c8014105165503400380e001202d415034081c1005100b20714004000c5d61340 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 305545683 1250 305544433 305544467
    0x9050a030f05040305030f0702150702131505120d0f090608010509041a070c0b090312160c050d0207061b030f140409020403030806030c0402090d12050706020c1c140406 74
    0x540f941c1e90380e079185103600c03080e01220008800704005c01180303041e000282c03034003144050b25800c140700e0f5000034080c0040050030480c125950742180c0031500c8200c5a40004100084c41c0c00390820100010f50303101ca01c04005800040c101d02c14071907a03103024503c2001035031741c0c030380c0c5201e0141e08080a12070004030182090358940c0021b0500c01003070b6044250346215101a0b0b40b240c03801303003841c50480e060322400f0744040301c10f030014010a0b500015000c616907012643c18550f0380b1502c4040390944010002c40c1d0080d00d40c0c0a040c420700d4031a5000100c036421a0741c03d40e00c28a08c000030442000144201150042c005110352040c0100c8a200b8580036202040740700c003035807506603164110400c90740140e1040b800f10304080100000f5150070b0101c0c208482059805505c0c0016180004981505650009180710066000c00107007a200b002510b11036613101c1411907840002c9202950703a8400000650b01005000302d2400c109846201604440d0180342d142c0360416050110a90b80e41000c0414019 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 305546933 1250 305545683 305545687
    0x40209060904080f031e0103030e040c1b170c07030c080f061306021b030a0306031a010305070e0c130e040b07020c010206060420190f0e0f040203270c0f010309050a030f05 75
    0x10300c0c4104692000d000310320075240c800ad00e00f940001d0009854000400806110149802040100d04480300d40990b40d8402014268510350003030f04591409058142c100c18420120044200007200b68601d094400c284c040300e05814012002e1680c076103007203034406030070070354021880c0000b51a6000341082d98140300d01032130042c500c00c110925540000030460000b0351519010401e00c13203c58041c1030b511304080d201d07142c0c03503065440daaa914a07892090316422440310300002c0d4480c4109003591040440c0c60801454240c1e261552403038200141d50507a4a1090071001c901080d0000407090402d65042c1c010305681d50b90602008000d0040c582031401720100e24080a005082d500014840350404080e1503050b206da55100900f6010807071003400c1485101c00d80e400c44e40d41c0e00c1c101800d0111040b1000b40e96a42c0d00c141e48400d41d003030400c444580103140d401041380000041040760110744180c410700003280540300110180d410825002c0d00340e030005030700700c00860b111b603808488070125414028 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 305548183 1250 305546933 305546971
    0x30f090605040b1501180506070c0b1909050301090c090e010204030609060903030e03070c151407030309020108060103060b030f090c090405010c020c0d08090f0a081203040209060904080f03 83
    0x18060701d80c2260200c540070a00410000315411950000111301000c1c070340044283c1058880748280302550042e02d205900c0810f4400411205200040141c100c240c105501d0b240c150003595060328542601001288901c0d8003c6030906051280400c400e0308201500c4030700d843e000072034004111078509180655003c010200c0481d059000c3c1012407840b410001806462508000b805c461000d081e48010b50420031503031011034000804403081d1440700503003e0340c7c07a102510a803000c660001030491001800300d51001403540691000d010b0740e0007031301d0340281c0c3c0d0341c0c12004408031039050142c55500301003440800c20000864284680c010000000c0b40d695070300c0703800007030111601210100e415030b450f0300300d071a4002c1d0706101e82e000007101911320005404003540c40e0782d03840c084d0100d100e008041803180301e00c1d91340c0c0d00c01c0d0340350042a0b2041610780c10039854102d00d0039035200303d401b0780c000c8000801040c45030522501140c03003580c110a801d4117051180300d0001c8568000381440404540d444490 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 305549433 1250 305548183 305548193
    0x1b07140313140a05030109120e0f13020d06060806100e0303041a030a0f05040308240618010e0f0d0f0303090804060503070215070206012601110a021002071101030f09 73
    0x54001c1c0005810b107001840c007000c1003190401540d013000c1e00a0f4103006030710703000481d401c00400e50315016041162050b10340b10b02040c0c02c4a641c0c40c0c3c00783d10550110010b110b4a16960042544041d158000d00c0314a403603402c140d410000a480458001e00d0300d68013006154400c90003040c003020020107503031a00d551002c00b8505d49041009000c000f02d0004140855401a4404c905a2106c1d42a0901c007a20302500c0c06000100c3c0244254402040010301070952000800c40d04203448008213643e480381002c0c1107001c0041c0c205100c090106003c00d03007078403052a1424078a035018100400f040c04140180d69480744492100385d044090584920104000030306c40400f0b00080e001c2552440c0d201d18014000a01d0400c900c40440503140c0014140b003607081d4042100c41c1540d00780840105450201341d40104c100c80000340082c0254a4000f550080910600041c9a0101984e00301d500740c1d000d02030404124071030900010306200903421062541e500071b1300a000d004918080010ba034030350035211 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 305550683 1250 305549433 305549467
    0x11a04080a0c0509010906050a0e0604020c060a06150c0203060a2409090308060d0209060108190204030b01050f01020f100b01120509010504031e09050409020303130803121b071403 79
    0x1080b103020307000c14418010360030502030759401403d030304009120141c50070021441e070443c14043c0001100343c0b01c00040c5980c449404584040b400141240c003030b842e18400050040845000341358604040400300b0003e01d1003100380301c01d0981c0050117480303580c6600e12918000d00c006032444401605211075a00341c210311190b00401407041c040e0100340c00c0242d00e4000d01250006200600c100c1c440c6442c80056181d21820750703480b1400382000a1035885400007a0110903680c013008070324600028010007041481540b05041315030681d0101c40160300400166240c0b9000503005069500101a030b41d28010150094810701707d041c10000a180c820400300c001b5507a08440c1c000031a910b602c04d010406038040c02001094102403503201c40c034660365100601c1c040c000d01c6007511450703d4090080c00e5541c1032048803401e90465045452595503101c0c0c490b107940101038155580310b1600005000c140540520046450203015010f281c105181d48401003071880380300c20501c0b80320510800c6c07110751820321 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 305551933 1250 305550683 305550703
    0x3041805070e0a080a030e09040f030e06090a030c050907050a02190201050f0a17160c030c110904210e0d080a02120310032001050f0c0109020d060f0f090b011a0408 72
    0x3005e40b019511908000d440d0025106030781e1301844007081040007081060001950f4503a040c540b8100b81c407080c000065480c000d01d415683d0000b5030540005c108081d5200400803203a0569100000d580c0380c2d241038580b4001d0070b03204070150b00040e5019640131038500036114194030505042d801e003810b0701c20b8070070f25401c0178002c50007041c6100d4442c403030030720482000c80c1e00c81040c00d44801001ca8061b0010120001c029006041c06010440c0300c00f0004440701c00100d41c00003a020303100c0e07854941007600c4c507001413840100300c9041612300600c1c402d1064030b9003070030719038064980405801607585e1000d01c1c0e44802000b0f400c41c0540901c0b0780d10111140c00643c050301c001d06080b2826821814554159541c1c0d9845011141d0408086c28842e60810140c45083c4400043c083d284d14951414502400c010b00000350702c40034136000d06080000c164011442d25a0b60b680403c8503e40307041d0304038202c54041314054034001c0c40b2001004943c84c0e008688041d04064082e0908065235140c810b450300070056 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 305553183 1250 305551933 305551949
    0x403080d0c020606030a050717030712080f0a0524060d090b06031218040c050403080d020307030608010504020f0f0409052b020313180608060a0b0a060203041805070e0a 74
    0x1001d440d4a01d60400c140c542002d4101c01811024191350f51b4a6030384d00c0385200d007900c0903d0581500000620500c1030718405504a048032503a40c25448004080e20002c4610700c11300c1030b901c0c0100740d00c12064494180b040c9113100b085050035134185400c0c007a0120754076260350700000410000811140c58054050b5582c40ba0340460342ca424520101400c1c49040c03402d442034210309000044018102c40500d142001c41598000790158003800111031a20458201070402000000c1200d5101c100da40118440c031142e640c204203e07a103035007a280c02d840c0c2c01d8a012f07510000f1040c0c112038929241c00c0140703142000400003e109a95941c0703441c14030904058085c07009c894a04044103c018501d81c107101100148007541c03503d4101c210303803000c00d14980a1250b040c050701e43c0c00b1500720b0841d481040a084400c0c12108207241c2041d000340035008203850b290107501030400005016000106030350a40b80400d00070443d02d00641074210080c070300149041e00b00030021580c41c00703946804001c400580a80 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 305554433 1250 305553183 305553191
    0xb0607050601081c0203091509030303070807020105070e030a031d0a0e1e0915041703090d030f0605010e010e03010f06062706091203021e010f0b0303070201081b0403080d 75
    0x2c041c1ca402d02c0d0311a9013a03c3c0c1030030004001c00c50241e0210071103d03800c404070b41c12407201554100c84006401445034045c3c05200010074801c40030742110600e8454442c60340240403d940d1000201c402c281f101c042150103a000d80070100001e0b002d0180d40701e2030302c1c2c1d422400000490340c0000980692540d405591217200701d6050040040305052500c90302c104002200c1c3c66070901c0002141c0e02c441d0516040c01c558100c9000c00c08100c04045080c940f00401d025054490a0001c00c1a0b11030f00d6071441369010074504079202c0c1c0f10171100d020ba039088074416182d07000300400000041d50b42c401d031603000350390655840c915101000c06921640c0050001c5907280d00100a402110181180190b05201d01c0e001862500b003004030f601803041c0080e1603101174102d40c242840d160680c50070b8030700c40800c0c049040d0400b800140c80700c154040e0080c144407030b10510604041c0014180c80348a04640039002030070307500c00501ca00711003003150403030350494901840c0307040d0317994840000c00e40288000b014a1a11 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 305555683 1250 305554433 305554439
    0x6040e13121d1504050904050c0306010e16140d0c030908071b1703030c07050321090d030605090412050708031f09020309150a060314160b04080a080d0b0607050601 72
    0x82d50340514a4a02c01e40702054511000143d07811180190301c03c8620902e65003000600f040001d000c10441da03e005801c82e07074156102c01350300700c0100c0300b160316203082c00d411116045410b104400403d48000008886480c0400b00802440600307124980d40d0107042c2c80d240322800080710900140003007400b61006249098207240d452903c5223140c0d008401d612051ba030440744118010003240c0c0c002d9801004941e03145450320f800c90442c040c000081114901d0f80c9410000c6100d5a401c4030310450049081e103401d42d410241c2a01100d005008031a08004688000b41c00103a05524030b04030740142d8280141880f503180e1300c00c6c56580c0126000c2e56180340c881c070100e0301c040281100307401811880d0030650451500d1089190307035189011050740380144010105d0b201040c03e038085c0707010f550459a2490841756014195564905200d8104031750108a0740015001d0313a041c0075142078882c000080c1c0303400001c0d0b86039940d080d0820183c0c20803846d07854180f50910754a88000740505c40c07080002e81030342e40c5 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 305556933 1250 305555683 305555717
    0xf060a0506030a05031c0b0418030206060d0b010e1e010909021e0306130c0503070803130603060608070507050118110108011406090d210815060906040e1312 69
    0x44081c0840b8001d51248004400041d000320540c0d0051507030064044a500640020b940035010f5408420f4102c0e140c41010203020b503c48980300714030360180e0221001510f60a040c07003045a002800503005c00800401482401800821541c0000c1040c00da0400c425800400604008003a84509240303647c681c1c84400f142060341d1041150401c008400e242c01c01e280002c60340310340340102514003000c24540d20710704015401c034010025090160458400c551508142a66540048051449584118000030308030f80b00c1d00624007178410035a91220141c44140307003564113030000801100c1d90754072890780214680f420007901c5a114002c181c6081480809030002d84070040c10703000400d080c45031400e43e50032621031404490030900245c85603002801d4904103650101c100048000303040c1d0401c0800113901d0303400148036000701014051080115107220402807544190711145800070018401005580d54502e40780780d20614010940c0480186d80d5104508065070507200c501054000100c500651 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 305558183 1250 305556933 305556941
    0x131410060f050307141b030c07051e0a051c020409080a030c090f121703010b0c0d09080606090402040e0a12020c040506150a0903080f09040c0c0f030e01020f0f060a 72
    0x225940c00c10b02e2450414040040c0281c2c1d051900718003a0000140b050f403001503648181c0c00d060060029240c84a0f1014515601d5000a2003594455401e9121014052807050075140100d440200b09500c801c0c501400e000c01000406036a1140030744004d104009030305d590040c1403c0a00c1590102d9684e08555400340454a031210b4910030006d00030018400003442c404031704140c4080d400081e4070202d0914056940014140d02e0383c1b0203800200001803982c5040d0040e1140749003180540f01405000003045030090410302c038001c800d40c000d00c08240c640c140340f001e06401c14009000803030202d480c20390041ca014141c042c1281c4611107a980c0c0d042082e810710050030345140464080c482800d100d0001000034a0106014200705400569031a02c1ca0256800200455000c0d080c9034607002d1042005540d5003110308018061801c00c041103074601d10030582401c0d1568030141203484511951003ca610801c1410514154400c9440f10b01e19100104008080c0c140640001e01032482c190307600f20252 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 305559433 1250 305558183 305558207
    0x2117031b0c0a26040f03050f1513061b0e01030501090627150807031109010b07151e0204150903151503080703021506060c0c13141006 59
    0xc03110a10846429140200300342416540084480d1601da100001003844026542c24224010400160000300c50041000b160200d030302601c2580e8080e00425040380c0c80301103910f95042c80e1f482c281c0000f40c1d031080130711542210340c0c0100e100040080288012001e1910310300032103c0465000d0b90203015540c0e041c0551030250111482c00c2c04110315154041070100d009401001000014840c80247c400706580903000542e60888013845480d515510161540c4190009481e07059080052006a04000003054101c1d100c4880c250f14000b46a119011089801c5654403a415225001c1e040c0580542c0181034010780d504d20010780d15442d2006031200351201c01c0c400e0040c440314210400210300c031615410a100304010021070042400c01c2c00e4484100742d41c1006100900118031038043c9a1b0000ba4000400d000441c0031025031100402c01556004048268025a004504862080c10f0140035800040e80b42c403004102411500511400c4500031102c0c1c811180d000b4070100b00d032641c0080c52480c4 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 305560683 1250 305559433 305559481
    0x6200c1002010b12030c0d2d081608070f0c060b041a09130305030f0702070e010b0c1006031509050106030602040b132309040f020909010e16080601211703 68
    0x20f000c1c2c41e40306c400c1e2250f8607071120006102120045c1403000c9000380d9506010300e82e00e580d0317048561101c01c1c0a8001101070700d243c51025580035031030002a000e502890301644080d2030b0501001d46900046403c4100400101c405030707100d40403402e090b01d45008107840060a0841121100b47e49400d0115484004250b4501c6903041d01004001c42d03004011242c2194184482080e15603807008241d05d00714140c3d02142031030f12040000510a134620014080e0300941000b078480070440c80c1666000c3da4410702001c0c064110b0500c00d001c03060101d80c03050f0580e0f0304c161700106080f50703280c0702e0400300c0c0c0040e4440c0304070301800956001030901c41d03800d07e40901020b604124610141d901b2140c185845aa0b40500400a99020a040c0b14041d90400c2c0e8455000f4200b00032803406950481c080c00000c3c0ba01c1c08640300740030327000c0307845841301120701e0981e62020021b0409a191044501c844d801140804281c031030318418030004114034802a0048402c0b100582d51b513401c2078213660860410107a81e59403 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 305561933 1250 305560683 305560687
    0x1110309010c02061003110307030f08070c15080c130e1006020c10080c0906090409032007080a080307090f030b010f0b04080a062c06060a050a06200c1002010b1203 72
    0x10702c0d10385c8803429005481e0010b1403180c1e80078544010924100c22a000940403800ca900907a081181c0000240034261190b0035031034406503110070300c02d010000a21b800010030320b0440065440e40707412000d085d01c0520200304c4000c00c2d90b00c0200c0900350706c0540d555030426168050900040d40c0420206200404c1520112424081e0060060140102130305100d000003001682d83d240381c0c0c9100c203407503c11100400c00c026050303051802074001001c44400e0b00440542c0c81d214603c0e690081010001c8800c0080501222422035440305041d0380010801410b0084601022444440300e01d1180d02452088103000034950508001921411f62940001c1504004000c01e00c000c00001c20801c40041d84442d021440c0c0d40c5000700203a9406c013a14010210020001000b11a00c1d00081c1d400d0003900142c2d0485820b0361902d040c4282e51103030f4001e1030081031030381c02400781008468548480824014003a40c0c5905010000904400c164589000050791950311841c010310301354031031520f0754410800640c = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 305563183 1250 305561933 305561941
    0x10801060b16030f020703080a03050f060108060f131b1107050a210507030602030c0d1d0312070e060d0501053c0112022a190b07020f01110309010c0206 67
    0x101542c41c801c0c4008003003010b81554625a00d008000305405590b214514a85507941c001d401402040c0c111014100340a100c00480d0b0554002c502c044e004140141c180c4076004003000074004111201162541403a50f911455400d20351494565585005603a868845048454641038900600380d00f006218411a480c20000241c0703805030034401404442003060f5482960524a04000c45a40301516484c00081000091801d400080c400c03d100b6140410940300d81032042c4095880c0c4128240340b55104100b40c03140700e1501c031805503021540c3e01d446517803a03560b90301189483e04202e1201c025107444030010301541c541600005640070000310308070600d0342c810110303040e6132a0031140d9000c00c12a81c2c04000342d991040c40c3d0b9030b0700001c9200b015940e84400c49035680401c024000f401758440300200b4000c9068801185238255501280c0e100c9200f191103407074450440002905900a620036000b0460310f21400b8051502e03190003040c030880d140e2a12191003401d684440c03ca010454114500300 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 305564433 1250 305563183 305563207
    0x14060f1c20130b0d020d0827040f0207081b1e03031e040f06022508070b0601110601030303020306060d0914191e050109170414060903030306011101061a03010801060b 73
    0x13082c401e501240c04a00000e00340c140607502e4800c425409070b84102403142d4224a016401c140c1001040c151401c1082401c0e44c4020350072401a114000c0c010300c4100700506064004e42e81c20860144502d040e92690800d5191a40c06440c80c1b00390b101040e0004000c2204040c0d649410114056000d40c240c48186019680d4a070087c404000090800307a0101c2c003100d444812203810111a030f80a0708030b05050a0f41d091a2442c0e4000550440b007100c08407000502951181495100d000c00503001007840b82d0030340d41d09401940009012540000c42130110300e40c075201034080d809000340181d60300c0703200c008480492410720300800713221304100e08418040e03400180089100701940c0344420b0701c446001607500e4200c0c0580340c0c82e58083d1100114000644142911000404c200c0302c1c48a0802c0504401d241444194002c08599076030541081c800503060b5406010710700511600f1a00000f113003a16041c1220003100031000845200c0e401100600000f4000d110700c501a0480440171402c01c1180221 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 305565683 1250 305564433 305564449
    0x30606080601120e03071401050109060b040e09030d1109030c011b0b0907120308070801080111030f04020f03060c040e090c03120c010204080118050114060f1c20130b 73
    0x18440c1009820b00015000c00d00c664050281e48013028241d030366030741860602c243e030140e020960506a5207024000204100c2c82d1148400300c030071050074141000d16012503905204002042201540010005039901d1105c6100b001480904850b07519140c8041d8000d00d441c01c101d032403815040c40960080301d0010342c030020720700d00d007580d000c0d42d02d010036502c14038407509213112540090f441c1d1001110071030803d5000501c86200340b01540d05c0c072200340e83e00c0009a0a0740c1c00c24003030f00c840b45420004148844000e180c403591050002d40349001c0b44054101081c07500e1011180c21745d40312000324080c01420344001000d50000701e11002040000c2c1d2160000761a04640c0e030455000340d2000400450b690001c0d01954000c2241500802c01030300f91800340300c60722001400c01c46282d460101845d41452034501140e0207201c002d007403080001003a1041c007098001c15940100c0c44012002c003a00003070000511126150144c442140900c508442031181400f540b1551000302d07801c001d4040d40329182c42c48 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 305566933 1250 305565683 305565691
    0x12021228050f220206030907051513150309140609070f08031815040801090311010903020717010b04020f0a08060a141c06050f10060e130b010306080d081603060608 72
    0x103c403503121002c00012004010f12600250000b6020041115541e03010501c08202e030400e8801000c4d02810b250103210501c201c6903485840806041d007070107000a082c0404e045a10b4604001403020b22a0f1510210b1001c6a01a90300c10346c010820420000006d001040080c100e0101c0204220b003009601030703c07405001c4901001203c00f03043c22031039a60302104024a02d60310340a403507969496105040c043d0242400550109415441003c0c10900511440c92030030380640c06802c6a41c200b03203440885801c5d10001c5580d542d21054800c1e626959840240005040c0803072003956000d4461001e0010b0000404c1c20740b0072842d1040401540c0111074030214542c008580403c00e2a84005000b0440c44c08410f01920346444c00040042719030303c029801d030050b4010306041501e259949002c540390520b4240307054120302d0305d03154440d484d24140c0041c445140c05060128106031240c03c01e900d0081800c1081d000114504107214010041d1640e108a00c155841c041c011a0b05214001c0c2c080e1201038 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 305568183 1250 305566933 305566951
    0xa0e0a12050a0c05242b020a0306150507030309020a0801020c0102090f0a08070b2208010b030609010509070302011209060c0906030e01020a0806060c070305060a091a0609040312021228050f 83
    0x80c40103143c0c154141140d040b010306c11156400041048030010094222008540200e41b820307401041c804007420251400f030049566881c6092040d540271030140443d884d0498018111a1000c90101800c2c0090a5440c904000050302c61070f11900301700108865260950056020310028020418041040019212541c1420799a0041d0220320006125181469510704801c54000701c0c8680b01900b09203900c5408600f202e02c01d4490040a5003210b80c1502c2888041d8481503040005500071076038200c0da80c4110800140400e0315407100d40584202e114040c0015180e580c041c4411078041c031a03c18200f4a080085082a500707410150480102400c002c1c440c00c000314662003429070410098014580c00f0301950843c1c100b10720395401404050380708031920350314079400c403c0c1d03078480714000c6104000060110b0b10946860300c090760b1404103140c824540d207808106000304d450441080d00c1c00380b00401c01d60f5005c040344d03040c0c1075010b0b554a0018401c480c01c1c03606200200040100407a0410164 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 305569433 1250 305568183 305568187
    0x2030304120926010f0b220902040207060e15010f06140c070f14030613111216090f05070e15041802040e090a080a0e0a12050a0c0524 59
    0x18a06071484250350b4002c02c100f103400305648906000c01030400448440000c001c1c000460144401e00030b807840126429005602c0b0150107030918440ba00d002d0305a04e4031800060150b500b600801c00f42c0e80904802d40d00540c48110440070b600d820000068081c60b9052070f8181941402d100d00f030002c0803403264038208003015181d00440180030084403a100f151000301c960490b580c41804280100318031607000442e5131000e020381031f41404500c00344038400040c06101c00440d9940d030000d00070980500700341c005800103640c00c02d01c1c9081010041c103046503410005400e1a010f0007030b0a443c403184506414505000a009140360480254011100300b101e140d4036080c4248519903050046603c00092070785411a00c00282e95243c0c000e009490102c80010403d94407048180e9a40c1841c0c1001072a0601c01c100c150784042c402c0c1002040348000600b611641aa01e00403100500003d00003520903030445480ea03010810600d20080041800342d5614403c082d030710343c45416100000c002001c80d40c1d00 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 305570683 1250 305569433 305569463
    0x3041208090607060f150302060418140f010e07090311220f0515060702090a0b04090b0109050a0c020714010c11060703050403150920030a21140a02030304 68
    0x40c0095600c0c080000e0304040e01c031032590801c04003030032a015240c2c0c0020b103000c170018400402400c5440549030003901c0035162a1610748440402d11285030501029503442c0c00c840c1d80d094a007412140204040c01d00895070794102028459101c0016103280c042c0070001c1c8040000031114214920310300300445451401020f50340c2c511608201d080801c0080e185071101c140d0419400b94032003401074907030300c10004850410f40c041c071000c0e21403040e0180d031001482c000203da9407546d800207a00c2c00c0b000752020940384060f03980c402080304281c00c854281611442007003640890f130f1040544800481c801004003038a400000d60104500c1030311903041186100d03004080c050300b88040401400c02034011a40c480060600425a0300940800ca4000100b0301600403004424096460243c0d08440656800307001400850302e4600c103481d03155011f024940c100d001185c070a070743c1e18405280013422601e40c1c1c107a02000405800f1000240d151650052021120b01540001683ea01c01d40c080100e00590700 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 305571933 1250 305570683 305570693
    0x30402030c0406090c0e0604081f090204022a0601030c091a0a0608010e0f0c030c0c0a0c091d010203090606061629060d03022e0603060b03061602030412 67
    0x1c1d00d0380840d00035003004000590240d050307015807000030042d62029030907186502000000c0c03059208001c416480f05541c507a400d2054081c92907540031059000a101381141d0100701a07030400080310700240c0d108034440c03605020741c11040c8007a030f507070101800c1c8542c1550ba60307041c401060700480300103079690340c5409001e1030040500c1b40100304c000d105524040d138920000340440c40900407002030f20094030115551450032400113000d04900c60400e401d6643d0121910300c0380c4c0200086180601c1141d02400200d504940c103000503000c0144081200914039001d0700200b40741a0100794243c0c410405c0200801020070380d641c0201c1c0489200307a1b50040c91034650080117030000044c0c6440c2078240c09600710442c04101003501e0100c640300852036550401005521171b02c07180003074050303049960f155468060100d82e80c190064080c040c1100c0642d04495a41241c00d150801c85403540c4d1801103e40b540740410403103030701040d091904235901c0c4400500039120f01480c415071504142e080d1f03803441000 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 305573183 1250 305571933 305571943
    0xa120909050103060c1407260f0a0f02010e0c0618120f010b03010c030902091308040b0703090801050a020301050a0312050403020d0b101e06200a0b070905190b03040203 74
    0x202440207104a503180d0400e43c000303103001c040d00b40100f01c07040700c50003105442806494101e600000104030504c0707134034403158081342c4100311a00e00003000c12031000702220702009407008503074943d80d0b9107054009100180c01c60341503080b030b0b007007542c00101000055642c110403502116603d071500c0c00f949020901045074400007610203030044c080d0201c52550004154000343c3c810004034002c0c00061b2009200b64100c07410046c019401000032800100032010090920000b40d1003514107d103400d5840520b281180c0007020304400290800c80e040210318000d0080f075030400300700c0c0811895540340800203948520207100082c0820b00c51000f510280b80520160f0b0010f43c1c001c0e144441101c0545004e41e24914100c80700c0002d8844c00e8004251828038031050304001c40030700002c0a185042200c25a061107100044140c0145010f80c000c00e10541030202c4003810388200700713a20b10b505101802600c0003800e900524019441d00a0701d503443e42c1040070071000c8421815209540e62200d0000c28200 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 305574433 1250 305573183 305573189
    0x140102041412030c0d17061905011b021c05060117060105011803050a0b16020d0503130f2112150b0a2c01091a04091116050303070305070f020a1209 65
    0x1400340d49444441782d80c12543d85550708816015150703080e40d0341c1c4100040003124030b14a6504c2d01e5004806e02682d4003079240c0e0701000d44103501c05c98040219900041741907080415462143c09510304c241c0030404200101d03809400d8000080032500d80b050790312940d03840144100c0b410041c0450301207140c00c004c2c0c0204030146800c141525800030041c28200c40b030040559140e481c0443c0b003950207445038404034807900c540d1600d40c0d801d841e54840c00080c8650001004c000da640d500b00d00b2581002170342103103c00038500b5003c0d800f454081c58040001c1c0c41510120306000b68103003041014806568180c100754140e90b12440000d4850b0400c580464003402040c01030a00403030040c1d1060300014418850042c1c844090340c0c3d40300d1882c0c80700d0f0303034940c24a00040f1014004506210a12404085c6c0e0007150343c81080004e80e030b00b0560b5420b00e2040c018440c54040c0c0e001d420001c01e00c45890b601d4020198000d480341055522101c101800035994030220740c0241c076a40894002c1800203218503104402 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 305575539 1106 305574433 305574457
    0x1311191220100806060f030108010504060e0607020a060c0e090415060503160314120a0302041d040305030a0c05090d0803010914040b18030f0a02010914010204141203 73
    0x10b030f40f00140101c1c0c1d20620522010314600b0030003002c0e600030601d2200104145c03d00c0c0c2081c03001c8460524400c030198102c4010002203903000036409498a0344540001100070150400b222b4070300a44015680c009a03e5051100340408407412420002404104001190390340041540c0d520004c04812125011b90a0400c0407403c401d811503c11181c44c01600c0001442c4074803160640d10445003500400c0d8003290a00c1061078183e1030098040f51101c00040d1402c0544003d811800700424008205444280794207006106000361003221201130504020401d2502d4802450781090045481083c541040c203030b0031640d01d03840f082c0605c1e00070480240c10b48500700e525551100100c810a41e6200802035016081c1d2007800900120110707600010b9100510318140b10310300300d01c0f820040300c0ea005000c14841c86001c49110311140204035030402c592119490300d1800d40c0644001d44034 = true := by decide +kernel

theorem cover : BRFrame.Cov 305395683 305575539 := by
  have h0 := BRFrame.cov_init 305395683
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 305395683 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 305395683 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 305395683 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 305395683 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 305395683 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 305395683 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 305395683 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 305395683 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 305395683 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 305395683 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 305395683 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 305395683 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 305395683 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 305395683 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 305395683 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 305395683 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 305395683 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 305395683 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 305395683 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 305395683 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 305395683 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 305395683 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 305395683 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 305395683 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 305395683 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 305395683 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 305395683 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 305395683 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 305395683 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 305395683 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 305395683 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 305395683 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 305395683 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 305395683 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 305395683 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 305395683 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 305395683 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 305395683 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 305395683 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 305395683 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 305395683 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 305395683 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 305395683 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 305395683 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 305395683 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 305395683 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 305395683 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 305395683 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 305395683 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 305395683 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 305395683 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 305395683 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 305395683 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 305395683 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 305395683 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 305395683 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 305395683 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 305395683 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 305395683 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 305395683 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 305395683 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 305395683 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 305395683 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 305395683 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 305395683 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 305395683 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 305395683 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 305395683 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 305395683 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 305395683 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 305395683 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 305395683 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 305395683 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 305395683 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 305395683 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 305395683 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 305395683 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 305395683 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 305395683 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 305395683 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 305395683 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 305395683 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 305395683 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 305395683 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 305395683 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 305395683 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 305395683 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 305395683 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 305395683 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 305395683 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 305395683 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 305395683 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 305395683 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 305395683 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 305395683 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 305395683 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 305395683 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 305395683 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 305395683 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 305395683 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 305395683 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 305395683 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 305395683 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 305395683 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 305395683 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 305395683 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 305395683 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 305395683 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 305395683 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 305395683 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 305395683 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 305395683 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 305395683 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 305395683 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 305395683 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 305395683 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 305395683 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 305395683 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 305395683 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 305395683 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 305395683 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 305395683 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 305395683 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 305395683 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 305395683 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 305395683 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 305395683 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 305395683 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 305395683 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 305395683 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 305395683 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 305395683 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 305395683 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 305395683 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 305395683 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 305395683 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 305395683 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 305395683 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 305395683 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 305395683 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 305395683 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 305395683 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 305395683 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 305395683 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 305395683 ≤ n) (h2 : n < 305575539) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
