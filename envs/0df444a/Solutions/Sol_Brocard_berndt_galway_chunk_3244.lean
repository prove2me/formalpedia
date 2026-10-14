-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_3244
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T09:05:14.621649+00:00
-- url     : https://prove2.me/submissions/f013ed47-e4cb-4780-8b19-c0b54197ce57

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 583273381 ≤ n < 583453237 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 583274631 1250 583273381 583273387
    0x7030810030c240f1224030c0512070317180d0c1a070209011a0714031804050105100c020307090c020f0c0a0e0c0f0d0e0d03050106140912070b 63
    0x241c8a40700740e0343d0144058041d00d01d0a48000c1c1c002c0c01280581344000c126a11296100102d0501d100201074034840c003a0b55040003040034074119540c214640142d07008031049a041450034080048085240d10841982c0c1c0049070208000340c0305041c5a840c1c0c05550f441c8a8444000c01001e16003217a00c2e0800650015024070603000f80242240e0400c01e8640001c90403403202074507010a82c1c80c0c0300740300d0001c3d000040280100520301c28442001c1e100c00c00e241c1240d18040b142d48a01e00e03170304480100714215030800a0740130f0040107406c00c07182c113040040d02c05001941c9402c00041c044a405000c400500440142c03810440d0340500c40400509001407040010074041074000b5a02c2d0409002c480d0507100e240208000c03403030b10f0001c0c841140da010580d0005070365520011740803034000c0711340d059000c00140481c0310103180b1802090650590040186200600c4140040a9800607800b100502044285a02a01554000710b0700e4050050360480b200c40303041e50340940743c40400d501091000f1404 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 583275881 1250 583274631 583274639
    0x10f0f2714071404120204050c090603180705101209030c08030703060e060d0203030f2101060c0b0f100902090609100806090f070e04090f0b04030809010e07030807030810030c 77
    0x600741c1540112600d9855540d68596030412805500c2140510100d0042021000b0010701d007542080f40e020b88100091404c10b22000040365550b04269040001c1140d14481e08207444001c1003240c0c0181811503118200a0b41e049025041043c01103500c0355040e250b0031400305050043d80c40c0d140741c075401003900e40d0300c0c40d059200900502c11400b404c43e6500410b000301c0c0951911404901001b5001005035103040c0f000350804100ba4040307042404a00c242c035504028407052080464001e26050b101c4000e40304440c90650801e980c0100b00e80d002e6408a02404503103038104e64018256008402c005035220505d4001501c41c0c01070b180b5284d8030111012780084c5003540020142d02400007a81c03420301c03d496001c1019803900781140d041000070007805c0c41c41243e02e043e0300000300c4a402140440030410040c0c03a00600614111400e0740071440c0d0409103c01c0d81001d2003003404ca035160002402855007103aa401000f4410b680000e0100708001740860f14090001c64000011548144030404039a6a = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 583277131 1250 583275881 583275911
    0x82401050c0a0b1008030c030a20030c01050a2f1b030c070302010906050307272313090b1b04230109050402182e0302030f010f0f27 58
    0x2c80700d56084007001000007601010000070f550a287c000b00c0514141840c10a0031039a0310301142c1d62040310318003078604e01d41c884d0b42400140350300c02d51f2a00100c0c0c14902807460381d065903504400c5000e81c108810030079154140c0103121803004090021300302c2c1d41c1c4040803c404c7c0690820080140180000103118103088000501d4804991003030720340d01192950340c2410703270302c900003203d102c1d021848659450310300545661102000c20164031b603468806031168003492201d1030f80100400511101c801d03680480c980042d0380e54180c29041d02c207000c10043c03543c5900640700c01501240c01c1a000d180450040c000080c01e440207815611003107107043e02048001030b400d07418146854003140041e54081104d05140c002c941d01400025a0741d02107211100900019125000c080040d49861003040a00180804084000c0080c25600540c40e42030240c0740d840d0350b0710180d00c482d4041d4142c1d04100180a40c8211900c00c0b50b0b1001450001410b0000d610924003040104d800b0f0081c0c40c02c100a030b50008 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 583278381 1250 583277131 583277153
    0x10020a020a0515010e0a05070212040806040c08060c070f0c05040509060103060e0d05090f040605190305070b0702010c080307020f0601030c080d03060302010e10120f02030115082401050c0a 83
    0x10242c412611100d40e0700801d40c00d544000c0c0954030900741c42000190090060b0340246030441c401e4411280082401e14030300c0000d4000b500311070f14070303041032003440240290014a94060056000501800d05005024005601c035a83c401400540c00c0d03240c0f0420701c0007540c22840240701c081c00c2481a4580350041c0c030340ba00b5003400300312000b91034840501c00a02000864024507015521014a00200c1404001e0012143c42040d40d11903114040414107031105007009100e401003400c101030041c103500e0407038200540c507005208240300a220150151b0381c80400800616000403080e903a940b104d54040b42451210f4062102a2161750000004c104034900080b04032880a8169241c0c1c110420086080e1042444003074000354000300c58182038030b0308400c40141d54030300f400c0c480e000000000f103403400c0d903200a5600c0390f1903a0100040010501040c012126070301940361004071449d0003030a0342c141004c0783c1c44404580c05e1400114000741d0051003180c261031201c804132030009d8202e15058038186 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 583279631 1250 583278381 583278383
    0x6030207030f080f06130905010c08100806160309080403050d05070b090105160305090102091c260f030a020d020d06090e031620150c06060a1211010210020a020a 71
    0x981d018032092605100f43d80d0305001d41c24100d042901c6407181c000b0000f982110303402d4042810758540d1410002402480b03800071950042e21803010794608500501d01c5500c0c5944135001d03a41056081294812004607100d100c85118200041d0200e09800d2010340ba00803508010810700c500039585038400e170003074050b041951041c2808051990b40f0595a400c1e10307010b5441a0800300e480e000104071601a400c1190300510600c001814204120001965003081312a4034074500e28400c0c0c0902440381031024501214602102c0c9c403140544608122aa8424020050b80c1447c002c00842d01c01001074045413001100c541c02552520404210702c80240b02522039454a64a080a1041010004000d50f8164011803450000e81c46040d01c0f0345151500d40d45044a01850b4500409106e036110400d074540d00c0707008402562074010b80f0b4861880e0420140c420352280c0343c009400c1246848600190411980c054048148000e0540040c0d2a00201c1c140c0b03d0320b102c5c0041080300041d80c0c00104d160030b079 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 583280881 1250 583279631 583279637
    0x9120a0302030f10031110030e0703080405210a0f061103011e090605030c090414060c0a230901050c07170c040b04020711011107090516180f0603090f0c0603020703 72
    0x1030302d803104c1010040b001c0b4880148515091581d448280c80c00b81c050b0004010b150034049200556940c0d001c0c01c0148d2a00200c90f055808030b003d002d0f80c1840602102c61080400074030920b00182c1443c90750344c1d25015001480d800050200c03104008440d0047c01c100c9a012000d144c42e961200000c10001804c202d02152500f91032100181d2443c071401184108ca070003501030b203419181180bc0c0103907078000400a6412255544002d0400380080100a03c2202000041522000a00001403c03460484007015142c0003948480c66888840d00484056030000d0038255036544030302030a281401265442a000017040c1d04a11760071220100f8801d403007190480d410000d001d01c10040100b28059440060b1040200800e80d035201d500410783c00d000b00d1000ca04940d82c0c9580e800c188400e681c0708890b02ca0030f1b0032904183e000480e0304503401c2c5811020020500f07015500f4043d01c4800d00b80d0b14031400040544445090f01403200b1120400c1d4041d400c81d808001050301d444024020f507108441c21400 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 583282131 1250 583280881 583280911
    0x2e06060c05010c022a030c030a050a05240106080a0e010906020405100804080405090402010c05060c0a080c0903120f0403150e0d090f05131107060506030d020a051509120a030203 78
    0x740318404100240745c10300300100800c0d10b03403c0041d880b1311345240346151034142c03081681400c0c031a5000c11142040c3c82c814001007a001d42245812420500c13009500402410703007840002c140d0401201d02415a001d07840c0c144150f540e00328a0001600c041c004c0c4801e103520b4403030854103100d4150000e1090342c03020fa8410110b003271440411581002c0c21030700600724610a01c4140702c0c0b440c182510a4110b801454248108102a10b54604051003a982c48191500c001a0040707540d4201d81c0456204401c4030001782407007540b0000c20b896038074548520400203c00550380c0d481b40c54401c00c0d0380195401035641010740616a104c040203002010349404c5071720542640040940c8142c00c2e01c1c050380d01d20201c400405c0d10344014009403100800e0192079030f07901c8400440c606103030f04c0082d240c0305015100206032401e050341030604144030318118108540000165902150000540c0c2a0609076a240062580c0d0313010111410120300700403031883c0c40d10006107641480c0d4149c02a5005606030803071004 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 583283381 1250 583282131 583282151
    0x50a060507050a020a1b0515040f0e040506040605100b0d0218040b06070305030910090602180402032403120c07090501061803020f0a030b070f0806060702032e06060c0501 75
    0x10b02401000e01400040c0e10140c0c120001942c1061002c000880e610031241c80e03607480700c00040c010030541d141a166890003040c02c1186070b09074a450001400c10004007482d90601d501c5550710b56030001d2015254644620100c0c004c0c501e9408003d00070960b8914030740d1580e226500c0c6001962011403800314003240c0d4803403c0032624183c42182c458200003460325281c812659000e0700c8071b80006100404074060059a0b00c255192400344268042c824000180d4400500748590504881503569600a40c41441000441070400000c4081e00700c1e0300c40400c0c01009104006450b0450790b26012890b090301203000029540005485400d981c001c4800380b00c00da072150f208032080080308c144c04100da10300c86d504101501381f4020141d4043c90103055102d100352207850b04541c542c1c0076941c00000441410181ca03006900000180e008101100c0c054076011f401e070000b80d0f40c0e40c000c3d8406400301c1e000da88000e0b414a0010300141c1c07090072111044c00a40d60341d03400544610002d010070386040d424400e04070 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 583284631 1250 583283381 583283387
    0xc0905090c03010501140904060303090302031501180b0a18061505090105190e030a080309100203430906090501031509020d0e01060f030614040f150f09050a060507 72
    0x74410a10904014216840c0000450300540c40e04400405c0c0340c0300b0447c0007100c0d01d680c0140d1000c1c60094440594007480c0d48181898402d441d203d004114408000500015140703e00498403141410000f10300d2400020004030041c3c0a5401440c180c140c020151382d64140030b4000380201c810000c20080640c0340c2100035180da204900c11a80002c004006e118000c3c0d910100300c8a80c100d03249040241c80c84500040383ca040b614600554043d41d011080000500041000c840c0b40c54400c001075096040603407840b20940101d42c10000481c50351515101d00d04802c4207514294490321140c00e00b80048000c000d401025107000b40ca0009012050215443d400f034042c0e044100740000806003094500804080290064554034500719150341080100e000c00f40120405003e01488594006203545407603821100b5040503082c00c002c5180c00c10001c0f4894500c81507050307401038400d60b0764039078001c400401002e142d07004040c440d240500d0a4180100001c842036004d1049108004c1519886025 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 583285881 1250 583284631 583284649
    0x5040c0503010b0901081005090406090c0f12060203070212040e040c090506010507110111070605040f080712030f1b0f0201080a1503032303090a150612230106090c0905 74
    0x44040f8400402108000794410350f20641d0001c05901514000341d103030b80020340a0901030368203441c0b050304c400000d4207012010628000905030450803030103681c81d0000780c07004204003001c0070781100d5001c07000807038840c02440000000d1b60580852030b5030307a4540c190320807605815503090300c2002044101282d428294840c0602859050311046c2c00c1000d1556a21810122603145d20304010200081c5905200f04200c088040c18058840c141c4076400d145a0080e0074000785c0c020722203a400700208001106210407041d501c03680601d00050400d10b10305059030702d224801140c20220208200c000140294400d070415064402d03a82c21070703070b80c4030300300d0300010368094540c0321f1403201d201c3c182000000d00602c00d030111b058101c2002000304035082a003c201b40c000719203c039610341040307681c0010025201c1d503106080703058882c00c001c020f041242009a0714400c000007440aa0310400481d00800c4045a185104d8842c070300a000c00e40d110507401c00a084a0484c0c1030100307003c10400b26092810441e0 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 583287131 1250 583285881 583285889
    0x6010302150703140d06030308150108070f0504150f0e04060803090d060f021b0f0615010f0c0c091a090610140c07062f0a02010e131505040c050301 65
    0x801d015000c62030030400c05038001d40c0b0480c00c4c000010724040d0070400c0342020300b000d41405100001c105145040280001c540205a4a021000f4141c0d4503034583e044498140c111025103800c800600711000240e031940310b02e4101ca18481e60601d44480025441600085282810346d80d02d21101250802e00c0140e9406001300b005580080c00707802c0b5107091241560340340c18080d400109200010040c820101c1c1c0c040c82031002e030044444520340c819081004002800c1481b02c0082c006031400d0080e080c1c0360303031050840314100301c400320424240502c55145d641c0300a41200d03850750304550b00d0741070360700038281d0410050004913000081d002c075190815136113104200140c803985401c400b0510486000c40c0c0c2e43c1d500d22041c0e90501180d41026003c011b040f0241c4860b4035003c014102506410f40381c9024400341e401d04294000d10003c200d24045480c59100d82d080c208100d855034080005018011802414502185001c42141c000314040c0c0d841d90440d42c080d28100f2130740e071034060212000d1200b40a = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 583288381 1250 583287131 583287139
    0x70515130c03050d1b0c06030f021213050730080408151005010e0604030803100b0a0305060315060d142a400917091002280512070c090c0206010302 65
    0xe0f01300070890280d0000381140e89c001c940146440500c0003559840c61060300d80f4a10b40d1a58141c050030004200248005010024100d150011175148000f1070714280c0391160044500350510300081122040070340d0054001c000c103403600c0400a030103030007600c103040300c410340c10080d5080000f45a50040d1001d03400c00801520070f520709420b649901d11145e0016014251a030b01c50ba02c0000c0c40c01d0701c400034140001c030700d941c0072030141400c0341050b24012181d00014201c800e040305000c6d00ba555007018a41190340140d40208441c4481d401905141030300ca0079070ac008410b2a0003000d9280040000d20040108130361940821142e0a901040b2446448401c402400c201c44c1d5035100d049103c080d810b240420407070202d0490082d542d119541c80c403070440c5c1c20b00c004000c2490030003031801c240722002640940c40205600d650b003100c5042454096074111900160141141c8140041400150306c001c1203100400ea80780003c1c03030500701c1044107200f1180010700d8020041c800d1840420b0a078101c9070010 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 583289631 1250 583288381 583288403
    0x10e0a0e0c130312030b0108060612041104060801150e07090e0405100c08061305220213180507170a2a0e06030f03070515130c03050d1b 60
    0x42a4202004005454030090752002d00c040442190200300e00d502551290341140950b64400300c014080d9044240d569050080700c0080000b035840799029079254140c042e040010740c1d207650030050000041d00d80055005401c0c40c80221310010150041a603c5c18413800841e5140d9444080030414001a10180006510b054003007018144042c141500070f07000d41c044d5445149140301070001c0395024504107000c215510b0400c080b52905000b1208107100904040c8520b1810702c40c000e584605a0405807466541400144250340300c2c44480e01107500540010050003180c07000d04513820b280081d007100c06210356000440c0128500c0010a0403900d48401080e2038079a0741c0d1307406081d5510701384040b0701002d50404c1c85e4004800c69034950080c101020030541c107050075000d041c100700c0354007001e5843e0341c41085580005103000680744202d03080e821005c56151202d10305600348c100d2502c406045003101e5080402031010103e0181d03c07440c021703150084405103480d110505042a090301620240b1a9 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 583290881 1250 583289631 583289639
    0x18180b090304051201050f0a091704060e0f010c030c0209130609080711030a030c080d0f020d1b05090d1415070302130e041e0c0b0c0106080c0a2402011103130c05010e0a 74
    0x158000d0609d0358803884500400a04140581c201504254004c0d40010700410350800c071380c00c0c02c2c00c1040c2130100a00e0280c0341c2d51385540700605600ba803628001d008100800001c0c100100c000c0c102c160300d43d0301c100c0c00c3c8181d030424208071641d07401014099071111900400d59050f8500002c1031030070b99516480b6140350390040d840d1081c00c1e070410a2440e95854480174980c4140005200404189984000c001111a000080d0f914080c00014180c028424100a280e010b661142e00d81c2d001c465106410300c0a54404400d03a17070a180e030744080728400d001030000340064a41c05401902001e2010b5440081c0d2940d120b032503186208094034090040040c160001d50300c5200d41107410a00c03800f44500e02103481c0c3d9013044c1e9225501ca2080c50070241d544030f00c00e208844003886240304542d021030382c19106a003804008804c500d9840480700403020120b400d01d0000d0300030341044c070450b10f2020880d0303241c0c40c05905584001d001c000003110041080d60303000c0384941c0109118111550082c1c040030a142c14 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 583292131 1250 583290881 583290901
    0xa050604022e1b2a27020f21011706190e0a12090302040f0605090622050c041502070b0306010c030c02060427020418180b090304051201050f 62
    0x1014203c40126002900d500480e401d104124a441c3e000c1207009002286807010311510702c01c07500400b40c02c9581e070001c0414445c030081d040e918120340980c0165119954000d0400e02c0c803a004500c0d4000c00041601c000080c1d0041c21107049402c03900b1202e1052903800c800c6c984030030040300e610301e00c2000310a600000e850b060703002044070841c01d03045983c010901e49600310150119000540043c0700000188110b00b441e00403c41a41d0107c90180401400c000000c0c00d01c4400800303050203011130449100046d03c50800000014414203010071140c10262182109a4400e0050840c2094220501c803982e51000460350112068022000d09503200c6500450b548000710800f0f404000c4105004005a500d5900502c000c2001d03064032028000480744034061407003030040c4070343c20340e00c1840100070080700c4100c1d401c0c806074000320000e00110136a00d4000b054a86200180444500b6810009007881c008000c00a842013118105481e00c501d083c4503003a19001c48a0500150700d50020800d9040 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 583293381 1250 583292131 583292147
    0xf1107061d01030902121b0105090d020d020105120126061b0306060909010b030f100e07050d2a030501080a020604050f0109120b01061b0b15120a050604022e 69
    0x1c14540403461202da90002944c10714400c00c6c3e00c14540085048a0310078040c0010800804002c0c20301d0340c140000d002c0000c544161119019008414034125002103a205d8000c0301d03071000c10799040105550f1030f01d40c4841d4030040c43d2541c101926504120007091407000824620a10350d644991000303150b0003440180d0b941026104a4100505004c80000b603910225814040c0022030440740c1c892400c41c400c1610024050801450380d5140b000c207104840041c030400c1d034404141d0070100c6e540c1c002e01030600e000304007112082d44100d001020b62200350102101c604405c510550f0144030700e98860075000d4441c5c200031802584001c0410080002d0306145d0781d001c0c00c529050400e03c0c0f03000d6803002d11240c5043e102c2000c8543d9075404006110168001122800d0540742d4a01804d141040785e84000c0c40d007201030240101007880401c0c000c1e203640c5887d08000100c00d01006c1d640b140d01e4034917106035500807e8804030300c101200c28542c940d007020f0110080f040000c18038144644481c0c218142d403444 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 583294631 1250 583293381 583293437
    0x8090f040605060403061e0e032203201207060527060f030a110703120b120706030c020c060a200c09180c0906061801020712030f110706 60
    0x3503150400014199036907000b500042d40a180c1c003242030841083c10003603500a04080c901000d07c0c2410355906e1040c001b00341d4a00000e00c28413602c040544a00706d00c03509401d0f03400181041120101c288841036809040700c1459000c0d9000120b03251032100480e01d1340300038042e0b44000703503003482203100383c490701c0c46002090710002c2c0d6229601d24000e000b242c8241d2011120141042c03001090241b5650640300c3c00c000a03c10381055030400b800750390003c002034120744081d40b0151300c60203996280c0c0e07510708405d008a0040000c030b074005656500702801030000e14240b0030160003400c044180504041086403100c500941d14140c412920a20000208507000b261809610506030340b000552104040c01e8050200701c00342ca00b0410074086040c1c40c10544686460181d18201c060040350b0320384d20213071150034009045044921660200407403030940c9560003c1c000001140016080c0f50700002129000c2e0501c0c0d40314100c28403940300240e600c2100d8401d44000070b2071003405062117015a91680402 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 583295881 1250 583294631 583294639
    0x30f0e011407051615061703030615030405031c0e07080a0c050121020304080912010b01090312031107080d05010b0c03070b06150d1b0c02030a020f150307020c010f080408090f 77
    0x407143c65100d044091050b420700c0041251b071100107109a410031000058040c0b4228000d40c99481d00c8030200300e03200c07041815414420b0380440450b0030060140265a800000c12181041e40c050b055020400b61000141d42c15050040b10707004a031200010402c4038065800419090300310789000011181c1d03600307011401c68654028200c58044030700c540000c6008a0003189819142d000600410400c00c0595080c240c490780741030b8440c003050744c0050300c1108403500003c03e04010100814150058400000c003203150101c0080c45ea41007221083c0684900e41d4240000c02c0b06030b8039500d00036035a00c541da130600c48907403051007004005215400d00c15407114002c1c0c000c44001444814402864020300c94940740c072500c403811680d50003024035410508003024900ba0705000c0c40b40d00420b4070758841400c007034000d1100311021100d070f07128031800042840940e5081540e910306004001d4035140a500818005405201c0c0714207500d03c80d20446004079000100b062605120f541049a0403141082d42600 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 583297131 1250 583295881 583295917
    0x604201305091906141c0212030d050a0b18041518060212160c0201030b0411120106020d180e06011403090c0f0402191805030d030f0e01140705 63
    0x41c644814042a0081c0e19801603203607080120518101034805541041c003015003140500c441940e81c00c3c4801c410880707581d444095421160000c81c500c00c016003d039407103521001400c8542088158442c500c940c2c0b0000c0100054284e2004000e4518030101a40c0d503060041da011801103002480180d03002120100300098882d40020281e0742207940364070982d00c10364045980018040b000d00101c0d44000d5107064200b0600c200500504100c0c65100064101659042d019525449661041501004030441544ca0b60001303a0084c10030917003402424018007a1017010130480d401001210512180006110141c5050054441d022031008091504011011410140c007440200082d4010010400545070343c00076002131110700360043d00030782d00462040003064110004c0900d400f28140c503502d800b5010800d642901041e007100c503084203500d8040c2503500e401040d0980d00007085a806c0040c2803005039464000e01d070888a86c078103100180c203003810014010f18415401010703100d64929110038 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 583298381 1250 583297131 583297139
    0x4031e02090103030f1701240e120307030207060c0b0105060304030201090b160f05120703050601020f031903050105121e1e06040b0906010b09040917070b0f06042013 73
    0x19240e9000c3c0d00035004200901000c003002d980c000c2004c00343d4529004c281c0c0c070b154500200700640807541c400c280c070b00d00c1c18031400448051080d10010701e01100180140088599410700039225800441c1c01c6015200388900029202e004000b40a4a582c10949088690386854148011640700802c110b0440d5170314012400050003503500d00c4d005108040a0b07000f0740110050151201025030a0002404000d1141c5041240c0960049502030614075000c1050303214000180d241c513845041140e840d00020464400207801160591000d012655052103540d036a0b0301400301d01c04201051071038a0b040700340d225681c101e044040202c08101601101e401d035070506c1c07050304150018408103005401290601052100f00d000c1144c0106c07820303014000d9940340a0300720060344212451a8000c0b0740300c04a002c02d110802c0383e12001d01d50885800c41d55054103142c6102c110b241150f00800442505000c22154103040c0b0a41240040410340040b250399641d40005058000c0e200100f0010040d0708081 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 583299631 1250 583298381 583298389
    0xd1b020a080102131701140a092d0b07090302061e13030c030c06021212100e07020303100f050d080d06090903020307050c091e06040608030c210f04031e02 68
    0x450040c0e030903901c0801d002e003040c0307485d401511034040560a82c2e040150066400d5520581c0641200e00e4100009107916945400460200060310064003440100c07441c0310100c0008a801c0e0744a4840c2018030074075618240180c1d42c088940c00041c0d081001403040002c25204090f404402c0e00130000d00c81c0c10040a843c01c4e9201c1003098001711030036000307024200204992210014060b121078000380442003a009a11042d038000c88000283c070606070404a10451640300c41d0101401c0340c1000d400b0b0616000b600a51f90381d00c25100690101640325001401d11b6801c440c42e4207540004020303588000940d10307058400e4100381c29610714075a403440002031000d100d1040081c15446078028540314046824040d0906109840042c002c808020410581c200456003003a407840ba600c80301c4015844030300100b401000385800c10309462000203400ac0c074220000070041340d8502c807111440001c62a6134160500384c0110703c4203c5030800705120500024a0034071060070009000c0001d041110450f800007 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 583300881 1250 583299631 583299637
    0x210020d1e0207240605130c08070e060f18060409140705030606040e04150501091505010504231212090405060303190f020f0a11010801080d1b020a080102 68
    0xd8010300d661070080a26010100018441010700325004600f05078413515450715a000040004180c41a02c0b00c1c41e01d030004641c0d000300d015144c0070b071200380f00b40d80207407250008148401c40500440d8002c400503900324030440309220110005003c2608024005100c0c00a41e0018403407000310003000110005c042d1102c00c0944020401084080f902c280251044031215402529500411400300200034030383d1200c104841c1101c800e0486881c9030740c0c4030f080042e050310f040c10541460605080c00000c40e07035415001407029000d15103001883d541e072640156120f10861142c40718010080080b907664104503180e0321f24080d030150008034902c840c009061700b010b0b8100d10109200d00302090003415400c0a1060350f510950680007907260000045501c00080d003018901d20400102c4204804c0551080c4004d020450741101150389084580c5000084415100b0149001401c2440001641d0700001039010b02c070700540d280c41d4600410404960780240502d00140c3c6c0001c001071000420060900c01 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 583302131 1250 583300881 583300897
    0xc01030506150d02041d04050304060804062c0705010215040b04021807020d02010b1e040c03020f070c23180702030403140c01030e012c0a05120a12140f0403021002 72
    0x181d80d1406c0101094004601c1c86090551b05c03451410040024400801c41c4d081c4c0301142000015640d41e80340c65400b42c581022100020540c110780e200329681e8250700d44011652080994035000d13121001280e44801100f810341184110700b000c140400e00c2d4031031aa030854005003031094180018007140c217030444240c81e401c00590010035140a00d650a11070520b200e201201c41804252880039800102c0998000359885140d4410800e04598000d0703045484c02e04075224013545415480c1043d411811840c070520548070100c0052540d2030071130001050717984100a02e10595528120559a80031100038503980c10b5120400c004000b0a00c10b0025034813501903080105036190200d000141540d441c60f0311180380c1d0b814100c0785448191400d401c81c04070b00c00355a0802200741482d401c0d501d008039280010f806401012140005c0440200040a003030040d42c40b40c0a1030b80d0341e00d501c2000c50305510600d05500440c0b1021030811940f00f4078042c0c00500a10460340c2800140d64035004036400687c07 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 583303381 1250 583302131 583302157
    0xf040903050a1b02060a03020a0225030201181d04080c060a05090c041b0c0f06090303050f011707210c080304290a03020a090f090504060513050c0103050615 69
    0x142d50101d0380d50110403203480c10f503849001c42d103415141d03010440b0741c01004520740c00e040e004030380816841e108114404070004072090f0040d41100502d154843c800881c041640000c1080504800c040003000312441122040003c8601c1c0b09400799100c0700340c0700701400031110108200488408101d04111860080d0300503040001c20f800c1510643d0314000c033380351816010307a007003090000521800f4030540695000b14180103244103510303d040b00f95140050b1000342130301e217030080b45001e055040d44054480d6220842505080e40ca65100114100200c51080e8441e84801d00602220204a8824401c10040c00c040c0c241e0148513920828010090380080c96641d2002c2801c001d2003080d08902e5040c0c2401d12548440901006500003061142051540134150006044d2003400c0c82504e509000780004000b100c42c064a8110f0303840500820f5400755606400e04011808410200803458112540a4010101e40e03d1034001540a824003d218a0b405101040c90460002e4620001c0040784400c036 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 583304631 1250 583303381 583303387
    0xb1b030409022106010e091b070501020c030408120415050906040905160806010f1e09030b07080910020a081801020d0609021201080109080a03090c12060c02010b010e0f0d020f04090305 81
    0x8180041940f00078491410014021069003664039080807941d000f0042d044588010503078a02144520300c12004010700b00c1d8400a814010208007002410555a900f01543e40740303414885442141e02880c01b951003414000000d03504018002d100801d1100e8000d0580e5080680e503020010403030700201c1d804840c1c01000c070a1102e40d164010303020b50f44003200b401c1c220880380010000908045001c06081c0d0040c07004104c045201e80290004001103a103c80d0b451424641032000070500c04040c0c030010aa80704800908980804034001d4030700c01c00319566010b40c9695903440f1100c1b6020001e03010405035508211a040c03c14490080e000038100d100f90150b0f450045425140745c0e01ca05a0040090b6403500d9404000600d10208495a1384403e10300030503100102d0800030382c00c000540c004001e480400f84640d0802c625500100d200c000960000c000912810005455610355803114030b80c092807014a00503503240540420000300e001600f4105484813070b1000c01d040702d0500a0640c0403500c08 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 583305881 1250 583304631 583304677
    0x180a03080d0c1d041e390e0108040f0b07020a0201120501030f08030a1814100e0c060c030f04060c02130c050a1b050a060507090b040b1b03040902 64
    0x1a0050108070b0505192150402c4a50182c81c0390f0380340102c500b6803003036071100f03000004984101c08102407216610810000010306410310903450780d064011400011044203c5401d1b10b40148524940340b5094980642001d0480011038003000003c1c401c480036018050b001c3c011610a51950f44246c009030001c14203e289800003604201c040b0100111540c1000014800118500d2086548551004085481e52900011007000d45042d4009461203004030440c1e800740961035100e000340300900c000782c40301c10100360000d80a941e40301c0c0f20943c043d0b0050800e202c1908100001742070100019050320300b000d144140d00c2465501079403080300080c59a1251f0302c10340c94801d440c4000058824410000d1b4822214003828601445040c181400040400e07039040c0b40c18072601c03e1140e81e00600f9240907103c640342050080c14140c5600001034111000413444d50800802ca500b51444c1c0c20b207041c00c107007042403106041071400e030001d145030006004c00622090380c1d00140c9800405010004003241e10 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 583307131 1250 583305881 583305907
    0xb180f01020c191203020714010219030b030114040b0c07060204080a0201020c0a0e010302010810150c0501050907030302070302240a021f0b1f050c0d0804050607020a0206030a02180a0308 82
    0x3d1030349524010a0911818030018040d103144d41101c0da10b5040250301c4100d617082c103500014107181210059400016910991941400c060b03003c4074064a040011369012001c0c14222107228502001640d991400300f004140d5001c0380d1944070031030034181d80c03804482d655044140c0c0c0155000c01d05950000b614242150b030103004002d003410007a6512006145000120900d01b0011302c4041c2c140480d141c041502100102160400f41c0f00700350f54041618178940740145410307140c1c1000c4c0c1c2c03d9460319000c212100c401059880449400d98010601c03c3d04540801101700002e103114500d00402e1156030900f82031200c050628100d054000c1d180d0348111461b0442025301300844410350900d4060400820f981d28041d004124001e816847d45840c6902c0d800d503824481c40406508602c03c2601159204e0361042116104510500a4614580382c0b00c206aa4544400000a511a00c14400954401400da0103403a07101800755a4603120710340c28000c500c00c00a250030a8548400001e1241d60b0452 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 583308381 1250 583307131 583307143
    0x904170c0304032909030a030e0106030602031603051005030309041a150703080106051204031110060f0314060c0708160f1a0609071e030b1f090618030b180f01020c 72
    0x1800d00403150061030042040782c0caa1041f0b82654041c950f441044400c001d009600c038001442c1e110400310b60380e0501100760b03910306140b2031100740040c0c105400a055401c00c3c420680c222030010b8025800c03d558a420000500410340c148234528070100c0700200690b0303402c1d00040070001680b1145540b070056040040c00b002d816040031040c4a82009030341c100510f03000302c07030394400d8052800c2d000801d0140c200302e081603803102500580d02d007449404100c6031307041c07034100d0f0449110b0b14901402465429010380c86041c11503050440d28000d21000f408142d6000050000305104040d09941d034085603251480c40000c030a094a0300d085000a0001c03002d0800106a0082412030340c00000e071070104001818413a41e01d010005860721a1162a031490180e0080300b00c01d03000510411804a20442604100b80072420600000d140540000303540d900030507101d40706a0105040626917800c40e1103001490f80060004854100c84041f00080340c20306016110103e40300100161f84c42c1402c00800707240c50 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 583309631 1250 583308381 583308443
    0x140d0b13090b0f1f170d0e0609060f0d0f050a051305061614031509012106052203090501020c030c0604090c1e1112090904170c030403 59
    0xe00d0040e5038400b0502c1108619885880a40d0483c0203a8a600074014084c2c40d0740254881503215141c0802c0401c0c07545030020340b03601c0b46801c58003582c5010408407024a405404143c015400300100f0030b01d41010b00c01400b6801500025500c0c0412070444403003210f5010700001456039490041c400d00d00130034010385800c510070116004040320b03681c40340c039112440500751b9001c00024000f1b140900c5e02030103420001840c1600c004d901c91400c021540420301810442600c40d04600e000420300f081d46950213520302a50800e4450b400103541d540340010324000e044030240d2421200c046000480080002044d10b110b55610035810780307080000781ca0680911040c2d880707600900c00e4111107440b03c0707090350104d8003101404034440940c0c031401d8400031040b00024400d862294404a1030b81d801c041c080700031034401400c8404070f81100301c5a60b00780c050030018070b80c4900c0d00c4000c540402c41014000e6040d031030000c04a4603050f49001c4080c0b41d540079074001c540389005511400b40041c24802c2e565541 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 583310881 1250 583309631 583309669
    0x30b040501180f06170307020a0b032419091a0907120b0f060a261015090f080f0105130203030324060703050d0b03012901140d0b 57
    0x5541405071840d0380140c03110182c01019a0b940e941410850300c4d030400001064140c0442c0000e11081e0011600c9a100d284142e0281454801c0010900c9d105000c60740305604401041c7d91445890b08440080141a807115500610030400120007015405840000f081d801d10001181d014058080c410481a010b00d584076a0600080250b002e0b00a0203c810007990b41030001803085007140020680803410038100d8000d0300102d0165000b581210844180300c14454110040d807110320160f202d07221041702d110f916079a4030941001a0099040c1c1c5101040c002c0c101118020303102e03030502d11801c000e68000769650f0302080d8a203174801000c0c0b154035003010056140e40b800c855190013203540d074400a8440d0907c581c21b0122149100c0e18540c02015640d03004244d10350b90026420020081e4000c1c1e0808010715141003020070480c42d0503c85ca0200701603a400501c1d010f01407502042201c5561400c02d41030000e540744c1c0000d0b00210314010004200039a10005001c203204041c04041d4980700310308012 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 583312131 1250 583310881 583310891
    0x60914062d01030b0a0e010324060b07120201020c0f030a0e01020601140904151812020c1e030c06040803071214070803041a0f041e1e0206042301030b04 67
    0x1040008480c0302681107001e00300414540d4903080407070301c0c4514aa0017400403181c07660000c020403400c40c942c0c042100c900381055680d000d001003201c040341ca180c81031030049001003003420001080b40400340c400d08024000142018400c8100500386104080142c40c02d80001601000c01d9410018204c02440284010b00e040d41c18520101c41854604080c24400c40380000064100f0038070303041d0042d42c605003900c2884905448030780080c1030810303004111414544003845801c0144000b80110854070003d142c0300580c1b41b1003070039081c500800070320b0716018040d01c1c054100780e86035107001348001c0c140140110340e10070381c2c0c3c00d14210700450200c041c0c0412080204003059201448144d03140c081d044464503a5a0701c8a140c409a25020813103403810380c01d035010801003241482002d081c41203000e40d03007410115200710441100c0055018008044940d0003210140318180d40340001c684603c00343c10a0f1415468449001c04a6000f03802d0720b400e904000d000080b1540c6c10b005a2218260990301480 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 583313381 1250 583312131 583312189
    0x42906040507180b0d0222051e0907030e16030b0a180309150e09090303060301050c190c0c05060c030a02070504094b0618050613030306091406 63
    0x58a640d00e4030544d02c440c14046008024403040380c0c100c0743c4460140c40c40c2003118a10160a51100315548202ea00ca484d2041070540b0200b04c1440c4a000240020001c4016a40b0140150024282c070040340c0c48511400807030f030013241d036481c4040c2c0107540900c0c100509890815010b40544078500744450312801401c00d8180001d41201190050b135110141d6841c140171031a00032200c804c45a40710b01c2d8840c0c0b1400900c0800040480114014003080d4024007241e40c0c0d01424820503c14422400d0b44055202d200c9804544a220742c090403d04c1351030036050031075550001840540014195030f205030000030300525165010404c110003484255014411100192640008001c0c25031000810386044207030040e207a607004400b0840040414180901060851850405d82d902c3e10002c0302c80514214002c10441c5964440c15805607124009001694918100040c10403605000324103258903140b001c02d40025500440c0000c441c9000d18201c00e20340700741000804035a60743c1c0034000c0380c0e0f03a132a01c103 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 583314631 1250 583313381 583313417
    0x1803070305030406020904020406030209030f011104090b0103110c06010e1003020a0b03070201090c0807092009040e03070c0602010c0e10020c091005042919030308042906040507 78
    0x21501509410116225a03035400c1040c068400e40001c944d21520008000c00c0740c94050f0f010303010031801941114450700080401500f281c81640c5468800c42d41032100f0020412940c121507100700040c58080b80c4c411079201036144603000b030100c42c0095040301d8014083c2c1144180c4499104511102800c0c0381c5d461500415041c0c581d41c058020441c6000000804440c000d4000d1580c4503400700c5203080322503980d4041d54840c4a6800340315240d038101310501c51091a035911044010f000c0c204210702d00382c026030810004040220741030030380d03001c140b154030003040105400500401c40754001103104458028004c005512000c5e6041c41a20107820901c05680e0004601da11050151040e107841e0704c0d07141c5013510120b0300ba800154460708020000c2c0611054000c0400b055030345004010006400e00204840a60416144030425508201c2040800c2c800c85106030894003c04000b50031044407008207181d140b40c0c2c407070b110181d0051010b012660a003486155449005441e140800c000044046 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 583315881 1250 583314631 583314637
    0x903060a0e0c0d0b0f1305030304140c150d0b04090f0c0317190c03020c03030c01020d0501090e150a1803080402130209031902130204060216050a05010f1b14151803 72
    0x42020202e000082e42003800b003001800847d0004210303500c3c2c3c9880d140c5000e0000309400808824003c4034a03800f6141054015044611000c0b41d005003401d501758440f600804110b01040c1d4455150f41c0c0c0000404c141c100c00000ca1401042c44c5422142181000c01d2001b071304c00680c1d140454100911058140c6c1d4070015661142c00b031400038000c0080341000c0f8941044903046a51500000402e0b0010003015801000544440d00d0140642d03030741c521501c000c488110071580e48603003080000c84120544030109680c0304610060005801c0080b030400ca56407220100c0450100e08000c0620041d4030304100686010f0200c081c0651500c001a00403035102c8540301c107403000540705d110700801155a1102c941408410001c001c42d161070b03407108000d503940001081c80e044c8031000c00c00407550741049000f03281914410303141c0e100040841e0104440c405a4840301c4400c041c0d0b05042c000000d0b01c0c62001e9164004098014480b00004890140c4900340c081d08442c80907448852050085d2008816 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 583317131 1250 583315881 583315891
    0x11101223040f02030a0b100e0603030a0f050a12091113050402060d0b01020c040e011b050307022a0907080118050f0606070c090905033a0f020903060a0e0c0d0b 70
    0x10305505070b42c10b00c0401e19002e40310380001c280524200c20402084120f0a0075000c44000c203901c4c81ca103456100506840c1c1c407e4045120008000c01c210008650003100100541112403a00303850701420010b05a040f0f618083c400c4ac2e0440b10185940c2291078002041c0d02c00c040034181c10801804c19500007000c0b88582d0100c0500b90751543d00c03d812503030003800044c0803450701400510680301d6003200c00d030090404000c3c0c2c0110003001401030320b000b48110240e03803103404660020003100c4070030409100d080082704488500e54048490511040e02c0d40c40149029074140e465454240d4188a0901041c2c070192214101c05850041000301107042c07600c440d0f030032600a840c516074a5a8500703041e51042c4294114110750703801c3c00381c5182003000000042410140c0c01d5030040758404502c40b0402d584c01072202400e618100503003107408403041d41d48607203500c2402d20310040c9080d628034080790030484100d40e41100580d50307041d6096506001d01c0480c80d5a0000c8a1407030ba02c45066031004010394000d80 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 583318381 1250 583317131 583317143
    0xc0a03110103090c08010b0907020303072c030124080c01050d09020613060801030201030b010503071d030f0f0a02190b0a050306130204080f0706031e02071110122304 73
    0x18020355264029805610300300c0d00020542d81903034031005458003919180c08100d00036915030340050015440841900c2c000e6520f650303403100c0300000c941d6034400d114621244603400c241200304c41d045a50240300302528500d40c90340540742d0310b149a90014040805030700001464105174031900c3c0d26070f808421503484540042000408001c580041500760062007242742505150301030100740c6a800c00f684034122031003680d00b844080c48000046401e40400d0317480c3d80c040340780014000da00c54024141001030350741c01303802c94103000004800c80e0306d00410304000f101d05400405003001582028000c0300e40c507041c4084007400091070719022003268459036240008100c008400b00c0c450f9038810b00e000207140710032002035490b07a45038004182c507410101184840d5100320f10700068030301c1c000c1c0030b07a45000841050196560100543c048081d5004090484902c41c00f14044d0311196520202d29410311030703d650b0340e65000f000c429107804407454400500c81540400a0441008112710680c0394020b03030200c = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 583319631 1250 583318381 583318403
    0xb01050604060c230a0804090c0309020f130e0d0c0201090504020a0203030c0a0203071a07030b0d0c12020303040519060f0305010e04021c30081302060310121b080c0a03 74
    0x1502d00c2903400c0f1845136800f850b0190400c0f14060100b0350300908182c882c007020030044481004010340807200c1040d802900000c0307024180c0010b103400540f00040a12842000c07030180141c1c00c22030305082a20b6409808a40004140002d41d6442601a8007030302e4241c400314544452244040d66078000280021650303080080d000030490710074010340350b0a81d4001c0f030240b46403144000d80821214100c980030700080c070300080e8440c01e14050804110b142d4008621030400c0c1e0808000018002c03518101381d030580f0081000081c583c0f900c022100f031908080c070130505c00a080c41c60040c88a001c04002030101400c2400500a01d550340500360b4100b941120302c499810401902d00d40c115021680140120138030031100d5080100c1220080b1000028005130395a00c00c940380141c902d1001501c0302c0c845510b5101104005040010040d900074a603000c031030443e01c0d81d545100304100c042410880e8000e81c0044400c240d101c103014001d000e802540007030482400700f44e0114500d900f1a21000d8036080c024 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 583320881 1250 583319631 583319663
    0xf110102070e04060c26010506090a050a090219020d02062a03090616020d0c080d0e0a060e0c01090e07120b0d0303150807030f0b19090605040b01050604060c 69
    0x2001034000030618810714460350326260414034001e00b0f844a1702d1000c01d40528080b20090070051840e0300c0b0a1004100d1003140e400c200510080c4d8000702482d40d00031041d0440410a41c1e62400100004c2c081c29001503034408410b84220030410200705408299401204c0350907203d90045812030380444110700c0065101d050000b1210b4a02d401540850850b100000f40311024502040c060720422552603003d44020305000200d83d03076001e4403440000241150011070010710f0b990010003980d85c0c02c250120300d401d00344c0300300f0781040032641c81116519680d40c504180c1400505c820024140309003440d008091402c1114003400c0c0d0f000341080104883c840310100040c50715440440c01e90b4016050056050b09850054000c240c00c64020316901890000040c00c000c0026255043da03511002d46402d02290360b8800c0362030358004c1d0018000001107401c3d02d0302c0404034030a0303054460141d10007062504141c01c0c4440e0076241a00300a00a5004200a02490360800d44c403009003940903074070f134480341c0c10 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 583322131 1250 583320881 583320883
    0x304150b0a03050f060711030f21070818151602010e060709030c090203070f0c03050c060c07061503020913061b11060f1306050c07060f0f0e0102070f110102 69
    0x40d0000340d01800756680482444000a0f080301110440c0c001c45d1442e441e501c0c4c0a584280c1c920360551925070041004d10310000481d0302520030f040515644d203003036034940660a2031000c01169120005040f29081001e1004c454401d0102c41c2c5240000d05010403500d04007a18841004003241e001d402e80640400015100750f0014204100c0407040d15418144101c0080c12840c4610007912811000400401c80c80c94902c2168000c3e2035075200d070030b048203034081c082d00c240c16030850641c00d0200034090040e411606119881c4290545010503940f00385900c0d040c000c0b151803401010422104190a0006880b01c0c4a0706800c100b550700d024142000500c1c0100192009034240c07000c140080c44008100ea03000403684120000141c16121207036901c00c000482c4d22000c6070059081c00c156140c0740007090041d0f00c42078022580c4000720f490026203032a40011b95019205c0c0c82455aa52260319038640000c0c8240020b003294940254644045522981e40118030510041c0491060491070002d681c0 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 583323381 1250 583322131 583322141
    0x150603010e0601211b0206220c03051204050a170d1d060f0702010905031f2013050a0501050a09051908060903040801050705030603030a1404181e050c030415 69
    0x28a1300b44003070fa041141042d201c0500075209590000d0304030248180e0781d40b8000301e170040c070a80c200c440c0c0d403401c1d4400d800c101c6682901c0c07103807e80f50217070522000303c08201c061100071040361900c0c104550311860101803003244445988401d80c2d4031a07030b600d50305d54068085000c01d241511881c1c94441148481100f0500450003845154010800100203140d0800d400281048500036211007543c5552407052580b9264141004401c000c440c140700103400c8900d600544510818154003220b4005085007504c10340e00c00ca40d029013881a4400c1000310b460141c0c88074000d85004c0c40e05d0303818088420800743c03400b900c44c020f492017100f50084040f80506903070440da005141e030404507205d80c18280000c03501c80e0b0286c0206980d0b07509140c0044c014900603011240940000b50083d864140040c004440150308151403e14440b0100030009111030000421130b00000c11540010b0f10541d0a41f400504500102e04101028145020850820303801004d4a034001d40001c0811211200da034002d0380189 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 583324631 1250 583323381 583323407
    0xa06180b0111010e10060815040b150a080f0d090b0d0e0a06140f01061418030a0b0a2301060507030813020d080c0c040509031e07080705030909150603010e0601 70
    0x141c6044d41c002001c0100142d0000000c4c01e01204002258440500030707251050701c0d0300d00350102803580200d40000c40c0b505c00b0070b40c0643c801a8094656008000241b80707503415a201080c0340d03002c01e07901d2030340100038860f1921001d043e00303141c00382503d05401801c0901805c01803550003a5150041d00305036a090003c0140d031a4808420850482c42c00602e07014008107942c00003600040c0c4002103419401290b54120701207402940c242003001f21016410b034140c0700b406040d01070080c80160400104048144e40c000e19076802d01140e40c001001030000303114040d155a0760304944030001000f4568101007140c80954052602c400641e0710085500b140d0240d84c00000c3d049034880c0c10300000c0c80705100251407410340c1c900a03070b0040c9144070100f0040c0c54040e03410311407d8004104989030030b400e1480d580030184015000302d003045005e0b21040000e40010000307444982000400843c4c514255107010750005014524074800035110303010031414001405480d014442d400082805c580c06100c2c080e03008 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 583325881 1250 583324631 583324633
    0xc06020a05040602120c032704050405030903010f0b150705252c16020109050a0b01050a0e1e10090c09081608060a0507170108060603060a06180b0111 66
    0x5884010390050079540705205040050269294141440c00e003038044903032a00314080214180780050081d00c8000880b449000907514200b01d00d281c56403594000c0c244124050405107031100c0d00c4500303160035142e0f0101c0b0545034030310b0300c80840440ea80d24007a0b101c054850303402c2c040e140c403201d1611a01e840d01d0070503006030004810341c01c050342c42d06003082c00d415130300501e00b81020b807122a1140c000c0c52038000122182442d0b50400198502d2420050054600151002184c0ca40a6071161804c1030b180c4038041c2da22440d503074010300c017a040500d0b01034001d1802002c001c2440c94840b046c1e80300c08010341d4505005007110b0021928080400784000c01401e1501e01c01c0240c0102040302401c1790245110758802c80c010510141d00e5520190040c10841e0074040290440740d441c4501c1800403c8000c10701c4003800b40800300c290341c140d8a04c80c502d020b010780000030100c0d810920f00701464480d0050244404c50b0500000b8022642d200d0748000f020700b0702c024040741d0f1860200059546070040c442c4c903242 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 583327131 1250 583325881 583325887
    0xf06020c0a0506060103140903190311040909020a080a0317280e0c090106051b210c190f0b13020316180c02062d100602010c0c0308160c0602 62
    0x5112002c00c4080c06901309880070040c2c5800d80d048200e1150b421604008140c100380040c4624240f802c01c403c4805e14540b03000a841c1040309041089900181c00c403a40596841c525041141805642c041c00740c907200006003040c01c1030341c0d40104508035030232420a00c07031101c1c0d0214903510b404d00c107120000808110140c21000300000b11100401002469400d24410351588074400d0414500d9641a500386566a40c5011146495115041e0b40500c100c040b0344200c0742d0080c40f201c91007415172600b0f010741c801a5500d5041c1c0301280d25207681d408180760040031111240e00040c1c030003134100a03000d501c10402e004c0c07540c60000960a8403c880400b80d010700800c0c0030302011203000c2300c0003415142c08071041d030355852014210508503a8081c258030b015a02c5900030a00b4100305c219500c043c58040440d95100c180c4038040959001ea003520158406a20340740140503070f540a001d0304a4814003032a044403140550340f402002c20401170f0141822002c40303551850740c548107100640342d01e6040041955 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 583328381 1250 583327131 583327133
    0x70b0f0702061902010f0c08060613080106030c050a0603060b0909130212100c0509090103030e030a080a0206010e07051611030f01150608010806010303050405010e01030b0306090604020901140d0f06020c0a 90
    0x2c9031509401d83c1c40d00551800070b4100c60b2405600c0341359000209987c401b8103a40e2440b080c006244c1c0580c07021170b03c00081d00c400040482007400f41a01a40c41005c5100c0028034020600c074040d841e03500913105050403c1d00a00c42d12480c2070a4480b014000c582455250300d44503030740b40384014560750281d00320040000d01c1048a0000a0b441c1d10024802010809080e0308035080341c0b18010f01502c254442c9451004001082c1b040b1400d00c50f140c00101030b955a041d19648003019a4810304c01310300541c0090004011600d829403000b94000c6a6080841c54001184040b11000c541084001c026450102150304075031000c01c8044046c0d02880000c00c0301c03400f4060001e072a0380c4503108d030314000b8510f040042904000820039030304032541034892038242030502c001526030001d5450003d04040d956002a6219903041020b94041d4200c0009401d043c1800e0040c440c0b005816048110410300c00781c0006043e880e20581d09070f081e85c04c690514a06000707460098041e20465181059070320407542180 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 583329631 1250 583328381 583328407
    0xb010c08030708010f05010e06030a0b031e1f0603080d050408090a080309030706170703090f021e01031d0307170d020403120e04062313051006030605060903070b0f070206 75
    0x3d8141c88201c00007651030341e5103100456035002d00e264070507040f90b8140041480c03210143c20012000320002e00340e40045020600440c1618807041d480c2d140c0340d10090303034201034090144080d00c0300c1200030401d211150070f584800c0c0c620f20a422031781000719030755400101400702c80c006840b07926074000c103080466603481161541d6a001380041502c00e02401d0400580310f80281001c0c041e40d00b501002c80d8040d81d40e011b0a80c000c0c07a502c8019180c680d00d1032402c10050341c0d07079207840205c0e203030f00403413886003200c0d03a0001011a190190f81c00b2920340c00c180031050184000060710400da500603240c3c01071000100c078040c1a0b000b1058030680c40c0e070000c00d0100c2000344d018900b40300c000803561983e010070165020803084d12114403a806481c491108080401d0f131030b254210160303c001400120ad5462900e400c001261800c03614460140c003071303160610840b6418002c10300200740032144a0b0034408040700181c3c0f03130941c41c41101da203244001407605140b4106400d60300904e07001042240c9820790300c101c00f = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 583330881 1250 583329631 583329647
    0xc05070507050a030b13030e0603040305032502071e03080c1c0905060904020901050909040b19050f0a0507140a0503070e030d02060f0a02041a04150f0c02040b010c080307 75
    0x1220180901c000110341802c2c621808400c584d0081d0b440071103600c0705030030004100031080702a030401400384040300b603989401005600403882940c8203aa01d1030003001301e0304940c01600707410a4100c980c8940340f0b1500c0d400524401aa800440860204040903808164540060307000404910010a0040760710314040384140140305104c0200ea400450a101220300800e103000d5a58094400d0002c1c80381410103502030100c5410604040e441c1202e40030002c4d00aa800302c0301110320661101c2000700f0440701800ca440e900c000301c20284403606000f0304041f4107140c0140f4a000c2203907100002118148180c0000c405401c10741c420f0356980404400091259008990710000318442a0b0001080d040014620580b41429401f420003a101c246040c000f13414058a5406021380034030010420140c041c1c0e08a0070100c00280513070b92a4035299200364202c030f603180782400b07000140f0a03002c40123400002e45103c00c4d13812180040d162035a14016200b00e80402409007a04002200b0000c80f99044541 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 583332131 1250 583330881 583330883
    0x10e0307120303061712030a0b04090b040507120206070b060a0302061201061e051e091002010e0c060306030a1103100c02010506040b030c0a05091b0a0f0806040501030812190c0507 79
    0x10600549445e5043c0c0d40140c0d981c0042044558041e440882085580c41c01464216030390340c602003902a48007000a040d40c0052000303484014644046c0001c1041c200100402010702c1d490400d800051138000410381c2c0100c660150021000500140031681c0701250384020b5a4002d1a4903140d40d5880e0300c43c5203800090103410041505040002c400c2e91001d050b01c22001607690704e061404510350718082d12001340d03224200c01060207100ea40040c0c3d0318500340c6128441c01c1d9000040d01e24081d0072003481c2c04040620540600300402c00d01c5410740f0081910f000323064110189400c0440b0400c0424074209450038284036252420180784203a543c1904107d00501040701e0074003590340308004168407040811400e03a0310060200040002d41041000d1503405410b1040361110510600308162166014407440e0780007403a0b4800b0300c4440c68006211380d42002e000c0d40c04205544c1180d1302c2c040544190b92000c0511515400050b661064122180419000e00501807200f080561800703031003034201c0e41d0 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 583333381 1250 583332131 583332137
    0x12307030b0105040f0b090409020411180607051504110409060b01020c09010b04230a0311090a020408031608210603010e03161e0803100302100203070f020609010e03071203 76
    0x11030785190b6101c0c50645060740d2414040301800351520302c012003294809601282c1094850718100090381c1d441c420440302604051015507200290700201c4130360003403201c465115000c24040c0c84d000c95000a00400401c03c245005030781a08da034104622501001048990710600300000c480070490b260300300c0b02c2050000c0c3c007100d45035604a00ac025240c1c00034082c000c0d8005041c030003001220741c200c08001c41d08801ea941c0344500340c0b40d440400c0070070640750030503200928058404403480c1860725415520080c40c60085092905000d186900c81c403440a600103a0141020b120b01848500e01c00c4030046411103422440e101c040d20504954440c040b00c0d20ba120394a40728420028020220845101c90400000c00c8407040c1c01d561640e1840344881041511200d0005070400003a00394001140100d80540e003d08ac1d06255104004c1c0050400c103021045420a00407100000d020821607043e0039030460b000c1d512406003200488000020600d8564180b14505000501c030740c3c0000303070098460282d0303 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 583334631 1250 583333381 583333391
    0x31107141507080f0f06060705030c0303090d0c0321020c060f09120a2114010816060c02030c090a0b130b030d030507050d0c0e0405091c0e0d0f020301230703 69
    0x6a010b954448013282c000d03d09504580c0018221500410484c3d40068014412414132030700d900d039240345400050580c50a9071002040c0003011034100403a292501d078518110000e500300c0d59000f04030704024200341c0d204030311130464440030081c2c0d0f406480010f41500c08552051034648154170341c248090b5600030321801900308000d001a100000c407503220b0000d03110301035524801c042000501d460309400101075036440140420b8004a008c22900800c900c070000c1149841c401146004a5019071000b800d108010a4280040c0c8010840300811203086684083d5a901d4500101c05401503401150388000882880001d030003503a40000b000380d005800320744040500c104147c089a805071003150214800780000d0004a4207500048030340c2d43c440c0344c00c507844800d08000c1401e542081c0c9500d007407500603046e01d50403800c05a0444143c0509460400c800c08402000308248000181019004581c5a8104015074400b50021540c0482d02d1494110141c100200d45040d000c05403100c5e00040c0c101 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 583335881 1250 583334631 583334641
    0xb07030f020310050105070203010b06070f0b06100801090f09020307061d0402120f040f060c0f17010e01050d05210702092401030e0114010e01080f1c0311071415 71
    0x1031080d288500d100e03111103a0f42d2402c000054409800002c1c003241c0c51740d2520164081511100090b0048074400c1e5002d0400150520f130043e0f8040d0020803c2c0e002e14039800518200c1c652203981c840c1183c010250008828800c02c00520180c43c005802a4061181d5080000c2d21544480c00b040d000c0c6084940c140e062650b9810002070f4490440c4251141c241100070801c0d0b0b840802d0901d070000e100d8071800c500251150384443c00d8448180c0c8107404601600180600c2c40d0f040080f40d04d200302902c10000d89503041918050341410107025180c0111171b00d00041082181c2044030940304041c11106120a40300410104520341c00032104a000d405000c6c00b1883c1400d042e01880e9410030072103010444030324100c3c011001003542140c06c0c480340d034807520b050740d900014800c1d1501070110716414403800c0d0704104240e840c0500c030b904140d42651000e0300f1001e40b2005041d0429401c2c00394a030100700c82140d5008980c4501800f10003038034024a07007a01c0300c2c0d8200001003400d2440d5510410294541d16 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 583337131 1250 583335881 583335911
    0xc080d03180510020f0d14041103031e0f07050114042105030105041a04090302010b0301050915010308030c0f031305160b07060b0109350d20030409090b0703 69
    0x46600d005009070300c203200c143d030080300a40160602000054682c0d09083e0403007120415500620a10181d12280c501840180510b4404c500c1140300160021441d0581d100d01b010b070005e041c004204061030002c180c0703040c00f4284004441c130503a0004000d1102c0c01280180d170418800c04e480440b20001c2c001c444c0b02862201c182440c00310002500e1341030450f840e01061002910300a45080d88012203120740085695551107801c09180c060ba000080c0c84074454181821100064540d050300d40c040581c508000c1c01108640d810b4903403104904d52030b9215004041d00b5405566541002d0b61800f208220901c1c10350411318000342e00038030850340340c541900c40001e40c0c0700503801002044101085840c000c115070ba040700703d401c82c041c5000101c1c03940d03600307101d64480500c0903000d811090269551580e0800128861200c0900a000d480389108984000e080210901c00740410103542d4846046a80e03400c0c07048e10002d00306000300380010314841ca04000d100c3c20071954070000c00d1502d400c0e00c5031130342 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 583338381 1250 583337131 583337171
    0xf06060d050d0e0310060e071d06040303051303050d080906100e01030f020a080d050c010f0c02030714010608030f030405010f0c230708130314240403020a0c080d03 72
    0x500240074000c8242c12038000c882042807141400e030907101e03024140d84859680c0c0308040003400c00c0700f0322004a003040100140100c00511541a180110802d10304259840714200c5080780d034541800e40d81c829214510142817441d9910150460203001c65080c50983c108054510801d00181603980715501c0c1005106002c5082c011000c0500c81c8100500c00518480040306507070340020480c11f10250b82e14000761030001600720313800c0001d5000c540749504505c2402043c403e1886c0c840242301401e50254002c0d500c1c05121405840c40e4440521414580310a5210001601443c03099a550700d540b080e000f681548182d0b400c0f180e42d0300e0004a840d140032144183c120f149480c0e81d4050300d03d5070a0403800645500e041c901060a50200103000019180f5801044040d480001040880e0b19605085c0c07141c0030100ba0480090b0403e03406104214078030b0000034169080220b81d4081912075003012490425001c030001d1552168000c041408071002841c4441c0705050383d0b050208002c4580210b10000c = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 583339631 1250 583338381 583338383
    0xa0c0303120911150c010516030f050105061e0d0e0102130816030b1b0d060305240f075708030702030715090506060d05060f091e0f06060d 61
    0x110307004480d8283c1d45803811500c2400e049501510b400c01003409852400c644040c1c80d02001c3c042d414588801c426014082c0300ea0450078500204850740c0752501050a5200c0c8440c2021a4440c1d58003880303001c06a032054503118084608204080056449080e000b540104049086080c02d518005214540003640d90400b000012028001615503510003c550a0141100151203010110800d596070742401400711541d001d5400700d1501d2640c14000d0510b102c0b81418050369441c01046c4000c031000008464000300c00301d600050ad50b40d04c3c0c90031502020000041d1601200440403142c0317051b030510321040301d06040800f50100090454054000c109030750a14602c41c00551031580100306540099580a155401628545405507942c2c010341c4000c11401c525140d5100650014802c0400500398000c0040d80c0b0b9040c1e01d0742c0341e200c081c0d40e108010644078411140400103105190284921810b40310a40400b021140c14814083c1d01c646182c0c605920714400c1400294541c984085000041 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 583340881 1250 583339631 583339643
    0xb090103050d030509030c0a030503040b0a05071409180406140604051513140708010e07080403200a0212010204180902100f090806160e10080c0702120a0c03031209 72
    0x1808080b4103801a01d0f004095102e140000e10446000351070600140c06103034820303928180d5910f81031a25030045200030b4207100c0f009140c8804c100c01c40790851151180c0c40c000007081902c42c450840007a002203004141403040007200400d01c82081840e8002c41011042e245c0004060b940d1a41401300326072040b5002e030403841d0032005000300c038244a007c00e074000b00f821402140d06e410542c040c024000095540000003120800100424900d001a45402001e580f4011107681801d0300d0080c98514120100c01d0b40d61f0401903e2200c211040095121140d0302902a0403c0112802010f00135002442125500c84020b400d62800d15030510640600d968000c00424294400100840780c40000503081c50600c40c041001003050001002034600c61028000aa0744d11500341c00014643c40b40c69052600801015560502c0b20350031800103903004521140b21070700c2c2c0b04a4000107032454010940000c090081c1c500f8842800041400981904c0c001d4446900c080d00704000b171822075540032009045 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 583342131 1250 583340881 583340893
    0xc08010501030f0204031a04120c0809010503072f1b09040602160506040c051f021b0a0f0821030f060d030c080a0e1005070b0c0a110304030c06030b09010305 69
    0x890741c020360207a580d002003003e005080a850343d40b8404c00c0128412003201441d036460400c001c120780a17030300c84909074061402c0c0c098500503640d075a0b014020340007441d040c4000800003850a5200d04001400c501016813510802c1c01554030020345400d00107400380c854041d00f00c9580b18040402d480d03004a1a0282c8004d11943e50f9890324402034101d0f500c0d80c1c6903400743c3d0009a010031030030804d15018a0041c40d442d020503282900700404001001d00450071903980d003500c00003258001c00c040d8500900030301c01c002005004000501c2c59291134011007c100d581440200b600c550002d544600c00c2c1c65455000500b813800001106640001c80e410561440071400103881420300c4110300350141d105e4100340c0640b002039030750b107615504204142c1002a02a60002c40207190540c101130100040d414400c1c603240458649140c081c0000700b01e10303580b2074000707080040944a214034442031030000080c1d94680d5120700d41541d54501c240328081c000303404c11070a003100b46481d07040d0798101d03a800001081 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 583343381 1250 583342131 583342139
    0xb060d0f260903280206030103030e04060626040c05210105090304030503041206151d060f1c020f18010812040b030621160801051026030424030f0c0801 67
    0x3909070313120341400c0722041000c00e0280042c0c4840c4045c50280d8402d03112071b00703441130401c10f020469905602010401000c0810201c035080c005914490040d0384210f655a01d40d03441c203144650300816489245c0020889058842464801004128601264000344080e80b0380c208007560340d024030702024100c1d4104201c10480f401d0410594100a8820b5801060340124000c3d010110102c540c480305400010050080014585042c0264002003c440030180c920b14880416a41c680c8045c100040d42d80c5848848155654411502440800200241c400360652030603460041030a200b262002d2140020083c0035800c40d0060350141c0c0c0c2c0c1094800c3c02c69990b4000c002503201c03803403520405440039402ca4000c080c0240801320b0303501c0c10356003003d0080740fa07c00b94900b1500c1c001c000d07504404009400b0b20002d4407200414200c02c0003145003101e4103684501d0141144500d920400c81c000c60b541c00700c0740518103442e03407500da004240c80410096845001220603a0145500400040d002c140180 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 583344631 1250 583343381 583343413
    0x9010608062106070504090f11161109090309090106020606030a080307030e0f010c180812071b1e05010203130501110703020d0501020414120a0b060d0f260903 70
    0x350360301e0b4000b1808007068044140c46042180c144d40050000710009014032010b0124020f250105600c080304002c02402d08650340c0c001c1c0030310301071903510202c500c3c9004140000c1030601290510010b001e03425034113220316038503501e0740085c0e00703540210002000010418004240d0600c6240c01601404010400c7c1c1d403000056400204004181035480340d20303810140003003081001101d101000000c0c021561440600050001e840c41c0024152441040c4002c84e004181210766000c81c0303803101d45230320203854940002486c907105501800c10a43c400981c600703440960364403c610780c03640c40200c242ca500c01281c032407169010b050244a40f9250800c100c0d48504403c015940c0380e00142c0b5811030b141d50000f94940700300503040e06c00740c2d00400d003400070005404020301900e038110703500c00c007803034801507010f0300c9039100c0c1d0300075101da03400500160f03440d2610080109101e40c40540c607100c95156240c600e14001e5941003040082c581809007805d00d00c0c258085407500c84c0b004000b441d03410900c8500d1 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 583345881 1250 583344631 583344649
    0x105040308070605130506040c061d0a09092607111c12021009050303060306060a03050709150b0a02030d0510061409030f0601170f010203160e0f0306150405060901060806 75
    0x20000070000031710760008103005012050049200301201d6a0551400b0002401d6450303900901c1c04c0e0070300320340201c0b10560729950038008466201001080001c0302c0d00b0040001d44000152103d541e0b1168800034986081d10001e1260300d21445102a900800206000b1414181d2510f00300d41030382d4114050205c0c446000480180501d4812990300c0450300781c1c4802a140e0821041314181d0001c400e11902e80303014440903612003001d4514400113407a544030203a440899104c0c0c0c54400d59903207807031070809080410b104080e080154405560303141c000f900135941d610201c83d6810403440e04c40803443d0310f03a540e1018000c5458a40c0c0d041c4000c011445541034617130181102507450700c5510203800a400041c000c4038002c00c101560030034038010b641d014030700340810881d100c00319074410410065820700e02c40c211000b0350000c3c5065100381c290000415a10900c03040c5040c1e0512800c010170030010652944c2e110001015030341800705488040078480090380a0140302e02103142d120000e521400c060002c = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 583347131 1250 583345881 583345891
    0xf140403140a050d0302070303141b0c0703020a0f05010f0314060609030114130b070201090c1703091e120307021305091009111e010915020c2701050105040308070605 73
    0x15250220b019036201450400f1030622a00840d0700445c0c00010305401d403203185600c0a030f80702c8250b100d11748000c013104034805060003103482c4400070900c2c1081da8001c11117980610f9000d450740d100680c440f07031040809030780c0e40f00782e500040c52558094113071842405120080403515468a1040d00d40341c0400a060f08802c40c0d141d055940c50003c2d03000c0300c0112940c20300414512038072070b071500c0301820104c190070701c014642d00c20b680c100350360300c0000b4121019500032a803107450041e000911480d050317400c61041504055000b03808018503e0111844010b90100180448100b80c1c201580d04040c0c3e00c0e8000e912000c7e521400d42d10f840e4581c5100741c1c02442c0e100920400ba94000311407040140d0485080510544030540d03808441005030800422207404111140300d013100d000284800280a60fa283c080c2d00e420040070b03002c0301181d60080010b0b80710b1000044c002600d443c151311401120103441d1282d003400d0680500001190750250381100c00381c81d04241450300c0c00b0019110308002c0c1c440644 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 583348381 1250 583347131 583347133
    0x5071a0a0f020d0f1d03090d0309090207060b1e03030f030c0c060705071109162304091e020726090a0b0d051008030405090a0e0105070c030f14040314 66
    0x7180d8900c810107031000703040314012202d001400b802c9003048031044600d441d070f1400626030100c0c0f40900d007260002c00c3c2c8900803012a84c481002509107400c881c2e090550b44a40542030002c20180104601074110301015075058660440e444c0381441252244041e8644507501a0000c000051204155400869000c4000f051461919810251862030150202d4509000450100b4120b0401017040c05034043c034031040301c85134214101441c056003007103840c0951400307100020803525900300402020b50140700380d10031103644660782d440c040c00180144004691640080c0340f85010075081c00c0c0300f034803115500b08143c03012540104003810b540740700350300ca4411002000d1103401466503511008201503d14000016150301805070003800f6030703d010341164400d000503c81840643c1c0000165030460780c00b200c51100c10789030100002d00070401d02d1450032565080c0410414100e81040050012a05c0303030340c4d02015600721000407241c01d0f085040320790081008000820110f141503101d01c10040c5004 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 583349631 1250 583348381 583348391
    0x705060f181c0506010909170c100501061d0909060609040f020d06020a0e120d0513031a070206091612080d09030908010f05090c0613080a030305100605071a0a 70
    0x100c0000d44a02481c008242c00010b80c5502208001040c000180185441407007480841000d0380c503030a00a000e2001e0340c1c0c14100c0454403800d440f000700901d400b5102d41400420442d40c484400a02d8100200c0a5899105400c160700005040c140d100300d200d0b1164501030481c1c1e440d0003040140c5c1c24030141054520a040c88824005a5591910810514851040140c4d81c85102c58054014001a50072901c036220b60000e5a00081002c181000301176a00c2c074102d030b550325420306108907805540c0c0002d44a9160610f85441b0602d44501c000d020f0101c40d022180c0d00d5450179074640d5101e40140c4010456819420100600c0e080c1c00290124a4070501c0e40a003041e44c060404002c68205103025800903503000001c0110440a2103000300606c8410b030144203d18002c0107290b9500c410400c0725002c3c06002844921591241c1a071401615860096860780110b9040060140030191003021485001c0c135030005440340a4021200080d910020700410403520707140303103031b08010000e048040e042c1c1c070340c = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 583350881 1250 583349631 583349677
    0xd0f05010509060a1d0a0305031f120303110a020a08090604150810060c021806120601090b04050a0509100c0201060b0a0302271509030c061b0c030705060f 68
    0x280107080c89140040c0080c8400e140c0040c1303007002d45805160045801034502c203500e05203d4003040003c51103405082c1990341351505043e005e8110250030700001e500002d1440800c952003070300c1c80740890038060740e414040c0303002d005030002080c841e810061026902c07510901000444150241207040801094681442d50366039406141802d10704480c00050151410084601049042c4030301800803071030485002c03105640490580c8000314404001207448100007041952030600400428201e681a60340c44d59448140310040c2180ca82020702c00d13030814000602a90051140e54480c501040040c0200081c095141d0014041060203004654848401107006101c8100608a01800740d0380182d440e01030741440407a150600b42a5503040c00c003004140c9144d640c0740c902c00103031955280440d545500900019103011100546207422100102d440b80000c01600d0368900300c00fa56505842d40b4103c2035040544411881c0030b699408a07041c801203880301d68040240070350018200c0c602140c00d0103 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 583352131 1250 583350881 583350883
    0x301090212010c0801081c0e04060f08160801090209010302190f06021e0d020601170a06230615180f0901030b160e060d02180a09050108011d0304050d0f05 68
    0x446544805a034565140300c601c0c65201c1c104e00d00400c50302014025542901032100c1d9540c038079050110810420304800390441e9641c4d070000380145401204040401d40c0e176a961915120600849180c0811601002815040c1070061b000c015038014071160b5261f00315400c1081c1e250311503c0c00c80c0c0d0f08110000115845603c0508540a801e0703a400070000c40c11030510b1245081c5010100c6110750304500d541c504402d80001c0c1060544404c80ca03224802600031191074076080e00d0100c0038102a0800071790f031200e8800f40d041001d0540141d01380b0102c580d105001d12040c2402c0074400c505008007041424541e80900401e0309004000407c612051781c0e4400003e50201c0007038000784c0340051032106004611032050500d107145c011034205003c0b01c0b000c108c00039429018034490702850030340000f0024843c5c042d0000754041000c0082961071600e8a80e1801d00003010240901c4900358038010a051125410604100c02c01000100461801e8100018050b802281316400c0781c000c40601130031800190 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 583353381 1250 583352131 583352149
    0xc01080c0d141929221a01020303040b070305130501050f060f1203030a090c120302150c1201050f0103110a02010506010e150304200414061003020310060e03010902 72
    0x1280c0e40c1a095401c3c80c409100c000320380000c8000c00a468811001542d0b007521000040741e44000702400251407952002c510300500c4c040e45c003880c00301440c006102c41061a0320030501c3c4000401e5680900034600016070b5a8442a18003800803500c1d240040c2401e84280c2000794044014041c2d00103103880c035a00c003429030f00f040c5c2d0602c3c94440080b04200300c50800c003440e03c80e0050210b450304140060904204d490380b00181c03000b120035440704a00030502201071a200c005010780003004141101e1800c0007920b41010f00450003000c6103513404280100030310401d51310303010328002e040c02659180a040100d1040c548440303605260f2039078802d8500508a81c080c241001950b0000310b0580350a5000420043d03440c0e01d8144140d0b845015550400b1910080d00e9105a100c000d60301c2040003009803010300d050409600380d100d41030001502180c04038405680c010842924070000d2404002003e40c180d000c100d40b0800c050400000401c0024441c06418141000c0940001100446500410a402 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 583354631 1250 583353381 583353401
    0x3040b0a090e0a022704090b04050c0315100521010527061308030406091e14061e0703022214030f03041403120310050901060905030c01080c0d 63
    0x341e4615410403440c001052501d50200c9020740031484c03c07074100071103406820400e03031200c43e000801e81e031802e440d00c0e41e511162620f0340002c44c0c100b0918261520300e5507051201030303250280c0101c0f2428810719004404803401307049514141203039a8100707414031070085070301e030940c0c1c1c0e03000042c61401e01160340a06c0355a004010380c0010300c036046079074500140517030900c11421189510803c1040329817044080c0e4040d43c59840740705d059590b100d50801e10040c21102902520f0003a000d26206004044603440c284814400c444070b00e2aa0b94603044907440321012a8042c1083c00950700340c081b84a8941f14540c1e0101d00c5040050400580001244508641c0030a40d200d0144604061001d0613405001c1981d803101200102a065030070383d4000c2e141e0189204021464088510b007810a40c0d00703104080c445000c03801034980760702d0002011100401a44100b0303010314080d07000803651070302c00c01040042d9070340034006200c0d608605004507000c21000b440038500f43c0d0180304442004c0c20b1802504000 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 583355881 1250 583354631 583354637
    0x31c091511071505030423061501090906030215130e2a0310030b070e190501030c020706020706121107030c1506030209150409020a120b070c031e0203040b0a 69
    0x118410a603251410100d074101c20350700c01407410f20015980c0c3c090300301ca6029074450000720b40110214070090202036503100b003d00c2401640204030300e0f80303020803018441c40c9007640c030088244c0d940c99107401150810700000e500701101c841c01c03203c9400d03020300515160038802014a80b00d55500c8101001300c40650b07104913003800c56941000e464464507081980d030a00c0b00547ea1850030409403150310001c051000500070420b20b800039403464002c058402101501800f0318407090700d40f240513281e1150074081c131fa000c280f400300301990391440003808605491580d0024407a803410410240c0c1c0819000c1245410541c41d501d41002c038440d91000703032070050710030745170103c07410303240d00c1c0030010745030030b107401250380c40c5091000c002507510107070b103950821100c00083c800c9808050104020382109400039400441540c80042c0503250b14006a4090b03000740700d0117034213442e03500302105c000303000d005d014000075000c0c240303240b00144d1105020003020990044a14007035403290440040d0300314010407404 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 583357131 1250 583355881 583355897
    0xc080708030c060f07020618010f020a0503040b10030f03030203060f0a09020d0b120703140c0a0b041a0f0703031e0e0c0a08070501270308070c14030705031c0915 71
    0x380c410401400d42c002644c084120381a180c408002903036450000d1502e2002c0d802c0364907800404000394000180d4452027602503581d02100c1201400c258426941141c0501d040c20000c1c42c096484840b10054983c0a455883c1d405401d4500b02d01940001c0e115070b902c20303000740401d8100e079540242c0c0001403a004a0160b242c4408100c0352084074030030615180104081050007045100200300710342642d900003400f00280751004900c03440c000741e029009070885540034000c1519110b407000307082100c0206600304038404001100c441280180c01c0119100e010511009002900a03017017070380c1c854900d00c1030f210020b80381c80d844002c0d607008503c00403090b00001090365036820b002d10140040e00082e4024034409241400083c0b900c421444400021071350340f500000d226080820741e81c01145c00c8040e60340c07100320ba410007541170140e6214100760380c55103a005010909001c24280b0843e41c2c004d0103130603850b0345000030700010700440320042c042201d20301000c500800c0d0021400607c203459910111 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 583358381 1250 583357131 583357147
    0x20904051207230f0d11010f0c03090b0a060f050d0303090b0a050a180b0a0b06040b07030504050f010806030d0509010c1407050a0e040507090f09061407030605060f160c08070803 78
    0x14880c0d10240e6020180c2c112400f013004881c800692601d041d001842d101c0820009038443d613004222004041003800d007041d03001102c1a5141c1c100c00d41c4280111284100d5840341458a012500d103071080308908402007008003c0ca00c1d04140001d83d80c1d020341004118a00180c0d210707030f03242c0c50841c0e01c0c0401c00c0d030710014004000c2c0d00b80302e9050600507009100c010300c511a203800441c64002040c45030f01d02d4581662054039250007017618010422000803070f445030310b0ba140c098010b030064022640950903800d1804401d40c45200b03042d01a04c40a400362a00a42e580b1084540e98401180181881990682c03540022400608200c0300b410fa0006041031504103000c0010309e041650052000c822a07005004c0460804600d00d02125849000091070306110a0200d002d8005e03404058481460000c00e510002c15005050348141166a400c1020b1501d0340c04019050045819041002205002071000600400444a40c03280503640f1080201e9440e1500e9141c00b41a4002026640010420740 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 583359631 1250 583358381 583358423
    0x5101406010c02060d050405120403060f0507030b011b02030313030809041a01020715020a02090103080c060109021e0f0d1107050c0307060e01050d060b0301060203070c050303030f04020904051207 86
    0xe411610074a0034601d44581c41d0000fa1450240b01d100407030140d030300c030042010020104904100c0f46500d0300742903101c030342c1d0f410003100900340800c044d102d15091000142125120744659500d02e0f50503180d980b0512100083d400e440e006881c8102e80600c4100440001d00301107440b00307801144114421943d030103182c410301060b41c5c8520755596034164800c00c46801c6030780104000f010780b41c08600e0001d0312412248206d160118505010790000d10f181c0010040c0901d8400a2804070000021240c00341d0340c0f524003004a00c101c001c104418001071079a89101c1000000615070307400442c031601c1c101940d94414100f114181410b040302c8a8001a400f41000000d100c0e2980800d800c50280620390300c0e1a0b000303082d490318070016a040050000e0080d482d0b07481c81d070200018100901d0001c1c0c80b5030315508081d50780c1e4098041901c6c040030310b03240043c180c50004222881411342c01041c0d049034580e6403d00c10080b07801343c0212844d0281040004404140310054a2024002c2641c298401c00c1c6240d0702c = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 583360881 1250 583359631 583359671
    0x52a090f0a061704031718062a0d1b020601030506150f0409060f090302070501110f030a0e0607050109201009231e0405092e090510 58
    0x49800380041e048100403054000c40809680c0854600d4a045640c2e103283c2141c4000017000100611001001840080110b60103440c11035079134841142c540b0b841d410340403008104103d901c280100e20b0b00010440403403000014214000b034840020880f030041390042c5019500d1441100c005910160041050000c100482170b0090000c0c410501241082c81c08580d9042c00d5240060085d0b440d0400c000400c019907008001d400c0c0c208500f000005035900d0001d4941e2458815140059803400d10188405000301da80c851001c0764038025480c01d4520101a500000421129680b004c1c082c030104022032800c3c010401030031b10440c901684104458004844035001e0045c483c010000b0503038410302c041d008000002036440304e41c0242e5a21003104d200340807009402d85040d03046454000c01d1554050640c14240102c0e5046905200903a1000003840d0384007500c3c45d00e2010140461203001c00c10b40a4061180d20102007400807a049030300ea21503034030342503042c0e1003103011079590a0301c035000c2412103c0f0 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 583362131 1250 583360881 583360909
    0x32e11031e0c04180b0f091f1a04030609020105040f1502010f1a0f0a1d041203140103080d1b020d0905010503192a20010c12052a09 58
    0x2424603040440081003015400c4004134901c2c0d80f661040c88554403008000d9071a040102140e00d02d20b003481c0010b862800207070088440031580c010103d4038418600700303501da0041c90b6548a050616580301c00010300b54140059060001c00c0101060000c0340b10005006442201d01000d074400000c47d000382151040300d04046140c8c584601c1c480a2503002001d94000700c3c003200d4000c0c4084074030ac006a550300040c6e1207403400b0919030100b501320020003c0140d200b240506101d101f05800b04400fa01501d4052480f00004101c00005000080051010b0b040d2603810101c0000c10b0780119808141080e9801c00d2100580d200c2c40c200c203602c0d6400104280600820300c0d0113402d50900c104140c2c11460200350801e50207889034065a009100c00900503810341c2e02100c94503008120a802410118406030170502404108c907046481100500400f8a548a140d81c1d56040b2034094008100420002e04151170443d000301300301e00002c0552541000750b070320314810565680b008134108116807a00140e = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 583363381 1250 583362131 583362151
    0x705130b0f15130602120304060b12011503110a0f0b032e150c1e020111060a02040617090a0212100c050309070f0e04020f0d0803040c030c05032e11031e 67
    0x10301c039540c0c020720410387e83c10a40c010300110b4803000090000b80030340302d00303d8500307503e620b0840401c0300c03403c4226442c01140d0199480101c11400740051150020050240c40c44201150b4020010441c075603000f1544000c030700d03214801d0b5081c5d454280c40f10708409030303091680f050440c0c1d051040009035010040e0b220010306005150508941e5451580d0f0000540e440c1001e0590b13806805690142c02c814508100f2041590b11914011402c2c40003074005024402c0060030440a880281440d0b041e014080c0b20a20700038a03a84403251308014491001c5030005103c1e00583c2000c1c0c0d940b80503801050440c02d01521040d40f03d1030058040c9103040116440f98803018418441000046000401a40c04c590141c880c94242c100c00c4000c2a03119001c5480104a84000400c00c014040c5081404041c0c900c50b0304001d0744a565401056070f2038030010999440c1180c0355100341010301202142000418643c503000c180304403200d000300d400f90802ca03000301070740741d8004c81c40991900c3c040c41b456012100340 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 583364631 1250 583363381 583363393
    0x301030506060a080a11120c330c030409050a0204080d0306081212060907180902030a06090603080d0e011805060412020d080c03101503020a0f020705130b0f15130602 73
    0x1850b410000d030001c6d148640208280c080d00c000d07041c8180102e94807960041c00c0640d0817004a000c0b013003c100c00e03801043c1d1001041d150041072150755001c881211800d0303070085092505000c0c01600400d0702800c3c2020b4181c1c02c000011f9040c2e000d21088100d03909944001410901c2d111546051100c1280e0603481140100669016a11030a400d150429030584119603640c2d21041d080e2002e0306010030152405041071400103404030281c000354460382c0c1c949400d01400d580c2e004804140c541c075000003000682d0902c95a4480c6203190f2010005200400000c00c510b04641581801c00c298a04d00361081d4101303d0800043c803545010700e0800142c90310080c0520140e01030300510310000a05003000c040000004180000c09084811001d403006026041021400c2040078000f94030490290f008100c004200b20389440c00070944000301c0e5000b40c403410705e181c00c0c0c900b580001e1443c0d140ca01d80c03114841c1c10070314280c2c480007180703c650383e40840002d52381c4266203400c0c002c010701e9a0000007154000c0f = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 583365881 1250 583364631 583364633
    0x4030e090606120c070503070506090c0603010b030a090201020114091005060909060402010f09030507180c0206060a12030c120503060312030420120d120c02070f0b0c120301030506060a080a 83
    0x1403c581a5521450600d01a91201800a440c500c80c100c400351040c440881e181090002c086213040c003840ca014100c074000c0d1010303420302c8943c4c0001d12032410180d41c01e00014881d007100e90000156a48140300000c0c40c2050001200c2071a034050750201000d03032045071104207440813441000d40003d011100c0c04002d203448000c440c2da428005000904000ca0105a100e00030301030f42da54006154054140c0c1d0016480c0d4900f44240701d03140204803500c03424910145505030020034400e01824001c2c2840c2011400c1c0711821082c44101d170f00031020440c245100601080e14110041c110043c2580d0300c0340d44e420001e0401d0701c0c020880700070050f21841041400006003084000c0f00e036141840c1c040c003c039040d07084009454140360000c504498020a0400640c9a5004403801102d690701071003005403040c0070104030381e500014040d80c81d150100c000144040c0c00400040d100241049086038100198240402016082a4030441315030f0f001c1011b00800e4607092079150b010f080448000c0c00b4080c5a = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 583367131 1250 583365881 583365889
    0x13091e060b0a0c0c0e090a020f060c1510080313080c01090819020409060e250605032a0706231e06030c0d11040b030a050a080d060f0305010504030e0906 67
    0x10a41c402d03040c0b0141c40000d030108030307040c503a0100803c03805008003120324082030450344849000c0c504034861405810015801c3ca40441a00c900f182120010035003406817003c001841180501503010a05020b9000203001404200070503400d0302c1d004030795203003910f0007101d07501c0c000d0502140c81c10310031040e60a20465000144c813050138045641192070200e61400403c00900715104060710395070500c0c090820390040001e00403060031002c041c03d00700d2403c00010030603550003030095100203081040420354403000e0b200c0900980c001100f038010519a4080081d0391503001d410201e407030984591103030800d081080392104000e82116804105803803c002000c40c44007003d11140584590070700803035106d031403c1140701c0601001905c48046081c1505005c82c5a80000d60206c1c841da0814410702154200070680801559128006003c0c0092030740d18040140c0080703010030350f000e589031400224003c11140c60b000440c0600000101070400e030400402111004260301c0c000c1c05241e042c010181c036 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 583368381 1250 583367131 583367137
    0x1051014070318030b06240f09030709150f0f050604170114070c20090f070c0f29100513060302060c010c090608071b020613091e060b 59
    0x20382034000300e90700c01c090300c1d0581c2c0f1410250752440054100c001c0c0071080040701c400c2117010744030858080700708000c2c503804990a8954807111a010080c107014000700140c0e060040c210590009041d00c0947d0b13214030341103080781d403800310200d10399aa0100030426901d01c0300f25100a42440203292a1290038440032400500c214412003014446140c44114034071b40c00c2d8030110326243c1500d0011031a042880009110f0850550240d8400d2940752080c8545000742020345004030000e0305210590350b030144a0100c28070020040c60502965500c1f580000d11540403001e0003a10401c40340340049110809000822010340200f9001410030741400305036540100b00c01e003140c4040f210401110614500e031005060b05030b000a420810100f84d1400510041d04098036040c420f980354010941d41d4441111101d109860700000f0035266001132000407000410140041e00190119291a000c26120721000c1e02c47d07032200c40e165039941d8840b0780400b04d07000c09100100648406002e0503080c15110b901f02c0c4 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 583369631 1250 583368381 583368407
    0x2010903050a05011d2109041e06090b010509130518190c150806150904020f040509090a0c090f090230160e150d0501050108060c03090a030c14010c020a0b010510 71
    0x10746c04112609141da45412103002030000743d108107445000c0c03041710300103400e00b0700a940f000e41c203101c1e5003448d41d40300d001994900d0f4401006011074505014050008080c0a401e4a05800042d008519600d0080000700600c000c0c03c08140e1500b8118104100318015640049940511380c40c4051a1b07070341d0001c0704a802180031684041056180c9060074068400d1100250700140045004070480c0c01c0c507000780007102c10030b0310314503896a170700551b00707480e90003003800240074042030700c5e0510003040d4590048005580003900010303103404c0358001918504076000c2c0006482d581c000480c1400d2150302c00300c00081941d0000f00900300299407032080c0f025403405030041c1c41c21020700144409002e41c5080007410320141500112000b40c2c1401c0b4007801d002d014401d224452040400c1178401036004032481080e4400241410a80da603900315005010041e007990320407504d070b20b065090345007849a03003003103082034008141c80302c036910f000d40d45039505a00c9180b241c80c44030950034446070481c1c50101c101d = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 583370881 1250 583369631 583369693
    0x20307031808100b03100c17090d020d050c07120f02240a0e0d0f05030304140c0609040b010207030204050108010609050f0606191b062403020f010c02010903050a05011d 74
    0x4c05060042840e00a0510807282418140410481c500f42c101107203504200a030700b051500707542d03182042590340e446194501c1c0164800600100028070941c040c5c0f035800690300c2542c1c0f455a40f015428aa95101c40090b10240000011081149002080702c0d10b41070b210f00b2610300111511022019030700600d140c01040c020f05164120325641e440c0002c02e4807a5000480000001c1a030504a03520f8100321411520705800118844070003a0001e40200d80c8000101100e180c81003c0e000d0001801c440203199055204824001c00140d8032801202d000e42484000020b1103441c002e140c905503103000d410407882903000424440c15445510844840011015030820492034101c000c9580e03030a43c1007641d481c070740c42c00b410204125031900070103088021140036604501e1040390f42c0b80811050b2000a41c80256100051203035401502904a6a03005040c404440355480c0c49186c104440300d40100c0740784c0d640780e107419000d8000070b06d841c1c11200c0a034010142041c0f145540c036008050180e8800f16 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 583372131 1250 583370881 583370891
    0x60106030207050f2409010e03040b070618120905011403010b030c21160f0207230a08010c0201050c04080624190509010b0a0527030d02030703180810 66
    0x1480010000001c1340c2c1c0d80c60f000c030f403502c82c00c44407041400101e0f10b1214072008028004612040d60502454980c0340d40d05000e54501440e00502401c0d0340e00c032060882e00641c0b5031a043d84c02d09010015000900d0217001100034a1507242d5000340000d846070131403814010756841c0003110309d032140103580c10f4a129018059881d1211480410310307000e1014011061a40d0400f52004e420300381c16014011100e1402c81882d03941800c10a072030b40c0c0300003208000140c1c06590200220301519a020030444080c0310301d80302484415001c02d0515045804c244080d81d10b42c0c01d01ca4085030b09100c0c440d802151540d620b41404e04140296031038000143c00740c01c2d080d00f8100001b001d03211140c05200e02140080031070702900c0c00c10b40d80d00004001441668445d41c00300b400080c914014a00b1103045000d1656110710b4141d411011850020111803080f0164066041c0c5950f1a14200550b8000042a80041d82c03144868900104141000820307040300d11400c07881080b4082c40010103500e00702d520768001c15 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 583373381 1250 583372131 583372133
    0x61003060308072010020a32010e0c01050910050c0313030b060103060605030705120916030516050301060501080c090111012904050403021c121d010f05010503060106030207 76
    0x4040c200325040030744048000100a0100315990061402290201c0002c525000c0c05000700000029540c0400003d45c01110400001905049030b00c4902c42e0540c0f0f4240c0001c0e500600054944010241c0c50381e540c0d50f5036084040310004100d0041d010701d00b441c0c02468040c01c900407030061100020200240100421403443d8448107109482c0340e107082143784019191f036410048200a01038600307d010034079240021030018401c0085911031a41d40d241c1a00d405503000d00d1242e40640108240e045000e007504034003c10041018000096010700020304d24500c0a40b41c080354814541d021501c41e030304d4900100510790300306083c254085c0030078002e1910f4002e148016102b8122070b888004140d4a40b002070b00b81c5a8200070007480c86074801c000c4003860354070842400111001a10040e015034410024080a000d100c000403064581030300c1c210300340e41c111501080980d10140400400c45640d1600382c407400d0801d100d101c4c041d000190f41403000354500004a600d481040c003682d010190002100c0b8 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 583374631 1250 583373381 583373387
    0x3090a0f0645060e15180307091a0312040513020c01181202010c05070506010b030c071b140102061501050c03130e0604061d01050d2a0602120f030610 66
    0x22100900d80100460b202050b0000507100070030500403800442d89444042d80c203410810f800c1050f000d41300d00d8541c0b8000102007183c1d40240c03c40145a030510031860041942e146502403185146240300325042e6000c3c50340201130a0100551006001980a0004101c550b079400304885c041e002e100700041e900d5548265072409059450401080c5501d40d00d0220200149814850042400b44d802089846240801180c0314407524401500660000005125282d01c070f600070364102000c0a0054603107034555442d04104a00884070045142013172004201c1c4107112056900000b00034030142c001d525104412019082503081071070b04010000c140e0115030391003041107821058249029140b95580c9040b40341c0740840464440c1c2c051030610704001080006030b880ca00c0b115040d14818491a8286002d00c400304501c00742c01d4802c3d0700c00c40340d00c100102c0b000c0c42d10392609900e5806110040d080090203885e00300c080c8142038102d5800c02800000c800b1520a13640c020004841c86000031034030754812 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 583375881 1250 583374631 583374707
    0xc0c010f110a140601063006030209010b120f0f040b090304050d0507080c040e06010303030b0118061722020d0819020304030c0e04020a0608041406010803090a0f06 72
    0x4125a0300c22042c03600d050201c4441c0d0b620b0280344803800c03101c81341c1c0c840008031080c1c000d44222802d0920b6517030000720418501c0303000c100a204146000540d00e696034000407404542030380031128147d800180702083d0a5030214842d401002058511881d0516642e04100c0590041014001d5500030300422a5480c003482104d0003001c0c020b0001900c0007032410460f031140c0c03142c4900e00f8280f00385007844a2500303140c0034a2801648820244c403c580c6161010b501411520001310304210a05029040b0000c03018151000382600d9600e8032661116103505a110700f602030301442d9065048000c426584a0042480b041c4550690b103610f000740880c07a010b030842c0121030444480d4205036110350b5110342c2c0000900700b164064a000c074202d640e203c2e508421684c0940307019405c003001340000e0201e1030207900050380007403068909032051015a0701d40c80c2841400c0e04200080d4000051004003480c12900241c05080d0b06810440c0703e602c1e140d40a0032420034480c1d181d1410390084200c82d00803481d1448 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 583377131 1250 583375881 583375907
    0xb090604051e040f02040f080708150a060b07030839090d0b01120c090204030507060309110301051f09110702010315090501080c01090e0601080601110102040504150311060c0c010f 79
    0x101384402850011503002079041401542001c0c0d04d84c40d0005885440020f925080341c0c50500685840e01101000780000d480007454121450b0729094009180c124880003807400700d019980c0c108450914071445d0b00b02121404100c3d4082e040801070808001c0d40903070107160442481015581c811032030011403c0344840d00409003540d400c01000141003d14040078400c5107214408000c40c0c552030304401c9040740110300000e841030380085424018070740243e01c4517040c1800b13a0300f00e045c1c808441000070f082d1002240c41031790141034104a07170500c245912011018003480d01c2d0600031080c00340340034100760240c0f480103410551500e000c007100010041c0c50380040c0c007404200388525078503a080c84e5075912072030314206e0008103500c0002440503418002103004e00b034140c0d255541d5864030401101e520852030400c1005550070080003ca60340c5511906040603450003010111500e14181000160b610b2500b403030042104001000e02e5260118104501003c2400e190320a1516158101c5581b945140 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 583378381 1250 583377131 583377139
    0x210603060501051f0e010e0f0d030306050f0607050604060203040c0305100905121801081b0a0801080f0c2b080304050604150b13050a11160501060b090604051e 70
    0x11010003031003600e4100c1070680c0c4041c1c034030000748004500440451440395544800103600142250300c15807085110444071000185400010600b02d800500280ca08441c01c502103030b070b286410411820002c042c00000c1c03204a8078582407540c552181a2124001040180346641c004001020040021203410141d900002255442c02c1034030302c2c42005088a01003619070b0710075480a4200030840404079015040c100380541d414922040044d50340031405081d441405441c15052161000e4250252100300e56540d9024110351510041c50700700f05560a03407a8264010007103410007522030b1102103074042c20300841b52101c1e400750042140303504c0242d00001c04c003820010521052110020748180103a0060103408052108070880001700d072540c043c000d4004020540280c045200c507840590700c03295500c8049101c0700348010080c1540c2c00540b003d01c480700c2d00ca0750001440380900c1108050140203761502d41104200040e00c07030300440c822103106000b0f011030280c1251030f465007070343d9040005d8 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 583379631 1250 583378381 583378391
    0x9061404060e031912111b0c0d11010e03100e01090213060b031b0c07060903031101060e0c0a0915080708070201051306020a050d0c051803190b060a0b040603020a030e0a03020c0121 79
    0x40b58030030304010001200300407841100c00c40f0a01e1f152014022703036055401804100c0a140c640015564264071000741e65050280d00050b000400142c0180341c00281d41c4800007411190364810488801045460642842d10300b070f01c148131148000c000c036600808200c1041f6001003c1c182c1c0000607110f41d0f20000d00c0d9001c0c0701400a011900103030802d0549200e0340741c0702080b031064084542220320a01c41c420000300c80d6030109520303082140c01000a00d006207000103211340c543c1c1c00d501c200000d02c4556030008805100300921541c1c00080241c00a91610084c8824140340850030484d00f204817000e0070903640052040f6409006d9030480e08a422000c10600546102a0000d8640d030400c1080700c03200000000e50b8405c2c1e240c04030341c0143c03a00346001780b803500134074548170102e0080300104101d4008486440c04030f8540c01c0000540000c0038142c2d809a070320100382c1402011344084000f07024042d0b1240303c03105c000035008500c80c800b01600f0700e030103001107403000d2a2031000010824503410342c80c942 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 583380881 1250 583379631 583379647
    0x408070b0d060501050a0f080705040305011109031c0212090a1805060a120f060f0204030f0602090a0608010602100c030b04020408071e030803150409061404060e03191211 75
    0x22005071030101400201045141e954100550b214800c0c01482ca00042d000042d4103400c500805220360894410300d4000c0c02c5c41c2d1680d440d00d0031250407005000100301e0129119183d454104a160041c44003a20054040100c24001944d503024442200d07545910114a54a6544034522000004c04100700400c2070400412018401040c00740d03880c2c0d02941c40d005001c0f60b42420301c00040c001030361000181168190548a080c0201601032194900340d40070070000021400d020400350119014a03030040c0e84801c00d0f07041080c203803179940c090400e1003c200300400400b9004a440d00c460012001d0101e9005c1461000310010180c0c22107944d40a48045008038500c80d00041d9101551418440d00d09000d9a8074007a060302d2155102c010600d00080000407640c85542a076600030b00760140010880003840c0d5161001e6520703114048a0320710400c400c01061220a015030200700d1800c0340694901242150084440241480003406000d41f24a0200703600c002c550140600b40000a00a034403103910b = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 583382131 1250 583380881 583380899
    0x180714130615270905040204020706060803031e040305030f09010e01150305150906010521011a1017070c0c0f08060103050708160905090a1506050141040807 69
    0x604107940740061500394291014240c0400840b10600301042110006844e0812000251030001e0089802030340a00c41200021841d004107400303030a0b504040c50300c87c54034000c0540728075000d4245110f03d034020014480480d40010840b9081a0307070f640d9440b8150ba0340004980503040244149105610b000541051072003548422410b6074801d005440c1026060100d9001049068812080c0e5420100040055160254410041d40f00c00c410549081d0000f403074060865007031142d640089501000326180c9440c2464081452445a0030200d008107030080f180100c002c80140528144002c100d1210184580e048004001b88820344002d00142e0710f685500b6207404003888101d445200343c84000c520f000001c82c850b601d041140d18100b80003443d2038071a4000c1c08000c0c04c0002c581c0a0749003810701050120350305a10308030307011354041115458080010042020204c00c001880b0700e242d40440d070002c0008400030b600040d00180401e0f0720a4441000c05031007154404906c0e403144440c00201540 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 583383381 1250 583382131 583382159
    0x6120d210209031b010f0c0c05120a0b0a02210415110403020603091c020712030804080c0d0e010e181306020f0304030903030f08160f02010209040f05060301051807141306 75
    0x44d00780e130307a2940300c01c0c010b0701900c80d464150300040c090038002806001a060610803024412802700494500032029111800d1031340c4140e8030074155940010340c2c1a005d0000d102c60829030400070300350407094542903c400450043c10113841c8161a20360700200c100300c0e1094107031000b65030001c000c1a901d0a080801d40e80c0c501d858120314020348000079010590340e00100f11901103c584034807094600305240d408445281c0b0040080310302c07400c1030104034030040041194a405ca0625240c421410302c03900009060380901c3ca80251045203c881c500c050115400042034000410481a2480a15514009000e80229103018440207400302c204014980d000c002c1d80102c0340a0b4481403042d24650302e04480402c000c60744141c00840040c1001e103402d00c90b0040006070840e034800142402c01190000d030507128107104118085454400384100c500d021701c145074000c440c0440c0008000c3c44207010315100c48040c4074100c001084402d007a00207450740020100f0130200800e00704002610340840500440d = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 583384631 1250 583383381 583383433
    0xc2d03031e04050f0405010f03030c030314040305070b1b04060513030807080415080705091903080301090c03050a20070312060b0d180201121d0d0806120d21020903 72
    0x1440e055a013108609081c85100d058440340d480d085080350444e00d060320b041030300b03003012010141d68006038100410005c0340c4c0b0b07010302c4c0b0030f58070644d5420f042e040050b4514009441d4210207900c041c0ea042181401d50308540445025085c1300d40c4580791000240d00540040d480135103d9140082d104041003540c00060003a03c080203082c042e103204804041b40d215004540710382c0030403006c100c01d03422407400c0701001c0b03100645e001c01024000d4990340c808103550400c3e03201d5951146c44040b500340840e01800303055808a03550100308010744048201c01c1e50000804d03d58100400c00195003014076204000c043c8030140300350020711116940381d921000c01c3d8401140714003a2450301500c80c034136002b034a288244140d0165030700701c030310305480d50281c0040681c91010203030076a10702084901e0240070b0052002c2400c0c151202003040c5481c20501c01380c8008240d681c1406c0c1c11624042c0c0700300703400c0424501e41c640c00d80781c4500406030b2000d00750001c3c0308005900740d040c807408031502225014001400c3d000 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 583385881 1250 583384631 583384639
    0x91806031704062327030106030503092d04051905040f0b0a020a09090e0316150b0603100e06060403061401211a33030c2d03031e0405 59
    0x211009050506241340c40726000a200b0700200310301110150050701c0c1d0640304402d803641400c1c10b504607001030708440039984119416000800c0003071552030940502c10998003007001d00006450304500e9070300c966008080c030900c60b40d81c0e2000300381c4e0515104003400e43c424182d05d0030061420a8186005075000410702211010b54180000b40840c0c1e0038002da995000d51521055165400e002080d03020f04000a84584544002d0002c80380c031043c1c850344108903900844180c5030894490003100c0988600042c0b0a010750400c0092281d61071310f10502c071040340c561440e2614a52a180002901845243e00160109003004039480e15649c0450a0504032001000c000e0303080d52240305c039071410008802c1d0203000c251601d07103d003140c1c403108040304c3c5d0707c00c06031390040150b03100703c0389004038000c0b5000c1e4110540401c00d0203005d00307040c20024140002801c90f17011510b03101b0003e0601e0a07006140301000342c100d410601c0103003174030200241d0b220044980700781c540c0c18481c05001091070700144201445 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 583387131 1250 583385881 583385897
    0x160303021006090b010e010309081c06090501050301092d0b0702030d050f06130b0a03240c0315120f021003150f121709030316060506010f09180603170406 68
    0x2800f8114131941110030707010303180d0036003049040e0010340041001d000213840c4420200030187c81828140740754040e60f000c1c0d54000a550f428040c5060403120144c0007907010782c6c50a00d00d040891540616800034040080b14000d02052501c02080e0494840d00010111817998041c00300298020000c0e1502180b40442048181d90300f00d0b56044004083c0d61054002030358140440c050b810030b410140d10184064140c01150750b8998402c80c1102c41242d21042d54107503040110182c542074024200c001c48140703800c0c0403601084100e0030304440d8603c590f101c01d44c480400101040032020b505410720350014071610b8411032400028003d4802894400e41c401d8000d4000b04902414424000580d0030100000c00041403a41e142005c03442010612005900c0a04c421180b5590030401408004011050741c09080c2c010314100d0107480c0090b105078184280380c0340304a042c41e071068460045906089080080c00e50890a8000501d826000a401e01745400301c1c4150690f050782c01803044864681c2c0d0038034 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 583388381 1250 583387131 583387139
    0xb06031b06091003060e010303030b0108070201050408030c0a111005061903170c07090905030a0f08040b0f060f0604090e1203040b06060306040608010203070207090f0c051b160303021006 82
    0x38510486111040e803112051181214074200700c0a00c50081c1c416003000030391140c0781e03052001241403d9200b200003980306d01c41402d0320750340428419040006400284101d0a0507038984590f07001c010701215000c0300114022420901c11510915500c800d10b06840c3c41440a110b5072025000407100c03203008410041c82d0081809403101e000d070450b5000b0502c181801001c440600896101c419031542d5841a0f420124041549102e0001070071310407002140d82d0110b480d4060030169512807140c1c00e0014107402c120208030072500f0b460303114007500140412070b650a8000345032410074814484d080000072901007202d0078954400d00015005408807001c0c0310710305201c0003440c4400ca400520034a8107001146650904001071908024010004545d8944850b074a034221f070411514100142e01850003000780030054456101300b40c58041050002c2184604054494859802c0c980c24600c02c48185000f524018058404040108420200201d9070390900a6440d120301c221101c1759032800d04001 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 583389631 1250 583388381 583388413
    0x60e04021c060f051c140c030312160309031d0109120b041a090a140a0807060203060f0604121b03050313090b0301050f072609030715060b03060d0c0905040b0603 71
    0x101701c0100410018404e90740c0e507840c0040c1000d4800301403132900c64004a1803d0355003d1028141c45411264140d15078500b00029800c0b0030040380c2030f842818a0005407102080e40040070b00d550070f1000405500c0490344000488a0044da54080c0c4002803003407d507070041040f18030945001341e002f9160002d1106881d400c0d000d0048d8191059045584074031801400202e21800034071160310003e050345c04070346050300c81c540c441c0c0c040001194082d40c00010400e0b42e04d084000503158503000e95005041a062032180c0040d14808000508550401c2d4528610400310f0044040a107074005c00340e94640c20b400030030702980c00150080101c6c0c0303400c000d07a10070705003030502c10b42e84101c004c0042d20510340c50394442075400051903103e400320f00c5c041d10081130200c2c6140c0205409004000300469a035025401d282c040d40d4000d820428116061501c00c00c5449882c0d01130729003104084900c16080402850611035102d0644e1200c1c01c4141014204030500002d0740065100c4c081c150140c800d04a5035041d46 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 583390881 1250 583389631 583389649
    0x90801060e0612010b030d0c061803120b0310022107140315040b330408030901081e16030b0405090615030a060501030f03030e030c07060e04021c060f05 67
    0xa21081c18010700042d81d14a4108101402c004801000142000242d0f0100703041001105405002ca12030303100050400810384590011050310740384000b9089290396000f000121031054000d00551030300025211540d00780568581c2500d5003d00710750f19058420311900502e98a035035881000061070010760840c0c02011020342424002c4080c43c91541c1c2d188800491310896098982c006603a003900c0103035034580c2411601c2501e69240d0903808050b0010200740c5060359039105088000040c002002888400003d40740702c00d209081c50030711075a85181031400410380d4000b4071402c015490500c605e0503c41c0010703203901000c60f40d05008521000781800195201a50340c4541070340700500040064145d20304482400c07100a0680d4041e06070754450100380c2e04280c00940b4521242400038007090340520405403241e0948020314140110210660385650091041105100d03000c81c3d08074607546c80790304644620754685044210600b03503513030000080006025030195201c2c8144082031510305032042c = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 583392131 1250 583390881 583390889
    0x605151807030c1407020108040f020603040507051005072d171206040605090412032306030c040e0d080a1d030c120c1b0f030304121208043f0207050109080106 70
    0x1c45458034071719500464500754000d200741c078848004a24100160365160065006500810007440040c0c00c020030445075018134440007050001c200001e81c00100d0000104c0c28445803240c80c03009030790b18070b02420b1501c0b003003c40003022045071103504450101d40c2c0c0090b1030702d80d00c40c07492468641e4a2009200480e0428080c156106440341d000500003081420075150001191401040310207001d91406580c5082401d10181c0b2600d441c2045102d00b420044908403902c21034051100030315a401042d00c50612082d4481048480400900018059002540804402d0748a100348858002175591071350040441c0c48a540900500d8841d040390f00030940d8100d00c0100094414088881c2d11642e109120721040358008601d409608001d81d03040c0094002000000f11070384004079140380603c1d907040c407040510b040c400c5031424403002c1000301904014080b0a400c811440c04822580d03a00d000b50b0500c061800070110301c502001242c0d0204a00c0d08032907003a02e83d0300550761904003050076102e035401 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 583393381 1250 583392131 583392167
    0x4021b010b0a0e0f07030e07140f090c091c0f030801050310091e0309090c0503040c1205070614090a060e0102070914150a092d02030403020a0605151807030c 69
    0x3c04100005000101c050b0030501c02e040000740350400b140000d0901480c0d900070803501140d4580c8422900345603114121021040b11a0411494602006100c9014030400c2c1d901a00c0d80c0d8450204211030000808445a0484005502109030746401805403e003401013a004e801000c004200301b00e114002d40003000d43c4031031002041000c010072214031100b00c40080d41009100200010a200c96100714180c00c103442c1d41d000c2d680d243c10b0829201d1a0b0040d03000c42116061016100080340c808107a10054420b586040c0c5c50741e0300d0710846034105005030303031040703030b109a41620000784681c1000201407202000c2c0c007659901540d49101008507800440c62284804903640010600e40d4020003403145d004005000c0404a5250340d01501103400708202054100c05201600f505440d103203420110b000c0c40c3d14819031951500740d034000e44418611100600700703038031800803650307886d03403010302c4403c684002d46105605002d070300f000c0c2050311041d0b4070303140400c0c601001900076501c90301c050109410464 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 583394631 1250 583393381 583393409
    0x10518010b0f0f060d1401050a151403070e0907090314010218060f04080304080a170f090120030c0303041a0403051b030f0f0702181302060c07030204021b010b0a 71
    0x5003880304410b83c0c032541c1a4050401c03ca5009842c0b142c2c803580d0340e14481c2002045c101d6050400707001305111a60040d06041d9000590700000d40d41c4090398120107140c01d07000503201c0d201c0b4401031300d03080e090050170303a072026044041148143d401344840046a009103815010101480441400c074850255010f10303001074a041d200881c10000000c02d600064145c3c19442e107640c40b0b2001d070464000e034100d000035401192413102803000314444190303410031900c0c110f17103801ca075180115070358070908079414113014106182848403440b0448040300714a042050301c3d5642d4507146059100d601c1100c040710720090b048210800d4204991406108039411f48070345142c01c2c0c5d1120000502030303a2500c5c2c6410b5200400003240f03c410f041015040685011f8142911a151881086440b4203c0040c44010b80058001c00406d08030101141d1003c40d0159000d660b9041c000000034200303501900003030f40160000503180c240f400240622050403440d44020498044541d0030040b24590710710030303024409101 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 583395881 1250 583394631 583394659
    0x204140702070b270d05010c08160f170a0b040e0c1903030c0213090c12050f0606010f0f0c020603040309050a090203040f2a0e011712070308040f14010518010b 70
    0x409000310741500070a00811700540d80d80da42e003504c030440c40c090005605901800340700700c03040b04490754948081c18031f8180592000001002c4101c0b0044a07080c1650724000310750030340501c0c0d01200491501820a200000c40c502c03e0b65500d0100e99144c038001d00907440e000c02d84a100d820070a00b42c07a8180d51303600c4000481d07005c00507070700d05030300b14004550780e42c1c1150710026030421a200c0091002c42c0309142c0f418086e0400304c4c18807002202c00039183d0028010001582e0f4840b80c4400c005619050200d903011703110b14215030740b54100c60000d4000c4000428003044c9504854014100c40084488500240e100c02d241c400b640401d890090a07222a400850001980100010030084071040c803181036481c9980d60347c5004c5080d6210b0304603940d550006000d809004a0b60700e8a01282c07800411a0402c3d4841d0031801d44502c4802034108029540807a040002a07104810215002451642d40c2c100c0d0000b020700900091324200b001514882c1070b400c901c1c0e4180141c1c803408900400d440c60340291 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 583397131 1250 583395881 583395937
    0x801060e0a020a120e010c0e0102160303360512030703050d02030606070b070f0305090c0f100908071d01060c0f0b04060209031006030c0b03010b030c0a0c0204140702070b 75
    0x803c01c5441d040c0142d0740502110442140314849854400d0800414003401100d0042d12a1004158240c115085207115010a01240051100701c0f585840d091150081d80d140c16a0201d00c03291b940b001c182000a007140424200002c00d40584400310b821041060040090a1f80e920907000c0060100c0d10621440c0c01c840c2544d8061540610050b0056183c03d4803030b96440b1140c0750860f80c01c1c0c04203000c1642d01040c01e616219242d84000c1c041c0c010700103640c4400024100d040c0b411205840703025000c002150b03083c0708018440c003d2100e40c0c2168040c50301c40c0b402ca050000d4001d0141c41c00700d241400001d120b0f110b03903841150726130059800d030030104040e111a464a40018401d031401502006580c4031a00c003040074000403010403000180103400e518048081d503081c1c2e07121000100c018001032146a95400840b90403803a5407030b5072640e401c0a84025500003a2040e0080e42c40381c80c1a010501165404510a110301d603142d095440d200d0311462081080d00540c0301a0104184170703600540d901e91 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 583398381 1250 583397131 583397137
    0x7030212030406110a030f0b040b01090e0a060905070801150201110306010c03030b0918060f06060901051806120421121505062209090b041112250801060e0a02 70
    0x40100300c00309a144c0d03a50300c2c8203103540c4401c449000083d9106c17208140c0071010701c940f09004108640c244001814440001d00c0000c15009034480080c040d008142a40d0080c0d001d1030052070026402e018501d49584090900c0d0000d20030341c03024400f00314903100e82074418880c8100060521000a046485060045804000c4201d0840a240d0f940041c00c900d55601c00c5510f00c01d046941e14000340401c50410241001006440d000944d1900002c0c000310356a00f9090b030b19001c001380383c41d40e01d0789204d1140c48840342c500c516158015034001001c0040c180f130005014403460091807121102c4100f901280f9013006001d10000c0041e401d1911000320882c103400c00c000801100201c0c1d2520b41d1200c0000309180d01c00c80c040b9681d1107005061104511650541d00010884d5035400c12014605486031030101600401c0104404920091a60b05994952801001e6401c410032a002520f80c40d0a0f1825083e2007c2c07180c5814201c40400581d0201c14025207050b1840001a901a501d841e0316140280d0 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 583399631 1250 583398381 583398383
    0x50109022107080f041407080601050a0f080303010303080421050901080610020d03050a15080114090307240e0313081b0a030b0a0204081f2009090408090d1b060203070302120304 78
    0x6d84c0402541454502002803502515a01001c3d10055140900700056180e0340d40c0000c0640c0c000c0780c010403100001201780ca044a8040c01c000c085a0f4892800507112445d1005c80c40c2c00d14200703183d0006060344803000d0002c1c0442a00c607000c6980300d1108000d00c2510300c034031050050b0300c4821a030030743d24403035040103030400d418040108203040c02da8064a840c1035150405031082c0e41d0784000c200070103075203810280c0100030500a18038002946e01d8481d002d42c128160011001184200c06200e0340d4203070302c0b60446126520580b138a80191106404855030144100301d214400d501e1850410720b40c82480e4100c1907070041c109803c603455650790a0400d2002001c00b05850360034800041e541c1fa05200d0440c906141040302c3c10034568200c3d090741201e140100c801140040001c00d002c1c1d007088003080340e502c00b000712464180c1d5a110f18214920b840f441c41c1e46900103140011440401c4241b02c40f80c20f00b008184540001b4a03114403049a407805100c2c070150041c4d1010741421001c80a01c00299041 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 583400881 1250 583399631 583399643
    0x3050f0c0412030c0201050d0c0521010f03030309020f0607060b0a09050919050114091612030e040b04200c060f060604030201181a03060405091b04180501050109022107080f04 77
    0x220088e2441c80c125094080c1180100f01c0000b041d4a510b204100614852180b890300c000b0254107140c0700c08003e15141c000101419a504104015551003002c41041c00e00c000304099a59069482e028024052a00e103a03409224942c1c00400c3c422000d0190030f00c5211348400800107884079035410894107110a5040e070f04c556a51403900c9103401101304483c8180b200750020719080f40864050000d8144940c40b807c140340b031004810f00065400602a072510000b118041101001d0303c0020300101841c801c0c0503156481019445110003405028060420300c620607126030307035a0700f502043d51503c12640c45601070070070441072005600070a01d50b004402d2800540d08120745451660104044510420324121070100070001185040e0041d198840e0000c005080e008107130004945201003c0c00203140f0454a82451080310b655144181c490560000000e201950792003e01000030341c8000254080022084402ca41418100f000d00c0c4c050850303030b9a05500c0c1d036200001c40040c1302c4050011584 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 583402131 1250 583400881 583400887
    0x903110114040312020f1506010e060a110f0d03060602061b0f04030803102c010b030a091704030b0601140702060a0c05031314030721060b03030a03050f0c0412030c020105 75
    0x400e1305141c141c44e50080e01e400510a400c21130110620f000c90b40c428610b5009401401c0100301d0744d10104948034280c0c19500c640c0c582d04d00d05e100307441c402c00f40002140305100710f58000c41121000034208000c01c503035807002c2040c41d4440c0307000c98850f8001c41d12075500702e0007007540c604014441c0c6c00800c401004458032900302901e9548048035030340142c4240e80e03002c400358014050102c5201a8420300c9401414136035081c40c00700401c030341c3c00740b0500c250301c00400080700140e044031298008440040c4e001010f45883340200f4111000790700140400d6aa05503010005082540100c40d5000911a610341079400e042d01a0b0800c4441c0d07110207000420041d0841c0030b840000c0302000504041d020044005020354101010001c82110781c1640314841c4e80145400c00c5090741034204881030403015140c84070f520300b050500c0c50150098400300c3d070305448001070340c3c000c13298140d000038001d04020007290b401d515086091580e5008030300900c81c101040c440306000280c013074040d0090061060400e541 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 583403381 1250 583402131 583402133
    0x20309090c180a0902300f06040e07030f14010e031603050412060e010b0316030212070509070807021006230117070201020a110105070f0804050f012a09031101140403 73
    0x107028840c1c4d441026515008181e80b950004441e02402c0b03aa880351049080350315480b40d02c807244600107040d45509000c201c0c04503240d134032240c2101c032440364500119190b480d647d26000c451034012807c143e48a89848026040410040c060b544403400c0340401903080016440c642010200008811400d20404005c0010790700c041c0c94902c0f510b18010200041c101503003040311070075a40306411182c4a500150b52943c400282119050b054a4060fa003400584503803180c17180c504071a40d00096480340d82e0b0401c1140300c039407180015201d030075135900760352a07a140545035006945003401140d0f50301081c0140345140701e030340c94140441804e051400ca82c410703001441d080006034007960580010303500040c7c07911003141c10148901d1600321b414000c10031807819602c011309446000841a080020010103e424043e040000c590410300c0400204a0a8000e40031506216500964514107560380b180c1441d610b40260031050480c1e0700f240e0380c91200003c05004560300b016040010b00180300600c0040 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 583404631 1250 583403381 583403389
    0x43305090a03080c0a170a1a04090b13060e060a0603020109060c0c18150b090301061710200301090603021002160506090a0f0308030f0903130b090105040504050f01060f020309090c18 80
    0x51f000399039003a80041e50b00f810884102d624a40404194016400c08600760002205664042c3d409a00300c2403c220020316854044060aa03c4070b103c407080c8209004d11807102c409900501c100c0340f01f42c8904419a541c1c98080d100b00c1e1566401030003101c0c05030341c204104809040f0f1508038a0103036a00040c0d00481051440020f110760300002c142e95030120700c0c0415810300b482440301400145014100a00c4480000e80e40c5072250704210300340940b01c0b0001c1c840318041e0003900d0a10001c080b400c589a6845160410040c2103d2009901c00c0262400c0d425042c1e0000c102040c0ca2120a4001740005003400140005a0300c045000394020319000000281d28141a0b16000518404c41d01250350342041c8021070b08402c40a4804080758000b000107030f034001030b5400304070100c0300380384005616a0758071001070b1407500995001d20b03080360814040059982c9a40b908505803403250b240e03a011140c0c0614126660301403510b60325044020100803520403000f510181003c03460340b005a148440e5000081 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 583405881 1250 583404631 583404677
    0x302030a050f0d0516120c150c030c11030a111009030e2110150906080604030f020610050607082208190f0803043305090a03080c0a 58
    0x2510250450742e2805071841c0c040c0641d89000c80c1503d4014201401c540310000a044a40001404003048004071300415000c1c050a03d08143c008020100e400562444c10015203014102e010000e8a00140c0310700142c041c42801b401a00854020340c240800c440c3e0984040310114000300316480b6803c0c0801500543e4003801028038403c0c0c0d58001a514954280191003030b500010303001c2c0404080588680201c005a08072149172200c20105000503a0781c0c01055003d5035401c020b05550521901050018002502c0341c021403090340c0f00c3e0492102d0391000c0b070300c4130350680b8075031994030700b45008010516100703011307003041c50040141520b405d10a8210341943d02801300c03a070110126600041045801c02d0006406e089641e5100200d10304050361003015482501c10300030080c0354017002140030302100d4100d03501100d0400d00d2200e1140181d9864030010a101514034440d00d0501000031030035000400d4440c01c0035450780380c0c0211794880c0b40c0042e0964200d58091410045501c842010074004d103904 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 583407131 1250 583405881 583405883
    0x120a1b0504030b01050d0222090f060b2e140c031306110a03050316050d0501030804170703080a0c0203160608010f06050a021b040e07032003070305030306040507090302030a 76
    0x50641d5861440c80c0089922038160f0141d8810b1801c3c00100f0f002d0707120003c0c0019026150300c0072805248008085400900c0d0002c0c0180140310304800d08020808640d020303007107182d0101d800c002d03400c3c40c59070081e0f00b1103690400104d90305120031940131118011001c03155807014140700395040500102d0b2142c82c64100c0c514405290f85402010800039400c4507280c081d81c252500681401e540940b0041c1003444040c100249202d2014118210717940b01d60252070072000036030700c24809965070b03042035611a0800c1c0103151800c00c2d080780e11010040c0015105003240d502502480c105244400282c480089a44050b0b80500034501c840c60b4515003441020040d252644a082165041021070903d29210f5048101405800c10501c541e46400240c044400e56880070360030b142140c41d01c081000341051080000710362007260710100c10440303455242254000491400750001c07000b40308042e52440580b101500e26003041000c101a8200358101641c00b00107401d00c807400d5590303070707000c03034903111a00e10 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 583408381 1250 583407131 583407137
    0x1008010b0121020f070b010603050601020d080105010c02061b0709050a02121b0702090c0403050c0409050c090a0609063206030a0f0209060a18080f0304050112061e0e0606040b120a1b 80
    0x100600c06072742c00d84034060704854280f0040c500c040721040c0c09884080180915814400c1202a03441156911001c03541102c0c202c4900c1c03812894071b098915520b10150182011483c10b150000e0104501032003620020503640042c00210b4951545121031402c4109400340b018500704114400b68548200480c065606608000d940320300d903061403070521547c9440c0c107200e541049240c0c1e011410001d4035944080e022070308404a5101c48a0100040400354051400c10b07040100001e0b0300c40281e101c0c207000010303680c03820310000c030001c17102e100e402109080180d025205001007096064242d10080c4011929a001480d0144500000b1102c5e000701244100254008100480310103050007000c006200840003080d42402585160f5242e00840c09030074100110303100e0703004008021f40c114600074884031140001c80500500c615000e02a42d00a013142c2240740d0020130750781c0c1000c4003107034103c072610800981801c3c44200f03043e0603080007505044902d9205c0c41400e0718400b0120070382100760a591 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 583409631 1250 583408381 583408403
    0x903010e0a08190e0f0105031312030b030c0405010f0b0a030608070f0501110607270f080d080f190b190603020d06060804021305041a0f1008010b0121020f07 69
    0x200d1840c0d521100d0f01040420003d000d004800d92602c1850141c85074090900c40d407240e44504502c0f40780c8007800c2000e00a05029001000d540350590700c00050504150151100c01b07140740184404d646007071244034141014501d00700300344414000580f400d124280750206441b59546c0c2102e107080030640140303110000121042286603080f1132020909240640509a1417905460103845400071340b81c90500454401e0501c400452501a09800340074603840101003140c4800e1403955440740010040041400d2502048200540c100e11601c00c4500300380c0d6a00e668103060500d03002d446e4101041c0c0e0090300c0d802c56603000088440fa0100a801950350068071181d0f5101744005032249a070104081c044030100b40302c05a2036201e039008855000103008110ba4560385809500d402c04294146907911581042c0709801034894907047c0581280c2d1950310323581d07448072080350803501d0807007400780421030343c80c50103842820780c2e0400443c002075000010f003485866410010309600c51003044940490704 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 583410881 1250 583409631 583409647
    0xa1b0b07080904051515030601090503060a05040201020d0c0b130201051b06060406151b0c03020607060506040b0406080c1002030c0d2111031807050607061a061c020903010e0a08 78
    0x15224940e0302800111801c1d108405e09400b007282c1c088102c214942d5640000700250069010700d411900928016007100d80343d2404078114001003400380d41c100e0050041050203c09a441410000001908658500782540300c400e04500704903141c0c0c5007203050101c1800012000c0c403500d0242542c08075400c010700ba02d031400e541048100d651a8000c070117001c40010415181c1540203c0d02c82c20111501c1d022402c110440c2820031040d243c80d40020344c04040001e04404000c10760304180d0080d07400355000d20903400314400700000c0d1001c03401100004d0740005240e070014070b45140203c0f034290aa006076403620500100060900070722213030410108080d10040740808805c1005081d61000500c0c041044e202204001c0e01d46200141c00400f0300214880044150001405000018171005003156601c22241c03030100c000c0c005000d50f0040030040c0200f05a5542041e10881d82002c100b88600a0122a0014240d00035005500016010341d070321114030f52074042c00c010303480c2c9050145c0c049a45034118 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 583412131 1250 583410881 583410889
    0xf021807021614060d02040806010803070b0a060e0a09031701080a1515060c030e060304060b0f12100906180f05120a0c0b0c162405090a1b0b070809 65
    0x1502215040c00c02d15001c1000000c1c0303c0b0044640100f412110f45a6981008480c600a405640c220032244c4c001c0600000700540000018403155101d604030f40c1003988d5015104088400610076a14601e443d6000500c80031241d50115102c0d500c40c0c1019041e42c8a501e40c100c0b580f0031b00f600b000d1515800291500288002090001d00511090205110034521070341c46401d400c8062054100b8403611141d82c004041c0a03061301c1920020160502e81c81c1d150604000010b4007405402c140540f403404045030040c101054002010500b0308001c080084205840b00010b01c03114406440c0c0075511480001000101c40901540e0390256100ca0b080c2035460800b141031480303c0307048100d1141c080019012040d00800400c9105400c040106081c0c2e03108000c80596200d00e00c1c1d0800c1100d01414130408114404502d071a160a080c2940405810758107450801c50303105983c00e088580c44200d01c0000070350000e1031003840c048500480d915843e07a5a03400d10540e000050103d030b103400049603131801410 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 583413381 1250 583412131 583412143
    0x501020913020c0d050f0d0e0a02010e040e0c0906030a02060c0c100c0b07031e09140105100e010b0306210f0c0603071d040b0a060306090606030207050d08040f02180702 74
    0x504280c0852400f400e840003e50342d4003240d0442030501102040c282c144c0071010064500f055403000007031080c0e00c0c00c8000300e030311038060b61801c90105034420900d10b1035041c248039002d01140c001c0000e02c581c4006504000a02600810165142c440c4903440401a25068013501d1540303681002811032807131203001c01959180102007001049550551000420b00260884d80c104800742800200d00d081403805010313141e0802c3c0340e090303480d04042d42c910030480c240b031700154a5028000204140d4694190b6442e1900d420b110b440a6981d14000600140001c03c004540100303004200718010071104a00340c071846155074902e1900c1e00450401140b220741407020550940e0122501c614600d88201d020b00030303501c0f010911030002c1011610b03240c0b9840e180e0221008032070041225041d581d86500040203010346000301c3c4911402c20400090250081c02910b00c7c03554404068421840110000c46000302d000f4020b840007100d2011603005611091070a46010009ca0a040024504464003a142c00 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 583414631 1250 583413381 583413409
    0x60306050609240a230901080f1b041407090f0605070210110f1c020f07150503040305040f0308030720030301050d05160e01080d23160f05010209 64
    0x4448208000f4000121500860348400d06007010020b602d410f0042040300c400b5803c0a04010760840d00c4a034020b5200298480f0a0403c81c0ea03031200d42c1c5c03198522915a08a2810465070303601c02c854681d0358000240d015550b01002030b1002a1608910034107080c0c10000743c070090086001d810b0180241154040594040e000c1803c10900d4046542e0110390b201c544031100c1c10030441c4890f070700361341a24180505c00d500c20410003250f80724030800f542e16000380d20248c03000000d44207490607100341540114540701214050010141d0314542d0030320030b5a481d40002c0048040082c01c01000c034043c3e02c80c10900c401741d4041d54444e5200d10300348001819420b504102041d01c103096144800701440e0000489040d01c03020340d080c241201503441c145107400703108410111866001d9030081401000c400e4400d04850400d02141c03030241c84600156400d142d1104210104482c07486840500222500182000c0ba1481d0250407469030340d0321400b2603402010000c49050750000303160b800500e020f4050304490303 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 583415881 1250 583414631 583414639
    0x61002030a09050105030a0b041a030c031c03021b0a060b010e010201090c140a081e0c09010e04030e0d0501090609060b01050f1218250f0806190e070602010603060506 73
    0xa810074003901d0000b0394403449040210000000301c0052983e045503c40000c00343c01407080303103005240c100d50090780d46511400782c032034400344403003038a00061030030124510428410a64040e0f0401180650f020070850414409031041440d007041c810050784004034090302c170020b0b0800c10074000400c81401c03d00300504580c1041d8511011440c10304204c2d00319040070074003200c01050750000c01c9c8011201d038440d5407680200d507031071800d02038012075140c894404042a90407401a640c01c002d5051000c0c02181c1d01c44400ba00050006130041c40d1440381a40d0081400713070402c040c1c0e0b0312030b402d6a00c00c0a04036071807510348000d030781005628082c8589014090811600707120000580b01d8083c040c0301c00020318404031a0210b185090790700e002c0b12880d20a0350554403203000800a056000316281500180310300403110000e4a801407940002c1521783d82400f0b030000340c5905008500d1140001d0207000c0c03043d59140103254413a07003080040d000b00f0458001050300307461070821000b01c500040c42e403401 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 583417131 1250 583415881 583415887
    0x501080a0507081f0f0906090e030403050604060b0d12050c1605060a05031b03010806040b0a1802010e03122113020d0b070c0b010608040b130c180e010f0506100203 72
    0x45160020000303a80011460300140d2000c0680081804c0c580484c4e03c030f80d0b0820b402d804046504035032600420203030f51103c1420311241c1d00c0780305032599034469840050b200713401100202d000545944c100403a0000018000b00043c2c015031590005c543c06020020041280011418030100040c445846201c078600110850f5910b4070300444d103075115103102d0200300040000007644081c090100ba03045003200807040c41d100d43c0c4540015688000a4a00791800904c03280004c2c80d410050040140c0442c2d05606c600120041e0740c015580b2844c1301304c5c0903074075004020380303103241d48000c0700134000b400586c41c80000036003100d403041e44142a001e4501901a0480100c41300561105000c04c0703111903100c2d1407094150703102d010803034807981c0b03445004250340e02003000010504c2c1e0250b0410702490284820780c03540d80340c84152003c044010308000f072400c10b45205c208110010f00c440e0342580c41d5560004680c41c1d580b40c40c1c1600b100c3d0041c1030309841607581c000b4022642098905420700b03030714500003546 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 583418381 1250 583417131 583417141
    0x1502010c0305011a070507151701080c0f040b030f06071e0912080a02100204090515090402030d080601050d02041e0e100e100816051f1413030f0305040501080a05 71
    0x59100d1105060f14078080002686a0401808020a1f40104a100366141b8018018680109929000e601e00c11a080c022000411040804208135100e104003c00c0e00c03200c605480140805000b0303074000796038107004014032a01c0b542000d0280030301c141c0c1c040d039444000e41003806034150100442e01c50001000303c6c1000c00c0c85107003c096608034a15802069490700c550503a04c1c102d00d810243e4035280007a50000c540003444040710742286002d02400d10340c14000c1d64050003031008140c000c85002c1e6242e8014203a280302036004155054010324185803c629100701a101c01041e81d02941c081840d01441c001982e41e102100e80a0201410079003681002c541055440c0744543e40c014003801d180007401c180032502015258101c00c0040c00e542040c2c901006801c52141220300c064410140641051403109d040181005101346041c0320544070b000422103202e444040c190055240800c0c0221340308004130208000a45a5918034441c0c0c1e40d642c0d4035070a2000043c03c0d088003912403030303075a414082405 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 583419631 1250 583418381 583418399
    0x914030a0e13090812010807050d02060909041718100203120a2f0910020c01050a12140f040302010e06100302010e0301110a02010605040605030c03060c030a060902041502010c030501 80
    0x20203000030031039105880c100002c0740d10004100b84103008081c64000200d40055856412416049610f40e2068074800d658400c01e01c041580c3c00c910007075120108004842d10f0f071608180454208d4002c80d11484c0e00100c5040d5014281d00807000b0001e070310083c48803580140760090603c130402ca501c0c800f450800c0207940c5003074a00b41010b45080405501c034100b04a440300c44110696111401d0095010301c0154040240902d0703020401c2c440c09108030380003c0c2a054000100e04045410694919150052101e42260307000360f9120391343d058648440351103501e4010010018003441203010181183e0420340f9001e0308480b49003001c2e0f901904141e003081003200e8a440428100c82e02030901c1c1401e1051000028010006130036010001d001c08100c18510740d0b4154042e1007036400c151000c000c8240c0760010166a070780c0b1443c015a1542c4400c1c00030340302100083c09907030810200301020070b8050300c3d0500481a0b800c15000180b81041501000055a909000b0802c3d0020b05040c10083c0c0e5040c03200364 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 583420881 1250 583419631 583419647
    0x7020904030e1215160c2d080307080708010e0714040b0a051c090b070f022d151603090206040e040305031905070206010b0309031b03130b0a050a18030203060a0914030a 74
    0x5002c00100b0300b0480c20520001d403001041541d0920404d00c007d840b40780c902c5142c0c000741c40b2800043d050f040000c0c400c50180c0405816030382002c0c0c0c0d0340480e0341e88042c02c4400400c1e0041c540da8084c1706200000e5071903000000f4240c150300325203c0c144c540352204540d10001003040e0301e00003800d043c02c100c400401c10010023240c001205242860000c000100141e190032a60010f40b1b851040d80c240700303c00500b5041042da007000100050310320046a01401c0440100299598061214001250b5032001d00a51000340080d00c09840e0a0130103964541c50460f16200320b030198041940001000030f034055074200d0003425604144104581c1c20300c8030000b5a5264140a01c0c0d080350300c0000807500c4a00c08000b40c079644001e0902480c0300000e401203042d204e0f003041c04403a210488a200101d85428407000f55aa070f5003041d600d450401404030000c481c0036818000403800303800211800310240e1001d1103014480c4010210201d40e103a92450841c1040401d00c00a0702036400034802c61108561002907 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 583422131 1250 583420881 583420883
    0x3090609061b03100b0304050d021209061204020f0a030302010e010b100c060c110118060e0c15030624070c061d211c1b030507020904030e1215160c 65
    0x250780c3d140e9407240b088000c4004240c100404180f400b20801c03003001400100721102d5449907080c6c50242241c2c42c1e00404038040d840714541d103c06c0620009441150820016500c90300044c404c54001c2d0310100407842e00a1743d84c00c103900503510b4450201060409002d94881e0501c240c41903100f1003844200200451141c0c04e00405058a44101c400340900c151002c1d40100e4200d0300800898030b0f8131452501c0d0b0f030018a81224003d080c080c2e503003004800891201e00d01c410140c0000000040d03c0c04180301580018884c550040d00c0a0240644031428078615a010b80e0901c0341ea65a04c0541c03d000f00703210b0140e031080382000303031141002c260040d5848907042c0c2c5050a858145480141180a0320071400110250074284103602c8500d8400c00541c070180340c2c2400d6034982c03455000c100800040c0b6680803800103000320700204143e50041c1003102e01d10340e00500a151020101d03040d6800036a0f0a2640d00e1441070603802412501d03403203420001016004600319000d0745400041c6000a8008041c1e0f080c = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 583423381 1250 583422131 583422181
    0x30718050108070513050402041512141909050105042003010504080a1224051509030c060a02010b040e0d030c170c0a09090c080a18050a140c03060c0309060906 70
    0x40240740c1c0e407030001d00a40034050047c41551503548503010f540c03c600f21404800f00095800c0000010300071079104042001c02c5c140a00600c654a4800d0034820300c5c0b11420f0502c6841e6541c000301c0220f00c080c45003e006510030360394240e84414802c0344505850541050b140300381d1412050100081c507440071a1340c0300085042c100350b404030100ba032100500409100040200e1403245081000540c10521019200c00b111362505600313607040c1309815070060f00001d1b80c040d400411440d072140340403000380005405510011074011000380101c2c060340d2090782c101e101940401c00c0002d00c5609801031008003195813030b000011020010b0811290341c0003409410070190000b9440091902c10900c0ea805400400000c0c000c08007804d1000b03102d00000c490340c010320342c608610b8504051440e440201d40542160040c204011640c032100c4400344400302c040b02030b204200e10081251002c2c82200d204110240245480c1c0c03030895806030405500615624854000108100012007500c080014a02c0b03002 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 583424631 1250 583423381 583423387
    0x30f06121914030702120609010509030f030a1e0903090602010b01020c180a140f060a0603091a0a060807090504020f0d231e0f0124120c0306110307180501080705 71
    0x10b02102d08502c520180130307410005c6241366500071000019481e0203035911074000c010039619050920b4aa003d044c0e45c00c00304100030004110000e840d50080203036044040f030b004080030741e41810740c0c007111180c1d041240400c900600804c1460740a20484c0f2108800b800549440380c103120000700c0184030200d01840d00c1c4840008201c032902150710016180c00302c040400404c2c202001d0440c114003007110b10381e21801d00d940700419264401c6c01090001e40c2d011816500352304000c0c1000c0c403070007001400625060b66a506c00500e000381002540300600028000042604041c0180401403020541c4a8001d545141d010800100ca078040ca24405107402c001c40900c40c640316200f0305040c880543e07034034011400d00101c116138034007240011031a03201200030000440f0a203071040d5500c42043e080c0d00c40e17110307c41c07080015035003041d8804080c51013010907a0700f4a450744d031402c081744e60042554100c520040104440203800401510002284101409a49141600003407692000030040c204205c404 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 583425881 1250 583424631 583424663
    0x5030706030f1b18051f050306040908030c040303030605030105010b1c0b090411040f0c020709090501091a010e0a061a0a02010b030f030c010614030a26030f061219 72
    0x180d03200b03e49a061200c08040d002074074280040400c503040764440e81c022402c0100103980e11b0002490304140a42c80ea150014806144050301c0941004007059041074489203000001052080214496200c584002d40c0300e07030650a0043c21240d0f245c100e45d020fa0b24010040c400c1a00c000d0699544101040d000600c80b82c4c600c080d440500504119607421041007070903c01003001302056910010f0f41560104031810f21010001c0543c1c5003a030200700035030041c1c4000c3c0f01c44203c3d90445410309018030008101100300d41d440c101c90290001c44603180071031040c010b10650182940d0315801c010115021700000d07040c0f094140014070310006149000000040030412a8000e42011404000003002e8030714540400c40c1c0d080d100c1d030000c0b6920006518001001c140c0a9194000c40300c1a83d01600800c0da84444d0f0b601d040c26100d907510150340c1400350040700807500d514040110310400d1204084203081c10701c8401d100b03040212000984054001c9000600401c981e03120b01c40041e80c020603462444003007 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 583427131 1250 583425881 583425911
    0x9180206071220010204051e0a1e1805040309050901030519110909011a01090305030313051606020c040f0c0c23190b0112050a0620160b0a060503070603 67
    0x402c1030418040c2400711504038402c04194007030800c440b01070702d003600b401309890848400e00e40311485056109c400600c003400340742ca03859008031800803c407800e400078a8450075801201c08880301c0700c4400a480c0c13002c00c800c2641c03201400c0c00912003031720700c0d4026504542d5066124074030000c0c41c8031501c00c0205008244001181800c201c404050104d40580c10214083c40c06040040b814441c42074820f0104100e651040c0741001c11203400c180558150b441c2c0c0c004407071800c8100103080d5450b106000303042c2102c50a28035a4030062680350000c08092415031b0500c0151003081d100041071510b000c0c1c00cad81815411000b6001665400615040007001845141c5080480c2240481030b51284071107080d0840b80620b00f103c00da5018074911240f9a07a1580c4840d500d801c0007a00500680224841d500000e0300c507041200c100100c40c0d10441035508503249480aa00100d0402d4103181c040b036100c038240104000d03100c0e0029403030380e07007407003078900340800b00381da41d2000e1040108140c1c0d80e440c00300050705 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 583428381 1250 583427131 583427147
    0x203161a0a140703120e0c0a0e10050a060f120c050304030302070f05070909150b10081e071205060307050f060a1704050d020d020c03070302040e1c02010204091802060712 75
    0xc00600e84a55640c100140300c11509940c017211545088142c1040d06000144809980002402402c0f5a410918085280000903002d190900340242e4041820f40d0f9a4040c00007801407a501c440c3c00700d4080100604c850310340015000c0301e0b45005100c1d12216070120407240d006425040143c0d940d4014a8000d04003120f29002070441d0140c40c801088510341034004601582c0100c007403402c4010a82005412110011102d5501c2400c0660043c62039025600440d40000c40303000c140c140605048240c0341ca1701c0304407000c0c0e000a20012400040c200a4400c542d040f20041d801488403030700700408501000038a2144030700c5044040750007038ae902d200e82020303082c42a8030b282502440c10306160039542c609001c0c0703036a030160048040c08900d03544001200c0031003640080c02400854a96001c4c0801860400d2003441e541c01040c4055030848a000c0101200c007465500060f9500e1406800c2000c8072510700c04030036540e04c40c60440d405603646000b69040c50790002c500523102c048649054032101 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 583429631 1250 583428381 583428407
    0x1803070c09020409140907090914060c030a05011d0f09010f29010f0c0b04020d051515010e030a0615080d03050403020c0406031e15060906030203161a0a 67
    0x105900c1001c1a80041070b0007810443d24604000d1100040c07010300305003183c000301ca0303085e8586d000440400c0403100301c0c2c100c0280725000b1050814800075420342079003407000454500c0c124010010500074100801c0c40362900400d900da1101e0840d040200700142c40100240100c1124180c600200300c40c0413003903020030445012160b080008075034042c00000c0c134040c1403c5100c8900b8440003101e070f041d4021103028140001c2503980c20940c044541d20150b001c14090401e036008414800e5440c00100c0406c045103505002d00f000c01a640b52481c0f2100f02c5514100c141410000c400c405280c2d15180021a065100e6200d0400b144100951040020348000c1c2c1c2d11820039807240103d04070005d600759216600070b50207a82076400742d41c4d448041c4400c1d40d50030b00c07006090140328858070103a03a24540501e001d180c0305590321001600c00264500a45400c1c2e00310100301caa4464007042103150800019409101c2c0c1074400d0505031802d240c0c1c0c0518030201403000e0040d000007847d60340c501d10a90b41b000b001 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 583430881 1250 583429631 583429643
    0x204050406241806080307060903230c010608013815030708070c030512060a050a0f0f0e041110020c030106060f020c03150622020708072009180307 65
    0x1507408016040c00c50198030900c000350030001d030120002c04031802000207403050705c40190f02d801c00c00c1c1d48810007408025019001c0103d40301c0d05240010b00702c10700c440c1e619180d035011600c0f000c09410301401c481040d031158050746c2c5481c9164500c0100d280d1682c0340c1c2c0104c0070352590b0910508042105410444211640c4210011071034003101d88101d0180d40030703003110358400380f0541e6402c0080c3c4039072581d00c0001d000302d107061010001c456003014405d5030054020305500302c400d41c3c84010917500c0c4c1c0e040d0025951038000c0d01e414840b03140079108c204000d101d40c2c05d00c40b600e410151641000b103080004c04902412103503011f0100d990007004028090603026000300102d83e5030f005c00400d13400d6a100d801005000e50500f000340c0e4039001604d0141a1010f002e07060030364484104008550341d156503003040f510941084843c1401c010310241880e0790198035500c0d510031040c907103900070001c02403816a0304800e40e100c4101c3d0380c0321170054550111141c0401881c0004d10320182d0310b035008050703000b010 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 583432131 1250 583430881 583430921
    0x29120f030a02070f030201020718021c020c01240b03220f0308010501021f05090a02180601080709120b250c020a0501050703050d050a020715091a04050303040204050406 74
    0x8040000050203a100150700750f560454440ca07a41071540000d10029005034844d000c2840f201b1400d070840008020321010051404d10540504540c00740c02d90390380c0c0040c642c0810144481b40e003c1c0035620700d0904149840b00300080c000c0180000416a0252001040c0d022000980c0170050901d8005001c0c18a04000c11102e12441d00c1105232130041e0044000440800000411354000903202c0b5034500c50a0704c0185004e0700720851402080300504541e00d5208604012000d80c40340309076491118000a1070f8406032400c0d0001425000000c0c207240100400840d00300b01e06091103100c44101a80114035a400751604030400c00810400c040e04d44140ba405088035040d6034101e44006200391003600c0c4a45050355840040d20a0300aa102c06400b1940400c180411465503500c03540d402801080010b0910700c990700c0342281910740462451559540b40c0b01c940512000c9011503660b25081c03c0c04840c2407030955185034a0b400b0140000f4016500c600c08030302005020303000341180e81500181905 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 583433381 1250 583432131 583432153
    0x6080a0b010515040b030a090c1208180a061b171204061401050105120603012a081f0509180105040c06110c0a0b031e07121b090b0c030f03010b0903102912 68
    0x1456600281c81501d4cd401c503011301031000c1c02e04400d107004986064880000e28100b81c00e882c0709070000160122189161131502c1b03200c04000f01d0292085c1c5070481124407132071805140c100704451440342612512130014004004d140c1c0d000302198145002803615441d15198640420302410188480d9208440c2d0003a070b50300d440000c2c16808903030b07810a03507030703016035884640e0600500103c03a9010039204145050034001800c0030300c00e0940202440e038181c802d460001d200764ac06c482d400e540c00c40302d03901103403010000c144d031100c0740010410094015000c0407330200c0004582c0b00b07aa2082e80000074020000406403240220407801c008480b1404140618103000700800c03000d4000800301d01746103803614408641d0140e1030b140c000d03c200c54603012142d070705180702204507800121440c081c40c801004120740b26801840510300a082088150b1f850f07445040406050440211441059601e0301000d0750f41c460240308030f40d43c8180b040c000060301000d1200801c217080c00d003500000803845085141c0e5 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 583434631 1250 583433381 583433393
    0x2040f0b0a020d0e091b1606060e07050307020303010e07030906060b130902040311011b080d09020f011d0439090f062106080a0b010515040b030a090c12 67
    0x100c9050788507400d0301d488803012202900c000c0d840c0d034440c541007881c4500042c1c404c2c03021400c6104081d10020143d0500100701c030807600e190b1201404903040b603201d0342c00b0070200781260003141c0c0001c0e050030064254a4140170095480c0814418092b24003c00c2c0003095000303000b58801e2031440c2e004102030003416252010910076601c050303002010710920940008114095100380c40c1500c1d481300c03041904e500100011200341e01012840115041aa020340000480c0140204841c13205200301268071083c5004100c4a410b9581c460b50600c2040080080c0c0350030204807102c0444000c440c001051105107403071580c403010700d04130100505249140b51010700150240800c8407040c595403001d0440e103c145030a1034007580d105a03004100d50001400032071210071200c042070001c100c400120245d4030f1034402e00e8020081c0042e40ca0204000043c08507092004081010a114491051400b8604000500a40710042107940000d0346d40c8840d50800c94683d80040052140c580354085458041c1044 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 583435881 1250 583434631 583434637
    0x20f0619080601141e09091503011406090621010908130803120103060f0915020903151317070605091b040603031710050603011503060f05060405120102040f0b 70
    0x580811507450010304258420700d5020002c000240419040003003c000d2401042c80403503a685151005200f50006a00c03500707c00380c441c1b8000340c0c1c401440d0742c11400b4542102c10407031301010030003042020803041d0740f6088980d5400c6003041c2e809140c503084402180d0800084d03144100125424a10130105100c3c8400241c00000005d920a000250b61040c1c00c954034440d50352415560603600d0010004103100b0f40c00021001090a800700701086180e5070180c031419841400e60707040d076001ca1a405a82002c003c543d28100817848403001c01c0c02c148080c040c4c81e040d400300c004c01c509010403103007101c200b103c8141d61400307602480c2401281440009641c860440045182000c40d03081c429500e18076007070141c442100d406888890400c500801428540f640080661032006084100000d642d2500c3c00254024507078200ca40032070301c902c41d1005082d02c40300d80c0500990b22000b8803d000b555034040444080f0b600c00c44000010031101d00c0039501901680d03008013a00480c407000060091024402 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 583437131 1250 583435881 583435927
    0x20922080309031209070e18030408161d0402030606100c120801031203050708010905130b07030c03060b040302030c040e070906060c060c02030c1b2214070203180d020f06 75
    0x100810035540d050180399110315507c03800e00001c1c80540400c503912201000c4d2101d81c01501c050300c4c034150700c40507540e00c1c14882400c006070760580312100700039041500004422040031900d20005904068002a81d2220050b1030036200e0342741402881f820f54042c0802c1e07160164001d20461005a5050010700901e07024401a0390f00840500801000391091040d0380c030842098890f00c203640d003072840c218010000188100c0480c0ca4106504010a1140792031364400e5040366000300e0595100140281502c04c0c0c0d60220b8004901404244010303130b000315109101e00426240061400c060002007490420325a102d0454145040c60101d0303a140e00c0004003100c140140014407c4031441d050072a943e1040c056204541e410511000c0d1009950b0a0200d01260b0000d001c0712604c54401c1200c000c80e007000380d0310100c442c0d40303e4850001c44aa0205a68402400d0018508128503400002180d08640c482603205001441c2c51000b1507540b01854800c43c0c6015103106c1e01e44180d0100c1c11580b5920900c = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 583438381 1250 583437131 583437157
    0x501020106050616120c0506040c051009080a120507020a060201050a2304120201020f300705030414011b030c0908010e2d010219170402092208030903 66
    0x402142a00701201164075aa00548903841d14403019213841c1c2c3d0103910070304510204426001e4440c085a01005464001d6010303012b18000c99203810b04002085000d4202c10b414409034000400c015100450900c440a2704120b201c20a24100c0d982240e144c440c01500942c4050101004a18507a0540c03186200d1201131008220040c4020780e80c50115640f543d41e080c100c203007200001d0001742210a2a8640001800050700b0200081d02e6101990060740042d000300101203160f0006040c0002e4180f0900280d45150f0014105076030018003c0c403008001609101c02d0301100c2c0300311142580310148903a04603c0300a102186940014003804844406c480052038005c0d010500c03a6044c405c02c01c04619150080c18079010302102c3d81d02060015810301d4081c21a200300c51980c600a00003407540400125800410349421140a00703401ca42c2440c2c1058150b42000300320060306c03110f8005802c075007003824022851280a4228900008040300280506004800d102448100001030000320804d00 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 583439631 1250 583438381 583438391
    0x1e06090d03020f0f09030c03010203010611060606030411012106060e01030e0f0d0f02010b100503010e09010203060105030a180c14041404120503100f060504211226010b0405010201 79
    0x80201c05a00990101a0107540104000c0c0d4180c08404014000c0300405019100340c440100700103403ca030030981c84180071641511300e00c00481c0e81481019481a0216003060441c101521000d03c641001c6485605001e640350312000150704042500b21b0180451405010040d19004c0041102403c10240b5000c24108959010801c0300441c40c0440030308640c0007420504450041181c0502d0041000c4080d5503131400d21140980f00c0f04205170007901d030b603102e00c0c3e40e0354904815a009078200a0900c02c50b17900c1441404800d82c1d01400710b03030b080440b0204c0454040c0c2802891100706000c442c0052804040100001d080c00a0301022a034207101114100305007522072030440b421002c22a0001e02d103d00b02d140507002a40102c1c041c541000100942004603502c0382007404840320681c0009000c038002142c03c01006409001c0c5043c9111180c041c0c44d00008141d40d00c041c0a5094003c0c202803128005402d00454026249180007003402900d20140d940d4908010f48240d01c58003905006500b86 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 583440881 1250 583439631 583439653
    0x130804150e061e030705040504090f0308090724050d0509010902120a050303013615060f020c041d0a031e03090b040602030712020d1a12031b1e0609 65
    0xa14143c8058285000752081c0f0340f050b400c0c00d01032541c40240b0410900009004c0402c240c0c50b1446160015031040701c0300704190149090261070a98001c00f600101c0e03000c03041c2800400c00c0d0900030380380c503814a02c10034003510604505964600840c00c42d510024039110400000c0304054208500702e500a40b214007203100c1441600e0b403a589000409001c6506c10001088900e0b400011607500005800d1109149448e6242c2c040d51510716040101d04580c6030103405620803003041441c2d00516060400707000c0780b0103080f0041d48075510420b80b541314a90f10840d1005a4a07030340030000d03003860004c06a80a2040b80d01c1c02a11558480203601405410f0880d8107410b0780c004d204150384581c109071451410703640c40d9140d50203903100070700e840d04001c0e001a50640c00000e0703002170114502c421b4804101d03d555542420612003045e40071031711403804d0300101c05043d2008412914800080f098581e042041003488a2038418500207000d10584c00700c0d601e280942000c44e12500864048056075151889 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 583442131 1250 583440881 583440889
    0x121b010906020c2223090316080d090605011e0f05091b09040603061e1b03020c0a02180108060a09050c12010f140a0609091505130804150e 61
    0x501604000d80d012152101441c030f4010740184c03916034500c0c0040301403180c4030152015030302d5130a450780c110b080c0c00703507403040e24030021000940c0800040011803e00a44081c04c8401088a003c060040d6100060b081d0000101e034000000c00e0f0380081d01408513596075011001d466460700d00781c1c0002c85100710041072020b0204420000c0360001040b00d04207403102504881c05640b001c004504488040040310f80903119030088000550140030005007010f41220201e80415000180b81003007890607210010210f1002d20300d1070703622054500144c440360110385d11450700c0030500303000e94450034107142420b402043d008e405060300c103030b442034400d03584600c400c40007130314074554009045800c100440d80542c10031201b030075040106c0c0000403039441c90034400c000441d441003003881c100710080d50130004100300b0760240030014030781c1c40741c100304020aa03203545000b201c2604003290816103410110303595103451005644038980005600e07545a40d155900c0320a0260360400d000880c071455006581c07450 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 583443381 1250 583442131 583442147
    0xf0b040507140f1005031003140d0906110a2603130318120b0403091503091e02090f091c0206010e010e06060307030b0301021c05090c060408030414060702121b01 71
    0x4000d031a141316080d11410503642078000034102e0041142c42c40001003c560241d8140c10100071500103000d84442455000f005c107025074000f1014045010244200300340c00203908841660044441780542d4052506010f002c0d01c09001c3d480711807030120500140d100d4100000c8003e6209449001580c01583c05204910034284161b5855205600e1a0000b06007501d103803c0e0b005109107000e80f51191100c84c101c039030070708101d880d00c0085e0365840b02c0e4003003049461030904840f9034003100000644180d070009074800c078001e100c644154101c0001c1003440004001c2d20100d004c8a1410701c0f819105044002d594400902c10051004d6070080005444500600ca03540502000b800081c80d5581d0804254042d06402040c55050741d4200000e280f2624002c0e0841000d144480000c106030510b05003141c075000d14028058483e47c0b08200411410500004171422521400b8280c60381613108800500c841c02011000394200c803c00060344080440412216000f100c140c0ca1503010f03001c1800115075100c = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 583444631 1250 583443381 583443409
    0x50f090c0a1a07020a0e0702120405031e120a08041101051c0207020f06030108070303030608030c281e150c020d1d03011a0102060703020708070b040f0b04050714 71
    0x80d03102109010324403030000480402140c141c2c405103020141d40c007042802000e41d0105646c40c0d60701c424882d0a41e0706004000582200d651038504040c203150000c0d48505607445c040919542c0c0c254100152501031210310481c0300e0015400d42c540745c1c8000d015107103102c115003c40303500b1117100c4001d11543c01941602d40d60401108130540c0c0c804900c030860000d601c041800d9a00250164110100f60354082c021400780407002c003c2c082e5185140b41c0507081c1e485a400403036031900705020480480100107440c9104205041142803003d030000b94203900d81c1001080030340700841c3d002c0d140301d1072071b25003012029091065400d00070800c2101342d01400c6403075506001c40180c100c810040700040c440d403428012490594901c0c510703c192130300060300310313404a0448040640652003030a40c540c0c05020043d030041c001c0c1800e40c9014000d40e6214210b1003400c000402803501913011400b0722271b4030800300c0a0079501c0582c0d041b0604080c14503541da80683c1c411507400d0591058042c402d41400c0c00c3e504255 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 583445881 1250 583444631 583444639
    0x3070302070905040219170c090f060103020708040b0a0302041401030b010e060c07120606080c0a12060c03110c150709050a030204090f0503040608010602070b04060f0e1210050f090c 80
    0x1040c1402c042c1809007101a005a07440390711034416603460003070601e520b001000f014148a03040300071717070420a04029100d09003c0c0f00300011420403d40714031500790550720400c06d180c0103a6554207450712030181e0045410101c1c20700350104a0b020f03000d42642c010801c0e01c414059980d00e06c000304004500b035807509460320f8000340240102c01c1042c148100074003010070800c0103494020392a00381414540360031207400d607112a100d1204010510003800322031101c010603104045e881f410010440c1300d0440e0400003c2200d40e9810401c01a64481d91000300b180000e030314115521842410300c25580c101c204a040c40e21598107010981c558000c100503000c030b410240c006090140355400300300051032142001c6d07e9030f6030803000711000100d080c00180090040d540b030300d585950500344001d02d4003a45411a407104402000148086c0c1d410a06054580c01030745840c402d12200000450417841500c00c41240c0c0d44524400b60a1802c225000f4034882da40e550030b01e6809513605030900d0740c3d644510500d20b0300 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 583447131 1250 583445881 583445893
    0xf0b070609080904020a030603020f06030108060c03040c05060418063c0504020f0c010605041a040525030b0f0303070f02150c10050105040b0a0f060e120106060903050f03070302 78
    0x101150070540440d0700503041d241c204000c02000c201a64071031142800000c0e9500000e100b14901980305c15a01c56007500d210b1f043d5810184100c1c0c0d40c40028203130780c141080202c001002c12059085035801b400018105039101c0f0741da90341994003800d60712070200344141000070118018000c009015890041c0040d01d5680c1881c071040d00c56010011222a00000801007001c181c0e5112400142500750400c000d075943c0300b504103a09421641c058019510682c1030a16a04844203840e410140c40788e41200c1c0016075407a03807007400c8001d4021001515444580d0360340e0080309609a030150102500a440046411020204041c0c40380b05070704000b8200c840e210780410243c1030005207105c0340c2c584c217441e0501c1e008411555500d40f03089180300c000316070b0320b4000500c82c5081900905400650540d20120128200000503400004d0707070040d20700f000000d4149886a9480c0b5004208803000d01e002080f405485070340041040340a0700003607d0910495a1040421500000f00d0361120303056406006 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 583448381 1250 583447131 583447133
    0x180f2324091c0c1b081c020a0305040e0c1603110111070c09020a2a02041a130b01030902120105040c080a240605120607110d17040203010e190204060f0b07 68
    0x756950804015100c08060070100c90902d08144d49940207083e402d0028004a45c0125070210255610655541150410224000080c0d0400240c5083d0707860302c075140784259515000d0300514022030b1020580042c0c400c6040d030505400101c480d40c0c0c8a4510000c1c46055040c6241d00700381c0c407030080002c4c503400c540714082001882c25400b600c135a507000c5c80c0003081c100c0f44100d101003e09031010b040040008200100c0c00710b103480c1c0725814580c0c0e102c00002001909d080c0c00031f5131001c0b4000c1c0110300c00351a945403d4881e8841c0c1d00c0161521b0340200801c00e81020301e840c483c02441e00304c4084401002c20540441c07013407000610810013661040b811a03001046600751031500c110005400e504a03101c00c0d000c81c41d640c4a20701c18000c0c09c1c4100c024011072400c100300400e60290201a24025007103482d83c1c1040b6039100e0700780021f611103404040d1042d1644d2002c0790040402d042920850300814811740ea12003100150068010f000301c4041c00095180c1e48550b183c0c0c08c551044034041d4104112000c = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 583449631 1250 583448381 583448387
    0x1709010806090603010e07080322120204050627010510080907060c0512030106050a0801060302040807051908070e160e0d0b04050f070909020301180f2324091c 70
    0x140e20243c080d00100c3c2c0b05040c14545494554580c04c00341d080c2d0404103c003c1c0c4a0600c034a044040710020751784001d8a45000001d500080e44100d029015507190f0002a0194480e00c2c034180e00420030341d80c0140d51a40030084a02c05080078050944106481d00d1100c000600c50b545144c0a40e0300c0ea80078004a616043c030664000300580803c541502400080c583d1500825014600078001900c0b43c0e40d9928440c60300521440c01604800c061520500081c40f440034000348040540781d046c0c41444018540f4442d86404000c40d5000340290320039140e01117402084904018021181e0714003070350307444024000c01e40d45a401c1d441c10300c1d04261001e0b0600b0118143d0005240c00c54054400e0f00d0081d01811030441c246220bd82140d0740d4551183c90010850609205410038a130416610005100081d9a41c1050325034175040070300440e20b10031a0101b035020380455050012086011604840b0750700034100e4680a0135031034201c4000d006400075440c0c00012a141003210040064281c10052900f011307 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 583450881 1250 583449631 583449649
    0x71e020a120309031e060507110601170304030507121217070309031b050d0f0314060105250605190504020d02010810051903020306160206070f0302190c1709010806 72
    0x3501003120f444000004a03d015440c81600d440d00301e1980b0f90b02903103082c5841a900c02520360342c100031400820b9a10020041a00d505440c1030401c0c4141c0c0b80c60780b03001740e451805980c101a100d401600c030000341daa0404500c4100080c0b1442c4020b175100b000d100180c40e0503005500d5000418980c000080c150b62103a482515603910074205207070445c00c601c04860081510890803220743c3e0020a8076507880e500b00c6200c0322100943c1c40c040c00f01141807625602d00320400b0b4003a505121300840e6101200b00446e00e1054014a484080404140700b400e0003070243c2400d90b0042d480c40310503091a04010014080c10340b05903005040d0b4214031881794011960303420010030140d901c180148000ca0a035030350b814414015034103020f03c1c03146541503004050510300090098490341c02442c0d6100201900400c14980c00b0f001070901262859030494158040c0c1302d00a5110002c40905580c118025000401214043d0003560310084100c01107080780350900c155103c0501058462000843c589404012 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 583452131 1250 583450881 583450883
    0x70c02040506061216020106150e0d05190809040b0a061b081b030903010c0c12081f15090501030506010c060203040206090312070303051b0703260a02071e020a12 71
    0x20325240113a00f01d4000b08000c0c007514442030b045885203800b00c03400d03824080c40002d001c582a114241d681804000351214120001050154030403010034410300c0020f00141d003102098020981d20b108140c94281c480c0e500200702948940e01d014084840c1d0b0a01e00101e20548945413a036520481e8690010700f85081010012140c0d0142000101e003001d018007031800100075804010354a81e0026000c0600307544400090700700b04144007074981c2c045100d405920700240c0380b9042000ca25264100b8540700d800e9510340b03442034200c00c4800050140c65124011038441d850ba65074031509607c030710044041d55020755805000800c00d2042c507000c49d0780b07980203642051006010a141900c0034011904011028845442c102e070049034100c1455010302a581c0d0007050f401002d0f00405240c441161030740a20100501005215510700000c0541c08091079040001480d01c1c62062402100300c002a52044004031552110610006104c03904040880b083e60760050107142c507641440c2c011038a200b5132041c = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 583453237 1106 583452131 583452139
    0x20f0a090b1603120f0213030b060103050103200609120d12020403050703030804081204080904150510050c0304151d0315061201060509090304080c0603070c02040506 73
    0x82c86100c2e03036a141c00c00c0928800340c010b00c14018000c02ca8034444540c40095802580c460404018003184c0c4100c44006080c4e481d2401102561000e2200501d8080346204044500d008070864054030b00b8060305241c2003011000004108201d00d08400d90f641e00302201e0641400e41c0003110101600c0c00a109518051075640c40c1d56807030344180700160800c0099008141000303070507801c86883e050721420040040c2482e00b007900440e800704d14030600c0307140307001e0789416071442c03201200049640c001c1c80f45541450428041c0c5e02c5074802c5120088a0004000100f03180440c101410700c800704c1555007010754880c03600141c4208a039101d00c14840d0f44241410743d21807854881c80f9502a43c2600c0303c1c03891850b00c0c22240d01600150308484e606c40010010030004000002c064030880302e198040f1030041c01c44506002451105403500400240541d0142c005400c1c1038001c1500b1401c040c0c = true := by decide +kernel

theorem cover : BRFrame.Cov 583273381 583453237 := by
  have h0 := BRFrame.cov_init 583273381
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 583273381 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 583273381 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 583273381 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 583273381 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 583273381 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 583273381 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 583273381 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 583273381 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 583273381 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 583273381 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 583273381 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 583273381 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 583273381 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 583273381 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 583273381 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 583273381 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 583273381 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 583273381 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 583273381 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 583273381 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 583273381 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 583273381 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 583273381 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 583273381 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 583273381 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 583273381 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 583273381 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 583273381 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 583273381 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 583273381 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 583273381 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 583273381 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 583273381 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 583273381 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 583273381 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 583273381 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 583273381 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 583273381 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 583273381 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 583273381 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 583273381 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 583273381 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 583273381 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 583273381 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 583273381 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 583273381 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 583273381 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 583273381 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 583273381 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 583273381 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 583273381 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 583273381 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 583273381 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 583273381 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 583273381 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 583273381 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 583273381 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 583273381 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 583273381 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 583273381 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 583273381 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 583273381 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 583273381 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 583273381 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 583273381 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 583273381 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 583273381 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 583273381 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 583273381 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 583273381 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 583273381 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 583273381 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 583273381 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 583273381 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 583273381 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 583273381 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 583273381 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 583273381 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 583273381 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 583273381 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 583273381 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 583273381 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 583273381 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 583273381 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 583273381 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 583273381 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 583273381 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 583273381 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 583273381 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 583273381 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 583273381 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 583273381 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 583273381 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 583273381 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 583273381 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 583273381 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 583273381 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 583273381 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 583273381 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 583273381 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 583273381 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 583273381 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 583273381 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 583273381 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 583273381 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 583273381 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 583273381 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 583273381 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 583273381 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 583273381 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 583273381 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 583273381 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 583273381 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 583273381 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 583273381 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 583273381 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 583273381 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 583273381 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 583273381 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 583273381 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 583273381 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 583273381 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 583273381 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 583273381 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 583273381 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 583273381 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 583273381 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 583273381 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 583273381 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 583273381 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 583273381 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 583273381 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 583273381 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 583273381 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 583273381 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 583273381 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 583273381 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 583273381 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 583273381 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 583273381 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 583273381 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 583273381 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 583273381 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 583273381 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 583273381 ≤ n) (h2 : n < 583453237) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
