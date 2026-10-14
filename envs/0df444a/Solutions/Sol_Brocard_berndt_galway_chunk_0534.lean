-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_0534
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-13T20:18:21.986496+00:00
-- url     : https://prove2.me/submissions/55c55b2c-1f03-489f-a344-b26af7e5d848

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 95863309 ≤ n < 96043165 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 95864559 1250 95863309 95863319
    0x9070906050d021008090c0406030807020301050c0408060f0a0b040906150501050c031e040b120a050c04030503030f09071a0c070b031902070204022505070b040501020d0822030207030c 81
    0x90421000180c2c007500c00304000c1d084d944c068070740820007481c0e06460310849603003025943d1940201c6004600950030701c3e0f07903507a080c01030500b0342d80001d05030340c0c640c1010001048408000101181e02c102c0e8401c144840d5111100e034140a00b000b00b01c681ea1160900c41000e0a010b1143d1004002c440d0000ba41c030316142e5504015907403802400d500c640a500140488402c1c070301000e400080da22a101c422601c5c0c00e0f12002c0c9124180c1111214904c811900c2d020042d03043c54501c215600080c01c210401d04040c0b130b503900c2951b02d00c4001c5c652810185c105c400b16202034010003d00c0050610504800300c11016051050816004a0901d0005100c2c4690004d088031814080702d00400e4080c1542d20303042c1c030040c3e4400c080d41c4205001c03600710350300300003900c5694240207190031000580005010100d205080041c50031010f9040381d01c0c203001c204070410103a82c00180290700041a0700f00703201542d035440100f201800e20740743d0441c0315001d0b1200340c3c0201680803500800740e07481045c3c2020540c0d00c1d0 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 95865809 1250 95864559 95864569
    0xf0306050f0a0b1804020a120506070906030207080910140307030207051e07050d150f0603020f0406060806041d01090501021b0c0102060103351305030303100302040b01050c060907090605 82
    0x100c0e54954002444d00320714481500c4225031507500c44c0c0042c0405000b590398410080c105080305c4004d8445421010034868178681c000c05403001132006141c103509007202e0f0703103d6242074411241124491a942e4650b41c001500401109800c0180300c80c14a4aa14101d10050060b43c08090102d8a50003108462086824142c0120310300080e11401041d280c1e04007070910071200c154140c2541c40c4080c00300c54940b04011402116802c000d203a1001c5050343c07440c03062052003816200040d1056082c42c001b44400d582c040040c80d1300003c22200841d040200304810207244000031164142035080c0b00c03520090007415001010604003525140c0103100e1200c06480e12038242e00300542c01130f00b1140041002c5405103440c00c0200312501d80b04541e81d004000c0298114039000e070070031001400414940074125041082500429095015500e10f04c0d10550325007000c091800000e12443e41c030380c120640e03a4410005c0d07401c54082c0b8411a800c9003081181c15035101d00c01e118901034142080710100f080d0800c = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 95867059 1250 95865809 95865821
    0x101a01020d1803060b01020319020114060904030f0305100302030102120403090f0f03080f09091806150a03170909101a0a05160311070e0f090102030103050703030305060a0f0306050f0a 81
    0x508460560b100e040d0780d91240501810040c541c1188003d12040c2c40c3c2400707030b0131800000e004540000801c006082c6e4441c029070700c01080e20340f04107400c000f044080307904164a0012041c030391800050aa0f038044450500001c01d400180d010340c408601c6a91810300e0b0049039010354001d40f2401d000c039640b04c405003c901d4090240c13500944032607100300002060003010b844921003500107207050615103000301d00c44a00403200104680082030401000b40f0062001700c1c3c124102541c00860002080301240b2480b100d0710004045540400741c3d080014091400ea800c508401040a482400d01035000810b54980b40a40c2c940361291440c5c0c2c5401c102c1042c2110b01c0c404050301d51500344145040108070018188009a0520151100c0400b80c81c1c0244803e0002e0b200c62081041507061104481c0708100008000c005168410001400400c4001809801700c0c1c0e81440e01007010759400d004a00c0c0c4111a41c042c0711003890342e0402004004a6400843c4140b0099144080c1039840407010002d6582d = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 95868309 1250 95867059 95867087
    0x204260106030804030f0204110307031b031b1b05010c090815072007030203030c010903090806010506041205010b1c111503062103070614150a09020c101a01020d 71
    0xf81c10001000010102e142c41040c0b00d00050002403080c064100310040c9030301c201d6210f00000d540308111482e042d04020200c01c68146842d00f040910002982103191410602c1030400b031001102d00c4c0500c2101c01002e0b5050107034001d00900c04809401c6001d4540565805042981c1c0a560000c845d00904040c40300d203e16001e645030403884001e141d41680c55541403401001c03502a1503408000740c0c8080000b010312410541c00016900d80a0500410805940d0814911a00020300410040d5030700b800380c80948070448000c4c90203030b0440c82d182d03004001706004c640e00001c2c250a40320100c480060010070050180d0444945090309404100e007202c0e46054129043c0d90a00c04906242004c88128150402040f200d03d0407400c100b0846145403c01407080394666141c03141940f00030781c0890001c4d04407403100da200c04004019400141901c0047c059280483c0d0302152030581e1060030041548104450b540c10007550200340300e0000c10442034024240907100b0341c0f4810202610415030105964 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 95869559 1250 95868309 95868323
    0x10e0d1b080a050307170f181605090606071b0603050a020c06190e03070f02100c05030901031a100809070506070804030b070504030b0a020a0305130308040209040510020426010603 79
    0x1500c40043e0340580001d400c0004006201d00d504003403010a0100b94000d0b503140b00c1191725403404944882002200c402c4181454002c1c0060101007440701d0f20007401d0b00d10480341a16190364100c04503c050242207000341080b0700c180d000100244c180910101510841c1d501800542c0e500701070101a44905180e600039a4401d000007100a5429200f40c01c5441d103101000c264030417100c955528580080030240c44421001e0a100d0840c82c0a0b604000d034030449090403000d0f0340c0c0c50385074140c40b40617004001d410f060302c1d421545031b00380b848041d010600704020300e414160104610024119038048641d0f00640c0f05107400810740346881030a84e00040c1e80069514602421a581c1d00304140003d044502802001c0c80080009004418410721617141884016120100340100909440000d8543c104004011600002090b4810660fa9000c0e8060704c2d1401310352207500d81503240410700d181d90340d90f0038400301d00403c01e07058110a1003520303810030301b004141c0202c60440034201c40e02c0e440300821306 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 95870809 1250 95869559 95869567
    0xb16030501030b060d081306050405030f01060b0a08040f142a0a0603090618030c060605040209010c0803060a08010f0e12121602030702040f0608010f060506090d060e010e0d1b08 78
    0xd181020310607185c1c0b84907003411401c0c0512030314502c001e4a42a0000d801142000c40c040c401401c00700404400c00e51000001d21449240803400400d0b44030744000038042018400000b01031005540c18410035030b500c140c0310300c0c3c3c003401100d41d142c030f0300d0a40c4202e000a24150010706002c1120114030005182c001b000c0f1040c55141880607001001400012220360741ca62040310724920a0002e98080d0901075260a500d0b00360a151a004488481c1c100310b10403881800500e0740740e40e109581848256000242c641e9a48914000408400c00b640c0f004904d5030922a404040c1c0c061030308203040070b0007543c04880e103000e0407140b850240d0103110400c0d94070030707040d0001030140d890000f81c5505404441c0181c030f240c01c009402040540b804401d50407070341ca494070410400c1c0c000c2481180200c01c0305440403c9100d041100142c09485013110141c071030081c0c884400c00380f00702ca034880c01c00c2c07005a0008201005000007419180ca510140038004203460b1820482250b02c52050f00300c0c0c0030ba21010141c50 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 95872059 1250 95870809 95870821
    0x10504060e010e030d020606010f0831060f0f061205030306101404030c0f14031002090a170a030e01080408030103030f0c051e0601080a0b1603020f070b16030501030b 73
    0x394052281c0c1c1181001590b222400c07581c1c0b824030120f1030b48912503020381000d19225002410009640b03198104002c000410401243c03410360101c01c3c42199400030902c02c68216914002c00e091178480035161031b20304091411202c03030940c084c80f02001c00800074410b00350785214010710200d010300041c2450f08200001047d6140c61000035402c032001c2d0a0211590f00c480b18108556001034004941e80301074180e040c4807081c074a080000050584070528140101800d003c40c1e180d030580e10148c01c1082c1c000c81c0d0380300343e681c0d032503088805806c00e040101481d4404220349a03807601c1c0c000013070f00818080c03075075030300954840c542c00c501c40c9030401c0b01145980d2860b0b504a506522100c41c045c00c00c180b500c04c26000480600c148030a00e8110380c0c2d904010301a00844500f0b0500691100e640d41d406a02c80800051520503500d90110b0714582c0d2208600220205401038410054085004000003500c0380070003030510b06c0c40780038154811000c88041010041981243c3c000e01000c2c0042c0320080011f48 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 95873309 1250 95872059 95872067
    0x50312070312020304060e0304030f031b03020d0c03021c0c020f040b2803021e03012a031107080406050310060c0209041101120c0207030209161b1a072006040201050406 74
    0x85c00500c601d6002810100c150340d05070440c2c2268108850304001c2c00c50b500d060541c40440e060840c02c2010081c40d80090700d55000e03541d50825a1904103114180200a0038107000f84002c0800301c0510f100410200041e24004010303040c0500102e00ca0629802d41902608091242c960000009480000c80541d02c41018044030402e001c414032080700c0d54004801078407401c0c084003690002850200076040c0d40410035003906e1700c003290b009002e200802e44061100012840e030802c498941000182c0a410880d0b62450340b1400502500e00c62001a0000c1c402c5d91010086108031007580302602c0b640c0e1070704c80885002c1450100a540304460002041c007260400b0f44003504110141407640c0710709592061402582c41c00070003480581c000c000200190308241c0301c0b00e94440000140d041d8000b609a0b4050700c031038903058201200b845a1121902000340d242050300c02503054240c1d0b044180703012007006200d600102d0220076082500010848540b0000501034002c0d03505031211400e05082c050211 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 95874559 1250 95873309 95873311
    0x3021b01081f051c050c0928180c030311010e0a080a1803050c12030c0a030c02030a15020901030e0f1b0616060207020906061e07080d050f010503120703120203 70
    0xc0c0c8100b1640c000445a0302c080c0440c1c001a0104030198200503582051400c150081c00410700400040341005240d020f10443c0c443d11200101c0752107211800100d180c4014540002420114098404642c080c04803040b40b100c1103902c42d0341c4105402d17010b6110b6a0980d4034030221040c15901000800740080d240201801c440a070500c1c0000c141549020302c07140d515565807068403150400146c0c404e00e81031081402162a850000130b41c5440f00c2c20602566580c1498806000c2000c071940500844d176090201e680c100d13030014840c1c3d00716400b10040c00c00a40c04a03a4140c04a45080780075030017164003164500c0c45810f00d0340a0000103400c005046980148059004d0b8407420802c28400403c400310f60480071180180e400607103500907032061020a24003d449184580703001d005c29480250101d080d5076001e6141e07886152141d5042c41e0001a6014443d0070076407142c1001e0070000a410764112240c1268000c03001c49a060444100c450070501c40d090010b40050f2010020101c0c001d034640041d = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 95875809 1250 95874559 95874601
    0x60f03050406021207120608070e06060a020c030f24071728020403020a0501030b0604090c020a060507020c09070f0e04020306030c1807080919030f022803021b0108 72
    0x9450040301c14131404802404030b07921400309098001c01550786049201c0c00700504508070040c6400c60170003106918080008144a1103120001510308505200f4405043c5854002c0d04440c10079a41c11286500e07610440304034071315281214509002e000d10280e016005422300c1e103030004210000000c141243c0002410310f40240c2101301d0210105c0d201c007541500f604020b5200607100c9042d88100048002c041d44494101800c100c411100c0c0c0d61504100c40440e8910b010005107195001016418164a600c0c050f040038601403c010000e6008104460925800c5032400b0040d903403040190380c6d0009021900001440760301400001d402c1c25030003542c126200804413082401e0030030015100e0b4541380204207521a0034030600c98595000464960040e06c182d01414100c40752401d1100880c9103580302408000e15035503070400960003403044049840d01c1c080c141c8070400b182c518864981059240840040c46640c00c8103030800c023003111a007080b000594811016488007110000303400280800 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 95877059 1250 95875809 95875811
    0xc0b09010e030c01090c090c0e01050c010b060f07120201090b0106030b060d050709081c020c0d0f020a170c1f260a091103060615030a0213030614060a060f03050406 72
    0x1c00c1948003020005807a00400440c00420300c0712452412040780d0311940d0110a4240c240310a03040c4083e003100903011038000a10348603446244960382c0f5809003120220b5107403c4000040c0c10180d128003800144005070251460755400d4984000803403c0ba85501809009203001ca0018001144280c01040726060000c144504003850b034a040c00c00c0351402e4480b4004102a454200706540052044c83ca01000c0c40c25400590002c41401a45420f50901c0b458071601a0400b9001003003014605c4555403034019008804007521201d050400745088082c12a144c45102080c61141c41d08c0300520210960140d1080217070350f940f5406441801d99008140040c04848a800b07c0308101d8520f068444c84a01c440821440b2043c00c001c65011b15543c03031540642c02207010050b0316140c000d4a0190003461507030311030b6a81d07106a02d000c001d0007030034030482ea405400103001040c8030132034108400352200e091100d01d068658a00300b1003003156510584002c00c0c6d0040f000701c21680241d001940c45400780034 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 95878309 1250 95877059 95877071
    0x90b0319020d0f0203160201060e04050a110402040305010212092503060209060c0a0606030201091d13020102010e100504060b04090210030902030a0f031e02070501020316061127010e010c0b0901 85
    0x10944140c0e002211442e84500a0200c1c6d200c001d40c0c2401f031080180304000002046060903261a91511032100d0064440c4484c3d1241c029140c071035a04440086800030000c5494280c001c3e10041140c01c00d1300e20f001c1038490b1004603802060014004003401d038840600442c181d00d1640e54174042e401414440d548114140400d655000c418000039500310b12030b40b00090750b030b0304510004d00201542c4e0060000c43c00010800345100c0c9840d003034640c01c08083d41000c1000d520910040340035200007009542503001302550154600a10380180d80560f200e0001444036090600911084604504c0060740c800c829440b0380e400a0701a500c4500c4890020341501d110300300580b1a6000645000c00440005403404c0a0f241040309102c0c081c0b030300030301900c0039041e1a032402c00000e6803402a40310031070800340308240000400034140e0040d0006100004c40316207610103010b003041e0b004400051106954000020591998815642c0805419058584980c041c08544034034040c0b4000510b07081c295942c13a0 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 95879559 1250 95878309 95878331
    0x1a0403030e0f060f03100b0306010f0c0f080a0e01030f090305070f0609050114152d132a08010602210c070e0702010b09010503030307030c120905070303090b0319020d 73
    0x1034000c1c280703d41325078800756403401c00310300210701d0b0103031940f00d00405601407050201581c0e02c61090420a0601e24200e03604513118204020510750091004180b004000786038424180c00032100400040709880c208030b814000868042503c4060400400048c0100f004400140c0341c10304c0d420301c0c28001c10300016a10700c40c5d40e60354219680c500451261603040c0041140028101034100864003099412054222582400360121801002005c800005241400d640c548a840410b81c440c508524207007c10501031122100c0004070b03203202d8084003803601c024080d0a00a6082e2412100c80340c1c0100000102902e0b1107120001d003008007208030300200a0748001007020001c89000e0b00b1000200002403d181e20041d08440503a0482802518403d004101542c0d000c400c2d26440b01d010b0402080c50380201c00308840441509070241962860004180240107000078114242c80c403d40b20a05599260700e02683c4034001229161501c80421004040b00040f68020341029060f110300030440c2c0ca401 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 95880809 1250 95879559 95879569
    0xc03070302010504060501050d050714010507020a12020306010e1905040c090207050601170d08010b090d050a0f0b0703061202040f06050a17012706021e0708131a0403030e0f 76
    0x21450039001030391a0014041800714900c80c25004110446428501c0310343c55403901d844030458414240078540d400036944041c1d0060084507140d65004003440a8035843c0c40d80050100f0642500b0790203481524008280c0b82e1a07005900c0c0551120650140701c8440d80c1c45a40150400400444241c001c1c1031000a030050580003811020b48070344054046503040c0f08081100310241d1401840c00c5e4010048460314503005540c09055800d40d82050390384450641c082800340112180003046882070307007424810b100d102c00071040d8451051001c1d0344d0039200c41c074007101a90f609001d415011282c1461000040c80c19074803010a09030701000100303500c0e80d02c90014030007010b10352200007260b07512095440c0c0280700388103990301d42c04075581d024104d4160070400940700c440e41c8401081c5560000301c0740d06480c80c48520010f6240740484482d600c200c02d2070002d0312070b0844020180c407a24083c501259001c41d5096401c0d0920203003c4e0303181050301d15181225940b05615015030440e40e03200c000c0e50151a8 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 95882059 1250 95880809 95880817
    0x50409020f0306100f050702130908030f0a0b0a150c0203100e1b0306150909070509010b070308070908060703020f130303030605100302030c031302040b031b040c050c03040b0f0c03 79
    0x400802602da2a0400902070006040480c040410988180110750144c00c030055031901e40e015104050448220802c9800500401c2009050f8000200800180404100c501c51080f24001c2040c400000e01e4070620000481a01a891035075240090141c16203205001c142e860a00041c211100c440700c01502d0400c0390540742c540301c003e40080a4101d00b050941090141400d001d5009040c249444080c9603c1550f890300424459071210f004164641010841c000150000400c200020b5070341c1c541c80400d642c0212401c902003034100d00011b40850144c10741c081100c1d984009000c0f6941e65203400c074000d500222906150358000d001500c900d6807030030f0301840550312035180040c01070304140c00c2000c421a49075000c01014010000c11420740381c408141c0b604179041001143d081c58040c80028050072405901e940c0504c12039142c202d24040c0305011048014040d81c04200e00092048210344034401d80c181c401a9030b104100c04c104c400701060040032610a41d91740c0d1818008903e001605541c0 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 95883309 1250 95882059 95882077
    0xa0b0906060a050108040c290a0207050405160909020903010905070e010504141b0d0f02030a091401140c03100513020705010b06030403020d210e1e01090803040f020105040902 77
    0x110550030000d40b4280000924042c2c03e003400c0400d068030341075a401e04d1006450142032008444203002490340d4145e00400c0b000710840800705a1a01c0800e131f0001d588a401e0301c40c40d880b550820010a04000700d0745900840c601080e9900d0400500b01040800030358000c04d2841d070959640e40c02c0501190042c840307000507080f0710b80610301c1c0b0751400b0200b2081d258106111405d10b8414400c0c403181303250342010110004c1c2846121600d9000400b134dc000107001500c81c00342881d000000700040c2c1d500d00d030300411100c0c1c0702e04904c10414181e007101c242210100c020101c03040c549400031035002c8100102450f885240700e040100110b84030404100c1d00f07072031600d00302c0c1d090381c002c5801c400b0080c00303018015080900343c84c02030552900e6100250b44007070700386d041000c0c001d0703c43d01400d4000390081200d0303000e151050144403940041319010b9540e0500030040a20b201554201003003038006014801c0b1042d001440b01d400c40c0c41304c0c0c1303d40d69442a446002c0741071100800c00010190360500141c110307a0 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 95884559 1250 95883309 95883313
    0x7240c0203030d05060111010624020d170604061d160503011508040519050a051902460302010210060308040510020f0a03080a0513020105040603021305061b0706050f0405040c020a0b09 81
    0xc03481648511003d0405100c02b040d0b40085d0741d0b4840300da03030000302c071a200c4162030158400b40e01d40b45c01160041046400c005601c0d4032035560400b1410047c040c01d0700465400040500300100300c14215558042030003003006845034119024407a91046510319002409142990095000074864004d032134511141260281c2050b80c04005010b02070110072040c10741c24030b0311001d4244070360004001c0440d40200d846040d00b0103400000318001405454495198541c01606071400406022880c2c400303880100c0c01407241c4c070b03040c02140016004107411640d10070119800c0070b04141c2000f500415807890350f02103125256031107207030043c10452115214007944400e165410000c0400c010768400408654007200c01d6203081c030041c0d0f800350488082316100d00c3c0068548004040c100c003070301803aa00c920b621a40c08a000c0090b000c1569811440050035011101160340e21042a2454050009086100394080c0010082c0342007582190b9007400040c4181e4803941103a03610514a0041526210015 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 95885809 1250 95884559 95884589
    0xf0525020111030901050f07050309030a05160b040b03010b1e030708040b090a03020a0618170406030b091006080a020d021306031d280507240c0203030d050601110106 73
    0x141d600b01d03281200c410800740c00745261403114070010f001d5104c0c103801a416000c001400c181803140900c2a51394812005050303866041d400d0400c2d641c0c403e824441b03e5210440c8510000d5001c600c602158200d8036031024440c01d603884e09004807590742003042103125001200c0c1840c0150340401d00103500c2a00306071120745450074a820714080ca900c0081100e100d03a030202c800d20000c641c00040f6000c0c11984490040303600c4800c104005c0c1007070360301c0794020305410b040b01d4107002c086050000342c400e850142d1b4080160620700c0e810848000c10648044103840d015030414003140348603850701da600c04000080503107000c1401c504001240c1c405030b030240150780d14071400c1c05051b600d4000c2d00300d81e4810307403060140c9030550104144c90320788811001000d20b1003440c4401c4070010a254910791160043c068984903503032024201e510310141c42000c03012400c14178903029040d02450f00c21079115001f0f4019803c004441da0b0f408014070300a00520306100e1001d01d6646998824000c10b4050f101041c0c00640d0 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 95887059 1250 95885809 95885813
    0x803040c1d09100605060d0b120f0303090607080601080103031409090406020711060301050a14030f060f0f0115080403120b1203070312200703050904060905011706040c060f0525 78
    0x5000c0b03c10341d00c4204a00b020030411440d81d90320181e03001e5002c0c0600004003003441d200080c40740541600c1d800c1150041100329400504040b01540c030603140c00307040d1000ca940301042200c00c0c08044800c0750128400c42d006102007071140040d40100b8070301c051070300d161981100020700b807410104d03822030f01c4640011700c0304d00b040f9000b03400c4040408207840380c41c1554100702c0045c0d8130741840d02440d01c810f00c070420070741d81594040042d850325002d50f038203840700d034201546d0302e0180000440c3c0300d0003984c01803000080c210180f0740429080c40d07401d0b40d440c2401d80b40c0340d07400c07940034201254044a031601c0d000706004c40e5464180080400401030b004507521001403030301401503140d400d0380e080130600e00511a80c01c2c1140070103005a82a4000c0c1480c0e0300d04c83c034502524a17004603920503810610340030700840d0644407603020703a0503603604d03d45020002031004401d03a502e00086400800d042000e101c10032071309000e410307181c000d4200c0d4182181098601103452440410400c1118a89140d40c01c131142 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 95888309 1250 95887059 95887063
    0x131401030e010c050315010e0607030e03061006050702010302090f030d0908010b0102070311010305060303120103050a06060806070c030f1407050105070906020708060619051908060a0902010c0803040c1d09 90
    0x801c200c0000074040c81d0b00d4801c015000d400002d15021401c21044601807080c0c2c4a50b800365203044000700300c980c8031085820000c0c40c1108001c640c074000e200b2100892101c00c42150104d00315403066860600d4260a03500460280d0044114250041c0c041241d115941d40c085c4041224441c5641d0b400d03102d10300e49056142034404015110741990403e00d0306002150042101078550074081c203002c5410784030742c40405d00c0c61007401100c44031401d0850010080040c04209429140d00070791040c042541c8800300c040c0c44240903200d42d00480d000c132a40f034002900400c1480164a1a8142000101c882c010490b400368080441203429940d82e00400081075046480000945100e10042294505001119540d010090f24a82c8180c14840c248000e0741c0900311014013800c0003070030003140c03020a80c001007176069050041d0180c1c0c1c042d03400041e00344101c9200b02006c464050396000b403081c6081e1200c202c0e544c00035100356043d0030707102c4d00400c2504150808142070040210001514a0f03c001214 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 95889559 1250 95888309 95888321
    0x100c06060515040b0c0c0a08070e01060f12050c041205032a0a11030a080409050411010806030304050d05010209030a05070f09020f040603050a0902120307020906150a0f0513140103 79
    0x14402c80340c4a424005a40200742a5020303a48554905079640e0085e190311454510700340c100d50b40c00001443d01190982d00410040201d80c0c44100c00d248a0f600c482c1c09944661085001000290701c42514501100e03c41e048250000000d84586140c903031544280903203000c81c10030585050303100040c440d441d21850303440251030b610142180121000c420342d0040e119848840090306030510412a100c1c2caa0f81406000200d6a0120030242e072550b8603080b64001d00022a0203441e800c4542e983d0510039400384039400e2090304000c0203180b4150406040041101d0720902c19140d640d424407018402c0d407803c2000d0300c440c90048005161942c0f900e0f5420302400000e41141000078014008a04030101c06000d0380d0aa03111414086042c1c6c2d2aa00345400600c14410042d620030050741c40c206407400088000c08026000b41e850044954a076024803200d45581c5424290019040042e4130f4840d1207509048a51005032801501d0080003900644400c140f5801c904c04010ba003c084002940e0140b10f26 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 95890809 1250 95889559 95889569
    0x903060c050418020403021012060b03040b01060f0c0201051e0f0c030403260304240501030303061a0909041209031403040501080a0e0a020907180e1006090f050d02040605100c0606 79
    0x9605c2d040c19070740820b901c81d401d00043c6041c44824440400041c2c2c43d80c20a201621600f802c850b12882c10b8203161071240000e20400c000314031003100e000c17003a92150507044207640d0182c41c0c01d441c1c2500c030314941303040410740c100a60f6100414041e0b40070000703070301000f04008030402000759143ca040d410011000c61072044a60001458029502c0d1f40e400c09006803513100b500b045c02d990084481d4071a400c81e91000c1c0c0b000c820300501c3c100c000b00425816078407100175585604072000000d45020820a140e2242d505482d5002914000080c0060103c001e4046201a9490103d0703091365a641d4032603e007482c0d80f81c03e02003504085024461540d00600b15582302d5402403082c40031000c040080350700c40b0020b031006030059408800007690b0a014039107004210101d07018034104542d99103e0903004040a507400e407030590180c180041c503540314100740c0050301e04c00b1f100b000c0200d02d0700c000c00c2107441c81c04004a8000f611401d000400da03580c18080303c0401c000d911984000b0340c061603c00200c074215000 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 95892059 1250 95890809 95890811
    0x150910060903061805160e13150b04021306090e0606070809011419080603070e1009020a12090501050402040b0a0f03020609040e01090807030801060f0813030903060c050418 76
    0x20420080364401c440c0340c100ea4000d4800030300f508040108120106502c0b00c0900144103441c0c2c0840a240c0c5018248200e907280d4070f480c02c09031070301401c1d41c10a84000c40040c2800807401c04400e0341c0040c2c0d034400740001c1d000400041c648031030265200000c40d80c991142e0302040411104000c0300d200c01c2d00040c0d01c0101113030740502e003c1107541d44800b503000304c000381d6040101b1440c1c0d10492a4011003162600002e158404d00c0e011a83c2100510890003200d4050290084a80000f2116407004005006500140355101c0c140d0030805404002d40002401e401009044880b04000114900c50782046900403800402d20b45000d00501044d00c003581c45450081d41076070b2041280038082045402921740c11a0500d90781d03d28030000602402c8007039441d01140d46441200405c11507110014000b0500c292035246850307a888405840c42c00070022010701048040b0b0024103a410300303400050310070f44a4206005140c0c0c50751103d42c100ea90060f4444082080001c0030f10030b00c80014041c01c81040800d02c = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 95893309 1250 95892059 95892091
    0x60703050c040b0d06030b090f010b04020c03030609090309060301060e0418050d0c11060d0203040b070e090103080f1908070306050a05030a0605040507030f060209120118020123031509 81
    0x4100c8032600c610700c03a5040f10785020812140b81815604204000c50b0085540191070402c1e00469845500340701c000700f000d40c0303080180001d07420203000740c030504203051001c2c504541c1c0b41c000b0300c000c0c0e20340202032101a00003008040c00681c0c60002443c003a0801c1d40e142d031900c000510a0104680e80340765440007489440322150300140f8001400c2d4402101490105001c805c0d0303240036007501c0c64072882143c0c064404150800158000d9001d58440d82c090008845251100304083e280800044a8590826a014010300120b220b820040520300002c2820070310740741c5000240d1418660030701e103040002e402c1109004001c2d5160189202800701190f8801400340b42070b00003581c51882086c0200020703121705c0000c0500c070741400440015504015007080c4866a40340000c000e40c04880706910a10352802c07804035003041441511450040e0a1060003211015001902c00f4086442100758010b9107914400d0b59121030301c042c601400c03451540d03180301c0d404c0c0402c01c005d1200c020524103096072140307 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 95894559 1250 95893309 95893321
    0x9060503160f050d060305010509061b0d020f120f1611100c091503060303121e0b0406050406080c03011128020106090911030f03091008090f0601080f06070305 70
    0x88807a4220341038180303800350004525095410340140b440a00304d0078074186001040c4641900200e01c03820551060700d00719036442c3c4030411060501001c950355050b0030701815028031482c0d03005001d01b084040d019800c0002e4100c03d0041c98604582c07294003608420180311000290202d22004038503603040000d10940440c4000f946c480300c000040c2c849688904465184901482e140b101038200341548850711030949138041c000d0030baa1b120840008100415840e443e030f649200f01c011440d40041c04004c0750469200c9040500000398005600035515500054265078a10480c00148034000c00303020204490030415007160700c0c0020600900300200080160141c0c503e070346941c4124481c0c8640d040000481040b80184040e40206001605d410b41030400e0103554085618412030032001c40341603c03032100600c0d84a00811440300d40018264144803800c601070145554005034480c01c9910744441c1481c001e180900a038840181c03500507610300c284580c0188865a4000c036203040c00e10480c104a = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 95895809 1250 95894559 95894581
    0x31516020c06190e0d020d140714060d050a06241403100e0703060e0a0e010f0c020c041e180309060906020712150e1006050307030c0b071509060b0109060503 69
    0x143c00050704000300107500358450f076201101c2018464000d8908111440a450219604507254a984402d403041e0301000030380b0081101030712014280609004d05110461100801804000e0501c0e42c210303803200b01c00301e40e034490000f0415100c1400011048803144118025010102e240c2418403400030410030414000d0300280e501e07040321144a80f034489990780000c124010081e940052800c049000709024200e006d5800012050349141d0080040340740304803200303044a51403540d1402580098181c04514505540880c1c040381044200000d0b0b44004403080c0215200070780c108035040c89441d0351005050303021170b420b030127843e1604107100305a0408401035076665291140d000081c0305100e00d0070401610580e01d804001d0801014850442078000a03502c480c07182856a440380c0c90481d00041a180008960313007169046202008003505104103c4001c0d8840d4609859001581c4a10102c030b2040e48202102103014450000300644003e00040041070b055000400f01b02c4240140f210b04404 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 95897059 1250 95895809 95895847
    0x603060f081b0111030403050d080702032805041703031008030301030b19021210080105070905130f02040e13120305160e01090b04080f120c0a11031516020c06 70
    0x242c00082d03003600000100486100752030b140b804542e4080132800008010700040d510030300d03500c1e684a890391555211341c108d03900d01404e0b80c070030039015030400d442c2410700480305200e048060340e05d001303032a141e01c5003165080040c07040407008075a4000801c10440040d1250030002502c0303101c1c040e41c40d5501d182c0b2803030b038550ba0281203141e8400c5402e024150084503036040382c83c0b022054040700d06518100d07e5505040034036101380c1c0c4143d401c000009000e14460040c20b070030f46074024803107006091100000c4006040c04100103442690802c00070803924044a0310603c6207215242e22540780360303580350001c0c0c280030803c1d140702032500344018004144074240500250803464509241400183c0700101c0d04007841c0c8d03120200701da00c000b0740455070340c2e000300c0c9030100d0710741d558101c4001110a29a0600301e20030100b48180035080a804000010300d1020b03100703508a4000e00f01d50342100d2002402d01b9562080d01d5803a11402945003100003585c042c07092410440c000c8400c0d508107a0150781c8a0f000a10b = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 95898309 1250 95897059 95897083
    0x70201090b09010302091203030402010f08160c0c030b010b0703170103020d02130b04061701050105030d0f110f0709020a0f0c03050414120d0201060e1f0308031801090c0603060f08 79
    0x1074085980c4885034031070360540756080401047d80a03410540485c4c641c980e0b1068806a0016000c8102018218040c4c131059001e220b0141440c0c1c00010a050704440011a446040351100d0401a0001c0450041c029140c0a0315501030300c3e0359112a00e00c1e000d03001c000090a1707120740350011001080580d59946043c40c0158041c0c8800204181080901c802400e070541640e178800c0c90f0100124840c00c4203050841007040040c000c01850343c8400816688140707022222000800351b10790480c3c054842c440c0c0007459a10041111031811080c01e00311305040e6160000d41c0d0155001c59016003150b0b009070040307c140c0c3e80d400e01120b81d010a0310001d01c903124074040c0c54501140351480c42c4641d00d50b4200411060701d0001541ca12344003a8400034082d107110f00c645086c0d249203801013004c160500c620810031103005a20400040c0c59a501d45a0f2908018400555480b02140919880c0c00030f01075070b030240d486040061440350501102504480994105c00c9500342c6021091103001d0000445140d848 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 95899559 1250 95898309 95898329
    0x609060f0a1a03010e010203060a090608030412051e1006060e0102061b07051509150925240201060b07050c090901060b160203060106052812090302030c06060607020109 74
    0x800312210b9400500003450b401501586001e600495044065001c0d5002c1d00d41141c0d02c45540381d035500d10074141c50640c00386c066079401c20072041200c1c02c1d2052100040c3c40c0300c2d01c165080ca10403240b2400b40c1d2140a11740c20416000306818107605403042c4282c0d0054050350070051035004480300004e6a03800002c0a904100e40c0c0090080500f80400c0140c2e08099403141c00c841c2e02813200b0013613421000302580d94a00310321038862002104154060440d1040341028010a40390b030400c20703110100400d030380000a1540c07645001052046104030101c040c2c00c00d4640c0d22016888005000317085170b5140d48000200c3c0380c1448984c0c00038501241c410780e84802111110140c0d03c403203141c41d004080c103901a114101d0001b030b4188208c404d014000c0103442c000c605640c0f1070ba998400540780e900c100104801e091010021142c203030b810800d52000c2070b44561030203401342030100b40d0382070071140d01541c160056800495401e151560401040754800010341c2c10908111a6500182003811240103080c501 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 95900809 1250 95899559 95899571
    0x40506160201060f09060504110415050d0618050402010809060919060605060304120207050d08090d03030b1c1b03050a0305220f0501122d091b06020609060f0a 70
    0x900e200750448000740404c16020b203200c941d65a8800000e06031407042078012810001e003c46040b400c003058808407141d0300b40c030303410703101030038400311500c5d4044032103040c0040e41d5807404948586500c800a82d2410010700000300350401d4000034024400040c45146140e01080400c03e148001044900920745105190103100500d4079008001c2c044582126400c071901008100078044182040b224072540c81d000c0d56449a110014406509100d95014081c0c4000704800105800e000700b1f1015603900174a00043c5081d40b04002a100c903604419050503100d54402030014082d10180c00141e0300b0804241d080ca039841c2d944e929460301010200901800404902c58a82c009002c0e000c82600c8004580040c000d9100c8400070822200c1c0d00030580080e821040c509250046482422071030380e140c112a80c2e082040c007020080d0454164070510b4610780300d5402c2000142046044560854201000080c2c0d50074918000e250050040410031641e125a0500c004504640c550315000205113801041e1 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 95902059 1250 95900809 95900851
    0xb0d14041203091a0403090f14010905060904090c03060e07060309050c0103050603190b070807050304020d0206030c0708030c04030b060d0807030305060d051e070614030a05070e1005071505040506 86
    0x1154500d580e04d040c582c1040820042560003c034403c20b07a02c2d480c94500700036031901101c0c90601e4401c0c020038042042108c0078021450081c003d40305444005001141282e1a0303a01e070f00c00c810305684201d0f00291510740d0643c0b481420b21110300540001c0c94104113008450f21303460b40d910a00f00f44d0505140d51540492400c2e01c090140c10a200318140c456002c1c0d5240c0d107405100100b04a905000040281020883c01c6224201f124041c2d900100400c604a1098003004200e60000c1c000701d03a804810413180e80040c082c070000d90301c252034469006880d949142409206402c00801e0715110f800741c2c0440340b0008070314009880d112600340c40d00003072a07035a040125001001452010b0132511030009000e034615410015100040d0304c0c442652070340769444800344e40c9403011f401801c6140d2820b2001494a446a50003107038420307210f14002c0740148004011510002404a0b11400110000780d1a02480b1002d0004d1584424100003040103141680301e180d00c0e200050a1844960b03031482080032 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 95903309 1250 95902059 95902073
    0xb03070308091818010b01080c0a080702011d030409050708040b0f0603030702060d02130602031c020c07120308040b070e09040605060f06030a0c09090c090b07030311040b0d1404120309 81
    0x8112a00401e105034503040c081251303100203001400140d031640c20802ea140440d485545c01c5400380b0031120002c0d0410f17035150fa003078810b40c0c80100701804541da101080381c01141c01c120b41805240c01c01c005156240d080000507410b031003000b0640f0050001403400e120008074900f443c141d101d001e000e203058080d2190000241984114031010f9131003003003c6150f48049104d036005024181038004c03e0380b60310380d80300d8040e40c90b4024014541c0807001c04640d1540652416002401d44401200555960035111560b101c0700718480300058000615520801c0304000c00c07980c400e50041064209510707244600c41c0000d00c00c88000f032004120580307900116009840d18035248103070301c10003410b4589910389480d005000300b40c004420030005800e96000181d208242c424101a0819650b031401d00c242811159904c17a480541c085007059504d003c202010103007440944050202c1200840d5520303400a082c0044c1c0b8140543c1e145000d1807042400009285541c1000c52100c1c5818003086115403810800 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 95904559 1250 95903309 95903329
    0x42f070b09060108030712120204171506010509060a17010602010c0f03050108030702010509010314010305010213090b06090405100b0c100e03090a0620010207120f021b060922050a0c02010b0307030809 88
    0x3514004030740030680b0001c1c01c000340d00c2011420202c440000e10050314844cc80b005030b46803030100fa0301300104112403c04400600035841c0504102c0070700300403c280440c80c4a4260700c9000182d54440e00c0030b40c0c0503440009501e8101c40d5250521195043ca503603941c407071285072802414004005440180d590080d0003d00d401c0b00081035000d925a580d04045000c0d520916040c00341c0e042108000c1040081803188071240310029000300e00380b6502a0521006120140090654034441880000c160101c58004c0c041c69414070050100c40c5140140003027502d04107a84d11032a0f40080c82500c0302512515201c0c41200e01524200009810507640c000900c21b8110444c111540002030000520001b1503040141d141d20f0354607011107440f00e140c100c0c1c80381d00c5410351065400c50f50360032901c1880c0c002d020f00b0b104003000b040c1300040d5002c1660301181c001e18502015503c0d4880d0704000a401280c03041900c0c0d000310340003d01590b980d80e00081c2d102e02050100424000300400e4203081d0303485010b108 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 95905809 1250 95904559 95904587
    0x71215020304050705090601051e03070302070f03020a030212040605030f0c1611090a15090b030c090112110103060f051c0b01180605040605060405042f070b09060108030712 76
    0x856590030b0500b08a1303210440e0780109030040c0f4016000c580d8035441441101c00b100c4004120078080c0a1460520195900c00750101c0201a001e20000001c00c1c417420020f440284250010a030f40440c520700030b03080c803400e0310480d100c200042c0410130030713290401d00301c991102d070362042c0d0f000075525212101801d01681c4802403014031690440410090b2072801240100c1c800c50b0450300c1c9940b111070700415a01d140346500044c64140b4400c0115020799000440c00b11801001e0381c60f03041d540d4000c102507503c00d03400f10b0401d103660b458000a200d0204240c840b00c420030310781031041e04c1c140300d02000c640c5550b00c40e02d409440c0352100c510300309580170381a201055002900b10155607550b030903168074145d00384c0b480340c900346020000a024a02403046004880d4050035150800e49000d0030031004140069080140001c100f58003002c00f0b090b44420704441d4114001d080d04c40c900c0d42403e041e110b400a1014038207508c0880140201131000042e1101e1650240f0410118016030b1400c4661512100308 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 95907059 1250 95905809 95905811
    0x20306030f07081005010906050a03080a02030d11120604090b13020607170301050909030403050a081804050c0a030f05091b0a0803031014060703090b090402130e180d02071215 77
    0x400710300b403100030441040078100003a06025503603e0302c02c8542107440070b100327065102090050400000388407802800c448847e900640e41400d0500c8800c8040e1a800038200341d014000040907191015000e180c42d0300040d040d130301008501500d90b2001080513000e00784242c54083c07000d81008564030042185c0b0550b42c010000a81650349030300b0a04039420038051144141c80301400a0842000001618100ea4010004000c8005075444104090b800f644003041680300e0b41e0107142d4951260700030a4054400c29100e076960b4080a0380007401c4944281074440000d040000b402486040040c4000c81300f01c940b040703402111420b0340002c4424405910a442030300000c002c1048084901261380210780c0d15515000f00b5444400811020b03110391400140400c940140c140311895020014041100c0040c00041c42e01d007103005c03120008140707907100001a0310104104044c21020210008a48920000500c3d200c540c0d40800b94903407046000300c40d8440c1155a4107030901a040b008500e008040d950 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 95908309 1250 95907059 95907073
    0x120f17061c0602071e05030a140408030c060f100302060f0c031c0605100f050307120b04020d020d2007080304020d06050702030d151a0c0705090709080c06041503020306030f 76
    0xc2d20348065000640300f0740b5900e640c2001030b084110b40c003510300b0200b60f000e0091881d20202d54000d40d50807003d80c805c0c000f2241d0500c00800cbc040020001818854400030041c0079601d0985000744420388028200001c03207012201c10001a102c03402501e01c0040100449030b11100800660f5245015440003a0510004115200340400607580081b054407025030781c450455900744400e8801400d09400e038400500c0030400104610b20420207064005030306603020842807812000142070b6042840010f805690002d03a00f98042c0c024420b407414180501c2940c2825071003441800740d9801241e41c06013504800100043c01c40d40c1300240e0701c002d554403040400080c100346000954941101c3e03054040c0518102419079000c1a13030100703204880003c404c0c041709015035040502d0740c1c0c005074021901e91040f03000100d0142e845040480c0b09601c290388001d8000e10b00b100c00e514090240410030301413101040217000040b205010510080b849050261b503e0311107202103490f0040103e1451110b0084003 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 95909559 1250 95908309 95908313
    0x90b0f0f0612071a120117010506040c0f11070f06111c08040f0807050307140634020307080a0507150203090303060d0f050f010c021b03030702090c0d020a030603120f17061c 76
    0x1f1410040700070b0724000f007080d690b4080a0004603038a000740040450720352600541864411520500c100240c001074442c41a03945601085a441c80c2d0406c4012800405c00c400c403403202000340800007090603420b07110a03018003c010b080b41401030030140221248818560a2001102c00c50751070300c0d030010440350344070540c0c100100748a41074046142e603070281d00049400c4400d83c20843c030182d03244a4940c03061031115469040c4499003000100154001070000802007021400a854068010380759181d84089918090010300c5a22074007840c0c0b1481402813050b520700c00001d49a0045041d500c825110003942051081c2100950740242580b09070714403150313400c0d0103400c2070407401425003c988443c40712071034040b440c4000400668155000344903440151502d02d20b05500310911745540c510300412800080c0aa038840001100440c0d1102820010094075102000f07074070202e03280c140d400002c070400040c41030f82000140c01b110344c124000304d840d030703990032076064002c0c844608040103440300c83c = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 95910809 1250 95909559 95909579
    0x20a12050406140315010f0c0506010f0608070503041e021513090b03070302010806040902180f040b01092f0f0d0905060f06030d05030901090b0f0f0612071a1201 71
    0x1d8010080040d594003250944441c00c10141e0340120b4229038184010801c0d40011103001c0b100b400b05004000643d03a445010400030b02441e07021f4490b2940d101412030612a003c0c00795000036021900701302d010400c000119907501440804400c0c84000030300141c0041c00080c6d0940d8055190301c6465a00040300c920100031000500100e0b10300b0942803141d0040f000030907031103c0c024400030380810300550001d865071034240d00135690940b0042c20b0200502c00500c40720703907201c2c0850742071640c600300c0000d01051008499070700d4010071024201744510045500500c40201442c005080c491110001c0d200404000d10140d41c4401581c421854803182d07140c0540e030181440352400e85541c060080450300c0c28010880e058490400900106010361140e1021903030b076800280711120a540c3d41801c4d000151501c940c0320b0054801c2e68055400d8101840020440b103000360841e440b81c00c03032400300000a03c2c049405400c485c0c40c00f44070032040c6410780700400b4030710900311200e03e42a403000000c140c0c0055 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 95912059 1250 95910809 95910817
    0x4050a06110f010213060509130203040302071809020a050910080d0302130e010303020c010819020301143a030e0d210306031a0c0705010504030e0102011104050619020a1205 76
    0x5007004540198022034891401c0b4814140044022a0100010b1145c40d000e500145807020005d03210f04911a0041d04490807078100f610102c0068001d914100000c8a4000c42110002c044074420001c8034100da0000c0c40712010303880782c1c600540c0d400c80000d101040404010004203440170070380d0b1000541d014000c5c025401816040041e40c5420740210b040c0458009850580b58550001d041a540c0f94005407502e09000f01402010150081d41031061034182c009140207081e42014044610140c80801150411507010742c56a178254440600500d01c06000040b0903111403003445181e1070140c18110341c0301c4c4129110700c0c0c0103c020707400f280c1000800c0c0110464025112109418076017504411030a440c21031001402192501d1441d20f5154245030000e904803071052800b6141a04a681d09402e5980032502900800c031071240303c01c0c45507020300410148020100c0601d00c3d00e03041000040e498014290080114800b900d02d016000380200204c40115030452540c940600007100b00500541c0 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 95913309 1250 95912059 95912087
    0x70806060a0801150e0c130303030b0a1e03020405090c090f01150914010f03091209080c040b0d0803040204060f0b0310050a06120b0f040908040302180403020a0f020604050a06 77
    0x1c03400710002031014041c8200300c080803401c034041418503d030107a50010044007800e4001000c1d000c1103070020180c40c2802072002144a914080703203030300d5030b0b004104902e802a440702c4069000040742c0c140c0191b07c884804186c2e0fa0440b070014150310380c00c6990b0b2600b12486202030f0481c801400340b100b0301c0795a000c114103c410000c00500f6401c0783d104212820301c00d91160302850020441c41140719030140000c2c00a0490074600091450810703124601001503000c031500200303145040a01001c0e1b002d01c00f0018900040d102804180281c070040342e2a4ac2d08898003610b0040f011020a04556448e0441d038000c100c280704c1441e0998a4500d54495940140c401c000d07007001048000a0a00740305040800300c45140e00e5030040e2406100348200a0461074240e1548000b40c090130724031580e503d2080023481402480c103187c03207a0841c818080c030305039801c0722a50b04450b5407040100081c4e00081210026174020041e1004074a42c0c03000c00c0c010b0081d40c2110390b100c1c02411005c10b205a1002410780004 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 95914559 1250 95913309 95913319
    0x30c0d080415031d01060302011b150516031d120c031b0319030c050304020105280203040e0a0b090103120903020411190903021f1e0521010b0304030f0e0307080606 72
    0xb04180140500300c0b18113107c020b001c40c4a49181004d640d024400d8030100328026245000c41000038103541d4100d50040394004624003c1d000c811200c0380d0700d4441c0322600b010010071149080c00000d0700940e50014032100040441d0001074000c82910b040c425599481c202c50030302040103448030300f4603860790000c1900142a450401107101e455100b0301841205107d41d40720241b035a1500d800440d0103034880751400d521403d01140440c000a0f44825150700008507a010f0f644071400c206041d0f002c000050071040100341021211443d0390394000110341102d5000d12039651215041c041601d01041950011f54014503002a06681e842e602005250751481110385202403501640d0a8620b54020f0001079000754016a062048212075070580302540392504081400180c0c80c02d903a003621641800010000e003020038000c003200c4521040c003d1045462135601c03402d40c101801103e65000080010f4100b00d040d071900c032451030192964914402c806016100e4450302c1c0d10f200d641d60072083c0c07520f50140c = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 95915809 1250 95914559 95914601
    0x2121b0604032105040f080f07020a030c0807080309030d0e0a0306060b0301030c062309030705030f071508010312080712050f010e09030a0c0b061906020d0206070e030c0d08041503 79
    0x9090031321941d8030407a44503913040c04140150f01c68419035004155001da007110200030200150b507034640d02c14000d51080f426590100e0402e04a1810140c00707a11040540e40140a02c60319a41c0c003250002844040c2d140c40071030700c48803800040640c0e806a0014000700d01e81200810b014410304001c5050700d020303081030b80d0160764030311003100c00d02a15070703480d41c4100c14115100e07060b050b600014111410000e04a40310311345c58200081c1000e800709071011450340002c104200e50340e280101a442d0303100e2410161a5580342d92503511640301c20305103c038100a5228005015180150790845201c0c1640c4001c00840c9827804e8100b9681c1e1003801400c1c29130208200043d0791110010458071011034995511411400540d550103405002134041507000000c2000c560428500010482c01080c50341e005000b161001c1c140603060400c00303800c0700100300182502d40f2258400040110f0000d07015a00d1508607040d0707040c18081d5000c1c030b41001201011525030404013907450f4101c5102c4181c040020864 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 95917059 1250 95915809 95915867
    0x9010201060e0603100b060c03040905040c050306061809070e01090b010206090316200613060e010912120c08040902040906360207020307030c03050f0105010602121b060403 76
    0xa041d208444440e4580c5c030865420101042d26042100c10441c060500c7d424600390404007820f6401607001030a50aa60f1004c100520160040b0040140f10039405011242400e03c0441d801c40c1110f0741c1415000448408604008010030003600104507821040b40a5611034403100d010300b520b481030600612a10000c15403952000c412903005406901c02104503035842c0c6d817220182d03100710001501c1e0140280d401d04e010780703a440c0146401c0c642c011019402e18100000a00b410031100c00301c0e410803010000c148191205103168501d039940060005445501091086514211040000300384500c01704000641c04c2c501d401034019158502414404c0c5a11b0700201d0f4000c0240c3e83c02d038243d131a0382d075041015a00d88042c0303440704004400320151410f403494000c2490b05100d50300407035010f41c41510070002d000b802d11600c80b005400e03600a101c0355140c403e00039662040e0140041c02c120000807c02d8041607c0c0320702c0ca540960180503176240b4a400c1c2005440800d0709a00f206400350002e41e0010 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 95918309 1250 95917059 95917079
    0xe07020705150d1a130908090604030b060310050903120406200c070b0f0702040507090b070f020406092903071802030f06030d0c120509090a0501050f0a0509041412030c0901020106 79
    0x11340c00700042c10481c80800301d40948806001c3c07120040d0f45150041200d00b120f921b03154000c1000d1401021501c2c01410704c04e044c54038005e03400c612070030041d25060510105403400f00450700311150521580105498070705024008103c8116040c1154402e40c2000c1c40400031107024101d420460401d4074001a80c9005585080c4520003d84c19035940c03c20440b030051a241e0f0020340c100e0300c0343ca030450700f0644444480c2c0701e070f912038102610124a030a1120b400c5140c607000d40c0014143c0b5050a11580c12121180c10301503181c0780c4150701241d06002c0d0703283c050320200441d100500418612a45514807240600000e60080d64100074078842680080c0d114240054041c1c50160a641c40415400c2070b521010003440a0840480400400b04018507051f611030030601e01070100040f0001c1c403545000704008c85222007141950040611704800c1001d50b40b0f50b050585e02c23940180b4403807840c0c1c03005c42c07400c1c0c1010550303540300c0031012021062104581c8524090840c41c54282c0003005003a45545000c2 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 95919559 1250 95918309 95918351
    0xc0a03030504090e07080601090603021905060d27030306030b070504060f0806130e0d02060109110d11070203010939060c05010902090a14010b030405070e07020705150d 74
    0x14010800070801004461426800740401d01e4811080c0d840d1707540c4070201c0300d0502c4001c0c1c0c4400042900c5281c10b1081d40341090256240150030700a00000c0751a10000c07070002d0141020604005648503818508035112050304440c259603111440f084108030320307010b001090940030030b075004641d0b0b0000411041c0903800b01c8060f01e071551074459608a0321002102c461000400c02c035048076180c1110198041c250041d641c000d6001ca02510300320b01020350091070500160b011038441400c1401e1421031101000444000d40c0300102c000c1001001c8550300140c0b481a010029059803a0080000070b000c41c01c0048408514a03041801403540c0e46002040d0031011040605188910030604010250088110350740c0c2d54440c50000c40c4990540e00040c501140c04c44402d0f0255440c2ca081c00d03010401d03420454094aa130841d02e0742942416160a07640301194003a40d0300d440026408220114000c200e600014400200703d60400c41e456440410142c002804c1181d0950030070508e040c452690300308003 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 95920809 1250 95919559 95919563
    0x4050904140a0506070c03020c0306100b0702060405060d06030209160203030f06030c1008070f02010623120a060b0414060f090703140a240303050403020402030a2c0c0a03 75
    0x11804984490321040140c800744180721103148251840c00c80081c0302800240c1c0324491640790020300c8034943c100607040c2418120124482e80016080115034401400140c082e1240d50341000e4441d02144003003416441150071003980100c02280320742000410750000c4040c0e074030a4811030010784881c0120600d2084d81415000541c10520001c0c0780002d03040786a40e44460024100c81080040e0401700c0d10741125481020000303003030341d0304000280b50005940240e0000d45c1c4020062030b031400d12030035017041e542110444010400c1c51181c071151f81e00c9403489100c400340d00c1070780c0c0c042c81503103401c20091140d042e13028001c50514944c180c11601031250385101d50006451031500380d08807820011030700d4004207210245640d445a00506c2400d0309840342c81b810390f42030009050a041c00280c8070410ba11a22042c0810358a0300501c0001e03409016241140c0c0e06903030158481d12032907a00c0014100020395811010506c440158400b135a0b412036a2200340140b00380d13022071b03125005100d8a02518000 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 95922059 1250 95920809 95920819
    0x20a030c180513091a0f07050901050301140a051807020106060309020906090910061706061005120402010302040302040e0604031e05090f060d0c0c0303110406080a0c0c0203031c0506060405 83
    0xc20489400d12000e100041c5509020014004c2c0c029038601422071408480380180c41044003c100b49241d00b480e0f45a00602142042410120080300007011480f05000d0074602d1007a858014000f511146990f4001e04402085480c400040087c5400c0c01d880880d03010f00150700308030300098000d00a214802c8001e401800c2c80034545e4403003091190001020b00780c100c02c0c1c422883c1194074524244038070030180402881c0b440e4a94807070f08a0502e03056001d011240324540c15560304110540020444407082d00e480c0c500f401a6469000580003070165500c00b9402600b0841c01100f81d03507011944520803407194884c1c2e40301d0301d00a80410075182c005000900800c00810078203040c0e107010306800d00d02140c001c00e5186440c0140401800f42c0d0440718102f00803444814000d0304258150288522015240041c21300700b41c64050010b1503254058225a070217135940002e0f0850324411021810b0312600a01220340d01c140c801000824541c82c500000c418901d0b00300410000d00c0c080c02190100c80300140703 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 95923309 1250 95922059 95922107
    0x7060f0b010f0e031f0c030b06030705030f040510060b0301090507210207020a2619030e0603130b0f090709090804030b130f051f0e07170c0306040501020a030c 70
    0x180946070f20002c03079002940761044844042084140d003c4160110460031401300b019583c2d000c0181c19590740c0c02c2003078030494050040082403988401544d80c40343d100c10701c001580e1140d0903c0d5080c00007400c00300f0728a60800802140c1c0d8511000110304030344101400f04602d80c0c1d17517602120f242083c20760300403a00203900d001000e0698250003a1680314001051a503803a46d41d40800b0444000e845801400f8509524103c9400041800040e1034001d05041101e60a6442d50b03000300f4048141007402e103d2800800410074814a404030300346040e5000407441c2107030805900a46c01e26000321034031407280c40b034000041071041d014054018450360041510341441d09650303031400c22130001810424440c45e070901403404070b140750407110300c150700400240902d8040d81c6018207252440e880c4401c072060414241d801c5138070380001c980e41121526010701c0d0a201c0140549420f100e0a42e171000d500d4416030b002e110034400b043d030013020b0365075407910f00304012604190700303503032400c0c810801c0d24801103010 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 95924559 1250 95923309 95923337
    0x460c1103031e0603031b0a1a010b030a05070c08210108012705030708070b0a0b04020309030a03050a020d060315050702120403080d0f05010303081b091507020d0f050307060f0b01 78
    0x2942c42500500001c05072030034410381034603941e008038102c01c610030641c0c040c1e10001c090064140f030340c450390a6440d1000c1d0321907042111006040c880a07250003032060355900000d144520420004803000d0f4062051944c50390107061440f0f0700050b007004243d80c00601340c000a541807052045a51072900340d8117000408810050320f406011252600792040d0004200310380014001000801c1c1662141408100700d0030005080340407900310705612401684104140104200004151000701b01039150110b01581c0707a005400185c084c1c6d605071aa030724100740010080200801162a40010080040041da56a10340803659441107400703607800e44504000910200d03003100d008150100c640701011a400500302600e40c21603000768001da00142024007400170008028088468401005c030841d0306140001002076507004d6150505070819800296070000c40d00c1d11003520200640100d51403c1d42d16180c1800d54695000c42e50454000345014410400039060744210a443d200c1a551894020703891 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 95925809 1250 95924559 95924611
    0x71101031d24061c0809030a140106060c1e0c0807080a020306090109030e090a09051902100809060c0c010e0601060f0908120a0c06020909040501020d0b0306460c110303 74
    0xa010651700448100414071980e141040058010b5104011031112146180580b90071203040742c010000b0071820f65008008a01464040241700f00e001c64410102c2120340340194030016144d006107031030300a1800c00a0a05d0300810803c909500a500b915615582d0449450888441e200000d02041e41c1000120369424003030741c801d502038500c0c40005820a000d881c0d880c6000841c54041c410a19001161002c5040241a441185a00e8280510703142000b00e08940c4945000f845200c08103000704e2006440e0009400486103c0441d500307a41e05540c480c0401441d48910f207143c03001041000f41c0000e41c4010000d01200031100882d0340b42c1c01c00c02c08020031608402054803d032600c079001d1104020f13a6a50b030040a00852089000503030b1041c0d04603600781581d0401c0800d9119400a20400c07000795100c001c2c0482600b80b4000782441e03559601c0640f02d00c2c008142c1000022400d00c22140000c47c0c9562024252201c19190207464200e40c0d640350342c0d6440b04464090200c050071417048055607030 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 95927059 1250 95925809 95925859
    0x90a02030619080a020f03010c1d01050d090b060a050d030c0821130201021c050f0c030412030e04051008030d0c1e03020712080c071101031d2406 64
    0x401020421900e03118815208402c601c0e401c100c0203a0403c8028004528000301d00141180b0203030028042a0a601805450549121890f0040000351131082c401688658100c0788000f9108400308082c58040c284402e0f80f01d800c90f0414050301c410728012506207800a10001803950556406007a02981c4e680c0c0011500700036081171050081c90098080c2c46242c074502d40c856150108035111030142800020f00c3c10340b42030807074501910520303070440300203038007100f2102c03080c0004c503a80f41c1c0d94403040c820350324501c5198130804c52503c40c0e040250815911484180203108110750034001610342040e181545c442e41d102e101025401080343c18404455a0800c1000c840309080100640c50001502c540c0d203510242200006076000410404000c2c9495840500010303d00e400c56103407528005100180c802c3d1030000c2c0100080a4810b61160302c83c0d00049030441403d0207410010b09a403421a55034040492412000e85038110054541850790a07403600c141c100a04205202011051b00c105010b0 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 95928309 1250 95927059 95927071
    0x1e040614030d031e0e06090111030114150d0c0c1a24040905010507020a061401051503040501021926101e1a07120f02070b1b010905010608010c080402090a0203 70
    0x20304441d4030584d00e800c42c440c0c010742050b0140076010354034112180da801c4a800b034041c1c22401c4c100b800140010081041103851982c001e82e0714203000861744001035020700407102200301c900d00700100140000d0703001c6402d2100a2282100707103070140f01c015001516900880e12130b440c00b1004071002d0b01d1640c041701b50001e1214017a00000c1c142c1d195448107403c1d100704803a5540564880a200020801d00740300d80d903a0144c590381074141035410000021400340c0b00816068142d880400428240a401c2d4111200480c0202507101c51898501014122448001442100804030306103904100d020281c0c2c1d030b10465030400c00241c00d90800c049240c00205084042e0706450750844040780400c001c294241240e000d0742c036041d0711030344c10345440704c40d200f0600c0d011002c100040c00076486441d00007440005507540740b001d154980881410a10300207003009040c2a8030b40c2410084014004103511850903501000b009000e9910540170595907402c00341e60013900480945d000802c50f40e500d60240d03400207 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 95929559 1250 95928309 95928341
    0x608100906090c3f060b060c0a0b010501080a020903071806030602041706090f0c09060f0d0b1801090c0504020d09080304080405010905151204020604051e040614030d03 74
    0x4401611065044005074101d480540403802801d41100c00d001d065070445011407000101084001810202c200e9599070010a170580300d00e01d0580395070303541c070076100d420041000b1a0310528150400b2020850203118041c00f00e0000404a10a6240d9000303c49104002500505c00140b5210b0600c040000c21b5926880240e176485001c40007407001d000400003022861421460900020481424844040e0600029901c0600a502a00c10105261a0340e480c12601601e05503a01740c08224070b490b510b8140d03944164030044076001c101c550a805030050035080081c451a8a16914440c225840340101810408041e0800c00003890030b500101804200d8510202c1c0b00d103025926414640c10598086034090000700c1c0900c40741d42d001003c0030040800300d030300101600d620b030220100c40c89088401080c5070303007590000c1c0640d120101100c005140c0645064241c00c04c16604214911101c10128895800d0880c005030701c01e071049580c4510500100a080000401072003070f00241124594140780c1 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 95930809 1250 95929559 95929571
    0x30f0a061d18030a080109060b03010e040308040203010f0507031d0c0607060207050319020d11060103030509100e13060602011107240b0d06050403080a15150201020c010f0c120608100906 82
    0x2d501d050000e042c80c0001c0e030315400f8155040c03181d80c42c2507420913042008050400d00c0100001030ba072450b900d80144e09403d00c0705072500c41d400440d015110381452294004c1c24001403140c456490b84c0001d984441246041400e04030b07191155840b0814038441e076078010010b20000002c1003c980c001d0404502c9001103a190074500c2d800c0e00002c141c81a004000360304074a403d0801e80d030b000200480118603003000303455258119613014010380140120603008980301e60948a186000b80103070b0015440081849420502c645650b901800c86401000300550819682500480030310301510040c0d43d01c181032044000e61111b40700b04182c0a1182658602d072903140b10000d50320344280d01714542d40039007004191882d01c7e04016041d0740024040d4501e50f4640724050309228020307000da1701035a2076804074011404568a049029004400c040a49035103001a40f8000007229401000215942d0710341228059942c40542d040f90710920071000070350040117002c00801413990100c0d56240c4191400904 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 95932059 1250 95930809 95930851
    0x30b1324060f0305060421050406030209030c130f0c03050c0a081b120f01060804020a05091b030901020a0f080f0103030309031e03050106020c060a05090402030a060305060705030f0a061d 82
    0x1e181a6a0065907140c000b4010b002c2071119004448102e01181c1c00324803000c0340311403801070961042b48209802c042c1e02050004042c0c0e0140f000a800034001040c0369486c0c100074040c0802003100d40748940740c00e80340c82140b16200340a40502486000c0c000c0215050541c91034040e10545c0c001000c68803010030740c001c0f03070310102c4c0d402d0041c003600d0f4030b01d2a40300f2040c03611400c200301020068100d8424065000100401070b136800c40d4238429641c09441070004d544445140b500c18141281d0100100000441000380003d41540600582c40c4c89546401740d0303025840c02540c00c034105a0b1030800700c030300c40e0f401400424040d400c203400b8903120303140091201e04603192601c400d20b17000790300c800001e0301c48004000a0b0f0b4104086420388504480e180d140800d0090060042d12544905c1405240c01000250f0031040c03982c0090300031074110b0281d691501c0c2c00000100300303520460315245a01105404201c444100d4400e1700143e68401100032038820702d14041356078804008002e0f107410340e02c1d4810401 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 95933309 1250 95932059 95932079
    0x6180203061c0b060310060b2a070303021c090b03040605040302100e0d1107060531030b0702070e01030804030f02040b1e01110a05060c0c01020708070804030b132406 73
    0x5802c60250003803440c02d0406078101401c0103a18003c0d0303c6181c1c18030388140700141400088404104410b0401001006001e45044001c46040c2d00c22115002d000d07000400d054001c00d1001e140030214811032480741000d402586d55040601482810718002c0c4005400a0311903404641c21900900417500c08001481902c2c09a420025190b403d0350020000400c951750006500d90714a1800c1c0040e104980c02c000c0020040d0151030404100c0800441c00051048070444440420001e2001d22801158403410500384440013550074400500c10702c8800a2004840c40c682c034140d039440001189081e2558803007220701d11915006076441984d4108811040d607620040942c510308039804070510310360b20800900160102d542950041c1c00c18a6a940000c60216046030310040c1c8a03901901c580050b58103d00900590800a201402c00a00c5c0d00a0001040c058422684a0800441603a440012082819034440401021800316a400c007665803503200d034601405c00c0c800e500250b003076a0399010070 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 95934559 1250 95933309 95933359
    0x809060403030306140a06020d031508070801060f0f0302030706030b0f1206060109080a0b04021507080409050f0c0a02071412120301030203190c05010804020a03060c020d090602010618020306 84
    0x4000c0f9aa4010130000030700754001c0c840812104450b200c01c80b5107820400381d00c1d0b5a5450380c0c0700416584030840d0502043c0d0003a141d02410f400412285e4061b29082c00d20b0081600e80104250b248040000103644103d80d403007002a69400703809000064a025420781c0540704c2c001e60503a00200d620300b9105251603040008a150508e04020046d5041c03600000d081440250003000c3c0c282c0050041102044170300b10a550020390545810722240d40d000c048c228071b0b0180c854000c203052400900007481a200b038100600545555840c3c01ca25180c00803013640e1445200c400d0f50258100b11410040550070403101e200f42d00002c3c0c1440301c2c1050310160582050955004508074003000700c014002d6040821032452094200807841d0b401d17104688480d1102005849141e0400c80010002000c5444170044e003030003103034811014401640fa0b414040d482c1e0210720070303180000b003043d0000640035105000c0c04045400c4109110100b400c1581c518002c1e60009184980010002074951804406d03004d80f2 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 95935809 1250 95934559 95934563
    0x6030403120e010204050105070210021509030703030605010f02101a0a0603020304051002120f041a4212010912021005090c060d0203060f0a18060905160c0809060403 73
    0x1c0c0c0c2080345030300144421222284000d407010b03841032106005503600075045545003078040316010320012001c4000c0b0314103808039000301c840310703502405c1c00320414000000e0300e031451013a1014003c807500c80f1b0045a00000204418006138000643d00640383c030f5941c4400501e08240521039000030516001c5001c4a0b50390340140c2c00a0741c000100014440c01b0b00c000042031040c84415131030103514881c1020702e03030304c003a05882c4201801c0022504002c40694550234250049005070082d10705640340c8403207000c19046150480b24812000d940c084c0400303410302c48040c0d06030f68048103440d10400780811b80c403a0a640604039903035207000c240810010030801c00024807550081403101d80316240c003020340c0c0d4050b01520303a42e80507001180c0581d450106450030b00d00010360042c0c8071740e100b4000030b02c01c01c040110950420540d01e03011034214040000703082d030319004034801d202407650750007600c0072100c084030481c4a0b03a040c04a00c0005074862490b22128034040d082042c2002d90a00c00a52a50310917801 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 95937059 1250 95935809 95935817
    0x204060b03180f0f150901180602030105090906101e080a060e240a0b0f0405160f020c1005210702010c0e060c070b160c0306050a0e0d02070510030b06030403 69
    0x204549002d420001c0c0a065103000c0050032100003c20242070762541c074400c051202e0741e60b00c2c002501c00e00c02544200151522007445d042484400c0c18440004d51003801524082d2855800182030510005044c90140881901c40c0d2030103464080203c2d00e4001540070140e100c0f51180d130005908400b00811010350b03008200c00140740c0c0786020018541b00e0500000707602c0c43d00000c0c0030001400c0d800b5800d90300c00075240010039003007c1c040000d405141e42d98007455002c1d16202c280078880040c854480403a0501d91903e286100504409a80c2c480921a0381d56015004041c42d55000b8400c402404a000e501e013490400e4074505444100c80c0074003111404010b0b951814843c503e29449400c18050402c05e40303081d49050b00801d521078881d501406240d8424500042c42007003a80c840c24402c0003d600100c11340a1941c4915259000d00400c0d101c0040300c030304090b032400e401d400c00b01e032019144116800411845280505000f0584030142d907010034507580b0780010742d541d00c601c0010b6118a110380d031 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 95938309 1250 95937059 95937091
    0x4050d060f051609152109060506010509061801050f0d09051e0c150903030c1b040606050a081f0314070603060f141201141902070b060405040204060b03 67
    0x240c09021100000d0000c00c600002485140c1055000a00a03050b10b0048030061140c00c806038040d140840203501b0320602503030a54403485019520740c01030703026070700c1a00c0c00c0c45030361a1000111580c0c059401030725813052040196100035480003000311345080060501c142000c1b0b40d00280c6800d40c01c110b030000629516014020300308501405954280d0120555030b2400013149909a075449046203207141c0198075101400c005805000c0984200d002c0041c2125900c1800d204422f485800e580003440d051281401e0852181c500340c004c00302551060b40d03d06040004134102200c8080001d4041503031600081601c0e10300030b80c1c7c0354a410240d80203410210f8491404007681d40740580c2903208104051900d07200340301c040340b01d44003c4203c2c5c10303054022180401010000304141c01500b0000a60362030600880e01c5a040035550138400c004000004100300c060491b80030981c443c01034002c00c05006580028850301e0b05900098210b8009000024010749640507074135140e00560f42c0c00c10171940c4003 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 95939559 1250 95938309 95938331
    0x8030403020d02031321060c020f0714060304020613120b160c030206061212040e0702070801090b040f050a05010e0616031401090905160306090c0501050307080f060604050d06 77
    0x20407841080a2440150b183c00c2c1d200d0f01400362245c45014502e0440d008103031101d04440b8258480c0c6600c0c2d0807280403c1551141d41029580f06910210304d011400740a03400212901151035801e1a01d03405007425182d551aa401c0008541c003101040820400010022500d4141000c1a1140301d214601150140c10250905440d103201e0341180d500b01b00c50088a40c00103a0301140c1c10b0340100341910052244009050f000741800103403e07003070850034400308000600740209000203005070216000d40c0c910f16125407906003130b200001c4000d09503041c99004100002c4000c840b02c40d9082c051810740300d02c1c1d00c640d6030386400d54512440c1101281c2c484028002031110118460203004d00b1070404000c2c8440e40303903400c0142d00e0144110004035595004440030710030207000501034103883c206010741184d201c1c07420000600c084507080c4c0c5c51196446011030340c0c0d40510201c80c010202c544a601491b5142042c0da40540b50081a0315002a010310000889481e01c210b0b030341c9018813902010600300080 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 95940809 1250 95939559 95939563
    0x50f060601030f05090703062c0a0215040305060105010503100305030c070509010f180b0307050a06090f0605031512070b07060b03100603020d0b100b0a020607030b01031a061303060501030803040302 87
    0x4859901c2c80d20315140a006035210300180c00000c1f258400008501001004040b007415040c410401c00802c048048283d030f02c4a020540444a501c02c48200f0030200c8500e80394a05801a400020102c1d031101c40144119802240550340c000030503518060081d8581d620f41b411908405a1b001885d80a4002488030345060003c01d400b50507501201c0c0d000030b01d402c29000c3d52181c48024460116500d906041030f54805203d03904c0646400f9141051031a50303084c0080810f0b10911443c1c180600e01d010120b6400c0c410f03000c8038007556040d8480000c40c0003407030400a0f160003054050306148030b40c82000805491200c09402c4080c014600065069841c90503d82080303924050700421520b0445c040c00148c0c0c5600c50401d15680282204ea601c4e991044842100381d4243c00c10100d20070046406010a580010098401c00d50b07644c0178018000441c0054081d00c80c21000101112402003842d441814150050000c4d09220306050550941d40c0e120300040321402e0300291201600041040145901 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 95942059 1250 95940809 95940821
    0x12111215090c0105070f020a03020306090d080a0920010210060f080c120d050c1617010c0905090c0a03020d020c031e0f0702040e0a02040f060815190506030a050f06060103 75
    0xa15000d80522030300b01000a00900c540d120050a00068007002030031741d01c40c919200302542d03002e4100d0b1518102070510035950000703e450322002513a4035000407409891801001c8800e54496442c03006c1c11207810110103041c030080c40b4113045210314102854421158050480280040024204100c0c1850308460409031109505800740c144844484a85107001170702c5010b0000d185001c9460355102100d10341002c060949144800e02d08440c0402e501c44050202103d10a10304002c0103031400100c02a40c2400080c4513590340091540001210005184001c1c02072411038580145072204c1c0008502c120b0f04120031004203503001240058840c6202c00540404d808035142e403d081c00310a154400f40e80c480d111000340110740381c4094591514080101600f519070040c41071080100c01c4080f0002803006101c0c0c0d8101e0300c250201b1010720001030ba01207004440da144c001c460049003c014030003a001c00f80001d5014803582c03c0d10740100d2014000009120703845000341c802820000e0005042e260 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 95943309 1250 95942059 95942071
    0xc0807020c0102030408060a0c0c0b040302070906090902130c051e0a031d10020a090506070b100b1602040b0126070e0405061c11040e01020408071403030412111215 72
    0x40204010300c0480400038a0359030010701d10002052204040c002284c50100b5950018000e0f18144140f103705900490060151085c20341e0800400340e940c407140080e20140c40e00a504204c0100c005821001c0c113821440e480c80702c5050140c640380020443e21061505640071050b609004142d03400450750602036212155650030071100b08480814002c5d8645042c6203032042c41e40d60002d040c0320190f000d0030918000b804010b001c02d031980028102400d444030708449500070030800060104070340003000c094840004448400ca02d0305100c40e030a000c01005602080c034103018174265581655003200560004050b1404580c50031403c18080141c40000780c80342051160b07003040200030007a21500c05c1001c40e260303140d40b0b442c803181a506103400315402c00d18030b07150003505200711f60081c4001500148105c400803400c81e800b41c0d43d5100c9100016410011265040d0001c200811446880c55584211580a00c6241180d13450a80000d2404e509442d8aa2010380104ca107201c0070800300fa41c0940c0c026 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 95944559 1250 95943309 95943313
    0x105040506010c0c1203021f021c05070c0803040501060e13030207050315040b10091503020f03072403020f16020907090b04060f0201110a090e070c0809010503060409060c0807020c0102 81
    0x400d1507550084c8080a5000c0c020b0010400a190400e15108009041002c0720b01c403024040700d811081000c0195002002c5045244502440a44200c0d072038400c0303502c1f669070360395101903208281c0e407900d0455101505c20340381503485070343c04186080f44060b800d0181110348409064072100d07180c06030600000707912241c8240c000900d03843c1d682c0601c0c03590391343c0191b120114400a682d55150812541915000001202d203800f0b90200902d010405200540340215141d01c060555031040580c0d41c070160099101d12405800503203200488550311140f01d24640c00e0150804443e030094140c02cfe000340c210803249503500600941941011a42035401802c40d1824184007400d040c9814a203200d00d10400d42000703100131000840910070740c07140251002e11070920755100c01043c00280794041501800c00001c10017804503443c1c0d4003134821a0041a405001ca508059180005503403a410040000313400c00c1e1030701d1320f440c0092400d20507100b0b080103540f50740c203050600c4e000092038508403402980c155 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 95945809 1250 95944559 95944577
    0x1090e130305030613090c0f2405092d0f040504020d021903170a0908030304050705010e0a05060c0d260103020d0218010e190c050702130b06040b03010504050601 71
    0x101a40c0c10000d202550103041007036076a151a40443d0042003401c0c0c048a000d032a01c10076808100c909420b420807210380032180201c10f038807204403000f00d0302d5001d002c1d440e0307000c00b158111000e4003a07005000745200c018030150f01d2003075071130a20041039185a4140c010032116840005640752052010b10f190005903420061407800d5400700b03414078140c520203803040c44600282c007003507160540400c01859004214641d41c10495969507900e4100d4010f0001182041d80701203019200081540c1c0319503001001011101d01c0c207001900c1c24103102510700c3e00803102802c00724103a21080700400105071880014260a060300704020803132a00c1c01003140780c9400300e0400e1080011580e00c4281913030f070100d5080c48140700902c005805c04881036000c0b68000800000010302212107240726216050f4600707207040c8a40401000c10807601c242034001c004c20010310601004d070610b00b921454403100f0000006e500c200d0080003a103903801940c000000b00e48008014015402c1030b02500f50040403e0805c5016 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 95947059 1250 95945809 95945821
    0xc03010c1e08090f010e0c030706261005060f0d0f0c0e040e07050d080406030b03060c0d150302150d181e030302090603240108090d0c020402040302061201030201090e 73
    0x2541c192a80c0030001c200400010501002081c0702e0721528a2441000300480b110b80100a611a03580108661180c043c1000010b003580c05540a104030038410703c90100f00544251030b8050f460006400c201011174810004220b0b030b02c03035000801d0001401448552624a2106402c1c2550321060801c0041420114248049504101002c52542080741c001c10f0310502c031169a031070a1241e81c070017070b40914030007801810f2041c0c9600030815540207980511140c00c080d0203047e5034030f00030344d0044a8100d0030404492100b44031fa010318003600c4203080a2005907070b6a00041c45c205801201c0d203c08030000280c8441000043c45854010092456401101d404945680c2e40e4441c0d0800031a02042414459404161295044402540c1c004181603140e00303081052098600f9080d40c4068550070440ca034011a40c0100d00b064420840c0c07200408040386400800c4802c0042110101d812540074000400141d036258090078030400160304000140d0b2441c000140b00c00b170b840e4403041942a0310014005 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 95948309 1250 95947059 95947097
    0xf05030105101401050703051c06030b0702030414090403020a020d061a03011104061103040306050109093e0a0305010204030b0f01120f020613030b07091a041d04030309080c0c03010c 80
    0x82c1e2800034203103c2d0311b803040c41c01d058400d0320034081e85407038551a05450420a490b6a40000140e0b40216401020303540c03960300c00e0b80c0d00d120307034083d502e4800f90900b480da4036458514513541c1d002e40310303106884500404d68081103402101840445005849052251200c1c50312541c0740070b05101240240140007031038061f00490300c80c6004135003c00010b54a00f2618180130411140107651103e010051507945999030b0700140702c044400c450b00c030348280110716581d51521412208840b003c5103008450301c5031410740030007011800041d030411414440000482c00a2028000a41c000c140c080c480e1318000001c42c4003828140c001c1c0800d000c205e208400841c03403806800034800c3c0c2c16150700b035488481140c03803507443c0301661000f03006000b0001001391032030740b05200c881101d41607001224100402e0610304824041c0703024903011865810801c007610300e001c506840e0400d0003421b000991816a85900c4620f03800034140f00c229134814801032183e81401d02c50302824196500d4041c4642001c7c0302c400c5 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 95949559 1250 95948309 95948339
    0xa0b1014040c0e10020a02041a1804020411070f14061e0604111b0606010e061e09040203040b012d060302071719140301030c03031202070b010f0503010510 68
    0x1034012955059075100031809040c3c60110150028003007200c52012000c025640e0016807002c0703005d2030500c91000404a00307100104010f020041c034665606000c0d121030102034070001d10581c1d21a8640d8084290040443c0060142a004c0c514080300380c001790410b1105c00c8014420718005070f00a0040040c0032030b08407284101080301c40c11a44050700c3c0e200000303015000740e110141c0d01802c001101d00074101c09007184000389000e0010344209540f0746006484010f04200f003142c00180411014203450706200f800c2242004009070503007000b0250000c20121b0300110b5003240c40300d4941c00180700c3c80c1f00c01019400c3c0c4070442910b002400f1121045010020064460001415004107040c000c00111162071403a04503000145603c07040740c0140a0a900c98105584000c07400420f1300e071007419404070403603041e85d41291000c02140d1071560100c030106c108104500100750f0900c0081c000681088000d4002d0003d100e91444040c1044101400c4540140102c0007000107480e08202c8003204411013 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 95950809 1250 95949559 95949599
    0x714060304080d060810020d05070201050402010e06132607090b1305070e04050c0d060506090a121401020c0a02041b0f0807030905010e07030303060f080a06180506090a0b10 76
    0x703a9143c0d5803240e0058080c00f810340164486004040351001c817110f03030791301400c101100f1400900c46a2103030041030f070803581d00365000782c0026064072440f0614141840149040600a400303c4e1034103940325003038101c4019064131640e036402a04000d081c0e00c2400c01c480e00207000380c2e00e41004818110000127180c01032940d14a1805522100000d141c01d001701c051009800010f0310030301a602c1c4c9005000d4495120b07403131410020b480c1c82c002003600e00707145050320344000340542900601c50520000221024008404a0300003603040c1c046411000b00f130010380010401e5600504840007148100030645542c0d00306c4a0110401448003016140d000c17403000d18000d00c0c0e0901408586503410201d0181051003c05040c0390b0820100055003100040c00c04c04072400f80d9020000ca030b03100e00346440b04170024407402d4010740c044282180840e4280d402034104e50010041c8150004c0c0383d03a9600d0070045d0880d49140c4c3c94002000b007030140070800d03400b2940310180000b81510242032200c0196100340b8030000c = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 95952059 1250 95950809 95950823
    0x201309050c061201030b130f0b060301051003230106380c060402120c0a060c140a0302060f090312011e0911071103010e010504050303040c06090b160201090902040b0c0714060304 78
    0x800e5001c40d0340c0e54031030707547c2d6084001c03002c1005503801c0200c40042c040d18a640a0740ca400700243d070414450800c00c007541d078071180164408c13420001d9040302940c0e0030442c0000c0c4d50384410010b0386642090700324460400042801441c4060b589030314500c00904c08002c0d45013241000300c2044900c0c003003582648a68111440011011a84425803034504010b00242c1c114044000100b003680c0c1060501210501c5a080e001c0e1182da5034807090745404000c60300074096803200000c40e130075010018595502103159421282003410030750300c0303047c0500700780e01c4618510a000c112105e0300d18841c4a000142c2901002031010030740d0644042098498a5809003010007016250350141e0740a42043c1450081e42000384110b0405061150f101d07402902c0841c1d03c3c0606d500c000485900504051048071444050302e81040710100d0110042115140220704020384404049014440307440036102401100001c90b45480c580ea5031645010030329040013070500c407429403c006540c0c8650481e6806588642 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 95953309 1250 95952059 95952061
    0x4120303020a09030611121f030b04050307020907030b010e03010603050303070e010c0b0106200118080706150602010501150806090a020906040e0705070b0f06010c201309050c061201030b 82
    0x100c203d071a9059074000a0100b03091481c040000c4400901910003000148440c04050f102c1c4441d00c1d42c01e0b2000c0380681914003200300200085407088580951190050059a14050056001644c2408104c0d091400f103992980d0482ea59684040348400d030240960007040028116260259a070200800c0764040002041d18081d00f0303481303455a0307500107078070000b040ca56507180c82015100500c461041c451403044424046a1480b0502900c0ca0201c10b9060002e589840750b00c4030b0039107034450b94054034125140c0981c85034002d6400c2e5a0f40c02091568000902541410702500140c810355a1200c01c1150300030178003240b5a03613441c50542041200000681c1ea808d10340c00f25441303002c1c6610807030525415070301b0854050740120040c0403051007100a44410b80d59824840301c01e000944040c0e00282c00381d09001d00045607208001c0da068141802c440412180c400003a0341c0040003013188041d65111825603013002000c1241c0c8141042c2201c00904007160f129030185686014400074107440382d210 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 95954559 1250 95953309 95953327
    0x3080306011202070609020405100b0f07140307030f09091104050d0302120d02030703050c0a020a0b0705130b0408100203070f0309080708041202030708010c021002070c0819060605010201020412030302 88
    0x248102035010082020f41d282c000da414039100414613100d0680c001e0381001c00040d42980b080c4001300035240300c4150942040c01ca020064801e8001010480340d0805184c00140401800c0000c1d1140a10a81d5030101d24000460014410034290344030076030182c2030100c0b00710342c0c003051000d40701901c10a07034100014541d5030400b2881c18244507c1000c141000103900080100250001c601c5502e894400b8003254466608281c0700c0d12406c0714020041e000350903200e000900780c6804c40e4000c405490f00c83e06040d03180301e0184050509a02074a80a00b00103801c004c003c5043c024200e426202240460071840d00c960064020440c040c1031004055484d00c0d81d40c10401600265802c0d0f1390070000e51500c0e5911000104410414508240e00c80d1240d0702c1c0c0081c071720205020300403000603954040c1a103044509803040c041d40107c0c00480309040d4550012444080030002205401c01e020908103811001d41014001c0710516040b031811a401000305003c0309040401d1050019414600141d03503c4181c = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 95955809 1250 95954559 95954567
    0x70c0e070c031110021306020c010507020f010e0f0406090c08060f090403050304060e010c050c010b0306010f060c0c05030f0105160804050d260c04050a091401030b0621060106091203090308030601 86
    0xb104e1070300c0b182c500c0801c103985800499034410055403615001c8426140d004030065815018410700207502030054404e10090354413410940442034000f8012405072000f0fa07002078181c603043d4020080450340d401100328120703401032116822800a6406420b24409880490242c100041014060150000100701001010360001041c801c00301c0003000001c0303615078010120760203032005200300c1d82042d125a0451401048841c12a80401d215201451400005650541707203d4070542c1c5403581d8140006640d141401710080420704040000b8152a00c40c901d8036800f6818150f51041102280401000a0300000d04081802c55414181440c40d12417114a20300802445a10100e10400050103854422040a40142c0d40c08842d1582e1464440f20079004862519142ba00102c5002c0c0042020440c40440e041e00800f02070000250001c483c240040c03010114803d1015070380c802401008a9980040c07034002400011002c01c0c0148044e44000340103c4072408080c040e50b4000005c1946a070203 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 95957059 1250 95955809 95955823
    0x906090c0c010e0a0c09020a09140609120d08090d0c060f061d06031209030c0d020409080f07200915190f030b090a08070f080706020d02070c0e070c0311 67
    0xd0078000d014201038415800d441d20300c04d44084807600c02080000c544103075240260f40070441e10355691406141b40018100407100c200700da00b031b000082040400056160030824004100003030000744228405000001c026100044c0190a65002800301008c01c0c0c2e80000c0503107250740c1200340412403104520880c0003c0809500001c411001c482036034960410408419100f1082101031341d1444d00710303190000c56880b66051603136054002c2e000d40c103414540366201005030750000d800010b940080d0383d07130001c01f40e210f005030804512000c250102084080403010b030880e500e1081d0700000c000e001c008503206000103040f002524801d10302250a6490b0398400000e500c4a5580d04110140d82e503084c03040e506100d010564106900c280042c1c008240090681d5510394880102854904191203003415154420001c49140c80100b11003000b18003640054803101d0584d140040c1d6509843c5049140800281c2c081102940030208003c505078010212207003040c1c16081154402c4c1e520b003941d83c24004 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 95958309 1250 95957059 95957077
    0x501032a091212020c030d02070501051b010501230103020a0804020121020d0c17010503030a08090c030a11040b030d120906060905070201020901140702100f020102070c2405090906090c 81
    0x1500004806100c4607003c05a0000900c1d0203a40329400c9000500d900c4049100b91240541e000050402c11075110701300900e03100c2408a00001203c468800d580e0030350300c082e4004441d0115400744094070788104000880a90000d08013180340400c881c05c06004002c0040c03001c0d06008803401c13150b8001800702041042a528100304541d50a08614060014915403e4000015110804400d8072600401c241c034107a0b10b004000707605080c2407610407506d007030000b810700c041030140309890440c0b51800c209072f80e185840360106034000078210060008545088c012648240e2200e116181010741290282c0c600c0041c10f903002c60b02e04078500348103000d84926848811901c0c030f000d080107440e036410740c06003101d90001d030380d08400d50b906001e039510b00e8080c0d040003944c0601c030b00701c442010500403a0040d40d059020300000d4200302440c2c40300d078082903890380036400301c43c40340d26140038450705481c080204502c40c1c10883d040903919404a0303400c2000a01c1a0300548214000c58200d5211400b514075110f = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 95959559 1250 95958309 95958329
    0x3080f0402010215191512080901110d02030403031d01140d0b031203040c0f06050f0901090b160c05060c0a0209060307120507150509030d0305150402040611070501032a09 75
    0x1040451740d2840c0c1122001c49030209601d00b02d1110180020000c402080b1608203804103000d209549954007203601c0301e2071b101e0600c114090b0240903400c007407010508500894018640799031550801030110003036140c041580070300a0301541c0b500da8000e09088541d55900125a840e00d098442c1c660052004840d43c580c184600645484118450b000641c411807046031910310081d5103106090a2845901a81010032410b011222104c503100f005842c00d90b00514101c566107507184980c42c6298881801c035240f101c2d0802495041c084084129002040140c4001d0b02c0c121100c456a41c40c0c05a0060091244c2000d001045e0542e50030020034001e4003801d04400c44800062a02c2559107520384189844010440710f0800e03400c0c020020340d035030644041c0190400001748a0114002d00004104890505030f02c41d65605a413aa4800742020741070075150106005c1422a0941c40d204603039018034101424091a404030140c603070640c0e500c60040031014048000642019200c130a141e4005820036 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 95960809 1250 95959559 95959561
    0xf0405120c07090605030102090603040f0f0209041109060108010506070f08090405090a120c02010e040c03110313020411040803041a0f160b0609102d03060b031903080f0402010215 79
    0x300007207841c0c800c0f102142c0080249950b58001d0609071b000f5091242e034019418800200803480d1074840003c0750380700381c1c00c82010341c01c3c56001a517550001e56090b15268a0640540c609051840c5210741086090800906941c9045c0004442c1e104250005000c030402e8903290007003045030030903204095070040003400300380741ca01c6415a170748111043c29101031050290800c1ea1ba801003084907001a011786d100c0001080318820720000c3d04100c10050b0401d991250b00b0f4104008040146000314034503078030b442d51206c840c0108405c0c0e03405000710800000c0c0400c8104204203001088604440281071480030a000c11103402e03095004480340c94901d0400042e240910307070502052800094401c41e15086903880c4d0300144a42c07843c0450340c0c1410844070840900442c00845554030706000312260320900c0b0010a05540c4c1100841d6004560150704c9084046030762800340420051084001d1010401d2611900c1c000e18105020f090550f4000044c80850300b56442402041d111580010404200b = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 95962059 1250 95960809 95960827
    0xb0312180303190203030421080601051b06040309051002071203110f07121205070c0b030621010c0336030905030a051501060302040305060105060d020705100209010e0603010501080f040512 83
    0x341d81c01154100d40d174608480300720721250008c465406604c60250b41f810201e64488005480c980e1251345d00c4040c64104581e01119000c0811515201e54400c1e625140114509018000580b80c050025001e64100100030300113880001d0014a42d96018a403000d01d03503480b21061810403106049501d200e0003a101c02042408450305d89022042c4514506040d4402d1458119032500a81c0300c0104a9820000300f0400100490051500300c0c00051440081c2e0100d108441238030301c0f656031403100356511030700d10924860b058812402c045180c10a60a111201b240f95020340078030020192000803602c041102c14544201002d8000d40000380488182042c1030406030364603000c4651101d00000003900202c1c0d00c034800d0017a1000c888e1301400800559080c40100400340e001241181c5901c0d40c20321444002c180204103a600b10035442e00d00690360241a40010003d502d4003011038000c043c20801006143d0b440304540d98021049080216151180d1820504182d41400340b81e200c2d00c00840c800d41 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 95963309 1250 95962059 95962063
    0x414040f0203070e0c0306010309060605041e050c04060504090c120c02030309071710020d0b0301020712021005041a06010c020406060e010933121505040b03121803031902 75
    0x10380240200c080325520b03a034640421411020840d228191810144040340603035004c1d420000000d0706c00e0a0104e40240c030f50020600b1100c10310742c003030b000c0d0465a400e6104041d5600c1038980005250700035600e8a41418801b40091049126201413103a50b14050b10000f4802c4004d04e540c10403400061199424414000f541d030b40003502d00a25a004400780050f012009100304000c4500c4500038041401a040c0a40029004000005410758031100d8904096500384001d01c40315200f1101166618900003000b071504101c0d41c50444190700d04001e10011034640000100c8910440c9242107555a821004071080c5100d245d0094000d030410310080384503074110009400744103081e40c90031041e035a40c142c2c0e0740030354110640301d046c0c0b00810011000e400e03950004054400d030182c00c100c03d07003080d264031000403180034501150740001107841c24400c41c60706002d92030894504034002c1c4261090b000503005036100e6692460b0715200c0ca014595032a4506009480341030740716126036001280501c0001e9 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 95964559 1250 95963309 95963333
    0xd0809060301060c2f01030f0b031501030c060903030c080d020d060e16080f06010f021c050d0501080307050c0f010905041401030302190f02060a0504080105252a02041404 75
    0x851300084c10800142d0b05d2200481c209a8510b10007409800d10800401580240260244c0d9450140c544803181d00d55101003040145040503221901c61075891810710b0140f0110b290800010801164010404aa070050314401d002d0b070032071070180d41d811104000d14028803c60005103805800c7c5880040c07600390202c40c042c403440c042e546200301d42c0b400000886076140c0031900444500410000700f031041d449440810303d010b40b180112850407440b00c65000e4900206e81501c80011b82c005180c03446000c42c4d00810b801040f00c84011420880d003a540c0903210040b068040f0301442d01051861104da228004803c01010082d004002203d5020501200d0901c02d00082c0c003d4842c400c0c0011060580c4030b03104010030340105d0800c180645075820440258000c17200c1c42c040040900000c1803544007842010700901c603031061200e1040c84045510000b24155200e5400c0c400d228841401944032801c08618101e50440d5109440810744001401000382d0b0101c09103440461080004000b0303066409 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 95965809 1250 95964559 95964563
    0x503150d03030603060c0302040605030a0203040203011805060601030b060405060d0b1903050109050c19030308040602070204020a020a020a05100219020d0c15120207020a050f0d021216080105060109050d0809060301060c 96
    0x6c1c04460200e81d0700342c060b44200d11420000a41c00c2000840a4444e070703010b5034016100400205401100c0c1c60300002000541d8025109038201ea4140841c568040c4100d0b14008002c1d601c580c14245490001901d070301030003100c038403020b44a08cd4441ca0355201619640c1c040d41c0403c0b421542500c2e0b090480c003c0c40444411a03080c843d0755080452444c001140021440c00148100781c8141181e5003141d101d40003800071140c0715024011900166241d0011f0320000000d44e004013a40700050041014210b00390340980d01400c030191860980c15404220030b0899200c80da1079110b062118808145d072106070000250510b00340303401c08604000c0119824030070301c015641e0102601c1d00c07007003030004910882400950040001c001003141e1305000c0b10480382c000b002040a40f0798a0342e500480c21014210704019150341000194001208902440d117020702400e00080001d460060000303800d43c0500e00583d841040d0407880300d82007005a1b011642880c0b0041d20440d1203581d070b0000500100d80303038181 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 95967059 1250 95965809 95965811
    0x5060c130b03011a0a020102040e0f04060c0c03050915070602040902130b09130519050a02030106020d080103170309030708040806040c090b0a0902130503011e061505030105010503150d0303060306 86
    0x1001440100400959042e101c00900d211130040d40351140d4642d981c080ca002400f50b54003404009884410240c0d16481000802040c00c0d062400d49420011201d481000c01d085c41210794028021a40c007509503643c0c150203450900c1c98645c60301059103103003e410300003003407680000b501043ea280c0c182c0280140121500c0a03404e400e8540c1e0070405c142c02103060890f0072400020004000103002d8000c1c80e0011080c2008001010b22902c0d06004c1c1c81c0c04a60103c1c110b42c0000040000e140d041095000781000303440c02d00c5d8954115610006904d034134078020801d55001001051007003009008441c6503540c02100304e40d46070741e107800c01c079101c00b001c650035107100740d64110000d51013480c1d0040040c00440140040b0340c1c0c50924a489d0300075001003800a4084c1501c02020031030751024858040000e42c1c1100008103512182114420361700342d6040303d050840006403a0b41c450f41c00100381ea0541d5404d003029500c941d112000841c0805081340040e030700c10801032a110600d50180e01c00b8041d0790244d14 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 95968309 1250 95967059 95967097
    0x3151a0a0308030408030c040b0d0603030e011d060304080f03040507030b0f0405150702010b0d060902090c040803030a02181f02011409071406040e070908070906050918070305060c 79
    0x10094414440c0c4006010b0080810016000821980041d580b20038058240c605290701d4907205800c607017111018074a285d0360361906005150304455124103640b42440e0680c403a449902e602d124080d03030608141c2c090380002c00805c0c00c02c50740d081602d00440c0d40300841c82c1c8a140c01d00f01542e59442c0741c4010750300d18840d180800c0801c0002c5001a2080350080020303c8606104100802c6030b000c010003500844d50f03501482e030b09940c2c9055070580c1080c001c140100d0202c01c1c5004108048a014180c6c840003902040200b04cc1000401036030b9105004520040c1c68042e070b041c10300c40390000c451403d6808003030003d40d086003030340102a01c034204020398020401c0741d0b0082801b010b0740c5c009403030392849580b245500300110071000c0700c81d2031550705c090b04d8035090a0f96140c0b4000d0505050b1110400b01d9205c4d03c1c1403118805c100b03c1c0c00024040a83d06200c0d2900c0e02010800c041c60140403a40900712910f10070824100400401009561141c102e0f2501d240030408420250000c0d01d003990219050380c = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 95969559 1250 95968309 95968361
    0x90503040e0106022d0c10030212060a0608040201230301030b01031b03020306011406040e070c120e010801090f020c100506100e06030606031008120405100c110603070201060315 78
    0x1000490302c000b124008605285940170070206888501c541d444921401455091548800c009104200c1b0540c5025072505a0f0741c42200d40b50070020718160142018120804c06158826100f0f40c210f0f0302800d0070220004188801400740b107002c40340b081d0002c0d0010001041103003200e0080e040f03a000f0400651b00d00581804031341340002d0761202035803541c001c0c0d0061060210603c2e0320b02c014000241110f245c10350312a602c00b41c0c0d030310840754171000c01ea0b903080342c02c140102d00d241c038412030115103001c5c1cbc4168140000a80940b00601071031143c681e640d6114061400180d04442070318900300b00311030456105a18040c041d10b821600b460084444a04005034113000381c024080741d6100801d4036081d070b80d9000901c2000c1d0401040400c20914413040050544024440380303943e20800982641c5e554107013018400380c0c1120300e0181007044032007014a00403664080c200c00c1aa03204844142e520340720004102d02424403138001030002e0a00840c202d40701000e6a1201408030f070388104080c0115504 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 95970809 1250 95969559 95969563
    0x80f010902030f16200c030c030d0206150a051306030c0504020a0207140105070b0c0706060e06030c1203041a04090c110a110d0f0305130806010605090d02060904090503040e010602 79
    0xc0d542c003c1d40310500004200d0032501284511410079207454041102900045000c0c1409500740520809400c280d126a040e806c3c00d01011111220540c0108180a44c000e0000c0d540c1e0002821444150300c882d4200d40f0550790f0720604002800001e00d080300381d5206100ba00c006140511045584020361240080d840c2058026118803000a4029081841c0791220761211110007003035880c1001010007130a40007518400c60213014181240c0d60030344800103480c050307040b19484c0c0c02140d540f036040c03410040595800070340b0304c90341c917001c0c1d880358076000303140b80100d1950185400c441d00c501c40f41c007120001e089101001c0c008807040d100003070000003084102994040e410190040542d003107600c0400c08502160020108650b0217441e6144034030691716105001001c291048002500c0080c181510a072641840d0010b08400320280041d03524141018025125040300180540a495011400d651700c1d0000e40b42c0118024000b84013070046850500e0f2a07500600840000e50600c6001198403440 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 95972059 1250 95970809 95970811
    0x30906091207030503060d080f030901050c031311010c0c1421030306060c07030204140f0702070501020d1107090f02040609060e06070f050f0d020709110f1b1903080f01090203 77
    0x89400a00d80034907902d01300c940b64401002c03207400c5610020a580041c0384c01c00140040b010b101809034903820b102c281d040c00d551028114000300c90003401800200c11381401390b4811035078405c0340324010a20040058030444000c44d070241c00360062a400080c0440b203404103922284040301c0314098000441021101c00e005040304410a80c020320004245040c11402003800c4601182140c880e242d81c0c0d070014007640c0742c40b402c4952120091080c40b4030b80d031103010140c2d0003265900180040c40d0070309000039134842094001c1c00c10410fa00e00000c0346480c080c4624400341880c0081440700800c410160000303548a40704070000a0781600000400500c0780d032060603646402030983e8548061520380c60b881c501e0200003a40d17035014a00442884141c208415000da5001e50041c0110360700d001c101c2001c0b5900d591192403c0d160400141c2621422107084501d813000141c02a681c0070780340d00140340b515910705503142070300036518198400c0c1900150300e0392040448078400b03180341c1e895004e03030010307400 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 95973309 1250 95972059 95972083
    0x2070c09020a02030705010905031c051b090607021c020102160819060b040c0e0f0301090b040b0711030408060f01050a0320060d020d0b1c05030d05060d0209010b03090609 75
    0x1604010511044005400520705482c0a1045908003890750f00d51a0842c0c60442040b9045d600019512607034843e41501c4980c2d82c840084c003003081c2c0c5000130740b0031070004007404c1540042d400020075240c2036903814299140744c0d40182800c04170540740c0b4007052450003492001c0e0701500c618600078001201d00311a078002e9030000e4024100301803500e0100406400440811609c007600e82104042980f00e0f440f0300711194815903038a05083c1150002c2c003040300a40c03907045019034140940324000c00c103103412140c0c00c1944840407034603a96402a080f0b4005040f20608400d134000024006003102e00041c0f400d01810441d058074441d079aa81c01003064161503407000174081b1080501c40d05001c0c4070540083c400303c002900c12840c08002d0742c568022a03004154075544141ea46c88039603480d05002c154280080000b07440c5c88040f102e03030346801e50349000780d4803940c141e00c3c4c8460000b4001d444104609005030303805000d01a071075840784a03406040c1c100700c0e00da01c0780d03104d01d0001648180340001c11a203000c0d = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 95974559 1250 95973309 95973323
    0xe30040302010c0b0408120705030402041d07030f02030a06050106110f07060c030c060b0303160302010509160e071101050703020301080d020c06041509120b07180e010b0a12050a05060f03010207 85
    0x4403e6640d46244180000e109031000c0c50140000b081b10030001c01d02612035081a51440d5813407420344100400c81d5066115107440c00000b80f0800c50a02d07000503088241e940225084503184144d100181c039004100000900307180c1031000002d00c0c2600240400303000c403244801e90b1f0005842528050b030340c0d05640305050000d0300c1d9080402c00701e4000c1d4801c002a6004001c045044016100800e186602100c05948074000c403150703c81c01d040c2c0c203114458001111501070051f03684d80422501078090240101b40c6100c40d52808070354001c1c010100722041150700310090000c0d00d0701440c050000c0d002441100744901803c401c2c00b5010748042100f00988800420480c1407d0034600745000c05258442181c00f131081c40e0102248000240c1c0501e41d03ca0b100d000610298070305000c00509000c96190680002c20f5020030070700a038280d41c1412415280c8100e121502c1e41800d000072144641030108220700145000d05001c810501608964803460090700d234185554a540c4c1030500b02d1003144401342c80c039 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 95975809 1250 95974559 95974577
    0xa02090a1b050903190b07030e03030c0304110a2c01080d1205150a030501050714130501050715020c0c01020c120c0d050f030f04050f010c0f060f0e3004030201 70
    0x82c002d8000c0e02441e90050200c505420852140d02d0542e0380c0c94506565103202001000b00455050140c4445210104003550960410a00041c0180070190008110386e004a28110380742c2c6909800074000c160079a140000e2034200349541d0281100e407052448010207480c000318a84100184260384d1301900d9940a440c0203060030b4010040001410301d080d2814001c041c2c104e00da07964580400a14001c40000400c0e042a0102810780d00600318010303000c4c007060103c60708a0340020100f904454081c00c01c503035261800d1a0044010f1070303102404c04403502c042707a8001c1d0341e0800620943e52120070f808689c09a240d0800300403901c3d94603490900c031907201030889101c508007206035034410361140c400c980307065050460f42170851f00400c0015650b020b01140030400791428031512038660100307013040701e00300000307403039121030f400035060040d01d0706441d141c040744052200d03880012101a40e00c2a2031410021441c4001c0c15803c190555024003400c1c0040c0070b40c0d07615101110100d030360584039410b207 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 95977059 1250 95975809 95975861
    0x20c04050603031c0e0c040c080f0403140d090b0a020f09191d09060705041a18100c2609100314011d07140406050c0307050f0a02090a 59
    0x94000202019014081400f842c4804c0c20001800c0c4d075081800a80440c0b28600381001c42e00c2c15440d04003203440345051110f0303580030b180c1120140c3d8004804103030341600350741c80e07040c185c86050103038400020956000400c2c240c42e03d460b80c046402c15114250341c05e000c0c5c4417505150203900802e4240c0c01d9110040048410310300e00004008150550b80e0348424907160b640104100d400303452644000306004580c1003201d0031500f800031651120042c00c03d00e0030541000c40141c03d50024a40031214000c000524801c01c40b9038214406840c9001040000703100607440340109100c410985c212904540d1900c46009003030203035a04140d06001590701402c0601590030400d10300002001c03401410341d54981031806107002c2c008640a403200000180d50200240007680390f01400a05c190100070130200c0c02e0340b00000b154119008c485a62408035100c09442607001d0451140040c018038034498102e0003130f01058086004180039000310381c1d00700c003555000303d450283c820f003070143d40340e2104040713403446 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 95978309 1250 95977059 95977061
    0x21e120f30120121050a030c14120a02100203040807020d030c061515110a0308060a081b01080c0c030901080c120a0b1306030c0b0f12011401170106020c04 68
    0xc0c8500c81c1070724025807000450030440d00e96100390310207a8a00340600c0148042c91030b440000f00c1e50810740001c001d44041c591200783d00c80750303d148000c0800464003240814070007030501c04802441c2440503141c1740241d07080b401809074010150f030b00150052424903c4400711620030f0760700c950b03004031343d41e40303040750590801c9802034042c20110140041c0140080c042502c0d0303c20700c801782c40d913203c44544090403c03411000f220491039083d410001c065500040510002c101d0900c82981401d041400e6122200024034070300f126003102015104064042600e00308003501841d4480d800e0f00c0c0d0b0606a103e503556816284140500c52202e039008109101941d4892084250310812a075110341c142400200080c1c034181c3c06030f82081d00d240c4c0380d0440403400e25207800c0d5070768111000035042001500d1070b03442200c130031100d00c2080041032000c200c2c800880c2219084403000544880c07440d19641e150f03d0380c0480102c0044d032250004140c030600305900080c80c49414113a890a400a020440ca01c6003008 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 95979559 1250 95978309 95978353
    0x709050403020102040806010602030d1104060c0f0201050c030c030d0606020d08040b190f140a050603190f0602040f080c0108010b03060907020703081c1a1804030903021e120f 77
    0x3802c640d42000000b4001c0414000c850282480c0e60246070750321080c0c030815080c0d40c0b007841c02e501c0c2002d0801c030400c0810f40094405030340c598040074880307411185000690b800e006858506c110390000045401080e0400b0004000c100c0812404202c2d960700c520040342e403a0208500e800200d841c0c140890041b030003000b80300340c0c0403c404040c00d00f122080d0400509480400c554005026220004070841c4450340000c20340c03142c80c10100300107500c2c08000003503554590031103d2907101c1a41e929081840702180c9200c100c0c1350032400a560f5141d465200c0b0312004124800ca8905001f0b001c03c41400350b11034110141201c0b05003011720301316100d04017006a00b100141941081d4800c0c05000000520004081c0c010b40c2140700f0f034031505450341e010400075680548180c00f508040032101040036a980c0c0a87e944503d10001750042c02d070345629080c2c80c01480398101942c41384100f5030303c01040b24204440030580c60107490311a0302c1c8030305000c035642e1401002d0704000c00c1d80201c101541d403ca0300b5800c071 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 95980809 1250 95979559 95979563
    0x14090f0610120b0a0e1510021c0e0901080703020306090105040b0a0b01020a020406080d0908070305030d051909080702010e090403020601031401090c0b190507051209040f18020f030705010207090504 87
    0xc114044000003900800640e201e178141e281c90074100409140d0010801101a0086c0e4113110b11010403c40251500109a05194009150501a00c0c03e51180341c10b29800ca60162054801d940c580010a07507680715403100700d02c01c0c825000040c0c403a800c103001e52400b55601c500210400d03107421000b50007134044030481e181103100342000300c00980e803140950b40c01452004042d20300008107540082040d0f405d9041141903500048042000590000c102c451100e0b82040009442d202e40103c0c10f100b900d02c0b10310764426130130482e41e041400b440c0001801c00a00c01d80f68040301c01070311014030000000880d0040d0258000000401c00310701c0f2080203107a8503080350000645900f8554400042a03140d4006505400010600400d20100c00e100034150f9021410401d08211160344e0329030351815204002d02264101080086480d100c681245910507243c120074444104401444500e003c00c00c9000d0f07214505192040d00300b0706001c940da0342a1001a40641400d07410540c1a2011704009001 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 95982059 1250 95980809 95980811
    0xe0d120f021204060606091a03150607050d030e0118050a020907030b03030c061501030207081b03070c1805010b030105100332011701020901051c06080714090f061012 73
    0x282c0700650486501244a00d104401c0003405c0c5040c00001450044103801070303000c1054024281001c502c40c0c1054950140c0150181a06c0b200180e01003589401101d000820f50320512810108040e010f42141d0b4207048001c00800c1110503206074000f41c50a40c101c0035240382c01c1407880d0000b505000f02500d0b8441c1c40d41c140460340b864000f0100c0d2642c1d00190382c1409a400200600900b00d03502c00105424031024601941803207071540f0703180454425410181d80380e403841071100799402c0e024000d80d00c100f90815940c8903c65911501b0207c007052004801582c41d1501c00040368031500003061f0b81c107950029040c80103500c6518000d4004044003d011a50a031850000c0c0b000c4da8103081d002c441646169288a0980d407404000020441c0c0b4001019101d90050118030700b640d0744001a508000300000b0410702802440c5e034000c00a1400e504401c10a006520f0089080c1040c000501c82000c1e0940380aa21542ca081d98401200c00507602e013644a8000002c101e4501c1c4100082c0b0003849228070 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 95983309 1250 95982059 95982067
    0xc060318080d0b0f030115170f0619050a0608030f13090203040311060c0306012a150506011202030105030a0f080d0903120c080609181002030405030408010e0d120f02 73
    0x6400c1d403a600401100c4040503100c201400712410420340b81c100111041e0700a200900d0b0f219800b0100d0307403d5004510352021000600700c0c00035030400034281490600e40c1541c1084c2001c2d1b00000c0c0c99800700e21008265820040842c5550a840c8a4074080750003070806581807203203108a03d0b03240d60000840d1001c07503040c854086544a4144010340c000d6109840d8200d1440c003214609052010003011452444414010081a80d8204100341e0403450a98044094901c0d005d000b000c503405985000341500b00c90080c0300025900f180c0c07005024040c241c95100741b0001c80010241648000d0090f540c05130042e26285001495040d0150051485000e0490070181c0c1d0031101011101109819130025966240a00e0000300c0c43c030426014102a00d01080149411401310b00b000c98080c101051f10100d8403903050903640d0074046c52801e1a146035080d5581e0415041c403503941d030002d0050344959460110f001c44500400900c240d6640c00c103840d83c0f070340703d80180302d071034028511074824107801d5400f04 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 95984559 1250 95983309 95983313
    0x70201060518100b0c0d030902060c06100608010f08120307022509050604020a202103010513020c0d0e0d06090b04050c01030203060f0402090a050d03021b030a0c060318 74
    0x200b010b82e0210440c480041c42c514210301100c1440d0f0107a07000e11010a030411125070508400300c2e010444c18941d08022468010501c082a0780b03110f100654181c9009810600020401c02d0340640c00301d400c50b585210142c3d81342c928261107981d003445007e001d98080e24111041c40c4150001d1a402581801910300030b05001e8989159441e0b80300e1800090b4002300c8040c890850076114298000a00707440450400c114041c0180c0304088800c01c0001d441050072401c016400c0c100300c0714148806051031040800c0040c1c00040c1d40e2780081c01118441e01a014403c0c88003112442a54642c281190041600d85003041041d55045542c1c403c840c0c00254200800e00403414a0054070700c13052084010400030b18050414030f00f401c0001680c64101030042041c010241d440d00991104284109c0c4e0050b541c48441000400725540341c0e04c16504100080054014142c0202c0e0080402c44d01078410b9807110564010161612240c8100071300e62182d1500c148540c0e072003a806001d00780303500c0000c05071a64981d = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 95985809 1250 95984559 95984569
    0x1212040c05041b08010906050d0b06130f020909090c0102060112060603240b0103050103080a2d020604050706171305010209040603050309030c0609090a0507210902010e030d020607080702010605 85
    0x4206040d00e5003e019210082059014400d10300401d040c070000c1102606201c0010316140c0404409084128840d0106070296511500d2040b4101e0105003005100c0082c152003001e50000740c4094440c00c5001c0000303024440201d01071030002c01c140d0140c00283c0c05c1c84c03050004000848000d450480c0d64a4012000640c002c03800070012084154000c40940b2010340c00c1c040c1e03240e0500003810941084010400500a481551603180c1c0394200300800d100c01e08041500403801c00000c00e212023400c0b55500085130003003190381c00340d809402070343c0c91192510401d660000c1000c0c060101031700c030980003e140f075006148a00d5036920a90001d45415000382c0003500381c40c02030b0000e603142e400001d0311144500d0b04103e4404240016030b52b040c106079000380040c110f001c000381801d2001c3d0311000001e901911440c070188860400c1c0103140304004500d46410002c100040040b400706840842070401450001043e00302c0100740e40c0205800c0e95161000c0b117480202600003015903485110104140d82d0b0 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 95987059 1250 95985809 95985821
    0xe010f020c0c45010510020c090a0e0604080403140f060112060b040c0e090711060402040c020114010b040f0b030c0a0e031204030302010f050c07080d020901090512030307030e1212040c0504 83
    0x4880280704250a48070540f00709258103a000d030303105102c500e00b801005078000c02e91b06050001160100c14590310002c2c02c1015043c0c7e0b008c200c1041c01000208010840441c001c4c0c01901d0241242030551140d45c5503c0342c0e40c0200c00d490742040d50141c0010851101d00440c42d0152922515010940c900d086000c0360503104000056404105024004001800c004c6a0700e40d000391a0702d81050b0f25920340c800303a83c0f154000740010b4040c9464030041c908c494000d4108412101402a400d00c440da5512946800742d003190041e0304407040c1c803040000d009551030041e240a80c01c20040c0d1440c2c0240711000780e42c0c120b9480d42440c1c050140c108c00d150b000d030440004d03000541c02900049400791041c000300d0f04130b400c01004641004000c2c400d02d00440c003130728140c980b5200501001652582104010780b22a03003145d0000b03034400140114246c0c6184044041c40c02024691014030020500c081c045803607451103502296254018403a2800d02c0c120740c100c10b6006030040440440482d00c800100d010341d02 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 95988309 1250 95987059 95987149
    0x911060c06040506090c010c0212030403080f180916050d0f0e01020d0e060103030c0210030e030409090b0a0c080c0a030e160e0108060f01030305090303130602010e010f020c0c 77
    0x24410401403207014041c080d40045d0403005000d1900c84400040d00e500c0743c0b008040d0061310030b0064110303a140e0801c01ca40256402404558540c0c0d220503181c1d9142d440781000311070606548200400500745500403500801102c0c182c0000070040c05c1c022a0203401034814800c1803602c54501c485001c0480c480c550316840441c00250303036940030000c5c1806a81d4500303100c1101d940304200400120381c1c41022a03150580c1101c200f4903d84440d041100a4241d80c3c60751540b038080041d000400280c1c41c0d01088080f4850744507400030f41c0c0ea480c81e03002120000a0303c280030502c2400040c2c940d061074801080c04000700c3c1400180c1002c0c0c0c2646a103000e2802e550301d4041c18036600700340014101000c031280140a640010305241c035208101c484a080103200c01401c5c0301000ca56003042c0d030380a1003500e01c0c0c00780d0303451204d041954a460080c068041c2442e90b00c615440c1421450541c80315008031241c0c0500000101040b0051600340130780c2103c0c09406a801504500041c0701401180b480701c40c80d25 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 95989559 1250 95988309 95988313
    0x33501081006080c0306011e0e0702060402090a05060108070e0303040806010e01030b1003150b04090b16030b0d080403140102120901020406080708090a14030405031204090f1503060911060c 83
    0x65090840e034001c807031a5401283c0e660b4001d2030703a100c40d1750740003481d641036038140380708180c0040484000e030303042d401d1603009252090904800c01c08490350006a540c880da008a070f420b841a2a22001002210b03000c2d1a0755000514800001c0d072281d025500640e03e100028003103074901a07582000a0604070280c100d14100d04000c40100103100f05402c0c03031030300072201500c0346891034034590b00c1c941048403c03400c2010003621603466042907070700d982c0203032213054114025070b4541c60400000d0100d01c3d01c4d0600389010a252403440540740c103200c038400d2109944502d039a807420b411910391640c03190300d4280d4200306640821900c0c01c080001c00c90a07024070507000002d615941000009440712100a00e483c0c1006421010800b905d04001012000c49401c9006040040581c4006504501c5190441030300340c49044c0d001c1c02c002ca5200010700881380c0c1d00d001082045142040403080d110744007414041c40d0714410060011030070b10781c040800035100341842000c480d0010003141194210b007203140c0185e = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 95990809 1250 95989559 95989573
    0x60d0503191e02120301030b0a0204050607050d020f010e0a03270b0a080105010305040807110a15090302090c03040305030c0a033c0e060c070201030e060a0e0d03050403350108 77
    0x41034030582c00d50070003a0034006015032141c44024801c0078001480301401b00c50007440825007444141e41168040c1001900e51aa2802d5a003800faa459420741100c10040c41126030540b500b007018810441118030304800792003104429101264100c200c0a90180f0035002c001c8140c0704c240002f50300034000d00344000869162a5100c1c0050501031050f031020781031504140400001518035003c403207445506c4104110029080800320701d0701c1c500d540100c1800d107c4208441d0741c85801c00c1c1030310212032084502e5880341c1c2c0c0304050904c0a00082d00c0080c0480c82c18404928070207030100140c05003405a2400040c0c5035940e1144002040400520180d40e020130000d40c0c01c0680d00b00704d816091203000005021050100c04025a211402007181c600c2540100c0c81d0001c40e0f2080d040755018414100484500c0e0410451000c028411114005001d20542202c4440c16011b8012503101c2c0790141c40341c026060310b202044101c0e03050300801c1054086000702c040b820052000701e26000c1c1602000601107 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 95992059 1250 95990809 95990837
    0x140f01181512120f080115141201032303090d1101110706080a05070503090c040b0402160602041d070e10050712030605030f010b0a050d11060d0507020606040203010e060d050319 78
    0x8042d00040c4d0008003c41d010040c04488000c11b8003109402540c82c1402d01c000c040c9001c02101e005d090844140004035800000902580760405010042c5001d00000403068401019950b4407400c0c0b8919017080100702e40c080414010030340100e0043d4181400c9000040d0b40300880d08040c0503400c8030700811500d20912003101410301c5100d6000301c103410032030b10350b082250207940da40e002411085d03c00c80d100c4030030540c1d03a100c03a0155015401d47c600c540044100e50b2a0501c041d40080c010f0301090101005442c5c00c2109081000380144515191402074400400911011802c4000a0020b1004c2006100e0000e43d00080035280c100c01c9980000725a810703c8105410810703d1510326005a0402442d40807540d141c0f0042802c88104440b50035802034185404c0c0c0041602d030986d40e92024000c50b4041c2d800c40c068115510400041d4256034080e60380008110480c00280984107040100400052407820502d8005070703041c1c01034040380c0c00c2000b401e401250500c403034044a80052904062014 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 95993309 1250 95992059 95992067
    0x92413020c06060406030206090904060b0d03110c01020a0b0a050406180f02040501060915030b241201060504030803010302010f020c0303030108010614040207082713140f0118151212 80
    0x40c2040d004c582c240040c61950f0009901c6020b0341d881a48039002d000045010007603603038001070390b880003e02424a62a400d00b0080c00010001703114035580d02603003030180c03202c0d880866822000c5902034090001c070745407a4003130002480010000c81c0d0541ea02d0007041020505012029070040c410030b030b81030840071548180010b4407c103a00c0001130060703008041c4004080f501401941600f0740ca0006181044000001c1d80850030031622501c0c500a0150042c0d4103908000800111200680402c9140d980b41401c5859106034440176000da8028401400158401c02c0e120a4044007441114071403044040003d045902c2a44840260b0b0f5441c40108011414810030a22020702264110b003840c20548034803071948074141545d009040c0c0a0000b03640c80c092584204515440078107a29003014069181100a20221420980d103807510000503003016071048100303060b03400c046407102c880c0c0c0d2481003010203480c4032100c0882c06020400d012800500074070400e41c10900414825101c015000341c060 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 95994559 1250 95993309 95993311
    0x180c03030403150c170c070f3801030203030a081f0f06090503191214030406060f0503011b12020705061302090705270a030b0f01150c02092413020c06 66
    0x3106011005c1384c0c0c050003001034417000350310a40350790440396541e40c170b031030074042c1e0030025a40201108003a03003005c1c0c18102c1614005140c181a01458125070501e60a0190404401d2000a5150727200b0400d02034440e1003240340c2500040c007202001c0e04400e00c03070020b40300e94055400412649410160402020782e0100c3c082c1c00420041d40a00003840507041c4038081440040750181442001100d50640c141c41007514034003045034484125180c0c04d0916000c80030f04400e01c0784c26451504a41c01045924040c41141000003c0d240107842007115008155542c2942c003a080c1e50040d424400701000c92010f1206600c07600f024240c80000d03d255204200381d210015204c0000c00105001c06030611003142a0996016008107651800f00c020b200011020009a00010288022081840782802e014012a8140c0c1c4c625140d4503402c60081030704441d810f81c2c07070700082c0d4405001808541412408090b454880c50004040e64040c050b00e130103c0c1c80080c9070040c03a02c04603400101c1c0000c2c4c0c0c03010701039a = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 95995809 1250 95994559 95994581
    0x605091510031b0e04050c130e060a0803030405010e011a01050a032406180b09130e0a06020d0c02151506030603010b0d030503070314060904031b06060f050a0b040e180c0303040315 79
    0x440c08c12102c5c1c1d100b42444e41c2e40d401458007069208001ca803030780e9184003850005080c2c950440b90f4901e003e1034100d0280400070b40d140c100b9801e002d0030204c900d1425000754600310040e540c03503081100d44c7d64220043d00c1c054001680d1a44203800c0e2081c20a040020080a04040d031036500c4489a07060000760102c07055803020024840c2448443c125955003480b00150418440e000300310244180c81d45418460a450014080b52000414526548140e08090a1401c0e641c0030b030f84013000110035541d500035046500510b180c0c8100c2c0110500c2c0761203405103400a40240c0000380c101311100108809c241449825408030303c001c4100000c050341406120144c5040c5090100ca0781024400b14045400142000b03081c401c400d6002008030300d48420032000c03240c22440611105607560b54040c07110999015050040c99008004280c030316a902c101c03001c81381c1c40241c0c5521517990b040c0000540740c0b00d100701da90300c0c090364454504c40e5074100f0141c80914060f400801840d5248040203080b15800b45003 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 95997059 1250 95995809 95995831
    0x3150a0b04061812020105070c0b0d0c080f0c0313080705010911100201020408070905041a010b0901030b0603040b0414030d020d05070314060d0204200c060a0605091510031b0e0405 79
    0x141301008000e05911811a42030070010707190b480f140740000307610100d5007125001c24800b00b1190320394803071a00074103482030b666201d07e0116143c54904000c3e40804544111461074100301040510303991480c0382c4800f074040ea40d400e0401c0740c5d580d01d15007036940140c410340ba640300c05182c64200c2c0c600a002c840407400580001c40c81d080c44d0104850312a60035104103c0c03981c0c1e03100005028000441c50480c0303030b18a4502a4002987c4408030303c141900801e42140c002480c0404075202803c04408490150740c21101442480c1d070b840d0740790130b80d00c021000380b11624001840130020051160025015481d045030010846140c8900001d08071840075988280505a44061007029140c1317080c12544c00e601910041102000314021060690380e940c400001c6500001d0540c079400c0d80031403803900546041790144003c6645000304414010240d81505685001001312051841e02030b0000740e55012900300802d01a08002c03100c10214002032180300818070619400a06103450720032a5071101c20300d03007 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 95998309 1250 95997059 95997107
    0x20402220503030a0807030209011e080a0b0a08061b0909040b0105010e04140708042f120705030718060909051c090f06260414060106080c0a0503150a0b0406 69
    0x1004003003600146c2003900b410b5001a6050003039219102c8145010090884900e480021080003441c840c4112030440d8072901d04151a0442e151041d0007001315030042c1c0050010b034880503043c02c0102c06980c5800c040000c200403200fa1910b5003407120b8890b40c02402e0340a00d170340c0b41c00c00242c02d101e02410014801c0e441d103440d100941c0c03010484203401110034544200f0564443c509880100909080c5e644005841e204010740c44e140103614488100058401825100caa103c2c10f540e920f401e40102d540c5070f040140180400b40c0821100e140d0164440000304280384d540d05800216002143e007500c40d03401c11200752000790800d2100011248042c5448894a860b00c03a00d80861035083c010075042240110480003003015003113a25803400c2008041000c0c0342003a103404101c03641a01000400c4c0d0003403000004100c2cfc00385480d588a0b0039440d207510b1501d4403140003110507034001481075101b1807040504a9060312119174600c05825040a85a9943d05048002c1c0c103030300d00d5001d801d1800c60825 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 95999559 1250 95998309 95998327
    0x3031109060a0c02120f010c1b080f0a0905040606030b190501021903090e09010504290403140c07030308061309080909090708030a17010e0402090103080a02010902040222050303 78
    0x200840d1030000c0c0724075200d201c03c400c0d880000c1c210f1115481d400c855200703160402210f1a410360180c400e10350251507400c000080030b01d050340c10340c078403900150105000340310340c000800900e0000d000d100700d44d01c2e1030f19103e9160070002c0d003110426089000001d56400d06c4a240b401e00700784961104c3c0d50644038030010352918000135a074915155801c0204c8603000004402c043c00303035036200060200381c41c0d54510b41c601410300c02d0003801d044506a4880701161a000e80003a219040f20050748403040000c041603480ea2800d4800b5020702c40100c1c1c0383c0c8420407482c0043c68042c445000034501c41c0c1e64904050900e0010010041c08201c04203400514150000d0001894841180c0040205a448004e142d4800c00b40d581012559400385525003c00190800102e50189030301c03203070100c81030380d0041e03d0342c841c240503040e650102e400035000b440d003000501c0425087d0000d0034041c44c0c41d10001c103403030005034041401d980100d501c0141030002032601d80d80e000404140400905070640c000c4d4207002c40c40d = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 96000809 1250 95999559 95999569
    0x60606050418090c1802090a03050c01090b0403050c011d0907031a0a0807031112060f040221210f07030801030c050409080a1101111216051801120209091303031109 72
    0x6228200c02217902c19400e030b03032101d160f40640710303074407070040102808982e203090a9031200d0b0740c6c0d05e44074000740503a10041540307281d001c1503605980d0000001c180c012411401912400c01d00c801c6600c080c00103075122441640c4004450740304880355074001c502d40e00e160071128200e00360000342511804d85180c1c20300c0b14940c0007506e80102c0b82c00c0b09402901e1202c40d808210000c00c410360800c550f02981041003104103114043e14003a40c400d440c03e24540071740a90382d0001d031400603072407201d54012040440c02c0d0a80f00c5045101000301078903d501e852a501081c001ea41c6c4401811000700d076011004000b0311042d000340c07600610b03007030b1402e05c88107a036035070340c000584103810072102030141001617060046400d60210205000d2020400d94850071054030802c50381c411600801c103500d4001100712010710400654500c40044003004982001004c0150703001c045444c40000c02c42d07401d00151485d41d4030311084902502405070100c0054503142001400d40b00d00c0160030141140810094907640c0724 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 96002059 1250 96000809 96000833
    0x50907080d0302090f04020403080403051504030e28090914010c0813080705070e0f07020a0803010501050715090303090203070f06050405040c050c0d0509030d0e0603010311030a06060605041809 85
    0x362500583c0c4c0c2440400091660400c03180103a000761001c02c021080280000091040c0d9000300203c0b179103541c00b02d003480340190003240d0040010b03000b0918098207003462500191000c008c4415400c030b060111405400d0030b038081d40502e4a0646070680f900911490380300c00300500c458000284880c4035a908050038800b006040c0100042c10316520360203016206050383ca07032aa001e001d035001c46668405500c1030352029100042d414a07100e01080d03c2600005035071103955840081103055070720b03000040d81c25420004003030300c905221060341001d42400b48950000d152083e2000140c18080c1e006051400c0c445030010304104140e81014019107070400d055404407081110f01080d151225603048815000c0c00610401c50b00c104180c40c030306a6001405840840002e9007207826075000380d50100d8440486400c6d107074200c5000c100510119488036203400031704101504407265408207982c0d0358115103c56100d40e00003040440c00344031544080400041c503e21300041840041243c0c3c45914000d12 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 96003309 1250 96002059 96002083
    0xb04050d0302030f03010b0d0b061315200a17030903031302011106040f0209060103020f030a0209011e2c030c2202040308040305010e01020304031205041a0103050309010305090708 79
    0x111400c18941010b20030011201c0346410720440c1078903945d42d01c1c001c4440c0d03000181004407003414640050781074200203064441c0002c00c1030020340320f103180c402c400741c3c000800100642000540120307901a9000c4030501c207401020f800c000e08d440549070400c00c1146031180040c103000c00c410010b020350600004281e07a040300c43e1030030549405441e4401640c24041036011b4461b6402003c00b0002444042c80c401c1c28510300070f45250a05545e41001101248915500802c0041052002c220134072a2940903202241d010f0400c0074043c41062498039a002c0310144030000100301c180624481c01001c0b0105079140566800c0101250000001a4640400509090144070b0b54034582c5104004001e1003025400300314003c564071602c03401c11502903405400161346075801c0c0210207590382c405200300c1c0d1142c0d405564401028015038200409480c028000f510f03c02425441c1e4400341031586241d0380254401d80042d0f944004490016007914802401207420707400803002000080320110710071000341 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 96004559 1250 96003309 96003319
    0x100609060f031508010207051e0a1104060e0906091c0503070c1505070201140c040e0118090206030a02030114090907150201240305100e0a021507050f160b040b0405 72
    0x288210124001c0540c0c4020034880c0d0410f800c0020216010360041013000d00460581341c0000300000140660003001680711041e46c0411410408200401c012150318003004001203403066a4140340b40c1c0c081001d80704071807140c00030024001d498404008006024043c0c0e08400030a84400c400500390f40402010a020b0000750090b49040042000074a40000720704042007000d800d24210013030007894a04000760900034580c1c003068001a00c0b6068070100c070501314607040260300704080d071110040e05202d560542a124034448005a4511014603c6205071080040c0ca03985040c0c1224880c619480c1d003107010b00c0e441d00512403031038030102d10781c4240c0310004185443e00c650301308200d00500800c126011442d40080383c1c51800c080d00c0c01010b0031603000d00d00300c840d211443d80e8100300300c49450128203080d9201d0b007007020050800c80d80c1c04840c0403050b500c0d94240b9000d5196181009030714948850b0941008129258180115803544090018070302ca042c00c050904180241500c280c0c0186440b030 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 96005809 1250 96004559 96004577
    0x506010914010e031f1103061e030f071202040615080a0203090c0a030501020a180f050f0a0e040c03021f020307020f06040323010b10120b060d022110060906 69
    0xd03400381c50b03d5000004050110762085c00000c0a00c415a001c102e41064400c0c100341c0c229030100c0b2910b040e47d0103113600400c41444a00b221142c80011503801c020960103020388c0708849500c603c14000d002c000c21310a000040282140c0c41080111040c0e42c05c07403140800400e401f1005207034460481d81c3c1c0719101c543c0c0140e80f07440703600310180361100c004000b507480f0074101004010490b0640207401058140d440b6034101c040c4070f58060100440e5070081d41e1f6816038000d0100103074503054060b12401c20002d8000070b14292038601c10141c0e400215000c1c1d403103441d044410011400c00340703001c1034083c03000100c1d0381804c410400002d4580c85901d50292103840030b102c5180903039454400312001107501c40b0409a55240205a41e15121505903130b500b0154039010304e0f5070141c2890f242c10041c0c418569909076450f414054648001c021608440740c03c46000d018034603503aa801e10081610890103a040091840f0764445440d110400030309625801400d40c7d0b0801070703190048403120035201141441d00340 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 96007059 1250 96005809 96005849
    0x10c050106051e090105040504171c050c0a02100b0a05040e01020c01090507060216030b0f100b0d06030b0105060f0f0315060307170f070225090908090109080105060109 74
    0x5028541c00550b4440d0f041078203046501c0d02210070081075082075030070b140940c0e41d0798108403c580e402c50b0080c181d04030b8041c0100c05040c180004000c2c2ca01018211000b50040301d03902001c90304101c0c2d000313a444d9000600d4140b059010001d945130300301601420b101c0382c462000401c0a6074454030a0fa80517a07120381070215190300a406407110ba4411800820120350f0340d0a00c140d803007550b0300c215405802103110070560200c0700c000b00d0040e0fa403c980c10300078644420011000614000707050511502c0d101401003400d4400c517004040c421909400861514103609000e500028180d10141c400c03442000180b0817000110240c0b5441d400340d111407038030303030380c5441d911304c000a0003840341a403158002040105003a005148484003000e00480b0908659170f5100311490250203680100140e03000f1a9118040c52075410f40b030604183c0c07403080ca5829959024403a0580303405480894502001090090013943c0c4030420b040102101d000078003142c104480080d000d00c20f68000c40865405968011030 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 96008309 1250 96007059 96007061
    0xf290a0902160b09010506010e06030406140c0315040227180a0609050a15150e130f05100609030803040602070203160603150503120307020a0b09061006050a080402010c0501 76
    0x100365400d401c1d9a50051030040000644642c42c0448050001ca404507018210510400d0300c18541078445804c1414078a040103a06c4e0401001114625180c4280d41d40005e141042c603402080b0207841607880e0704010002c40e80301e6000d241014001c0b0300c18080102c15600c8400400440c0305584c109204500c0c0d040045540101400d545840b80809041401014406588410221440d0010400c8030b916208104010740340e01c000c4145000d01503600030303c1048524510903040203424180812040308800106118501401d20307a04201d588550040c1000c2c41406044d50196000035803003a110300b00134025001865500014004000102c0040c04102d280d40c11115520740040864000c102a1404044150454086c060001e8105080316881d40c04c00003212040e02e900a0181c440120300c1880c01455800c014006021031107078600ea8800f20f840700c03151501811000d80a0503261401d0240301d81c0120640e400315040080070400c510f2040c0d03000303400030b42080c1d0900e041e1030f09141c5030030218 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 96009559 1250 96008309 96008329
    0x30206030a0b09011409070e010e1302190201050907050d02090c0c0a0807050a1106090d0f1b060c12020706120b030c0a0b2101030c0303050c160e0405010f29 69
    0x40e0304003142a001045d0300d40044071480032072604507280c601030b07031300d02008030344117401150090f0104000d401003180311701c0d004404c0c018035019140d0041c1400c56204c000b44000c0e15080342c45016135910307030611401080500208015007400d99440b01050850341c0400c0f80058010200c0e4114071001c149403000c0c150521903e1522a0498984d9445d640b450800c80c1e1299000300302181c5005481c0c07096040741c10700300c0980300401c400a000e01c01d01c00c601c1d21b88201d841080d04003241d4041d80103030070303030824000c480d2901e001d4000c6545503c00821103140040300c01e02054490019540301400c10005907030300c101d00c01152030b140007001c56803800c0728000c01c0c43e2542001010307a07c00180382000c41c0d40c410503006414001c000410b594480c14214000040485082c000500000d214801c00e1000c070380140000d091485001c001c90350341d94400342d0244280c40030340e000100038041d02e00c1031106202c0d090080e40d49016080008201c6814103000d014040782800105400440b070b030010202480e580e1100c42 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 96010809 1250 96009559 96009581
    0x702071a0a0f020109170c1f1d06040c05010c020f2812050a0605070504090513152903070b040f0501230708030c0705030c0a050d030e0601030206030a 66
    0x50100e10021a014021039042a1040781c005010524070000c4284140185804150080304146c44070310300714041c016079807041590800c01e2003941c0700c842c06103100c40702c1448230444a001c005007488400280540d58426070801007042e82c0b00406101c040f0b140c1c2400c26045074001d01340101b070705026102080801c5103900c4aa03a00c03084038003c11030500c0c285107004540001c103100c11001035031582e0950b0403080c0001806842544101030103400284981d00c0a07400490728240315040036580d20b90101580d20132550114848030015046d820002d8460001200d491403910500000d02c41e003d40350403524002500f0410600c81e8040c1d501551414003284e80075250003125030f80e03240e44851202542040c5482114005a0018200300f020011800c1c0401500e0005404a151290304d40301c80a582c3c0015152008903c410440000040e004000070440c48418130050242c064007401d2581c18640007d034003030141401c1084408050030302154003070660358101c901d10303120380f62503007501c000300300350010 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 96012059 1250 96010809 96010829
    0xc031209031b06071b111008060102060606040b070803060102192d1a0c0903011a031606020d0807030f0903021615050a050322080304170a080c0901030905190606051e0603070207 78
    0x4444000ca508c480b05038400e01007a02105d8103605d0b00400d01c042403003240304044514405002d000005514031008681010051045030400311002000c80d80640050804480215810601140380c6140c1981c81c0902003140c20107050021540d1030340443d40c615124110344160340080040c440e405504152000c0101c0075008201c103600c2c0404c444c2040a804207458400d03c80d00700c4d600801400030040c032040d2041c683c0501230041009405952120001e0701d08401d0544a250320800800c1510407036049500079030003400e070740700c00c0c4560206508840e00010564140242c103440740c240c0100440e02d8101c621718240340d80703546034007081200c442c0c5050841c88032400180b028042c442c202029600850080034580c170141510030a004545c0304461258002c6442c100010300d03c0100c49010307208100040c1000f0400d00700341ea031007508000c012003210f090120306030219010700609115010150406540a040030710319440f51a001118510420707104480c004000703551103100f030000c0030040000c000 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 96013309 1250 96012059 96012079
    0x1012020313140a060b03011a1905060d0b10020a050c0f040f06320a15050c0105070306090e1609020c07030c03030305060f0301051501050c031209031b06071b11 70
    0x44490f10365042200581d516810602c0e54a0b03e40703018030030030308424400c114486099500f40240080143c00160317031501e0303030142880002c00e61610401001504411000091344c010340d00c00b041074029110144104541c07100e100c040c000760780020701131400e40045a008100b0325407400054007800400d0080e02c03060341400800201d89020f0a84d6800d524510507071156001c010118402c60200e051a2156002c100c0c080c0401c0700003481e40b46036600011901c0d101d482d00e44004409403d6890a03a0440c00082c3c0c3e40303d041002002c94407882a01e110600d000d8203421059503035034000d4140c18050004440e6001801c503001c14010024132000b90b0303000c0810300034280d9134280503000300412a0898047c045c0205510030354941841840e206240d0040307101507001c2620011126500002c0402c10301d8401045003910048507815090703c504140b00086a80345c210550401444010142e502403692241050100e4150000c2c03c00c9484c41859044091904682c04c0101e1081131865400d0f4102c078000c1 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 96014559 1250 96013309 96013343
    0x602090607082712060a05040609211101020a0203390303041106030610030908130f150311300406020d0614030309040207020a03020306241012020313 66
    0x34040c00c0d16560f00307403502c0604010f0014003450600e241400c09160700000001403a260319075011903002401001c0000d0254250365511418045400b9041c0d040b071b030030404d00c2425a41c0200714408400b4418000c1d07080c03400800e0040d540e8000e6482652004a4540ca8404040040701141d42085409019020316000381700b1100e40343d50003500c06803900c003090700e01e1611508080c0c003140d000301c00160078444003041d180001c030010a410103049a03101000c00514079410451046170b000341412145840c52245890401c1c0a41060f1744160350515080075100040f622001c400d4502c00e07004421022064014a000d982040d410141d92016403002041400705008842e405440b030712510a804025407900c804c0f40b0700d04c150a0403103043e8507920800044049042c103401a048091015100040d0203403030b54002800c00c40b080301c0c40c00c90b149a81c22015541003044010911805041d41e000061003c0034100030b1081d0501c45803014010b400001069070085200340701c40c000c2d6080620a8003094a00d = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 96015809 1250 96014559 96014587
    0xb0c07170a0210050d0c0f090303080a090b15030c030705030606011b080f0c0f070302060306011b0b040303050610090b0906030411030a12030c1403010509060310020c0a0b01060507050a060209060708 87
    0x92507003905c01c624002102d00400e000d050704541c038a1490320f4011119265503001c6690501c0140f0040302c0701e03102c0da4241c001482c800011b90254646248010008041b03000b030501d400c00da08020f83c4a42d009c81c0c010005a1000b01d40f2942040d8203290050074411030017000c451080340524000d042400018070100c1103c41440a00841c40c2d0002c2528004030011010036680c5103a070002070360245007000402c030151301490f5921480031480301402104d082d151590540040e04580c143d01180d00c600c10070000b4901036411402c0c1580c54100042c0380fa0400310440c019014030314117240902800404030701400444840c504100100504403103509a45241921070541e22502a00209050400f072084160064000011070415500c1d4a8211ba18160070042207140181907240c050140952842008004d80000c2440a0100004060120716803500d6205814140c0c05001042010b2005500181c004100d01103482d800c81c001688804104000911903c41c91070000c1c841c2800050a51010004c = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 96017059 1250 96015809 96015817
    0x5090f060403170a020c0d0e03010915060603052404090201050d091a070203040b071b0e070e090106050711100e060409060311040501030f030c05010f091406010b0c07170a021005 78
    0x450030218865298004e6610682c00752030002c520790f8014140724003450b88191003e544c400c00080021800c550385454a03070415000403200d0740304540307407007003881500c4c1c2500600b034114400c20285da08407941d8151799040401145a051b20450b150828907095a2141c0140e41d00c412944204104a0b0110720384040881d82c2d200882d5210140500082e03038690000c0306407000c075240c0d40c0d90289070a0843e590b110039800008116101480c2922020481c0c2c0f8254203e584505401d0301ea280d042021072042000000050b402441001303420045800050b001a4000c03140308829140030f01d480220003029110b02019a044c50740050002c9000182c00019030080802c507809001c182c1c5040f40504c00340310a86100740005060388168010780000a4880c25045440b90301030400000d40d18405c0344070130151406c5900c00d40d44103d400c0341c0c03030454410503c0450f00506e030b40c03200700e850400c0400c540da846442600c1035560710881001c42d00c4020748180040d55880b540240f0000117042000409881504 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 96018309 1250 96017059 96017087
    0x40605150702030f0607090e0414070608010305070f060906110f0102180a090c05070201230706020909070320070c031a041403040e0f0601260919110405090f060403 72
    0x401c400800d40c80840202d05c150082d0074943d103c041c4207081880810204002130001c071030104051041030354600051000d41e000d8181c91391030740119451810203500d4400a030f0031110900103450310800100e0b4208524070121019410900050050341d80e149003030802510038034800c1d5000040c0c10310003044e249011111140222003202ea03d0b41c560030f09100b143c0d540001034020820402100b0050b40c050000620140d10100c514000d00c0e19912500b00c40d81c002550440f01c4030340101d007103142841c007200c00c1d45c2d01c501c0500e01001402562070041c4004c8000c04200101c0480005140c024022682503510185801c00c1c0003096007030300705080e1007000d42c0031242621a552122000680d07801c011084034115000c85a4103001d688460604103043e10340500502c0c184131503255905800f10706440c0341d1712420503000002105c0d1908030521030503c066001c1e0101d5030342106075608001600300f00b800321103640c203071800200d82d034840140901e00580d00c01c440b680381c400d441c104420075a2045c19290815 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 96019559 1250 96018309 96018313
    0x8060103110408030a110a05070f090c0809070302061606151509060e04020a031407110606010f02030f030709031719080405030d0b01050d0e0705040e071d0604060515070203 76
    0x301c0d201c928241409240101c0b41c00c0d4104115600e6400c0c0f0500d50402502c0352802075070701c181c3c5240c3e01c1d28034160306644403410f1025094004c100c01c089511400b684825241040351191808510184d02e138642404001e21400000c40c5100010070200380c11702105500142c1040019000300e0340f07007003418141c400d80b8501540102c1c02c030313562032040350030808441058403031400c007240d201c2c03c2001039040911210101581d584240f100c1c030200c106014041c2e9100d4442d40070980282d0781e44c60402000608a03414000440340d5060010382c004100d66241c0c100d51089034880c1c4424008440c906007a6102401143d9050a40034058498000901c0e9110303120f40003101c0000d802c0d1041d24200303c103c0300a03100e5081440b030600b80b10344940103c1902d020524000c0e241490a046074011104521118480350340719038820b01041c10107100f100a844640c1000f03000700380c13802c20302c1442cae107000c022011140d20201010507419241c40d00400c000d07040040040990407071100c3c00031303461381149a0980c824 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 96020809 1250 96019559 96019571
    0xd021602030d1404030605090c0d030309060e0d02030403060e030c0604050f1b091303090503011a010809120a2a0308041a09121602060d0b0a1e090b0402090301090308060103 76
    0x80e0b4042c0240301615200f1080050400f441e40e05c1d064002c2c140145800e40a0061a10b13100759940c80c6040d2040c1c80740700c1c0d2000034106603076023400412100780201d8040117500039101e00503075507000810359003140d82c07008011a280c000741c00750f181540a0384405007403620903001403000700000448c1408842490030111020604900340f800e6a00204009190308000e10001144550010805100c0018080d0812085050366080030a0848a45800f00f010b03420316402240342c2980d100c0e42d07254001000c038000f4007410aa01c4200341c0c0c1440368030401810f001420401c041030b0f51508201c41c0c00c8044e0079002d924584001c2c02c0c0581200801c450489410440194200c4041c0a2300095401125010005d192071409c0514942c200d6000c038044800020f900d134030030b900580c0c5082c010a032104503200c0101d544289182800b4600703000b1b4105008160b03407070a12102000c00c0140345c104980306824041003900107a00801c0081c425844100c4d01942030540c5807003410b80200c1040e016000a076000c10403 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 96022059 1250 96020809 96020833
    0x30612030906040527040b061008061806150301080109140f07060f030b091807050105070b0f0c1605150c07080d020d020f0412150204030320030d02160203 68
    0x3030348100840c059202c4810312050002c3e08104515402a4160884884054a0640e148001400c0448046900190007402c00a15003042e9820700303944000760400c8036040c205000090420a030b580650b01c5c40c4c02d08600040c2e116604d9108900b40459070700305032682c95841d0700d2003901801d01c2020985102d1821000200409000504560440c0c6004007038040703581080c400312170400c50200e04a00f0035480e03c0f03c0d00400c2d964544850b0040340c0d00722102c0f031050724607000c0d60306184043d031045051140c1407121a010038191401942d0289000000303020310390b10144200614000c0c990b072703121400c840c034011608004000424200030f2146011101d4540c0d210000746901c1e00c5900c030001e000004c00c1c0f200c41d1602e1281d030007412024502d020050308100800042c020309400c070b030340420190307800c0c1c4a2140c113212442616641d110f405100940c6094207603100034011810300604c1034030784400b01d241070394000d0081c8182c95007602d800c074040d0341e01c1d03058031a451860081000d06034400d0061600c1049 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 96023309 1250 96022059 96022063
    0x9070201091b120f03200f0d03060b0d1503060e010203070201140c0a081306020a020318060403020904020913050115050901051e01080406020706060e190506060d020708071205030612 80
    0x440c0d1600c0010a0482401d0392010b0044e0044030b07049040c8803141400000007251007050050740280300c0c0040500d003030b1f060141c81c0317055000c5030440d0502d49401000d10855400303c04498600440034000b02d20b003d45801c41c410488456400900107038504500803058000640085000b600c40f03500a0141071710160852045102c10f84902001d400c1c01c0050504c0706028030400c2c1da02c5114081554010019512031805a82c0f1880d105801138200040103100444411a07510b52aa4180c9040d41010f00307590100700c9a034800303840a441078a140c40010310078003001038070311000c0c0e9014000703005100c940c138000b0401c0204ca000b040c0c80344400c107001043c036062040c0768005d14104080600f9134000d211005554058001d84180c0e4100c1c2c08000d80300109040e0b0243c100144400034503403200d032920060040c8603c0d14400480b103028100300502032266074030b8050319440c41e500400140e0320520791904009a1103100e80c024140d6810051009e80e4a40080c060b503c500e03410303542e42e2900f51007c0103640d = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 96024559 1250 96023309 96023363
    0x15080601080601030f060305030c03070302191509150e010c120513030f0c0813061b0c0b13121a0f0106141b1f0b03030405010905040b0d020907020109 66
    0x280c0040c24840000e102584250480a010460740000142e21a240d449582c1150b2080c1203a0305a5840010f103a0101641080180c10140c448039800c001c0400944d1000c201140203041d81c82002c1e103419000c0d050141029040c1c848461514080000002c2001424068401090180c010880d1412481300c180ca143c040c0038410440080d100a074a0030761354058400c03c001024410800001400c0d100000e14000010901c0c2c40074103820080d140e1401900819128150300780030100d1302080240c40000309200c02110507503507030038000c0d9212215869154402d05c1903070301000000c140da243d001e00b84110844039420041c000800c41215a603003080b1b02084250a12400300004c0c500b90038400202c03281c50241c200001c100c0c2c43c01000303000d060b59907864203240e94000f10b40f0034070709404084100480d2103058002007003500514201484c1000181c40304045101e6940243d480f0f00e07084460303503a00c001c040089940104919418242001e000b40205500b0314122152003880003c11500c276240c075070003 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 96025809 1250 96024559 96024571
    0x5030607031407170621030307080603010c0c03020318041e0b100e090c0702011205010314070e07120510050a0605040e0a0b150c070503011e060905010b0304120e0303131508 76
    0x407003c42d80720031090245c5009601c1c5081540603500c01ba142000c03030f05100450160b0308076540c00c2d041e400c21070109403c482e40705401e0018000c0c100c80950000c1d4011060741c426807654980c003c03000502d000410040c0070f48001507001c103850040b07c0448910b20760310030712603a1001c0d07665003429110709005480800420a509510644903400240044080c1008181c02403044c541509161091803116058540c20b0300115280d40b0950441c8903001010040340c0002d22039490314a9603800c15500160210b00550a045020342d250790000741150441c50902c001000081c0c00090700c1c664a1600824540182c01a80200410314001c2100114580190195541c000304071148001d0040348201c0c041c0d200745945140b6001e5808005429602840380101e509101744001030403204030708024040307074020380003a1a8286450010301c815242c1c0420f881c0d01130782c0505c40d0070b1810700310402940c54050f01d40340503a040c44005100007000c42c800328513000b02c5030702c840414192081220151240d050131528 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 96027059 1250 96025809 96025847
    0x11030304050d080717030408120a050c04380309060a0e06060f0d0c030503030a0b04020408060103030c02060f04060e150c0a0b0c07170307090f03030807051305030607031407 76
    0x2d902080c4000010030001d0701c03070300c0e51300c00b40540c0348071021050300300315025100145c0201ea40e00c0444020401c079035000c00d0600d0204507500d03190540b44554016801a00710501e001d090b1802840341c004845820305c1e160a4012150740804501c821981d40304840d23642090040c0c1000c2807070300300d050041f4561500b4403000b90129a03606024003040f03142c40080954000424140f020128901b184844040d6014801440c0c0e0780c5013440660007520380c1200020f0040d031042008114160700030903140d040d40d03898604600c404565000040742cbd0b00962a018400100c00580003e0340e0340c0227075580070111400d41d02c83c2c1c0c866400f1021030203240034100d02c02071103420069101000450010429500c00320403803010342403211580b181645084c520a01c100ca0341e0001061103a12a0400c054400900e03076200002945810b507903004100100140545040c0300020492001c00035480180d00c02421014040307441918003448001e014043d1100d2548500003a14040366080d403103019207a406804c1200 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 96028309 1250 96027059 96027079
    0x12060415030f060b0109051003050106020613050c0907260105030c0103020f1c18030306030c1703040b0a03090b130b0901020903070b0f04030209010315050606032205010b120a1103030405 82
    0x200d0710f002d002200440703810004071304c60100c0c582e91250864501c0324001d0b0b400082c50b6040c644d029192490103480c00941d1041d01003101c0005800144180c15035105580204464850402c1621408100303682502e03404c1c0308000b851005105d40174814100d400031000c444000c065000158202d108100054600034010043c005010582100d1b0354660354030224006003003848002d100b80c11108402040380060785480c01001070006007034955014100d401c007802403182906032010360300d1003240700c2c410740d0300400305440010b03d000380d024007101c1c1d800ca1000c0700b16203440c0744126040030014004a450520710008908602c10520942c2c0e541c0c070740600109040307410b01e64180b910350132a050303400382040200408401a220b6003000d40c020351094101e00001030b2a13480034020f645004004c0c6004070710902c1001050003d602e810030007201c810740085000400c03800d00d1405445482c200070340103000980300a4180b00001071981909010341e66068402469008042e1a842103214080d80085206 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 96029559 1250 96028309 96028313
    0x130c0302010804020d08030108010e06010b0a080708040807020a060809010e010c0e0105090a0b040801020a0f0807051804020d0615030b0301050405060a0e0f071409090105060904060f1112060415030f 87
    0x800c816030018002000422148483d07030b00c000882d80260000e0509945503941203072f9078101007040d1400340044038101c1d8182f8107426001082d040c4010540b800b00b0240c030002c1b9042c00410300440c1d01c419005040305089903140c90000e0000b603010703554100341d0b42c44c0500010324a00b040c450303240041007130b5850410881200c0c0046802c0c0c0c00500380c06601c1864485c3c0054425080350003000103205510000d602e480c19604050600549040c0450901c200b12003084135a6a004044a1004410900e070101f422081d5001c10b000f4060031151080303031403504034046034001c56960144a141071540c3d06000b980b0200007454203880b410b550042c40c5520600100364068803e4000d06a01d00c2c903801101c00f50103200c46898540a065072003c103107040e180c58520402d04040c3c0d5a07aa004090b2002882281040e03030100717a01d80002440584003035a201d400c0041c40c082e0b50800210b2201e120051340d00c3d4001c0703415000b8024011b8865901c5649040d0048111b4903d03803442e00100e9400603a14050180c81c0c2d = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 96030809 1250 96029559 96029567
    0x20d1a04050412030c02030c0312010602070e090c0603041e050c0a052205060f18041205040b070f020102100609060e0f01030206031503070510020a0506091b0103110d0e060f130c030201 81
    0x17800c1c0590030b40c0020b22920004000400141c5005103c040030084194901580603080100e1600100e64910f40202040b2040400003441c0c1d06c80902a05d50070b075a550b40c1d04181c0e210380894002c0c001d4507450348445800780600000c40403e8204121811200d0903612030400086074802101c038903080310107240e5000408060341c49a940000040c040d50070501e40100000d8004080040341031418940c90140000c0c080d681013604a40c08580c10100d00d0581824010b669600410320010400700c00c08030502c0442e48280500c00408540e2807084c010300391a1403205025000070300882224000040000391b00a03a03048609040365005045207241d40c035000325011494001c130828070b4140c80b031140c002442c1d80340d030f482c1030410b00c1031540501400c1d2803500d8180d04155000e0000244c40c0c0c8088010040c403ea130b0003003035241c02000d08002450049130030507400d0501903000f1800c0c05900d440380c201502c00005c140c09106036a2505c0035051a56903014440442819107006007031403c000758284015405 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 96032059 1250 96030809 96030821
    0x50f010302030c130e1602060f04020d150e1b03010b010f080a0204050306070815010c02031009061b030903020f0d1407020303071407060f1707051606020d1a0405041203 74
    0x250b0946484e440500402c1c982c9016402880a030514000700011011750b1102d80d814035245102070b00240c14000f4202c0c1d0324031005400644a44000041c820801503a01e4a03692981000a0240180307030b0684079132a2158a1400b010300714101c1c6120004043c541031140c04501001615026501d11000c80c0c1101d828000420741034000b542088042120750b820484684a001d171903480000c1031800d4104081100210b4050a052100039201000144c1c0d002c80c8010b425450144c1c00100d10500c0d041c840040d201000501245520004004a081c0c1e07154114210450080e000c82d40b00740000c5d035040c0d5a45620444420002d205484400c9000300944004c0c40603d00003400c480c20240283c6034038125980450401a00c1e42c0411000c002080c0c00c940aa912044030307060441d10409034681c4c2104003100185070404011001035103010040f01c003079400790341c40e4104074219121801c28000e880100500c15420340c1011400b020014145000d001d0b40b4800d551042c03005524044030801680a088 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 96033309 1250 96032059 96032071
    0x1407080a0f1205090c010e0f0a06080901090f1406010618052e0e10020c1e010309080403060203040c090203090c090c16051c0c0c0e040c1d070905010207050f01030203 73
    0x2c64280d8034907815050b0700400d030083d404075014200c032144080c005040e4130450310b03146024900100361180c0d00c1e5a5621208102e50541c1031540055690600f0140144000300c3d0080c1290700e148955018400c07500c1c5490b4081c0420170881d40aa41c0b5250f00b61503000c40601c500c0303115800308409100d0760610700c2d000044400c20884810035540c00880e405030000a044103070000542400340446d481c607140400443c007070380c0d50000c0c002201e20580410404154001c10102c20a01318052011591080d80207c0c11103030859611921551070f85081d8010392b00c2642c0c1a655215081404109200140f00726401442488000c0c103070843e09400303010000300300a100c18100c40781400521131198005080c00c0803984140080c1c6440c020500700d04a20f200c1c265035002c100505140b11400160b107001c8440300313035001c94580102955540c07a2465000e03615403c25001e1510088442c500d40345002e851078058207003502d4a44403a078854004a0f901d9641e40314141c0d1240c50145400070341e5020b94001c43e0041 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 96034559 1250 96033309 96033317
    0x1d040203120c070b0901051c020c07090b0a17070801020307050c0105070207050d060c02100203070302040911030c040b0706060801090f020f030d08011e050409080901080c030114010302180a030c061407080a0f 91
    0x500b502d484105900e42a005210007500002c00e07080110ac00e102e004094460120200b045008180108144420380d024180c05d0720601c000541001c0b00c10003041c5d00420700c410007550790745481c840c000c03c550001e4a101d0003660812020681c00b600101d412010384401038114020489580c581b00c0262003200700340000d5004da04c4500034218000c1c0011446002e01e914003503505ca117000800303021034444215003060600d0600600102402200864085407604188552034110714180030008200c00d41c0880d03055840c1006c00030411412400c54211a03000f1241c1200d1191450305054603010074000c41780c0000d0724640180b1101b2000c40e40d00c5c540c40903158101c0035a94840d008241111510300342584c4024021507046842e6034442500c3d070f4450903140c03400b810340d403428499111040f503040319541455008076100c04d02c0190b0a500100c200002800502c040d0340d282401004084140900300010303e0021850140c262441c044448140d031020600d45000010a011550380442543c450104 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 96035809 1250 96034559 96034567
    0x50103080910110a0506010f08060105060702040222180b06070201020d030e0a0b09071403120a030506011215030524040204050411030303160801052b020a1d040203120c070b090105 79
    0xa0204040326410341700d00300074032103035040402d01541d003000c0743d0281460f43e0001c0010700c000c1d1145030907a0311107503041d036000d40c407140400d11103020803628070039044007445209000107400c032288400e1869a0301c000c00070130030902d40405120080c400c00d0b01c00303030140e400f032240500c803035201ba0720047d0710325052015100154210fa40345081d00c80c0560300360900307a1281d1000d00414008038a04c0d0714140c411401026003110014564005010395100c030300616541300000382c0546d008200d01c00d51807014071810001c8504180c00040100c0b118002030313072148a5103008250347c110441403c207c0c9034412841009998031982004058a4010000c0320403500801400c0601d0702c0c20405035016208844445181c01d110460003826114140e1010344200310883d008810201e403181c0c13034031402c514006400d04150060000c6080a9025480515a0300020505414a0040312140c501491080b01030720b280c0b29404061505a024001c855040d54100c000c04102000700180100354485042c1401c5040c = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 96037059 1250 96035809 96035837
    0x507030e030c0a030506040507050a0302011211040e0406140601020706120b0f030a03121401180c0c1401021c02070b060111151314010c02032709090d12050103080910 73
    0x200c3c420355004403540c2e4040360500c070400009015000140505407000f003083c601d5500004d02e40996a1051251141d480c1d0f0008074840b0b01e0070480d4050b10803001b090b9240e0030241b41600040040898408040100e403020841640c404600342c07040b2009517640a01403040e1400080003485500380c000d51208054070440140c0d20180010700c00c143c00307070305c40a5004002d524600e082c0c501c0c00f41c8120b18901c02d0001400681100000c1c40e400e04056900065071001908043e107a00c06071843c040e051643d05564100b20300380540050100c003d201700105170048045d01604213900540d1001082140400c0000b0880d510541086070026584000c544600da00107094401c610420340b050641c1401922a0b9800c0c00b0ba1050b0554452120314005c0042840f07011000351203026080c4c0e0f03006080750307150003072090209a507070b41036400f10000c01d00c03049801c0c0425520340c2c8816220b40c00c404200ca018020340700b02c0305845014101d83c1c00010003850a031040742000701d10510504040c061007402108084 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 96038309 1250 96037059 96037069
    0x20a02010b0901031406160804030c030e130203011d0c04140303040b07120e010e0108060103110d060b0a030e0d0c0f0804080f010504051218060307090e07021f05070507030e030c 78
    0x10085000d020302c1c4081d00101305c025401c04c0f0008007156401c42000802c8072103582c0c0009502d90040c1c15140c82900f03e0018501101d0b40070b00440e90075881101200907a009182560065041f070345029400901c0d212040a200c030701310000c07503800c2045901400200304005801541c031002c480010242c902d402d88a0b0b0141c1c45680020700150b0700b00c2a14032820030340641004082d41d400700d0900b40a001101c640000070828070000704402d040540350f0980c0d0381c2420442007074440303102c0514014850b4507201c00210209070011110744001134113088200b0050702022600307030074402c001c0c0e480000d02c00e030362344819501308031104044660040030000042c180005201107000302d594800080382c2c07403c140c1485450090b0f03c3d026020903000400019620100200300081800360a9035040c0e04c0359581c0e0f00c242c8003543ca40d4080d41c4600786200030007032066808902c070503c807010301110a104441c4003411204586040707070b0301d0740031a90811000700840d0041d900c440b280c4500900312807040c80c036070010907 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 96039559 1250 96038309 96038311
    0x10050c0d020a120503010e060d050304090903080f0709030201120513021206100b2712190525170106031b050f030f0304120501021614010e1f020a02010b09 68
    0x300041c1c00011550040154500344600c0c110194a807441c10342d4140945205050005025584141e01104120041083c18070959000300000c0078100401486410054915582217440081103103024000032010b0b400780e46040c042d03e8040c1e403100042f01422180c03100514028100c3c0e0250100001541c00503543c508034072811615050290446040190361191050304a070001d10514406214021013000980d1680c0300407040303206002c400345442004900a043c0c556600205401003807035290500c0c2420100b034440d58800c600311600380c9410045002c4414800c01d00b0032559000c0714041000380c4180300103044650418000146e010307901e59481c90002d0702001100c1118240e00c0023046645000307010045c0060b4150044d01440c1c0d035001321a5200e2199008001d10000061402c8007400401d6040e120700702c4500c0e403a240078500354100004180102058a0404e6007094000108003201180745644108500605800c0d030038030010355406074114414060440d076840e242210146c0e034903207102d = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 96040809 1250 96039559 96039583
    0x304050a0305131a1b0109020102101e0e0109020a090b010203120c19030e10060302030703080304170d05061003090f0206030a11130609120b071d0904060515030f0a0210050c 76
    0x5150381e5017076140c58032480308860b04c40c565039901d0121104050303600481c0c3c4054036142038500142460208111140d10b6400d0482c031800946040c11030b29800005500598070345000316040d0300300316603898950080c0d5010035002401a042402040750401c103c90215401c42c6401e040c4504107242c00e2850780301500ca01c020a00041e0322515402c00c0000d00303002030707203e685580c801809064110b401080d500c014901c4014419840040090140030101c4403440841500c0303011241d60b6194481810080c20003920b80714403c44140342e11900880c020311954034103661141e41598920681c1d0204407483e0001400e8803840ea8841400b61810004100281910406081c0200b03856081a070003c1c081d540c944c00504007503105d0001400400c007070205150380300500b0702d09101610018004050940350b2043c07036a030064181c5041c44108070305a00071510170451514800c111426001c00c240e40c0301d828500ea868035401980310103004d400d150b02e00300b40642540c10070724076003403601802c2454960080340d1 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 96042059 1250 96040809 96040859
    0x807020f0d0501061716031104060f09050703140402031009060f0603060e0d0f140906120c1b1b130b030d05030403080a0b06040501030b13060603020405030609030304050a030513 78
    0xd010f54013042c1d201c905d285a161000300140c4075600f00140c4000c4042c00081c1c202424240b082c10745645035081807014180624a00c641c0a544a810324090003081c0e9554000c80c1c207041c40403140f52078900145102d03070740060091540389a51807a40000b0002d00009441060300c410800020306140e0050a000754800c01d00010f080c240b01145034200030742c1903150001c000c201505101c0c0c0c141c4c000306001246641c0001956190107900004030203100e42c2c800002d80750a05402c21501c01d2410014080c02e18060300e03407001d10340744000c00584900360854038031a000d660801c00c44041c04c0c6408072088003d004c4100040d550f5401c03001928181007114990002030b0000304010815503c281d81a82008030741c002030250320903c00001e41c4901542c0100c50426a8481416209613070307240f00c0361154100403104220030394550741c004001c0e60050052501a101d0340c40400da0b500000000c0341d10503500301006d440551860340c0c003282c040d804002400c50b00c10210300081920a03804900341006506104 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 96043165 1106 96042059 96042071
    0xa150c0c06031a01020c1f14070c060f030501080a030f1710060e031504020d080f0406180501080f06090a020d050414010608030301120807020f0d0501 66
    0x40003030300c011400100051400e07016400328030040c2440e01070b441c40c01c00c3d07480166030751209030500507000760310b021441000b01440c898030350b1030707c0f02880e0041e291190052800050381050318180c81c0c03040710307107000c020b441d0b044040915102e1481c2800c0c4060740c900340c1c980b07480d61380148001d000d200202c001140201d21510004000540d40c40800980c0e0030441106200c540d080d002d8240442c0c18a41d030120075140020710300e2841031180a1600726a40c0300e5092140c24401c1d03120403542030f90f060040200810b4104041d2015051940d105603c040a280c84070075154a1644000d05110720340c402d201c864000882c8407680f1020581e0401c1080d20381d110070038004d00c0ba1981c15a5281e2410307041c0010403030b0000340e142d4040484070007440f907035440c2c2e0000385c1c50784006c1c400c4a6000c1d2542c5400000104481e001d00070142c00140405038590502d400309000c12070084088600d03075502c0c2 = true := by decide +kernel

theorem cover : BRFrame.Cov 95863309 96043165 := by
  have h0 := BRFrame.cov_init 95863309
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 95863309 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 95863309 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 95863309 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 95863309 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 95863309 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 95863309 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 95863309 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 95863309 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 95863309 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 95863309 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 95863309 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 95863309 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 95863309 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 95863309 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 95863309 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 95863309 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 95863309 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 95863309 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 95863309 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 95863309 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 95863309 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 95863309 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 95863309 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 95863309 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 95863309 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 95863309 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 95863309 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 95863309 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 95863309 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 95863309 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 95863309 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 95863309 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 95863309 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 95863309 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 95863309 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 95863309 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 95863309 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 95863309 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 95863309 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 95863309 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 95863309 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 95863309 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 95863309 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 95863309 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 95863309 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 95863309 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 95863309 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 95863309 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 95863309 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 95863309 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 95863309 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 95863309 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 95863309 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 95863309 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 95863309 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 95863309 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 95863309 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 95863309 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 95863309 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 95863309 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 95863309 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 95863309 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 95863309 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 95863309 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 95863309 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 95863309 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 95863309 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 95863309 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 95863309 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 95863309 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 95863309 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 95863309 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 95863309 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 95863309 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 95863309 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 95863309 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 95863309 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 95863309 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 95863309 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 95863309 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 95863309 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 95863309 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 95863309 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 95863309 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 95863309 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 95863309 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 95863309 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 95863309 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 95863309 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 95863309 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 95863309 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 95863309 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 95863309 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 95863309 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 95863309 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 95863309 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 95863309 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 95863309 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 95863309 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 95863309 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 95863309 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 95863309 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 95863309 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 95863309 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 95863309 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 95863309 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 95863309 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 95863309 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 95863309 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 95863309 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 95863309 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 95863309 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 95863309 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 95863309 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 95863309 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 95863309 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 95863309 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 95863309 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 95863309 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 95863309 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 95863309 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 95863309 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 95863309 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 95863309 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 95863309 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 95863309 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 95863309 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 95863309 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 95863309 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 95863309 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 95863309 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 95863309 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 95863309 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 95863309 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 95863309 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 95863309 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 95863309 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 95863309 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 95863309 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 95863309 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 95863309 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 95863309 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 95863309 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 95863309 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 95863309 ≤ n) (h2 : n < 96043165) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
