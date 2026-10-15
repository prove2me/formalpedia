-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_5356
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T15:35:58.727613+00:00
-- url     : https://prove2.me/submissions/8c16f9e2-a219-4b72-8ce2-2fb04a508ba3

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 963129496 ≤ n < 963309352 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 963130746 1250 963129496 963129529
    0x20f0403111503011202060712021c0c030e10020309061206130c0c02010f180e25020a03030e0a021e0406050f010c0809031e060709060903080403020907090e010b09 72
    0x80144004018101e022030b4111201a250105c5880942c80401c0303841c010070390302038003604044501107001c0342c021902c4180c41e0380c00c603d001329040d125070080c2c4424a142c00060005009007a01c2025030070241300d80310b030b18806801141c6c00e201ca85d100203011a4485900200840341290074000c1e181411074140300e4840c1408018805503028a400401c042c4003001d029040103034468043d20728600442d4035501c0f40c0c42100148880c07946442207004548025103900c0e2851101c45240e003600615031030465488541580a88040102c5483c103c014024181c09c007074050040c0c1c8007001c01070782c1d082c805d0708449001943c460b000803100e504001c2241c0c4030307900003030280890a081c800305a9103c039030310100b01c0d80080746680360024a4042072070008601d11102d145401c0b002030780b10443c0c000510500c2041d0582d9100346c0c1c25280c0304220f40926152000400d0b041c0180401c3c4018076000c100c440d4071114900c2c0c404c001540d141424803491760b003030744030301100340000400c40c0b010b0814100e59142440c8 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 963131996 1250 963130746 963130759
    0xa1a0d06080114060d06060b031317030f060d060609050115111b0d110a33050324210723040b0d12030203010e0f0405100f060306020f040311 62
    0x5101d403a14081c3c000809040c407558500b070b211410400c040d48128050100e071501c440d01c0345800c070000300c1400c51050381611001c000d003c544010134942d104583c4119424a0b400039191296400e04c10220140102200c90584410000c562004c071441000d0003404480f40ba1117104030108000303850b40500300d41c41c000c031343c20078802e00e1100192001148044c24064400c00680151410003d400d50b80c04048150b00000c03800700002c0b01102840b1000740e07180d510341101d45c0b40000c0f504105424241d0940d01000c40c10030f0001031245450310000080700c10b60301c500004103241c1c610001740c01001d007400030060b00001070307442628008100180b0000c0e20350059001c0600d8880c254001c9034015412400d84640c0e21101d0205564a4800388041e1072a030250340a41540089070020f000ba410901034840e0f40098880003680c0c21100c503c5050046412402610203100e809440801921659802c54256a183c601c0040025014802031100c500e402d84129211410b5150004400d642030f84940c0c800c03407 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 963133246 1250 963131996 963132011
    0x60a05040e120306030a1704050108060d17090d0605040b07031b050316050c0a1406070804031e0908070803070c0e1b130308031e010618060e0a1a0d060801 68
    0x800000c2c1c4a0390810841d048944a40d22100080d2070000150001010001042c90190015515802078815140c003604c48003001c5d658101481032500700d2080140540351012500c00315042840c0050880c40740140204021a031262220004d441066a0449030790f00100c0c10040c0e101d6251180d15009152195804110392001c0300c02000d50001070001c0404846100b4034580081c050001c64075000f50303140c240d880201203400c04c0c0103044441940c1401e940600000604c40d6881202861700c560307030644038559444007181c0360b0111200b01d0550f031801c0c401d651710302080040b000c011a00003403041030000e6980d661145841c14041606074000a080510710741800201c5101d0301d0400d226060704c0a4641d220b02400c2141d006205076640058010640002809003038518854444174010000480c8451a6a00e8104581c44a481414a8103c41948c0c3c000d02c4818441c49851516000041144500e00d0b01c818152004c0005200e4400003d6000641002c00c4404c074080c000040094000820585 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 963134496 1250 963133246 963133271
    0x303060a030308192a0e09010905130b010909030e0d1214090925020615040c09050405130b0c03091002030c0d110d0605040603021f120212060a0504 65
    0x40c0d140c04000c0600c0030020026102c1034180c414030904000c07078003090020310b4120110444042010500303451604a94121070941402800b81e26000000070f00006500d03031a1031850070003010042c1c0036080540c5146402e1001c07403011132059010304a00200041d8a51143c64064801d0703844a20240c090341c00340003503030086102091420590380c0c8a003814031008203869445e607568810300910301d501c0315030b50041c06107401c081c2039003075010300c5607801516503140c0c0140b0607aa01c8808403400f10201811a80b211007a040035000b10950a03600d0800b464050f8072140000c080e194115240807043d101c4001d070102b84000b85000076000441054601d03e5420b00302001900c83c90b803207141481c0c40303400001052150140e03500325801001e0040c0c0401c2074482902c04680c1c1644051449801582800c03400315681c40d2a00c203001c2102e600400061280240d450f1205140400060140903c4280f1044110030429400203090000c441407101440340340100030480010020b410660140e45005400001e2 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 963135746 1250 963134496 963134509
    0xd1704110607140f160b1c11071509020a0b0a08060105031b03131103032a2b0801120f0f210215010b0f030118060306050c1b030306 58
    0x480809484807a502c0c541c030b0030301e041c2d9600c10040265482c450010f0843e030103800407469650b0703220215000240295200381162817401012060600d42c54580c698820400541e03000003c07000110800c2420a51281c0300c1d00e0305002880c1056104a850300c52070001c51a08401400203803001610f45404c126840200401035903005040a06010001001c90312204400b4907500500c00680710113952032404055919071400005c0b4100d40c0508c054100c4070681c0740100c140c40c07500d80440ca500f000504400001080b003501905509028000e01c200741d81c0e800ca800451340d0000c0601c400380215148010030040407014141d00c401314000c401c500301c10008481c04800543d0581080c030003690f146050030002c1600080c0b45100b1040010711940e000d800b5000304809580740c1c1d032101e06c01801e2780c1e6000051118421030b15031130300000c002c000501114050084d12500c400000c4000070b0310a860359549400c45505030f076449049400071070007c2d220003241502d040860700ca180a11305500306080817860 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 963136996 1250 963135746 963135773
    0x1407050903030d0207050a0302010e120702010c1e03020706080f0601092903100302040e0f15070228050c011e0309060e01140603190c050f0102011d0d1704 68
    0x20044002110101940c00b00152541c041d028101156102e0461614690360094458224055400d01c44064028400800d001d058407611041061401c0010360044030345170f003120002c444909001d10484801c04554402e2004a8880d4000b00303034040c145039016005850050100c841407403503a04000139640d00100f8842110903000481030b00f640020402241100200002100c901c004010010b10304584050703407084a0098030f040140e80722550800b611100003995200301980065088240110964001540248984155054013040f00061032041143c0e2007900619400c030600502804424030880811074400d08040d5146501c0d40c62100100e0030b40c90300c0009250f0b44a0940080c880305410250000d61848020050108180460401c410094440c18040e100700300c3e80e19950b02c0300c104003408083c1c1107918029150302c0e280400aa00c0711006440b41155220380c44820102046003800324446032040c09010b2019682c07030f0050280740c0d02c00180b034418825030140300106480400350722 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 963138246 1250 963136996 963137011
    0x2d050328150516020c0f0d03020a0c06210c0207090b04060b03040b0f0105011704021c081b010c0504030f060b19030602032202010e0f120d18050414 65
    0x8160360348100c9480000d680310001520404681c032526009601c40d5100c1c0d031007581003108086285481040890351030840b0300417180c028600301401d07005440c1540071030340181d210b40304491000c4004d9403810074010459200e100441c2c2946800e20f0409445072400d8990403200300100245102031000075511200c501c02c41e07513071a45e00c142091264a40d50000b8001c0c0c02e00d0301e070302c60380c0b420b06103402c1c0c403141e408440b00390b960840ea00011465603c07400d0f056011004d545154442c540361602000305e02c4c0c06c40b010140b50400301d41d050a0010310000007508810120380c03880116100c903014403900391780c03078488954101301c01040b083c0005120200490011038010700c2c002040da0000e0042942480e60031403401321200c0f994000410449541c000f1031160080c81080b59801641921f500001d56001e00028046810364110b4046424a600c1d200d440c18401001c51010480c0d22030f4882c10840329101080018840320a1078900d0101002c1203401018181c5007041851000703010907825200280000 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 963139496 1250 963138246 963138283
    0x30304170d0213090507080106170907030b0411030f06090718200a022b05071b06020a0b06030f0c0d030309060f05010e0a0b060904021605072d0503 65
    0x49100c4521400d440002503010021559050550f03407894200c1c00324403880204500304030004a06901c10314849048401c03940307400001418004070a600780900505a280c0d5104003940000400c0c8c0100f80640203d004483d06850030185205050130b0402012a80516500602c14003405941c0001c4a1003120b00c1c1c820018116041c0c02d05590250000c400c180c42201003000410f0020940200205082400d40c0c084078000799965413005100042c11503030715010117001040e0340c80c5034064401003080303500c81c000d2041c24803d0181503840d02541074002c50011307401000540200402c1e0000260002c00417030042010a0300d01240320381e55004646a00c3c0100c90900c410400c140c043d80007144000cad0700c50024040e070160507000600820092141042c07000585000c40e200451900c40c44c0000e07440035004624100701c0354148000381d03100c3d4050a220580c100c50840204600b1703c0700d03001a1079002c090406042c0d540040040c95100840041030282c44040d0070000e655000410f10345000c49400304 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 963140746 1250 963139496 963139523
    0xf07030210030f0b0306010303031d011b0302070f02041407020f0105040b011403100e01050601120902012307020a080c09070512070f170a0501030c08010603081b0c0303040306020903060a0c02030304 87
    0x401d000c2c1c401c4d1403049400d481600c2c004806c043d0541c0103007103240740c0c1c805080700d0030080c10400e07400e079900c4e5440384896101201a501c05107101cae80040103218007981808000c40a941e000c0f030121004158400f003804082401d1103a01079041c0460300390200058000e02060070241c894914210040c40340c00d41e0b00e601c492044056413004e010301c1a025010680803c40541c10103080c0380603110444030340b070000f540d056074442e20310410f1142186054060303513030b1580030503a40110100c0d0900d034800410025030510200300169265070f80c14000e805004040c00f03482c810b9a060041402014111106120050005a8103c558446003981c0400c607880c5c94809440c0f105403d68002002c102e03107070b00c00540c80082100d000140c0c0c00c19812203208550407041551707100040c900325460ba003c001d0240f007040100003a0040d013170000e401e83c1511942502c1c0d440b910790002a103158082c1c5d1040f5903840e000304440890346414800a64401b100c06824082074100800003516071000600c02002048105103 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 963141996 1250 963140746 963140771
    0x4050607170f0403060c09080307140c0d0503120f0c070602070201030f06061d040e0304090f0b0607050d0e060909130f06050117070902040506041a09040606050c0f0703021003 77
    0x182492808500381540d40c0e41c00c0c000010b008035038000c1c00140c80c9581050a008030161040344500102c80000b0042c41c280b01070396489115006903a0710030703013040c8148000309440d131b078a00d0600d0340a03a201c0d20003180c0d51440410000c4c084500106409028540e0300100a003080b0400229a5070541c48040140e0707402ca076100590052074069a88034085140c610301040c0903401038601062511100e9602500000b160100000e541a0b024010020707081404200f152641c2c0f6044141030844129022640380c0c0200c0101e42c058000500030384550340030000c01000590094200c8540002c103a960300c1c6021500c0b00807525032078000c0c00f640c4040070303561110070501c17400c00707540200d02d82d1044040c021541d5450007418581d01904000645000784800001c50960034822182100e40c05880c0900345458020815160f100041c0740c008252070401c0041c40a6495100b5240503000d1910784c03907101c50200c0c650707038601100c0c02c820b92060740c400c18003840940d60792810b06010365105e24000c20b800b41c8049 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 963143246 1250 963141996 963142013
    0x6031101080c0708040e190b1c111003061e03111c1403090f06030417071506090203010f06050304020f04150518040605060306190f020c100c0f020d0504050607 70
    0x8050075803913003c200030542e404290803140c0140c0031300031a182081c2505011030200c4210b0b0900b150b2000081c5040d62104003d41202d8115038012000d00034900514000324540d42100d03442240060f43d1402d05004100001c00f4071a100800501961070309419990359440840c18a0b40c11849401c0c0341d0501483c4030700b18a140300d0016800fa8180c4e1841444a8016640c0e030880410a8490b141509107011a41050002d480c0704e079801c007201c144040350f19200d10565a01240c0c1c1036504020241c038503611035406000b07410007014174000060340ca40c50700c41d0800318401d05401001c2001400c1040c080580c0d00d4038021201514100c40c0000c0f032070b1340c000e0310184107015907018942002495260070090b542c13280703e41d031095004450500c01c583d200c008264072220100e407d845103c0b80381c03000040d5000381c0d52102d45012450400140303446642ea5441c1e1174100c94411101341c646c2c8901c00c0f0020264006101002280640010403030140c1c01c0001403c1c1c1c1c041c50140c14080c142c003081a809110f07405 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 963144496 1250 963143246 963143257
    0xf0a110604150e012c04020f16050a05100c17060102010204090f05040204061e030602090a0e04140f01180303180204020f07050105060a24020a05030412030e0406031101080c 76
    0x782d400000d03000035890302503d6051091000341c041541020b40b84200074245005200103c481300804d9a084940c00c1000000d402104821642030418081086040050030340401d040340200c00811000d44c961500034a480c601a00d00185a8240f520300e02c1a140c00a0020040400e1070440c1c2241d039a80700c00407402801181e000350011400d0160009501d000da80c8028011402a1800d201c1346882d4641e05503110300340418800090a1030300c042020402a070301070401c440c070080a8040f4107a9a1802e49060798050b00c042d5079200101c008080982820424411485981c4001780700e40081c8402425202803081ea010b4240364640c41c0088503035141c11025810705174010310441d107420003a150a032054003d000212425840c3c100421502d1030b0103454101101c2000c01110710664024003812160000b05003440d056200c0c498200001440910240c4060114540d00301c46403211820020100800c50940078052442c0c90340a001003043c4c640310045114081c207003ea201d842d41c3d80051603d1081 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 963145746 1250 963144496 963144509
    0x1091b0e040e0a05061e010f0e0106050706020c1203070f09231212190c02090402060c01022b061a0a03020a02120310321e030a060b01020d020f0a110604 67
    0x42c2d108011b2421a41d85943d0315044d05100c8403186680ca40c4414240d102c0c403802040c48500198004020151241e0f0061184920400000d8142100c2c070440c649841440886800031102c040100110250300000360b980280c00361030042d00300c0b850403120800d0202c0d0680704c04004000048218110748400c0707110a01c109401c01143c80b40c4d402d412200401d40c20082451452102280c0040e210901ca9809940402c0e00148130904507201d640c204541507116003a0800300d95001e0156620303080095615401b540a540c115a0045a0701d601035002c584952f005602510709203403080108100310025138030060001e00700183d0700c0b5060074040c1e20304234411201802100c0004200030050700c5041d0a1800c840440c1d00b8449607a0740c0c40d120b401e0001148902900500704080054450720f043d82c507050341120001100700a0308042c102180c1040c040700020340c0e0701502c4450361840e0356130401414500d54102c0c07000c1e02500030003d1000b134a803810030801401290480d005000c0365502c0800f190014401d = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 963146996 1250 963145746 963145753
    0x329040f14100e010512100c0306030f030206010e18060103080a05070219091109060a2d030e160e150a05060a081503061b03190203090601091b0e040e0a05 68
    0x10900e260351104499805407441460343d090001415050105000c01020060800f411100f5001c0c0c00c0c4200409114280e0010151243e10000c046400034901c4c11180d40281d014165540c1000c40c1e4040d17005019144807246084110321106420011400c607054030ba100c11141c2d80c40c2c2107400c04582a02551101a40c0000303d5040d1201013403c200103001200c031000c0d814044201d003180e00385554010017409a4200c2010080411068451238840c0019050312801040700a80300083d4980e0721102400600070035500c940c552111141041508040500e440000300f080307082000020300070001070003080d441c001c28840107640e81d036201e1030b800243c10003801d01a150b43e030500c0300504029090b04c16034030264041000c41030750b040109082d413055000f0381c3c1c42803104021080c449015880104902246005414203021142e280d000842c046c1c13101d90000c0c00c0c694100602c1000310f655200c250f120426902220150490700300460b65070780b4100b140e00007000c2c010001d15600b003681c031480082c403600 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 963148246 1250 963146996 963147001
    0x524060f0915030708070309110105130f090b030c2709010207020d1a0a05010f05011206080f0715032901051b030a0e0102030306090f0c130303020d0329040f14 70
    0x1a9020b010714030881c4a95180852030300c440748243c046034600e0b00054581d840c46505480e0650051004103819414403201c088a190784643c440d500b401c07250080c03070005494200090b458501003050200d050300446683c0c20006542914480307540f22346a03070068804403000080c2084c1020340c107407005580c001e0100b1008483c98546014007180015600d0b511422510100d000900c0c0d0381701e000d060341c0800690040e0b007400c0a005660100b080c4503603800140e142d281c045000c66060200c860400d20700001012024100325030408401c059401503003c25240c82d12142000c0200701d40b0007030029003c0926504110304000484e0240306004030300000c40b40404900c022180c00100070282d030300c03481d43ea00d005071070403070300480e2a4403042d00c03526406812080419240b52026180b10b40154028000f940b5004c0c868a600c20401104d90042e0096080b0703442c20b030501d6401d4025107000d050050024000b41d120003081140c80d00100c9982e6014a40e18841c980c0040480d52180fa60a01030000030a60703071 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 963149496 1250 963148246 963148279
    0x909070c0c060207030b010e0603060a380108250302090109030506071709010e0a2009040b0702060f130609080f0c070315020a05161b0305010b01030524060f09 70
    0x14130981c0700881d074030300c0d00e8000051942c22440d813150044030010060204d5840c1ca100743c1016002500300105c0b00583c2001820020310400c551410900c4c02070400b20f00741071082c00240900c4002000d110b8030610201000e441c0b07040c084d18518000c41c0c00d00700140c807030001e00b004840c210082c1d0001400d511942042c800016008550120001099600382032655242550344e0b00b81d403001030104040d9801200d5141c00207145e0302c40c0c01e0640104d5050002c9074090031001131000a41582c069071183d040c90203004106506004040e444001c0b078820b802542404261130903500d0041c0c402a01f007a944505210800981d601255126041081c00320b407501c0e0840300e407944984080c4000c07103000484044ca4020b5500ba07000384c0320301e00c1440c0c980c41c0c28400905140341d01c149400808446136104d500314484840000d85207440a5802071000240e00484800054101c8401030002e0580c1031500800102c6002124108051280140c1d43c181d2600340b03848682d0014012920025400441d895000036030 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 963150746 1250 963149496 963149503
    0x6041e1704140a080d0207031511210601020a03050d020d060521061f0b16020d030f02061302060a0f0e0303040b033903070c05010e0f070e0108030909070c0c0602 71
    0x511000c0f645842c500c2c0c0e0f59039403c0d594885213000c4401580010a080001c50006825900090694500400e020401d0801c50f142648050341410040c08001d00365003d203101024400e500517000e0000f040382086644018000b4043d88014039840d40d00014038034003605042c1c11041c01004080d01c0d01c82201006030608840c42c14800c05e1486d18413a541c0014254181c0c0d106480c8000048480705102904251121a40d0703481086401c0d90300950a00300c1005880c0e4185500426010742e484070400406180c0090401c1c20140c0031440260170b551943d00981c2d00c90040b03504038640c50400d189299001032040d1032203945a00203681c107000101d40020000d64000045110341da251009005d00442031400301081852058988603048510f01122206010b240003140c1119003428208011016542c0301c6003912041c00c00000d07140c010002080309183c0c200002380c007500004961291640c103221404d6030b2070090010b214444c6c0080404640c0e00390142d408502443c0d003000802d00c01d261036040c081d6030b = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 963151996 1250 963150746 963150779
    0x30c0c060106110d0e0a0311030f0a0303020310150f1107080a050f010c08041a1b03130c080c060d051f060e01020c1e09060a0f120203010b0306041e1704 67
    0x1036500440f0719100701c01d0f215141c6105407250081145948504540310700c8141e03400e01d41e80c650540300384512b00491400412410002500c6682d0240e070301e15140000511002d02640260085801030752186000c1da00846848a4442c1914118000a14803041d5034500641540721560500501d802380050180226800c8445c180f028000d1028840c58241120034010403a0060038040d004004682001d00041f2140e400c650403502210744000e51004150050b401a2a140c05000401c2c511008002070b204441c0e00809108015250268a03400414050701c9808682120a55160001030028891005007400710074251710f81e091164a5a4010f0540c00005040310302600c154000340d025860803482d1a8001c0f8050b80d24000e90b41d42600c1404041c002c0648150307404246580c01044900302e0141e40801004010560425080240181401c5440c070982c1d05010750058010000030481a42c2c3d40c071513068000781d44900008060800e1544001035180f031041401e0000381c001101e050b050340706007 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 963153246 1250 963151996 963152027
    0xc090406031b0807050114031005060f130504020f160206041707210320010f0e010f18081e0c030307030506031509070605070f0c0f0303080a060509010b030c0c060106 73
    0x241c2c254032168040e581d44554842e03680020380c907000d00d1300a60044809903030811868441055080d407910000340c010f401c41c803020303924880c011644103000d4803c800c00c5c000504058504510740702c5180b003211207278894002d59072043c2004045800440d110401180c0080080c0d80c80d048a03030b010101c50640710041c0740300c3c418809400e032401c09841e0750301c4020350301c903145c0c50b494030480c071190fa0011442d04090408120400d543c1c03225507009a130802d000e0808a411032900005d081002411640b08031241c10600319005103007044400001082401114903412541c003da400b11500d04030214810b01c9002d00d00c0070207001c003000b030000041c1c041d0000d034000c400480903285c0003901c0180564420300c0c101c4154040303900c48401089858080c900408996021b45050441c420f0b142d1100d00014060780d00c5031001d03441d0364404105059000c0000342e0011024681400710b02c1ca02030002d0714209041c080c840c810b40001002c10a4505440102d9a00d103074107506803000c07580d4030030024200705840c80500 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 963154496 1250 963153246 963153293
    0x10061e020c0411210601051c0b0a0e071b05030a11281110230c0a05030301050a1706150109080d0f0f030c0c1101030905060903180a030302060a050c09040603 69
    0x2204c402030944d42d8140f180c0d2040c2e4401c1d04240c03505003950220074401c10a080d80c0340c0d0b10200c0751070760388402e007103d006031208081864142c00c10440082100040c50302406282650419020004a001c0111031044806280c081d00c0c070144182068109080408100c1c41e5009103003114140e4010035494000c00c5c0c0c0602d90000d0b03070083e44801e11130000301d070b00d040000040c080120340128001e5007a05a40b200044070b10941880d0300708040e1843c040c691a815070381607101000402c150f1070301c01d4915020707041d441045d40050035145001640e509001d003403100b640841c2c0c0c24008080c0d02c07039000e00008296503070407206161080303000a0b03e205900620311002400702e01c07840c501c2c68000e006103038041850b40d4850500714030545440c0e00044410ba109070415880d0b0345214081801005400e019803001d00c0034540d940e214810100108030f000d0000b5004075040b50040000c6900803865583c0302e800340c04003003042e5981014003080b901c200100581d00900e001c4020051061502d882c01c18151160403e = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 963155746 1250 963154496 963154537
    0xe06041e2105160c1805010e0f040501061e0305010509030f1912021204020a0902032712041502190b06010804050a08030a0b090609012103030906111210061e020c0411 73
    0x40300280c41c024084c1100c809105030205022940d0102214ae10038010000000c901d5154004800002741103400c0c0e04040345040801d0062000c284111078108841c080214505411001244900d015552004a4031428504221a510b0044191807060303000b08508666442654624a8260006403400c2c0d016000b004c1c80030800541e5403027241d0050141000c00380502c4881e00140c200c0410740382c03400d101405001080303180b100c242400350001c0d1412101e6410001e03d0404003c3c0380100c1c1da8250440c90264800600104142001058001c00c081c6030401141c0c0c0c40f8186685045284000240910310000c10001003504550202c0480c4000312400302154680f8400c100400d0002c1c052101300c0070555035600710f43c19460540b14040c1e8424100440c1100c1c25072500c00445003401804601e11074002802c2c5003078007454030483e51090706401d44400086c10b0940040c0900611180100c0c4142d1381000b42010718001c018200d0031361030051052003c02080345c20700045400642c02c1a0b07810191845 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 963156996 1250 963155746 963155789
    0x1704061e0306230f130606111b1e0904080301090f0b0f041508060a0621030f1b0512040303140a2a05010e06041e2105160c 54
    0x8000032110031101000c0000c8014025481c580324641c03d55500c003011032103611440e12100d1140c2074101d41d15034005002d6280903400f61140380c00180011280c1c001003401218407000d5080d850204034299003240903c2c4010b80815100c0003d0110a5171101d1501c00b00800c100e10000298140c901c502d8043c043d15103440b8a40090325050001c1690010b1442602c081d02e040c10340c000b940758080d1a0f8000c014607541d610507814170505440c480da10301d8546a00b4400c40307580e9185811000c04801d0085a00007440e20014903454103c2c10b9a07003000f6050307600d0040b0000f240403040c070060f044026280c0010140b241c1480d1503000d84011000f081d403003807501246650780400d441c08035203252188102910381c0040c115a40d4484102c0384021041144550301140003481206e85901d88180204104d007068104444880420081202001c81018030000000e18043d041141c8450030305184007641441c802c2964503024071074102e09401402c1c0c0c252020720840d010341c0c1c01110710409014510061600 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 963158246 1250 963156996 963157001
    0x1d010c2f0616080307091214061b0313050309101806090b040e061c1209051504030605041a1009060617040f061104062001020307080705071704061e03 66
    0x3810b12159031100c1c0b45060114402d03100071070744040186070405001d40c43e4048000c510a0728081940c0c00e00514021502d810820441c0b10341160718102c41ea01c900340000200d5405200c014010805007007503505510130001c0420036507918040060407840aa01c2108004114000d10392910441064001c400124036019040c1c040a4840350000341d45814100320180c40380d1240503080c2c03500716005034400d00704207103c5164030003240d105100400c440e440540000b802e0304801c0c0c102030310902c081030a07021000204821242103a40c001e4000c01c81c1d80d80c5040000c02c0d01c11403203601c03408403403607000c00c8040e105514194095030320420781002101d8513204215840d0003500c028403c4600600b000c90042038401e1842c0e07a0701d604c56480401c1105401c1c140010581041c0d000d030002c40d01c54441d07014100c40701e40e4080140c03003014000f1810351802200c0140004005403000d41403140c0054541c040c4000407071f140e0348412030380d090180e84540d510001001c21310711240e01008400402904a0164802d0 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 963159496 1250 963158246 963158257
    0x2b02090a05040819020c1e01031a011e0306050604080705010212090a030f022d0f37120510140f070f11070305070302040b09071d010c2f06 61
    0x42e400382401211310354812901d5004040000b5031291b21600e500d130303a8521044180a4143d0084030100c03010440001d000e480a06041c000e1815508803c140541d900c0b00c0386c041d07078030805503040300620754040d41507006120701d800054210308009004940107500040c4441100c0080c0d08a0b01d80301c08440c4100380702d025900c900e541c4046517000030004545904155000307280020660340300d2000c0408800301140390024050f000348408400301d826482c14020700d0b1064a026101e410200c1d104410804211800101040401684825407000e134001c084400000c0d0800b04070032401000d0380d040080d60313902d644151203420f900b884810300c00d06c1c080c0300c0581d000b011041c0000c001a11242001c0d103034041c003000e10004002c948030031101d40c55401c02c5480b000b5401800940300711070460044c441a9581c1c041d10350b01821550040c03100059200aa04000501d042000208120300b480101d480b11006032000c1d0540d00e216801d010078079210390303a8110300410360000c2e2018200100510019001d40d = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 963160746 1250 963159496 963159503
    0xf090a0f031e06230603061f120305070206040803091903050319230903011a0112020a020c0d06020909010e24030a0b010602030301210c050f2b02090a0504 68
    0x202c00c0115a603012a0aa00c1c510034071450000c20ba041c051009030b103407010015115100d00794044148800743c142400019003080000150440c0b560500c0e9000449210030320890744500741c503a8149051602c43c0b400c0d02e2109500600c003e5a0f55540c0700e00315034903000769020520400110292036401101c0003c0103044980c4400618240481c0e6120380d48840765404d00201070240007503a40c044900d040c1c09104405400c900c000380c6800c4170501385402c54100e03401c614540a00c69400c8500c50717030001503420042d12003940159407070450000c100c0c28900f405030b4054002440c00c017900100451034020388042941501c01e4501c1c0da036144000d0310415020703200380004c81d0082c2041202c000c0b24240309041d00d03c024049820507001640c07410110b41d4260702c004016040070006002e0140009440b00b0341700349031540c00d61070641c50789804148040a100384c5110350113612000900d6141c5441460121640401c2c00100000d00319024981b42c0d812542284602200000a0b80d226000e200e010b025542 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 963161996 1250 963160746 963160763
    0x182e0213240c0230030d0f1a060a02150f07030b150a050c01060b07030206040201230f0a02100f0c0207080601030b0a0b06041505070b010b03130b0c0904020f090a0f03 73
    0x82d80900c0f50703504181038a0f80a00070102e41320f020000181a0a5406150803001980c0e02c280000e01c8200b00c82c07100c0b1518401d07a0804403030352900303150441c0700f260000c011910745507101c484101c1640303400310300e14a900c94600d01000300006500007007181171080013a52024013003081c5071420480d2801108089060603081402440ca5551045c0058010148120000588582c5444650955801c08941213005a020400708070440d40d01201ea42c644c404408400354076450f00384160390081c0103201000b044200e000c540b680314035100304500d403840643d0070820403500d522224118041c110050848000d84070f4000002411040000d00394100c0e500041000e049444928405000d4100210308943c8103500f40b0010540201031042e120f085c0c40e081c0c0340c041d9609850f28100c44401c10581c40b40d0400395081c42004849420007800b00310303541c0d010907007160079591a00c0304901402041d00e00c0b50050310204004c0b0402042c40b0060031519411101452b40f60340e12010201c1c5a68a804021701101 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 963163246 1250 963161996 963162017
    0x90501021c14070803090a140615040b04091b0302011d06030a1812120b01170f0901061e170c0105040603020901030b0405040f0b182e021324 62
    0x203108000c8041061031001d88585051095210700c02c1540081c1c61610706c9030002c0105400b00000c00341034050000c2c00300007805441c0b83c0f40c1140048141d00803001c03405640c8509a11465960b00c0d4000240e0580c00300c600e200303d40e901468000801c0c0e80340001c9010400c0d8070003400e00d2185100e0b101d5131100004085610710b558801803179002d00201c81428215500b68108600003034641f47da524440041e0350f0312050903034201f559403405c0da500400907506000c602c1c0250b411220300d8108150748076250140d02c150944848407610700415140c1c0c044807011000800010f40000210041e2040351046003100b0190002240413584035000034900c0f0340414410401003200c1402500900001c040506000488501910110301a0341e01260201c0e100282c2e8000c50080040304046542c1000441c058250311900c0c01d02010780e103418400c01d281c0242d250141344900705003440c00040e00c40c11881415910396640d41c4c00c0225654050003030605600898882035200c4552098851543d440c40e0354031a4507a = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 963164496 1250 963163246 963163303
    0x605090a140718050d170f0310090204140910030c18201e0408060c09040e12090402070f060c2604030210020c1015050a0905010e0103060e030c0f0d09050102 69
    0x103c0c005d200449107420050344420300300d4000c00140c40c2468003829101d17903c1c50200780000c461503c0707400508246105020074004001050000000d144060ba4500055120320407c0d100f0b00c0d0981c0c0c0010041c403d46000030a040810300c0702900d844610480510036822900043c030041264155626507101043c0081594094100403003140150481d4540e0f00d0030f510b42e40e01500300030b403c65200701c0c41c040c0000d80c10814201440740300d2001d01e440c1c025003040e03108651485894400d400c6618420f0b6000300b050b1050160303010010025582c0480c0400105001c3d05002e80038a5511241e6402107050304002c880981840c0340482c41707070343d150707018110030103c00c10114000d401822034200ca44c0b04882c0e488003412858480d102d44a1420015040b0161804041210b80155600030101003810718004220342c41403d200300381580d5001c5404a6026180e1440b24a9402404141543c3c0d110b924112444d50f607022510b0000d151440c1d50707281a80d6154401a40c4e5041111440c6100080c1c0241581c20b5 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 963165746 1250 963164496 963164509
    0x170c33030618060d050a030905011403060901051521060307051005091e0d0c090e03041d04050a0f080d18020d030e120d020102040503070807031e0201030605090a14071805 75
    0x30100400d0313001c20540c05d8a8151420071001c40444c080b4100d00000d21466030403400d454170405038044000d29510303003a408905444d1061003020b001e03d81080b8400700360302040c030aa40640303444410481c101d00e2411070ba8075040e02e05858450180c06545004202820070341c28903a0740c8042522550700d040000418040b040c11040b000f594032070385c6506036070a541c4c0c41c01c14102d4014001e4003500f54540c20600b12200311208030451401c43d50082008104a0003211400c149010240118171072943e03447c20040d04021440310000c0c10703803103191101420012510090403803035400c400100105204503c5040180f408003c0c007a5001254070300ea040007074400c01c40700600140260200c900c40074030360359862a02e46040105400b61b50049400c1c40380c4e040802c2404018010000240300491030340c0c592151168116070041c0368086110801c0096902a40209008141c0030b084c080740351500031b009000070f00400b510010746040c2d60780803440b01882100c48508862108184059840c074080c00c2004 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 963166996 1250 963165746 963165751
    0x70b04110a0e0f070f020123090118030504060e01020106031109060111010c11010516090b0a0c0c1205061e0a0903020f060717070903030207170c33030618 68
    0x41c0a0a0000701064039605100028050745281c50a098107040c06403000e0300c1d0243c0c0349002400c40e854020380704031070550b550403401c0185007039120240c640c03190b042c4d1034090414010b6010902c44500740c0c910415a010b001803086a6480d911600c400f0940c00049080c0c3d00284030240000f44000e100c0707165840c20516160300014141064020b612410151070709460786a40c81c50301080600001e413030503c00030300840360b115001d01041419508068405421000103024495515001047e19400c1c3c03801010b801102540015107400480d94403203882d01300200310310040f5145c0c0a008040f5428003a419108001c1d01e42001482c0d0081e5250001c1800504800c04281d08604c101614843d4951043c01010700521603580c94000700080d41158400010300601114100071041d0002c0003c240e01180b00c0c070507134107075a60f42c10281c8285c0407524a0b0583d0450140c0c0d125004284c21201c80000008c00c01c41d64103104900030710700d120079806da6070502040341c00d503802c046001859007020422a0402d076 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 963168246 1250 963166996 963166999
    0x11011103070e010e090109050901060512060a05180616170402010f18050405160f0c0b0a110705030307030b011e0512040f05030f030a0f05060d0308040602040819110303070b0411 78
    0xf00350313000d89030004260180a07400214966521800e0100020082c05a04098801580d00c4111030f07a000c0701042d0344640c01007410352000e5540c0081590a809011400089415541100d0560510180c2d5000008280f42d610b80070410310f0110750514054441218443d130380507103a80754603520880040e030305160450503031404c40403203140204107661240301d05406503101d150745144510201c40c0203009440340d210f01000303000b001d00c0800f000a080340e09596100b01c030030300c0118141220030010a218010740070010f14900010042101c01503160b800060b80e89826a80c054070b004100d1b010803203e440b070595050024404101100c040c5180320070b090b800900c42e80e1182e501c58080d4481c03a09580003130119100c4800d0000502006007054041c488039929460810001414140001840030303103071800080521400c2e60002c2c09002c25541903c0c018600c5d20191410511719010342c000204200c0c10403140b054585542d000507047c00401c0e510241c0d44400410b056481f0740c4c540100340d501808110307 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 963169496 1250 963168246 963168257
    0x9010b0706050a150f05030f07180b061c0b010816090b090a050a03030c06050f0c0a0f021606030903110a03051b1014070e04090305031b190203040611011103070e01 72
    0x4034013105180c80c44100510365544078584aa00b007508160520416240d40502c2d42d0140701c061240740951880c103034200480c6180000d5042c4400c01144c503602a82c003080100d101c40d4512150f000300140c000c185602426a00c0703c0c05991648802c40444103100c0d03103c800608190014005034235901c000300788401000300200f11341e035510000140321507140d42044000a0056408104000e034501410b5001100455151107525200007205024040c241000e0704000310f1600c119040c900a110f0030034510000502c0d1070f155078a410000d0081c0c20740303d07411000591400142d211403100800c82da03007240e50564079607103019001180081c03204004500f40303000d4000e01308180d40305080da12406034500301000c0d1045062501c80f402901c1e00800201050003903040034402800207503c601241c1e8403030507580ca2000150381841a00d800d5010b0030603441c241e000c00d40d04500601d0303000400303081110260351362240780080cad400307a0300d080e16600bc1060103009024008123003614000c5003803102c035002c1172601 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 963170746 1250 963169496 963169511
    0x501060e0a06150912030c23010203010825060320210a150608070c301803030f1e03050105030c03030f27030a030e09010509010b0706050a 61
    0x20400c14842500d254140035500e038010070009014506411009015050a00c4050b01c2e202d00c020b115806410014100038000c400c9904200c1840140e074445955009510060b51018110724000d5200b0700030140c0c0c0344944030059280804040d01e18a11018001617031b0003551810f4026405018942c0f4013a080720310030800f0848002200b00501810704010115038103040c0300340b6a60020b03100c0a0110401103060881342604480c422000e9070032190381d441c0916040d540e850301100d003a0009900109a2488400441e102c4e4404017202c007844214000101410002840b054858442d200d000b000b6107c006134080012034081c00c450004486182021018620302e00c00c880c4581c1011010f000219507a5001442942400c00204030100c400707400462608000085031301d02402880d0103140c0e01c5004c0340c05200074200450910501c0b0b04050100c075020750a51402810401c0c00302180360191003400300002d80ba00d005449941240d030060f0205103010441e4403a0009010010804003199031a407a0 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 963171996 1250 963170746 963170759
    0x414010323070810060c0b0a020c07030f02090a050f15191e0609081504110301061d06040c080c13051f1d090705071106030c03160201050412030207050106 68
    0x1022060240c2601c1610010310307103402e01405803103001c0c202040c0d1150104081c07080781e412a0301c000c105038109070640040d90b0f855049201070b125085200d60513000705580001040404050f03441c2d00c41c03003129424010780d9131040c1c80089030001c8840c02008d020600c082080c50210440c40c3c0e1b400d0001501040d0b103c480c070340040281040903808010406c50000d001c9400300c5003000a5006407031345140400c4594605010665510040401e45e41a03061f1480400c08001000207130186042d0094000d100e101d50b05d06a0011070b82c115988210400451800640580b0701441603140e2001a5200c862031074039012141c1d80c40750400d14010b0303056402084c02090b1940c5058003520406442c3c502c0c46003243c90034100030f200b03a2074086100e81040c0031146241c5140c2d80e07001c400390302c0100382c40e0598590744a800c0131042600c18100c82c94200400006000f40d00011000a40c8180e104900364207240141807000c83c01c94104a4016041c0c000702c6082c10610f41c070940040651034003a03c0080b4220361940c8 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 963173246 1250 963171996 963172031
    0x30602040308212703090d0c1a04050306072001050405011e15140a0f090b0406080607020601060806120f0a061803080105010c06021605010b090c070804140103 70
    0x2041991842c10114000544a44020a04043c03481c612226001070501c84800d000081800c001c481d107400c0c07080b0440c180c0310030800030358030000e600030700740b4840500a0401362815441030180380700440108a40380c0c240b041c18421541159006401840d0382c0d030f508441281c1d80c01d0000d96250a501030740300c540e48110b04c01d003da10b0142d80184000100050352030038001c00380f2410750340f040286040081d11140c107030b960500201184c410a5030903c48142080c0018801441500f0480c1d80403512400842c914980d030307004400c440011750f4204210381e2994951039440f802141c84800503404000144811445030411642045002d043d182042d0350180304641000b034050740d031100e01d9111701150014400036008941d6900791040c0110041e800c55140106508030500645040c0a0100428020482c4031380c1103403201600300c20001200c0045203006406418080301e0203210794200b001040d90740c1004011541078079840000030b441e00d490302c0030311003d60221100309410300d9078450100c0c42100045 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 963174496 1250 963173246 963173249
    0x319060302040c1805010e06180f090108060712020403050c040b04020c0f0a061a01201e03030a11040f090b1c0807210c150e07080a060b191e03060204 66
    0x1c4d1542e941c0041c5060110006541c668011410440d10fa070340e440300c80c0c407404101c0e40c02c03081881c3d0403030b016001c442c041580050007844007500101070400009170404041000c034003d4085a0348c0c800f240b00c8400c0264280d0080b40009040b6410001c40a002490b060f480880516070107031001d401d0a20003814181040c822041d0003140b604012046010884070348951021907030850907806c0b0180440000074841c0c1c000404003418074403000003e0074a00b10401908450072080c40d400d48141c080a880c0a480c1e07042601c00b0742459050441061003a880d00c0d0545060310100d0304480c0310790349040c20352000707442041c0400d500100e140a00101c00d00101d1805e0999a0040c0c05403551010680342440b4840c00c0302d42c50a00003510001600c44071980f00320310311003141c1c028050b045426460344150780140b000000d207110a10a042d00041e402c0000f11b041700c10781c0c2c0144410804400304d40e05120000400461071040d0034a40f5000340311244092041a0038044110060003101c4e441756501c60490788103 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 963175746 1250 963174496 963174521
    0xf050f2d010611100c050708031012030507051006060f0e1f0e15030402010c0303022206082a07030f11120d06050409032102120f10120503031906030204 67
    0x1007841116420f02c0400c03a0308800c91140908000e002d440c110014518045d19030f0041c00400000301081c510416080d402c4050078208008040b0a5400d2070007400030390201008031258050b940c0e04007400c124901c118802c469540d1201801c1c105a408129036600540e40200d42c81001100110b140c0366100b041819022010384440300100036180030014400b5590303400e40010f4608008020050740d01940040241d81d04d4107026840c0c480c0d41ea0114800001c0945101050b10343c02d0002071582e03806a869401042051580000ea0648480c640c11015483c103003a040154200440c1001a120710a00c1035003145514002c0d10340036500c10802c2c208200740c400e11010000228646003c0d9009110b003c0040c20100c03000c0100038855503001d48144950310942041e201849800002c1c041603404880c241c2e6100f0740c15120303030705d003401001c81e0442e01a6401c4030f0341450180d0124411000300c0700d0501c1540c0200046003035036102507034204d283c1d52803050f4099840d260080040180c80701d00400600441 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 963176996 1250 963175746 963175757
    0x1b040207150b0111061b0306011707030906050603010e0a021e1c440904110301030606080703170a02120705030316030c0906050c15190f050f2d0106 65
    0x100e10b00040c5590402d103c00209a0454024406441150f021014508034900c11142d00c070703540d8000680340380710b0030841e50340d212041208102c500d65143e448103202c188105000c2065841302c1e4285800c98030f032042c1e6445550321103250a8090b10b002181d45441c643d00541e00f508140c1d401e00843c4c80c4940000369502d03480303000f01c110341c1000000c015642b400030001f000e405e5803018410040b03000c03e1204450024401080c49404280801d890840d080e814026009000e0f003001255070050a500074031040d03d040d0b1507c08080394480b00404c0c0c4104898004070a4040e000c5403480e030300a10707844061001c05500c030f51405403c0c9082c048000e44030f050b008402654881c0340c803006050a8010502000040500e010100141144c020180e841a50b14038a04161aa040c00650900d804002d0150b0005086400f0400062040030710104591004202c01031000f4030035010303c03000782e500039a180c440d0101d08200140100201c0204480c003c0881e180040325040c2c21010f2030300354031007a00440002074 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 963178246 1250 963176996 963177011
    0x90b0f160618061811120a0c1503140615030a020d051302011e0207090f061701020c12042108070f03080714040b030103081e0406030212010509091b04020715 69
    0x100f60f20401d1080240d000d030704000e031010380e035401c0c040f4041580c41d0b51003211402c940c040c2040e410000085016070100e10300303112039200e03000c03020500141417100e000241410300305103a600c8284141401214007421500620381000d00c51881600020010341c20554280a40c40720140d0a0150502881e01c20006c1490342446000040400401c0c0c0d0004010711481c10035004802c0e4002056030480b42201d01c00200e203071404608034040c042c9948240707901000904004002c24040d03009000c2020300b001211111861080952214000c910852043c14002500c1e0716181c6044086690702a00c5501481e250440faa5103221304014851025400207113500c040081592b00604407040b100c00c00748195050503d41500b000240c481400000c0c1940c1300400d10802085410b0000101003034110421900ca64440e04010001e4200c41208200b11030b404000040500741400400e0051011034003078201c2407600c102c0301c0301c420b00030030005420075804c00070b00c07001c10640040868084519100850600b = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 963179496 1250 963178246 963178253
    0x81e0403021503090a0201080a230105190612112205191206020d060b1b060a0b01020307020f010203040909050f1e06010621050103050c03010c090b0f160618 69
    0x40c400d2642c0600030b542081403082d15000010080a0103a09103050320701d503031f1550303128009000d100c81c40300600445034080d110180c0342c540038241178610a4803103411801002250901c2d2403001c3c840c81c00820b0f11800800e0840c80550001003240501c0c0301c1e031519001d01c58248042c2080320050142002d800c0f03080501c058600308007210259051940d9140010303003000c107820201c40b40100010001d640c0003030303803070003201064105000901c0d19a401ca034a428014135809000190040303490440e00031100000e02203400f6100300d80c2481410381c01903041a40a9083c07020b00c1c00c045165506500c418040010070150500801180510442c0605940c10718030340da6510b000c58040e0454171064811403c40d01c9014005082030459100d49031003003605c0300c154502040da410082c107401c6500d06110011040c45400601c4401856055008100b00c003c0b03800300312280071031800b401c91440001c0016003040c030b00c002d000e800205040c902c0134080c5003445e0382d48011a403014a0751501034168032544820f1 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 963180746 1250 963179496 963179509
    0x1306020a021315090b030f2b022806060b0d0c0206010b040627080307080403020f1207180f06030b0405060f0606030103021203071505090d021f0504081e040302 70
    0x102c6400c1030140152540850b44141103007541c014001c0313503a0303100c0d4151401d603001c1240002c2c4001510656000495500b50132404910403414002404040410f4003481840040d01c60181c0403040524074600c4401e05140c40c40c6960300748203403055500c88c6800300c0c00c0d200c50380050081d070284240000744070000c0381d070107400c20030160f104000890080c04104866508481c10803c1e044040c940400098843d40000c40d50b80c0283d001443c00d8880070440380c2c10001304400410a881c000c80f12024015141d0b400c002041410028080c12508550420800385030f201c2000b0044400000001c40c00018a40d246411501c05620075602d01e20325400303100c1400014415942c0100c040b0000904501d0811701241c01844103100c006e00600c1e5040c1400c560b0002030080c1c2e28001d6000301542030b61004440c0d000040e14061790481c145014045000c41201d000203120036546c5440580410702d4508140d40d4401420020401d640300001009926442c507802500022000602c0c00b02c50b803224214014000c2 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 963181996 1250 963180746 963180769
    0xc0105250b16230f090a0906030305031b03070e040e0f0f0703030f0f0c11010917060103030e010e030705040e0c060d24180b0a1805040b0703180f05031306020a02 71
    0x4000d48850b045116a500e8122030f9200740c81d09146596050000100c0c01c03200d8151f00204040341341520100400d544440118000d044003006100c6000240c004a80244003d4807494003040308110f8084040c1001e40000034004415016503003c0d000e01d824147c204920442202ca0980004600780304064005015004030001e5181152a004850340050205502154080c04d011640c510714401b0b680304207407040151049014021640d800c0d81205580c5101c00e00003180860456102c4032000c0d4450251030030111001002020a181b0341010700c0001c1c403010b9404d001d18015018420800e8403454020034110001c241c0000301603090418041c1d864411f140703452803002e88403800b00503000940300c0c131414403a000b6100003954203843c000111804490b0f440880c00760b00c0384109041803440c990016200d14010a02c0c103049695041044044400d00825000d0310f003480145a404561005034004100d0311540c01c5a2400c10076924a001c03503541d1340e01c031000503030086021a0450030004007000 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 963183246 1250 963181996 963182027
    0xf04090302030d05010f0b07060545030f0d0216060e0d0f0e01080708131401060627120614010f03020310050108030a0e061303030206180c0105250b16 66
    0x5450b28101000e030301080c420200044d0000382c4940c041260502501c0040f002042440c07000030b0711000e140d2100403281c160315854644640b801a482c0c001030404400c03940600a050037031403900b4100401003000390444555030300e8000f886510381d8005007103407140207441501c20b001089050450b21000b0b011000e800c100f902080050080c1c08030690b0003441c100e8001045041403e4190b0350000c00203d81c0c400501c01900c0c48101d41c02440c00a2810740c00070007036034070a03a2034900302c0c40300a480c00801c0c00400442008885a90402c001000070790b014240360310702c1850041901003903a040d13a4683c007001c1e0007a40003c00701c08001c2003107103420411485100300d00c5000b40801e61415075196200d0081000d00000d00903500301d651426910032045402a42c0c2036858240150b4a90400070350301c000c21202103c0030049003004100703110000903440c1203940143d42c0c2c0d80c642070000000412841900203803c040c031402c2708030940060182c507042482080ca00300b000004a020303c0c8014501e42094a000 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 963184496 1250 963183246 963183269
    0xc070b0c070f06021b16090c0908030706151d01090608010902010801090b0105090d080a030c231b0a060c0e0a0608060906120d0507030207090204120605060f04090302030d0501 77
    0x2440081e48402220750900c1e00441c1c0141c9404001d89402c600300881845c0d86224006c0e511480d81d0741460800c0325054540d0200100000064081d095a0301500780c010302c0540e0340306208400010306075030011500054003a42d070015460f91030820000d02580141007401c0e0190380d04c0140321100c03041c4502d5008052280090000a40300e0f00042d110b40010f015900340180c0b500f00f410030590140c411221807000140406800013010b040600081c0c20488560340024100102e22054612941401c040c0300803480c10070011913070564030f01c0e046610644800001094031500a14495010f01c0805200d5000d40c0d80425001d00c5400024401c441321a01248078102400c0b0510804e1790045100e50b1000e03090302c00384400d80368040003d034107400138001118184640d40c0c14841c0c1d50340c044040c00c0040c2c829004c41e901c0c02e440300740500c04d0340594018110007140102c2c00b41c001c620207400c11500444054900d034101d40d902c0700420b050b0741e4012029005a400003605944485c0644038050041c900c007000d8 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 963185746 1250 963184496 963184507
    0x6030f09070e0114010f03061412120705060f060105070308191b080403020d08010f0504202d03010608070309060b0310020909150a1707050a0f08100605060301060309050708060c070b0c 81
    0x107600f00d401485c9e200d81c0104491050761f1312a0104011b9601443d0034141e016490300101d15145a590038200d0340d00c0000311510010403020350150041c1d070801941174440508503a1109582417180090142d00380050761940d01c07c24010341d071300c1700740390f019402036458403920b140c98180a85044108040c40e010000c1c0e000041065007051030780401952412140030542c104d2142144d5000c006800109003191800903005200740c07115040d25903801c04800031880c40070611a02c00c20340c0c3c00248a950040341e00c0c180000d40c00c5200e5404030700c4413441880001061f10440380881d2600d40c03100d103801c2105500180d81d02d602e14041d440030380d1081440a8600c170f003807000c1000c118204007600c128280741c2c501c5101c0180c0b800082c04410301521000d0400c1c2c08880c0d90b10b02c203c4980780180b090b000030b4000c00c0d070000c03107520460107100181c4001524084c80d41c1d00c0c10b40d00720010103c03490160341c14014480d01107644201400442d01070003030138808684441e042c0c280090380c1100074160b040907600402a = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 963186996 1250 963185746 963185759
    0x40603051302210c150415020d05090d0812010f08390a0b16140d1e0c060e0f1c140f070206070302060a0507090506030f09070e0114010f0306 62
    0x4803003d50380700d0602c0c404403281082203040e01e4080d1401149038480102e0400742c80c00d041500150080310014103c003003182645010a90711400310201c080300103401041480800c1c1403c00042580c90301c190010340c42d00e0710000b241c10107503000380c0061064100ca0207042001180030082140d1620f00203469050000f5007113906149850124504840510640c80f481c0d203555034a0f20010092400000d4241d464158001c42d00307011040f04021540080072040040062400094400e52580039803902c0e503810084142c03500b8104100c0351200f0030000901d003090002680b500500c008101800020520050842240d030300740820428264000e5116600c0100e00660020214541138081c3c00703941c3e9100c079040ba0a007054410118080d402180025810003050b0340018018441d4403840f600308070a40724840e0888280d030701845525030120b000d1000c00e07012494102030681050151007181d82d103035554008014a980b01340e203c44412040b490903c44256003000d598800c0d83d07603914081084605200 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 963188246 1250 963186996 963187009
    0x170f090d020c06180a05060c03030f010b18041e0c0e0a090507170651040303030b0d0203010507050d201611091518040308040b1b0f040603051302 64
    0x13400741880300b901a40114242c2c07224241d0001401003c0c0c07085694110410722107580b0340c1305a0b02c907541c41130110000240c003400c100540716094180d8824401070b0b01c009040202a249109a5210558a4400d5400b184405d03101b00310704c0c5e0420b0b481e010020000b1031b04001c981806544080c8050b030400f4104004c0c2079100800e43d580304d00078004440780d51a1400890281d114200c0c1d00300786414003001142d0041a00e5820450203c9817003483d802c2c0030100a540140c0440e2440c03d2201c008040c8420b00029019030021901c040e0050030102c030140c1d141c2c001909503071054403c88041540041c0c9000d5010050040c91203140c035a2010090071003008071f07854010b100300704030b4400c0c001d03ca8010710208203500d400d094419030014040b441c13a061002000701e8103141e0190f001e204042140760840b4405940401a1065825807107101c02c5030f0302c517100c0a41c040c20040040d81e24040400d0144400442c0e80003901480e0207404205840710b05001014003180c0015000115120700c5003800001a901c1e01c = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 963189496 1250 963188246 963188257
    0xf0e010506100c1e05030403080c24060609011b0b06030f0a03020705220606180f080d110709090b0402090109140a020f090402030406090215070f12170f090d020c06 72
    0xb598000c680c100f40a620381d0913101076200034500c0c0000640001440f00768006030001d51804419035440755240b00c0100301e647d00603a550402c841101001070b04d1450a480586840d08043c1006000c02030307003c0c2c0601e00400304020448442c1d4803a0700b071100c581030420119040000100c0100228800358502950b507100c180300713051280b01300e0482c0b2071981e610f0000d503000c0d21004c92404c0c026151140070250507900d110340c400600c0c10710110001a040503244424084502d02000380460042c0c034503044070b0040a4200003c02071180400028501c00d2a114000c541405040120303c0c605141c4100302c048001a0b02001c000c50614000e0402c0e02d600240c282c1c0c02181404005070b4444510f81c9802c1c89003d000b42807681310f403001c0204020b01c0b22a03044407165900c04c841490b12607010051000c035500030224003810f658201005a000030754150308886020405051082c0ca24003c1221f0420380302c2e00f294510346203402e0400f80094540c00700320700c00d0301d24101d0000d00801d54100001c01c10f9030040 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 963190746 1250 963189496 963189503
    0x16122025120b060f2d1008010b070203070302060c01200403110108090f1b04050c0301062109020d03050c060105030c0102030909130b090a0c050915010f120f0e010506100c 75
    0x71000c40c0355070340e030542c2c0402d004d00080c05891389a494071054400390140714480690304c644081400116162003001180300c03040a840c0c0b00e81c0399007490b80740769903500144804c03078052259083c01300150303468401034138401103103500124540c040d88002c10400c00d803050101d41e40c1c00040c84140009041880030103000c6900b0300e040c4059944480103a841c00c1d41d006454011801091030741c800b14081c2d000c0c681085c903410b039002e020f9a110303078150344403d100910074440020503040411124181c80300c0ca20000304e090f0400070804101ca134001030200c02044e002100454000190200e481d54203010090041c041100a00201201400080d48170f00c100400039104020070310000c2e03c0503425170041405070303030081c94191043c642001b00f5503644607003000607a60a0005c4d1000078442c43e004c501d8600c9000b8140c03400704000413010054421100c802d089409021b00c01b040e14115200e03502c19081000040c440110704107001c1d41a1908450024118900440c1201c11290005c0c0c1c11880b6203089035072 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 963191996 1250 963190746 963190763
    0x10c080a0b0a030b090d0e030c010e090709150504170c030607030905010e060c220b04061409130b0103060803031e09030c0a0303020703030605061612202512 69
    0x81c000c001552a04a50801401c90300c0c0364092155484000804811006140c0c880f1482c41d0300c881d0405d65641c0a02d200140000d001d0030b01d41d000c034200a0403083d00603500f401e1040d0b2003a20346d0a0550391020740d16060380017a034045020081e040220088862109400015019294000011a0b20780d107004148106140d140d441c400c081020035400104c0c41d00c50403080c0e58960500d0000b40310b280d8040b80503182c00c54518004603d40040f80c10000b41211495800303a0314103440c02c001a40c004000d180240143c40d0144109481d540f05d591441007540000d100002e0800e0b482e400240840d91150400b08859100b030080086442030990340350206074201c0141b0340749544500d50285507214030081d841c02c901131000b81008154043e00034005451003510700b800644d444100b07002e010700900f0307940360b000f40d0164400341c003241503403000aa40b044c0341d00e000c151860000030f0540000180c58982d143c20f82c003100386015560360081426101c9900e05101d8140c0c9450304040c208404031440000d0003450 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 963193246 1250 963191996 963192011
    0x1005071404090f050c0a0905040b131407090803040819050a170304020405010909020d0240060603020a0210050a1416121e050402031203040b01060e0102010c080a 71
    0x38020695089050300d5031000555840d26802128082c200030303442064154207220100d0600140e0f2015111102d0b440e035182a0080c4c601001c0001910702c1c0780c107440d00034200307014820381880640100e103005200300304240c0013406c114000500511711503101175103d030030a1009016407a404995181001c8482072940648500e82c1410382c00c1040c1c029008090240c0c030f03c00e0f210301001020145200da402194204096aa20003550003650100a8000e60106004801100520b800311005101c4614103207092650344031000d88010b00c4000051506001c1ca1441120002460700d02880c80681094541541080f28440b03002e540d070300c007603401c50706031a4440700011070450072a40320103405814200c04004030300b4200f0300788048524042c2810002014025440c900c001c00b40509a00c44000d000c6801603405203001d594020a00580308a80c94003594601208111000c0c020f58000c500030105402035515150300a400141c1c122000d0307042d0390500e85940030035038124040683c403944401000c40c0d0003 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 963194496 1250 963193246 963193261
    0x20d0c080f12091903121a060a020a0615030c260118050c09010b092704050106060f020c03030307050313022d0105070c05010e060c030403030e01120507021005 70
    0x78055240c540325101000b0038568070344001d850005000f00c0f00706040c0c50b2070303280d0001c01640081c0d107140040c000ca4400c103407001d541d6a40c0e0344409824640714901c441d04260b241d00048496104150090069004008a070107004140c4269081c00c0d4400c00300e024514074581d182400060a441207a0b00c200f04d00a0f24040202d41c400303040780c03c0f80b16100802054034058540d0003440e00400054615110300b04010216042964070301d4142c40c5190200d5051040c0281001840700810102144102c1c4440381c51901c8007401a645e030080e4400d4001045080c00c100c401001e944c05050b96404540c41500c44a180343c801200710307a045180d61a01c1a526600c0c01098542505640f5000307410002140c800c1c0c02c0c01d0b5070011600c015440c40000384091030000c10045620b8040c102000e000324070103000400403503014100f8000405005040903050000340400d82d400c5802560094012a0141d02d800541d580e11a00c500640d0445402c00c01150500d20700007982d40003142c0c04503000594403004501c00 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 963195746 1250 963194496 963194513
    0x4290a111c1d060c1c050714161b08120406050304060b0d0f06060f0b0f040905040501140109090605010504020c0a0f0201090506040f0806060f030a26181f020d0c 71
    0x10107952504071211410401358a650315400001d407030415065074a90700310180c65600503240a28040e07516064080901c61901d104c581c0240d5610305245003c140301c10006182050030342410036030144113982203160170010f50070200d1400c0e4945040034100414448a60041c0507250040d0b00a1000684000c3c1980800c0300b00003c4980a859405011000d90401000e5040f20f030035500c4d020011a500c0b55610300200c0c03580911050f6012100081c401401184580e82c0b105a02c00d024000110300c00c840c11883da6403244083c0c00c40258070b500c488801007800346500aa5004101c00c0d50110303e08079a103001c0300d49419000390000c2c80300c0a03480f610b10a581c070403400080a0540202410342e01c55a50005801e01000c0340301e0700c0607a00405000030080c0c40d117a2050390060b04c1c007070080c140612203981c920103440500045d0003c048043e00d0040c0b800b1404801a11980004020440e0b0341c20000040040f200d40d1103900002021a001d42c01090550101785a0740040700d0382080c0410360a5450034010 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 963196996 1250 963195746 963195791
    0x110901140d090f061e0e030a08100b04032009061f09080d110f0604030206010312180b0d1d0c04021c05090106030c0b0703080f04290a111c 61
    0x2a0000078182009100032a80011788110000b16020a02e90b00130708020251841c003900300a140e0024460a551240560052a4480010a00e400c0380079100c03c45c100712500283c2080e00d8030625214903009543e0301d06171b1480d600d1000c644054192a1200c00111210b070944100401491509d10416041d4080c180006c0601140419a040d0f512540401440701b036030800b0241311807203204896030b0101e42c0421818090342d055030241010380e0840e10b03411826500e4001c00c4040001c4080050411140e03001504081d219070f0301a07980d41c6081c940c0f41d200b40e41c001000300d6a040c040241c41d941c105030024104158000c15a0056240d0160507000820f4038500301070200340c203082400300b0800003410b500a009403441218100c1005072030320342d03c0e0102c1c050700c607000700464100c40214015601c00f00e800c6074000c0c070520040c00743d240c03600c4400842910351042010010b4020050000c020b1040c0903413508907852203507803810840f50408211900803110f9400c1131140c2c2d542181c00b000c80b2410030001 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 963198246 1250 963196996 963197003
    0x9060d0c110703150b010c12111e030d06060e1f0e0414070212030f06010804020a0b0711030c0d0b0417040e010e040506070509182701050604110901140d09 68
    0x7844150350342003042c00130328050320b46103e992078040812035941c014200c3e4044030360451008840084440c10a0b1105900450043c46521601c40440c1c110340000d024010240b00d14005152180c101c11f44520682c2c0b032a40042081c05000003040780c1c2c41d1910881c003494000d914000500c0c0c07852015096802c0c00c441d40184d500142806200311500ca09c4030001c0340102070a50803100c442c4010b28448445020548891030002140d41c041a10b562143d0f2540350410700061200011a98800007210300350301400088800044180c120f00d010310341800480702c100401d85e0302e1440f4848a681c0c2034034849000340014401407104110043d0711a0410556000e8485030140020a5854017071031030030500300f102c0860f8a071081d000010bd25034441c2083d0b407042da002400c4e0f04120140b0316002c4042a400401e602c005004a100c803c081c0741c100302000c18507041c103200000312400d056040c0015544120242c0c0c592007003c100034211640c0c0304103000492400c2c001d401d6102c0d03000310002400340c4426079024 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 963199496 1250 963198246 963198253
    0xb06070302070315091505040201030b2808070b0d0e0c0303040609030b06061801031806020a0e090a11031803091003020901170106140f1201030b190209060d0c11 71
    0x804040d000901102a28000c075000e08904500c07010f900309541e00450014140d010301075000c00b9214203034004580140c4141004600c0e441694041510100c2020035030807103003440141c600c9901c502140940c09881c8140140003034030300b092130110071842610200301e100d694841d49011000c406100181155400809480c0d68a81d43c01e0f0003030102c0d085000a81d680d07558400460f0b618a40b2604940300011f1101c070340c1c041c0040100c01500200f05c814046200c00c2a00300542000030700601c014044459661224100240e4400502480d004014100b40700680b40041034404810349000b500e5210b41c5054440c400c070381c0b03810b0240e8110300424012030b400c4440b8080746000660950054540c21000380c0c0c98014103903a00c1d100340300021080c0b080c400420120109200011030040003031840c4a07400035098684108500d603461600000d07402911300480034010f101141e41c81c0c1180110111003c8402d50030706001000145176845443c000c03ca42c00c1d034451072860040c0c040c0f448005002680c9007136 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 963200746 1250 963199496 963199507
    0xc07050a150206090a050a02040b031009050d09060e06070f080d06060e040f18200d0c15020d17072c13061a030619240e010e130b06 58
    0x36000e03000300030441c0005030103182c0000c1c0350140c0002d000c0444030381080061034100b0198007400000d0000781c040715094003400046550b19401b9024a10000e4400c600a042030315441c00300811500c0c154101c1c004024404000c49000d039600400e5502c941d40114610170701d05a14546107059100c0d10307840b108020f0601c900003c45035007003102140c1085e002d0f20207111540a080d9001d00701c420468844001403818492000420f00070070f200303196020713074010a603851468080003403101c034a419400c50700440c0408041c001010344440800001585000800d40c51000310806402d8403030501400d402c0030407840014400511440d0510151721034160140b440b000e40d441000103594000440502071480b11a0701e01c4051514410941290101c10700d0300d0909409904003542d561000e0130300c540c04034103424506580f20b030b280034840c02080d203103607440000d003030800400700107442002d50f4201707002808805510590308103405842a40d0221071582c21945184003a000424010b50b00c103422400100d903 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 963201996 1250 963200746 963200759
    0x40b012c06090d2d030807030b01050c010f0506040b150706050a0b06030f09060c04060f0c02041b0810050406030209150a0306150e09030301140d0c030f030302030402040c03050402060f0c07050a 85
    0xc00c0c0050f13400f0349148070040c8403502c1c1c5403014040481c0200040c01070000120300034403a62008d11150014034220785001048c6009e2800d460242c04411049a42c52080c007045203030910030702c103094000742e52801a80b1084101c441c1d00b8080c52001420a603251800a0400440d030307407080621003801404151a418101e0100b991103c00311041d40705440703004082040b0340f5100041ea0212102503a4040d0341d06000142201e034550094012a0015250021420925814603502c1105501651543c0ea0762412041c0c010302018140d00c524062031814006101688131016075560010601020002014070350010680243c150f52000d002a890003100303801407141c000000c070856100215110040c5c460810650700d9120a100c3d107540c03080440080411420804d401e009690700079410040c0160340c0b51580305002041d0602240040c1c0c2c0041040110b2525102d0b502031840645801c0000e4a01580882c42e240305001c1501c0780214081000711501d00108060070280c0406045070400595681 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 963203246 1250 963201996 963202013
    0x17030408040510110304211a0f22030516020901090c2c0f28170303070918020408031c0c020a08041a0c030c0c040b012c06090d 56
    0x51644600056043d003103410f48590b1074074640074a01000307580703083d00c1c254124245044a405081d5907070204400309011034a0260440c00b000e1100d1080c1000c2d140c071000c180400e92000301001484001090701c1c020320624541442d200303c2d410300301203030b4912050f000c801044440d44d600950003604980007042031f000030b800c11034900a403615074400c0e056408100b4159251045000521240100d51a003000d24050742c42401054003e400c6030441020390b520304c864081c3e0154181c0342004450800c00508240036540b8001c800f0f028040e40c02c42c1041980184169058462141440503006144260401580c1240c0080c80c4100450742e4540c0210841645004102403040c0c4052402000040072800440d1030700d810b592042d1030030700c3e090628601410540800d01c0c0103002d04010f000600d1000e07030420007404130038001c0700201015100c4c801003005603000291100d04118208001c0720540050641c40c054071030403140385407482c44850700400c02d18051621110740c08040f55068100303112401 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 963204496 1250 963203246 963203249
    0xb0a111b030c010c020609040f0908033103020c010e0307080a1a091f0e010902150d06060e0105040620062a190806040605091806010801271703040804 66
    0x394281c0300e0b840071000040d00c200740e0000002c0d40107042044804103615155001c0410f02e26540c0780090b01c400907440b4100f49810445000c2c040040c6245404000300d00d0040825202000c0703500d40080741c0d400e541c020f440d000c8000c241ca0520120078010b1110307540a01481c0090701da032100320381c403180a0b0b0520200e0749010b200c0700d0034030407840320214054403008640c90611150059403031681c181460450070003808200c100080750b540e1200703010010f13910700340e042d4488180104602d07203e148410f40c0d0021141c066001e5024050749041d000d2040e608007042c0c80403510282807082c0c012050060591a0154108181c061070251004102c0f4112100703404880c82400c40f941c060400380c43d801512064402c005070b17007819540e8010b0020704203125160603a40490082c102007002036a070004a10308400540740c0303a010042c0c1c82e49001c900001048228010300700c2100922507050084d004000c0346081c030840c0e007a800400c00d207031021b02030710b0200b001c0300d014801030540e80c80c601420200c43c1a0480e = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 963205746 1250 963204496 963204499
    0x6030a0605041512080a1e080402130905060c090a08070e04120203070201140903030c0109080d0c0c120804170a090501030501080a03121d2a0a06090b0a111b 69
    0x1c040303403d078040280080420a885a42d0040c0da13242400d40c648204036001601e000301000b0686010303100b10100f0000e01e0035030400c643c48822580c2864410411103446003691280b9413481c2102c200045800091044d4105039417103452a40c58526030302003020921039401600c030a102d4001c0000708001c0256144e03108a0180740b14200154100034100d0b16445900c4000c2d0000307143d05403452250384842d004042c3e24000408580c5410201440c160030b48a20b080306403190100494841c003a20540d01070b000c075105641c640700711103148959981d0a907031000b212260810908000003420031113160300101048810040c0785889941c071280040c00701c1c0560142c1e0b40020b04007800014050360020b00d40d44c450394592900903a1000010013070303000f080100ea0710035500480640c5172074410700078032171100707840e505140009801e1051a180500320300600c0d4041c1c0200c6042501308242a4002007101c185c6038030300407955450f6046a42202c80403007134000f903c2d150007a036042a00004480c0003081c0039000 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 963206996 1250 963205746 963205751
    0x4050609070e011a0f0705060f1503071a0307090f18110a0f140d0204030f1a040f060c0c0c06030504060e0706020304090b0406091b02010b0f130b010e06030a060504 72
    0x8882c2d0180a845100b0f104012443c004070303440c100d2144004010f05088440c07407040d10b00f00040f60310b88900d00482503410200f8505588140080c0e805044005454904190020040607282008407151013042039243c50340c10034041f020610603881500d6000c000c000182004d24401d8a43d1b08002030500c242d2442c9030b6542c40d0100040c0401c04d0324090320084140358a03160070005200c401910a043d0791400322409400821180d040d043c0e940c4044c2000c0d600400400140c035542e80b4100c0c08014109440103111400c0c102040001504007901c60003c603030010b00400e00b00e18591080d40c9142110f18004d1900c24454004224140c2c5544058072450040c40c081c0143c410404420341c0300c00c06802500e0058200308014001c540c2c090300a55100f0300d024100040079a501c1600708100d030035a19545030302c0d00141040030071841d4240101068207904840e80d10194031220005410824015200128a0744480b400130250380036203426070039510040d05483c3d0360314105003040010110b43c082e07144581d1 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 963208246 1250 963206996 963206999
    0x9010f03091502040b0417060f01030308040c03140a1407050603130618030302030906060d02101809060b0405190e04150f0507020f01060b1218030f0a0206010e1e010506030a140405060907 82
    0x81f0000b0340c680140095104515180d00b5510200c0f40c03d4002041600c02d0710100c00e00100103001454001002954007000e8003449215150038903187c04414100e25540c2d09c01c0005100540d541c4080f260014480c0701401c089030420700d4000042c1c00c070401080d1030107101c159200309143e05a00154400c80114041d101c0c10703651a0100100038000d50f00103500040207908d07961425000311009420f09121100071461569542800019901160400440040040707000c0001c1d090400001865000000d140042039007031110550301c0040c0284003a00e02031400590780000b02c3c166100c2410340801100911031850000400b030740d100c0321101031059640c6450710006901c6034150540e00188082c00700f0001030f88441080703009940c10881144201d00080121074050000c6c04001d0038508480e401510266140c62108464000014071045003611405103c0d0381592151120506441e001c807080c50300c075166040c64400134100f49590409440c0002c05120510000040240c86031215004691503107 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 963209496 1250 963208246 963208289
    0x61506090b0c0d0302030a151e08190f210e0a09090f0b04050c03150403020c0d15051005040f090209090d02104d09010f03091502040b04 60
    0x910441002c11541e820421504042511030707001945c00000000000c990b1301048100300607028401e610102074080520344800c89a404401c21070010b041c0d40001d02407048001d031001119041d048801400b4000321000c07202000304100951b074181d1140c803140912039880a8000e0320040500c85650310a00c0c1c20000020941c02902894925940c01007200301519001e9035131010402c00613000315182c0c0103503902e54450781c03000c10551800b03019a01c01c444890816003806420009603807042c0307008410003403202012890742201140c0300030701170304001a41c1d44d40e0019081561410307001a9071003410040104080040354001421240c000c503040c0c2915207607660b40b25920101e0a20303040141c0c0186054440d4003040358040d00e9040d03901c4a18800c0d64041460341203400c1d03402c43c0c41101c2c0341510022001e0005808030000150a00d1913034171880c113051100045c001701d40306044038042546581c40d010030407080c204480c46000c9010300c15510703113841c0e40c3d40040c1500540212102c0004075403a100b0b11 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 963210746 1250 963209496 963209519
    0x180106060e2e020d1701030f080304060b0406091505030304050a051012090c14010c0213020912072c01050915120d0906020d050f0306011b06150609 65
    0x215052916070404903410982800202e0254046158a402c1a0381c0d6411500212902c00510880a94054456020042d80190802200300018802000c18800500000340508030020720070307030010862034803580c4618200d400b0f40076814820f500103080500004220000b030b08040723480b0100c95030214034107803601c003450b82e41d0040d845960750184500d0020408e9007031051a0b66481c2909190581c212240704000c1c0c02a5140c8000072565a5801c8004022903a500b40d0b0b0244414001d1074040d0102c480360b00048d8229046091003031007036a00140b005010b07507030201e031008051510401e44201d281c0c0c4402d00c41c0c0c00b0301035080800d080d001010768088040c11035141e49041e44c03030080025a80391a80003420412165aa44c01508040602c3e40d68041190411454008407032540e1425020360070301c0c100a00300701c40143c0038000d011090002c05902a5541d00b541e030320150a18044985013100114000c1c24808000041c03d103501d05000d0014600d00511104c013590b0311521241e61680c0d449455110 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 963211996 1250 963210746 963210749
    0x20f041808090a1e090213030512120f041a131e1b031205070609150c09060201020a09050405132009060109030b2a0a0e1c0507060f02010221180106 65
    0x9401541882841010261b80c040c0040009040e140c6040380e440e80e944501d0854001c0d0010011900828907888048041400690040d0002801416410155205100310484010303240c1c03e20002c0d000500804408815400306135000101d4620309048000401800c0305d00c141d081d12003a45648400c40711094060103c421070364080c80c4d8001005110f00100d44580102c4002c854940c1c507025000302240c000040380300410703e1410300090740c102800d009009004140d2080b015039005000b01e000c2c0580004000f812180107480208155403841a508144e154500d40105000c0205200c4188a0140c082c20000e408050b50082141d0b01c60800540300c240c014440105540304400c00075401ea0310001e203940e036000072020388200949a4850504132608400b41c0e00d00040c2e0802c019211518008550001030682040c1001890511b0385a980d120342c81400b41c4c03414420041183c003c40b0703100754102c44862a401c8241c140380c1510244080440006036681c1010800c00c5c1d41c031425500c3e040c8100c3c4c0 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 963213246 1250 963211996 963212039
    0x307022812110301111603051603030e07060201051504090c03050d05070c05030619021e0409091e020319030e03070f05030c220b0112060b030106110307030903020f041808090a 77
    0x9040c000d106d03103c3c0c540c0e0202103c044007044020300140080801ca0000491511b10a4030080350342041c0c4000d103850084550300031011603051006111711b42e0907000b034486212609907400f14005110b801e00001000b8207038030040862051110304c950702513211000d0044244101c41250f03825580c0c1b0b080503520241514549804404a040306400b240550300500040200104045180d185451082d8458100794480441e490b103074032040080000300049501d4403664484c0c2861071001c640c000c02c1c0d80d118616101e03d110409181100d0501d07000e000180e110400044c211036002d5141c07940602500410320610f4042d2180c100121414603041d1101180210f150040f003529603140903040c4050000512014103001c0040004410081140207101c0944550140c41d41c0e01d52402e940100742c2d100c0e0b490401ca29070000d000e0140040c2c1e014010604a0703404890240617040c065000400505441e21400213107a0080c40c2c00c0700f0080000c003d800c03115000c5814440300b0340e50350b000300c101c0c040002401 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 963214496 1250 963213246 963213281
    0xf0d02120c182808010e101505060c1501240f23040306050a06060e12031c0e01091523040219230a06030204080307022812110301 57
    0x3402c25080241c3c80461030fa03c00c501d143c03800d010300c0c10070f200400d490350046201d0365120038000c040040d00300b014000c002c151400810482594079207003002c0e8211030188078030505000076003400b0f01108000403000300e0300c41610300c0c50725659949420380c814000d0710b48120380400045600e1081340940d01d1151088001c2e103a8600d140c071003007030a0100024009d203d1110900900012010840901c50180302d50a80741c80000c605081400103001c498001003031500c68142c080300240030b00030110640d00d030301902110b541940601e82590700003800440a00292662a004068080c0051201b0340d03d41040348000170001e400f14010900441340f1040700c0c00e0740080840000c20014205201c02800c0c500f041e243e03000b41d0f143c480004c0c040b070b03d0509824031400e015013034440401c7c3c501551040e00610007802e085141c58030b0503203102c1e03d9000f090400b82c030070001940d6900385110340606c4403a4607100c1000c40d100540d15051001d0340c410409009442140c07041e0407840b540d0078144510f0850010880700e6 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 963215746 1250 963214496 963214537
    0x1050a120c02122109070b0a0315090c03090c051518063f040c0b2803020a201c050d1103040b1b0904110f0d02120c 51
    0x80c0c1024041c1500300d00d0031446040b2190008029510141100c0d140e03d40144000784034042003024201405805625903402c50348040100c0d503c20012a000141c407030a000c0f4040230112076a0b446803196500c0303001d6050804118500d9142d05600c915411403040c040030001c1a126400c1c0420007003041032a8100000c104100c2031071010701710341c19142410013800145042c40402c4c0707900315900c0700d46050344442081c9041032011030364503541c5a2501e60801d102500ea10f05611480d10f20091481140511100003d405c0c0f040d0003442e02ca150750440d031060101d004040b656005000394020f2280708005411110211003032030ba400d0000401a286000801c4441a54001c242955039000c0b50310302400010000e8080710710881c0518040104441e00994481c9000e062035200307008010f11038401c10101c0310a00c0b00d40b11000013a503450041c1682d002990494aa05600c0540b0801081e030680030408a2580200810307a001070005a04035034141030142c03142800503541340200060803a01c0d0300c40301c07031 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 963216996 1250 963215746 963215777
    0x20c120703080d14010803070f03030911030d02072102030304090c0504120515070e15090103020f121b070519060605090f06030c0f03030d050907230f01050a 69
    0xa009419098105a61000740d0300e640c1c0b52465030010800d4880c198448a200c40840e40700b81595005120340e0019510b882810765a40d01c0c1d80c06030300801000d240da070302c141d5001d010740000e1034164104c0140480d00c00b0441050081c0d503039a418811080324018040403070030301c218900b0440040e1540500111f007400e090210316005064042400c408020052000003401c1c4042c04900d400070340038401400e80c81c44441c184200116004080c0b0080c4054800006925181c0c0e0a28035000700840c01f0007a00e0b400043c1c01200a40704610802c00c5144000c61070104000c50009803500a03401584000e42c0303410f0501d00b501c0180942c04010304203030024880c02000b411000b15075412a07200384c0001500139168000140508000d039411200104907404201160800b0000c144030307103004607014803802c2148400240e03a4401c94502100c8030740c4803004070b2901002000810041c00f10034282040b61005d074030075455003247c060f11507846042000480100c55005000b108c0b000c002956a05802044002 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 963218246 1250 963216996 963217009
    0x70621020309010216060501051e030c010e03120a021510080d050304030306050a12020117010f031e140d0f03020306060301051909021804060815160201090206070c06030e060403020c 80
    0xc02c0b6a0a654080003207416034104811945405031107070350000b0301c0354180300a102c01c038aa0b0740051200350f140c41c88036040c60340e0300042d0201040824604203401c4040c0e003022070705201e148454607070400400720700300c0151900821030140c051a0344a4801243c0d99540b44d0030340e90312481c80703003264503045001d455020358458002143c0c81030180c200031401907940e0300400c0d40d9459552000003118640003202007150f81c03000c0403e07600403100000f0f281350f5043c40c040c0850304865100042400c20070028184800701e0480d612901d1941104aa0904016500b4140d40707410041c0b44e020f00203080c9001b0785d003d20740240b00303803070140b8009000f20741103a08101c180f00440c2a04200000c0b00f008190700010246c50360b00041210300c410301884410707290b041040c0710903500c15070801a81c1d070700091421a81ea60744200d070240e01103450618420041c80c41001030780113209150300690041d02c0064404280004018103604452666900f0009440c201000a81700c110640e0300070b005800c002009490b600d80003 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 963219496 1250 963218246 963218251
    0xf07020904050c0a260c360f0402190e160c17040801060509040b2205060a0b0906040c020d050c0c0d0507060305010b040605030105061b01021305030706210203 70
    0x2030b0200d6054804032030004d81c03290795a5000c80801d50056011110400c8485e0660030310700807000040ca0000d10744c00c006028200108400036900c17100440c1c141100d038415080d500d00c2c01c1070100c0b0840e00d04054003890200c20086a003640110400303d43e51040c5100e44000c0d1085904144806a803500c4011a480d21070b52070a2051081254800420f404242100131420380e01407a2900c80e03548501c0c100300c1d182940c0056025500c1140f0920412010074210b0001980c0300d032a00400c1d400b4001a0030310440d520701c482101600c280f2076242040200748181d400555842000c0300c85001c41e9807a0004c102c16940c0c1101b003800181c2010101c0c4d054503006201400d1b1b100400d03015500300c0608080400c0d0a103444450a550940c0000e030200645e54140c49124050442c1000c82c0e880c1c40e00300700380944507100610074603000700b40000350810340042d4044c43d01d4284030480020365840c0d444014040c200900350180324428064200001405405400e48051120340d90805001c3c5460804e0804003d4000 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 963220746 1250 963219496 963219503
    0x30b040803060112021206092809020102121306080c07021305040c0515191107031b030c1206060f060f05071a01032004110f07020f090c07020310020f07020904 70
    0x884c58000007001503001400543c01d00207207560f1300781741c40b008205800e480a04200c0c940d0203031150300700c1e200049915110310211a0307000407814441c0c0340f0040746000600011080b0701400890045503100c00c1900c9401100d01039a03590103152034141d008001403281c80300c001e40c8100c41092584500c42c0d15041580e2103805848a4074a1941d2103011590344044400851038004002603404111004188072492040c02d518041c011038802a030710b0341d920a06408054008055800e000038480c07502010314005d1548825500c00c01039031969100c0c1e1104482c00129000da040050101d8174540b011a15401c81c1c0081c2c0d42d032030700150070003002c0d50342d6800408147c8101c0342001400300e80705c000e0340d07400d030096120f05221540c01e100443ca04542e059003038106481141480708039022211188141c0780015800c0c901c03039980d510180b000503607402c00b5032015504040c0d810200b0121140e40806445524020340945e4807007042e64030071104902ca03004449404990900c640000341c03c080d200340354410310 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 963221996 1250 963220746 963220757
    0x120d051f080d11060402010e09090a15050105041409070603020714120a120b010203310b190203040e0f06131a04060b1e030c041d150a030b0408030601 66
    0x90a240c50800900540111006030700c032003080102030b54003101da040c20a043c90003900260409a000030032070340d1440d20141c41055032030080f460030344080c0941c5440b9903101c190844c1d90300c02d6581c8040500307001d01c40c5034810f07481d1031440500301d13000b0b241c011303c18480300002c1c120040c1481c40c1a00250021641a502ca50070001100e4a42c00704001945506420a51450b12403042e102d0041000840c05018175180e414400341c00e030a660004141c41780c4d0403030340b19503041450b042c0603003010410610360340c4622080584e200151080f00d47c40100080fa86980c00d2010029681d074050b40d4a200d01e229158a0400c104005903040c0d0b02c0120786500400001d00c42500f8041484410041c1c5808400882c01c06101f026603c1d02c610f0184104401410f401d81c1c80713402c002e68000a0849101c541141c040c0610000000849038401074040300c024090810801c540e034005101010308000b41151f1121a018144890051601d000d403941d90450380c0c4002204904ea4980d42d540300755402c09800a4148070 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 963223246 1250 963221996 963222031
    0x11010b0409060b4b1c0309170c10020f03030705090414040209150102070f0902070605010602060405030703050901120e0f060a05191e050106020601060809120d05 71
    0xe4490060100c414021030340030a00c0f5110600b00110071603410010159441800d00503004161804246501803400001c09600d054560781c0d608420b041072001164059542900740150948450f0004001406a55459441c6845c2d001c100a4071085100164880d80a006d90002510300302c040d86d03400300007620507074110a5038410b0181c6075800645800700464004284103160341031030b00c502032004410051014982c205500820500440540110b0a529032145c0c0405a640200500d00c010b01020054041d882d5890700224025001040d0413111582000c000292542c070019140e401990004003461403c00709907816280390b84095075075414800d0600b4031064040341407150818145d2542c02401d00031020741410b50030300c40000c025180d103514050511030302181245161201030800c48000070401840d04040510f54003910300703028860701700400403d1041e03000c241319041302c1c0c1c2522180f000f6101c0c0703a88651243c40740341c101c0204080600c5041842c0829801c82900405600700401521 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 963224496 1250 963223246 963223249
    0x90f060f0f0a110c010203120406020d200d1a0619110304090c030e0a081b01140a1415130209012c21060112080c030304060603030806060705070611010b 67
    0x2c0d080744a1240100700001201c0000850a0102e6820f204007480078524144801c0d410b02814a005000980200d0380820781c44d1003024594001c8141c005802100000803a050700b01a00c654400c4075841481410903042040c0028111252405010014442420158080604560004408030410800a003c500505115030a20060000d0700034850045084080310070041e094880e04200e52240c0e40c4021807070000701c1c0410701030343e509481880b00b000c1d0501551000a02601500300c01007034189141c0180b0040c82035952006c1d400c99410300f0007103102c4c0e0301c4052012090a0400300103400289480d15a081c07400c50394001c2c00150f01c141020324010210b0384060740780c103911413009080c40c0071504440d815807503e040c01e104951070b0b0303c00200920160702c0549844120600c9600d100e2441d4208200070407252034207403100d100c403550449440386040d050040c050000307440160b0100d0319840101c0d0704c9080007001c85036916040002442070300d1500000300e842d408400c0b49480346558540011449 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 963225746 1250 963224496 963224527
    0x41415030f1e1c0207032001021002092b05060f04080a0f090b0a0c0506010f080c100309150b090109140f071b060e060903130e041b030302060714090f060f 68
    0x11030f4242c0c003e1041031704602d0443c89040c2402c1301144000882084114244c2c0d0000e00006a000c2e41c00015841e022400040707080880704104020381550f0b15000c0c0c0c242111483d820501090051045860350b4498240c441c00c041010754000e001700e40c081103030300e01a42c00780c030b04500d200c0c4e03492070684c81b400d60f01c6080e40e000381c00510b90300d000941140840c030140401000001d01620f660000c90242c2d52900200c255030b0711010f02118014003969003403049150180e80300041042d0455100300c02141e01d0303043d400c0148100040c1038030954520700003251301c00c1c0c2d0b0300c1000390b642081d2150080c591202e264014468600030010340070001d4000d00204103c2c0403550601c0f440303119240100388041100e44403401c0003170007803804003141d02c1030207021401ea90b9030234000112800d6030300d4201242c80b1406c103440340f9402880740a2941694100c00010154005112440b500c0ac55441c0280d0060000380001540324a100e4240e01c41e0b13007e0001629441d00100420380715030780241c03230761800b1045c0040441c03 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 963226996 1250 963225746 963225793
    0x160f0302010e0c030f0c0d0602090301240602071a031515071a07020a03050d09060606050711040603020f130b10030c020f030a0203040909020f041415030f1e 69
    0x141d440b1603580c0032070802000b01c603100030412800390102c069042c1c0320a13940c3c009608550b205a411000741c0081c485213034101c030f02c0746074007a000b4000c03940d40800c0f40d08442102c0c6803c200e40051a03000203030703142c4041003a2003555a40c05421050300c4800950218540000d00a40003d41c23058100700d215907220940710a0101c10000019203543c0300742410018840210030a50b407040c03107102000b00d01640410303222800c89d41404d040d81c80d03e6040d08904014448000007d044030310b8444c0105542d60454082c04119110382d0701140d0f6000e4070800c1c0000d8403241e1000035004151607141518601c0d1104101d100b140000d00d000139644071010015403920365402150000c40d60355500810383c554103204032405444500d0040d80342c9805008002e60f41d10482c032986c42c1103982c0c2c507885811995000b04a02609800410500c00660007441001c0c000400740c510303120428602c081c80f03005003804903410019501c0306010744011403030103130a403000f82001966140c00b4012113840084890b0650340210 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 963228246 1250 963226996 963227003
    0x2040c12090c0512010605100f1116031202010902101d04060b0a140f07030c0212030d05010f090c050706050402060f0a021f180f02011e05130e070503040602160f 71
    0xb18852a040030701041a40302000380c581030741002002e00440d2942c50000780c811000f40b170500303600c0f9404801122120141c176082d4646005000e00b2403102c030255800e800549014200b4400f09210f149020382c2211503648000390044490100c50100f9402a01c850711009501d0f0340302003010080d600001c00316170594000f0215510080f40c9007103155400807038031440c030340942c01c407900e0310100d0b80141e56140602e00300102000702c010005030441d02c90040c80586084218102c0f92142d0b400f55204c0e02504d0240510154860690000180c0c01d0460207425514403a07616800d1816185480d003c010307000c010001d907001002000300c0c4500b0100c1c50000c1c440c1c0c03c9aa0302601c003844164520150400c048166601042e050030082203e40800c0416021880d500c5204038812046c10300c010b817881c5246200381e003d843d01010303151004035080f2005104c414486040d281881da00e90542014841d001d48003100050000d00c0000d0004107150300a041c5400300000c044180f00b06951158850080784000b117 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 963229496 1250 963228246 963228263
    0xe011d15100210150b0409020c0a06050f060f060a1d030307050f0615180703180c120b060603010303050316050d02030c0a0315060206190e0a030215070f080402040c1209 74
    0xf4001d604912603041111845880c02c08000d19150404440d03005a010300d2035040ea0001e90036841c500100f01c04d1070f10a50084060116141c428806411240c04840d014000d1140c01d110010910782003003100c00c06406900c403205462038051409000e24207440f106d542611080020001058040214a602e40c44070801400b0030b180901308888140c101002c11400341e080c01e200640da20300b820700899488201c501e400104030108014001e820003801d200031740401c0b02490007185030f080318600580d000e8000c0c940d910168841e41c0030300a640c44248000b0b80015018408103113518544025103c050354a490b10506191651207804200d0f842901c0032001914006141c0c000190103000b0b1082500007440c62400b92450894044c0d210302c2e000b88550072001a14042c58103100441c2d00c91504c0340c5121003140c0c000c90f10307494081d43c0d4101e40c07104941d0f07101c02940000c120503c1038204041c0b01d07485651340c41040d00c0301da09100c0a40040361101050125030141142515030900c03400c0e06041c043d8500 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 963230746 1250 963229496 963229513
    0x503040801020c0d09180b0303131415030907150c0c140a09150303050a0516060606080906011202010516060507080a1506080f040206070206071b0e011d151002 70
    0xf5464000409110303014004c1c1d51070200451178410141000002d184c9201080c1c40038548002400c6104004104000281050011410b0004a050001e2601e015618131a122640180d61078084c0011507640d03102e0b0307119038020310040c540e0a01c0d00e00320100c1402e1500304005907540300000f554068002c1e85daa07502500d4028402d24000340307400c005051292081000902c00c412008001002d400007a0a0090000301502800d20410403118108540803504d103800d07100c0e1502d500a02100d216260002e1254070215011060110b000c5040b0b45220321aa04680141e60056540303411580c0015055102400ca242c0484c80c6401118030a0b005a940d0180318a4051120800ca40f503215034006c84004010092141c903030400b15494020014485080c03c40c0d940b440017444034800d08000079000324001c138400c010420034064117030340100302c0d40012001c1d88d15251007904800e024480d40700c2c0002000c8280041000b84000c1940101c12208107a0703810340380c0e80114121301c0c07516407203070300613400007030b4 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 963231996 1250 963230746 963230767
    0xf030603060c07031d0f0301090f060b0406050604090f0216050d0f0302180f04020702060c10060806060a030f05010e070b07170c0a12051207030f1d1207030903050304080102 76
    0x80503405541500e4560a003c1c080c0c500800d800b101c41404400308031155400060380c0d666110300e64601d03600030001e10006c003451504403040141440300302c68841c1085503804452902d4007481095480c00760030182000c0c42c00d08108040d02c200070b000140741d613003003003000c1d482050b101c1c40314501402000284040c461440000b046040c60344107420401d84144014034421600c0400d0801003081140e0100e01451420000b400038458070000035400b141c001548001c0f80381c045101e1145d9000180c0c100501ca1b6120300e000e844200850321150301c076810442c01d01c0050210030b02c0d00c11040c0035000000c1d04581d1521b060345002400d80010ba0440b030040740c06010407110042d1500704281482c0003c4c18005c10200303055541d0505040184911025822034410610400941c0c099049894501500c0d040c0000c000d801000c00440c2c0710899410464084c400f50b15060015880345a1180140244501c0b103035010141c3c2c1014800310108400c50000001064040001c0c1c0098501c4c403000699072941c040 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 963233246 1250 963231996 963232003
    0xd0f230702371d0f060f061c0b0310060f12080d0f021801030e06070503070c05010f06170a0506011e08010504080d0605090c0403240c02151e0121080f030603 69
    0x289900f2100720b040100102c401070b600780c003504410107036000c00c9240e0300307007000800c0350103140801e98109241c02c40703580d0304103041d800000c40308a0540907103451101020080040d6425401020040ca2000e041008580a428180138045025103203d508160514210000755000c01580c0d640306500401d0b4450080c10201c00e500c06100301b400c080205003c050411501c86c08014440c40500c607004c0005a8a680565544000079a000000f0804103a114151030700400150080201c0f8281c4424ac0c0c240a120015030802c03019044002050160300e0402520080c640e000c503041400c580070640010394200900445000d10b02c00e081c0c0546032500c0b840c0c07034000c071007030340c0d200c03901c548200760500868009050444003a207400481c210070380e030811450b0f0381e4445c3d122680c03a144582345c408d0f91103110380e0120301340441030480d5044400c1c94a83c9485401d912548610300e000f040480e60040000010f08a0500081315181c0f2480c500b2031400c0c2c40e900804d0b0414084140c000c0000010000c2c03070715090 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 963234496 1250 963233246 963233279
    0xb0d0309090b0a0828020303070c0305060601140d11040b0c0a020906030a020604030605061912030816050f1803060403050304170a0e040903020c030d0f23070237 71
    0xd0350341241042c44c03c24040d6859003c44141030030765680155002290200c06080f100603a0080c04903552a0700c03910342503103000303d01e1005031094056038010910540c418010800c1d403001d0100d185080c40c1405048400070044c44104a105000410000070003201e031901401040341c0010241200e5165801030064071100209a02d11a0300204d104400680d00d88051720706a1350006000140c0b5035401006c203090a4541d483c4440002c80f04000103441c0c3c1c0e07400d00d40c40e0b07018801c0d074410a10b40c0341e01d1001c6c5160000c0d02c200b03c0101d001441780c00229025030002c2d103150031b00c1210340144510701c0ba002c83e0400e1010b44040e070028500100700f20a110421942c1c100441035801018a0140b01c0c41c001402903c4d0098483d1040341c96801d4070003810302c02c2040c11090403004094500b000e0314040040c184802100e09680800e0035000202034211120b803c1c101c480a0f02d1314135a00c1c001032603003001050040011013048580341012a1549070030350070440c07000030a4010004412a05105075072000d41c106 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 963235746 1250 963234496 963234499
    0x3070e0712061a1c0f060308190207030302071809120e1203070b1306020c011a01030b0111150903042714040c0902090303220906060206040b07120b0d0309090b 70
    0xc0010140d070440b0340122080b00c2e140400c2a01a420640b00c0500a4640600c4602e4201e08211b4040140b20080b4002d0420350f40012210b529482c08103026620342a0394131014000d80c010190802a60081c3c1c69080c0a141107500700040b29840c0d652204402c100040700c000000340110f2807001281400014030b10150268001542071148580d286a5070b04070007080e6030320502000349071108005442d0180e81c004200e800c024419400740034010010b80c92407056560010342482002d0044c0e5020300e43c03406004503c80007800411030b44c40c3c4904020f083c044c04480361880204800940745400e01402010b411408242c1c04a60303401074100020707242030020441c8410403c4c010300002901e105141012190090000750301e84c039132180024118024202100e180c003510440300030300340396000085016074130720700c0082080d01e07192681280c0e1400b04032802002d007419000458003c9002d420145d00d40040d01386e000c190301040c070001c186582c50142c0c0440106405080c18000b114050041c400c80d07900 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 963236996 1250 963235746 963235769
    0xc080417070b070c050d062a1206060801090209010c0506011d160e0d0222050f09150a0225030503191a060306040f0203010b0c0607140306090603070e071206 69
    0x440b525803041000c4144601c6110322034003070603842041000c0d008540c0c20400d21045101100140300809414081c0580000c0013a1b0180c10f44803174274409104100580f2090740da642ca00ea0309102407140294810300c10035060010110392400025420001140600f10082c00c00944800c1500110032030403015103402209804890080c01e01a0301020943c0d288400701c4410303052400e9800440c1b1030b1900302503481100c818403100c242a5075031981082d0300580111a5190155a807407000f19210b240d1503404a40740c990b0540410741c1803c0980190900102c003c000442c201c200c40044c0040103c01d03541100412008801c10410f00203030080303060f50250403507080c0a000680c11a156082d55101d044a08c06c02d4048042001d80e100c07035010003502d0035440340171513583d40c40f0500419a504801e85040c02c0303108a500191070580700e0159001c01000f0403e4041c1107466500800040590090042e505480341300d5000030300000e54503103c1c1c06412030340c8840404a4a0500ba00c040d28243c0d0000d41d186003 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 963238246 1250 963236996 963237007
    0xc0709050903030402330a030c020f010605150c010605030d0309140607020327030304080c2b141c030609060e01030c03030f0203041d060906010c05070311010c080417070b 75
    0x320b0b1100400c25440b03051034030781c00a00d0141444001280d0400d280666600c010510007405900350780900140c3c145902160b071000301c400303402400c0e03640e81c0c000c440d0010021042041000d0b9180090141003450c5c2001250361512100840e140810128150300040d03107404c1100b06005140313046e602d5110006002d02605e03c5d05201c0a5900d1154501c1d040f12101201c20f41b03102c0b400c22002c4058040002406d43e5541c81d1348840039130340c5100341034509129410035441c443ea002036082c40100d00101e25100380100144503181c00c01c00400b80d01303080c2068019488070842490140c400280840216140055498241b4681608a40f019080319001003000b00041c004a103000c8580800c036585481d248810440643d812400c500982d0302143c0999501c054101d500403000700010b03c92401501c4e0232103030b99140801159012030050703000d45503030000c04e07051000c00c04114200c1001c01d0181000700003012075039204143d651141d400040303908000c0320860315404040c41a5401020002c140c5170415 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 963239496 1250 963238246 963238249
    0x405040201170604060f03050f1606090311120d170109020c0c09150a080604050c0f21161e12030f0309020d02090f0703061707180f020c0709050903030402 68
    0x100d02d00d00349041001d80d044001040c5076515040000684810f4801c0000c0036a64604650359490210202126014030400d075240d444149146904a071010350310398003064516114010310050700b0200d00d03080a500c0400350007a400401810400700c440f0b07541d4080b5204644800c0001c51410f0304821000c9004000c050801ca0740042e800c80c001d00c1c02c9071012070a440b200c1c08003c02400c000c1440740c0040d140301d000500c0c01c80c00b20351948164021800c1e84d00c0040500100300e003141c6200c2d405031340401030401e032240700b0705190502d0844c45610403c07904616003000211180400b60342c011140c0c1c490803102007140300002e5200e60700800e000702d0704010441c0950b402800d040590702d601820903075154803410656550700302c280c405c01d401400100c0b050900d403182e014030240c1210704070040380c180b0300c002501000c001440c04180c40010041c140260820071280f00c042030201880b01a281c0f104003807132600340c90b84014039110b1401d900800c0907500c2c092901042d950024084c070300c943c00500030403016 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 963240746 1250 963239496 963239507
    0x8041a19020f10180b0c0d0f0504020120010f0e0f070b070803040b040c090c050405121c1220220305030901050309031201150e0910270f0b0f0405040201 67
    0x62504810f000708034500c00c8840c00e011000341c0b050161006110b8410b1105448528004000200c41d00209000520801c81410151402501d00a00140d00064060640214160140c513080a850300101d4003034108e241010913140425203100079500040713a8030340440700400248000f8142c0400c0d0703904001d01a06c881003c1d000045c070140507030a40000280410900f007901c0c4026103c0c1034800c00c5000b40040d0028510b42190003640c7c0507580095912883c4180083c05004480d4420040754000c0007101c41195120078400030240313640d440d0404204182e10400c4006190074070386040d15180c807804e00d081e001200340031500c4100000600703024000304101008840c50340307902b07013080380d030b039445940601d840e52041280c2c010500c0b01030800072940fa10f01c075581400000ca103507a0f48080800d04410410300c03e10945400c0000d120b100410001c01d021600c074441480186107480395103c4a0314500c4007650740801711100d040d9038030755801d15645480103841c543c800301a03030108001c2c90a680080c0c403 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 963241996 1250 963240746 963240763
    0x610032702180109090605060f030639070611211003060e0a03080c09090a150f030b0703060909050c0f0411040303090801110c12030408041a19020f 65
    0x180d148034820000255200d6408005002c1c0b04415004520b41c0d50b640e1000041011500c100c40e0a0700b00f41c08502c3c02c0c9084102e2408100006000d0409610354407080040c8602c84030404003200168800c0055604c2c11403420640090030340e01030b40c2d50301c806242000c1101c1904c8482c42c0d2504041c8841c42c4040c480d007a140f0b0110054070aa030b660350310307204040e5001c1062588004c2a403410040c2b5502803070300214645421038803a8035060119102d45c40648040d001d04a19650032017900720000d207040303a0540082210048241035245502d03151500b01d0100c1ca0036400a98000b0300325000e02201e5a81803098500401545804002034110340d6155500c45044607030b070388d1040b10350b06c5054045580320303444980100000b204460b41c0c0c9030b80b880e010b845008144100042540b804c0100001c2c000c490f8100c2d8220b41101000e0300038280d80200c2e440107500041c10a4420540c140004a01040e0700b01000107050360b03041c141621840305060070ba0102c04444000021074202d008902d21000340083c0210 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 963243246 1250 963241996 963242051
    0x1f0b0f0c0c0111072903070e0a060302090f090c0412382707150318020303090d0303110d0e0d090e06060a030b0603040c0e0f0112120203090d0b061003 66
    0x8848030345d2001e2400e41401e807a0345078010344e03000424001d003d90800e112140c20701d4141c0303c0e1580f42e40e4808003030b4201d01031074540c90380001d190354485160b403600e41c1e919540100c9401b001e40c10f080c0c0703d5003070000903882000d0445510a038011004000d9064440304030f0100090340960000000241404140780c0700500b407034170082d0000e498614401190100c9010b1080700c001100c03540766941411403246201c40c041440440d191001034090b0255505030b5440341900a070087d494041d0203814840b020281d0201038040594610018440001000c024000401c10802c0450f40e4038840520a09080d504d48062040c020480070030855862405411640a02e0486e04e01e80c40341c540030f5040d401f030010385880d66408030000080108204c802440c20b0b0654425072240c0d46140c1d10715a54004800e801c0c01414101c02d07100450100003080d4041000f041079092054900703114090001c500c04820182e01124141c20003001c000d1903040a107521b11005c002131400b40241d25820305003601d072a01031034024 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 963244496 1250 963243246 963243269
    0x50c04031b080c06181008011a07022b0f050d030e03090904030311040305100e0d020a0b010e07051b0606030d020a0b01030209090102040e090d1808061f0b0f0c0c011107 74
    0x188845c1c0d548289061a20780140c003c88107000d491000401e40f0509004081915002510300c081c030180000035600b8044c0d01070007a1010078505502c03442c45041c0952522a1400616200c000040c42040b0410707055114100921318103504240c0034040d9032004200a01903881440070112540d1b5504c00190401d816050000e0452101140126a0b11540c2c10281440c401c1810845002c90305601c02d20652882100351a07030f54140d900700320303164800c1c1d450141580c891040188201c0c2c0e01c1c114141c0d00038109080c821f240001c041d51064a04400c185401c00c10f130858401c100e4a41010700c0706000110991021340520601940e50039454581808064004c8942030300242803031000b5811140607103011100e0480d1072a050620642d07406800e4001800940012880118000240c0c03401c01901d0026000d000c041c0c0d14030b080302e02042035a218900084440d580f0014444030100c0003000d115041010f1a50344042039885c540c942688043d10300d0400000300111440c20002003407003420b4444418a1 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 963245746 1250 963244496 963244507
    0xf0306050108131211330c03070509130c0c111504140301110c0a050d0201020319090312061409010509130b0a29030d021609110d050c04031b080c06 65
    0x403034217100f07485640807251180e058000380440c94518552503400f0024004500c05103408200200d00e81c003503c001403002400d0000c901c402d4042c20160070002406040e1141e0140740e101c0302c400750f0b10140c0c07008022420132104007060101e5411104100501910100000183c0c04512901446070388910b607102e181100ca01d000641d421341110b00405c1c000c0720940c2c0c031006205542a19100d08400442c1ca9205101c0b1007004240103009503489298034030388200c16603403000750300f80c094044040203c3c100000f80c03101e11050344d060312036500980017005403104000b003680240700403010181c0041c1d21a03d4900104051101005005102c1070303480f008902d918ac132500301c6c8001400e46441d442c10000c442e80d91501000c081440b1220707901508604940854841d41c1c0181d8841710582c1c0f6000081c11600414406490380750090030a20510941c0300b403804440c0940c8804550058500c41caa44400090802c18446800c405219071880843c905881514080707101303036500e81052000380508408220b = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 963246996 1250 963245746 963245783
    0x3260d0f02070f0606170606030705041a0a142409041e050a0209100c0f0b092805070501020d2a0f0b042006031f050604060f030605010813 61
    0x140c4030b94561200da00d50203254140b4000c40a0f100d50f01402c80c50300304101480400d0040020340d0780c040c800c0540642441402c1005200203449a6402d01501200d000d121915039180c012042004040803600c401008018404100f14400342449660200521403200c003c00010b48044800481084400103188640300000c1c0d9520240d41c031181040d94682802c22801d413031560010142c12804441484039142c4400c030540d42010000d001400c10301041d44000300054200c00750782d40101c01c0340d00f1580702c2070780100b0003012142d01032050541d03203015684102c10008100003c502a09090006d003030b1103000d040009000000c060004402e8040312404001c207003040403481030b07801c1e8101500c4a080040740c1001745d402d82c0b060f034044800700a40c908104c0e00407031583c10a002c1500c010400c43c51901e420204070f621441c01028500c4031130b040400040c03030b40c0d44e071070043c4010121602d607122120008034014048410f41d81c03041741849a1041013280c3c004414540c4c1c011580d2100780071880c800803a4 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 963248246 1250 963246996 963247001
    0x50a060302100c020901090509030a030506030c0d05010b1c03170408070f05061807060e010c020415030c0611030f03040807151a09060a0e04020d0501180c03260d0f 72
    0x2480a9042088038040d00c080d5684800e240300030031300a9428a251b640d9503030f5544111202102d41502c41d8106001e0108001e00c031fa003000703800c500e0041c22901c10410200008072000c007210011980e5a54814500c0b1507418581c1840c1e910810032a0071400841c0c1c0341c0c401601c19001c1c81605e18040000800280030820a541030b9100381e40c000c1c1e654070850805181141e520074003641c0c142d01d45024900211441e1000160440c04e80741d5654443c480c8800c00c41c015500318103a50000c0b644035884144440c8000e0f00c00850303a00550040c9800310500c0e00c0e20501405135400ca2540c2d9069420802c440c0130345004007000c80e50003950140700700f030b51141103040071640140d1800c00840700505090380d0808030508140c52410180048480442a880c0c10040021060070391142c00c0240c030210000a01610300070b000e070304100d40202d0010600318070300048816903581291048540c000700d03540074401c0c049843c1d90804c60022056074030084440075036005182e40151001c0660090b1030321020400300d201c98 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 963249496 1250 963248246 963248249
    0x910030f030e0f0d050d050703030207050303090a140304060e130e0708010203010f08010b0a03060908070f03031a030a0b010e090f0f0309040b060f040b0a0311030a1b020a05030d050a06 81
    0xc18050324521549001000b601d0100807940c071030011485101d00c0c078501000751341c803400ea1003002014a0f01e216401079841e03030020f080035001d140c7d00b4000c100c0480c0040c0000d40c03291080300050b003100c0e0824644a480030345000c5074128560703c28070003400703001c0d004607400e91080300c01c031180c0300c80103020f58122002c2c0a038a8642d13020790141440010f002501500598185e8041c001c08030006034a03203400600326182d0400b201e5202e1951101000403800d02d6000000f418040d56582d40b9205007070300c0b00c5543c94041030041300040e0741c40b80d4000c1818401c0e65404a0001c04038042c2c000300001c1e03143c0030880c10040c010002c1c0d6400c01804503045003003c0002055000e01031080d01c84400031889150b45a800441845010354101004e90740711f441c20720101c0309031886040d5641e04040c206a0150006e811080030b200501d9a24038840035503821400280d0701c59424120b01184205103040c2500303481c50250300c00700a640c4820b40c11400a9400b20640702080b04030000040e442c1d84404035680548180e = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 963250746 1250 963249496 963249503
    0xa1401271223011b03140a050714040f2c150406050d11100306050a0b0901140d240b070b150904050d090e070504050d0317241e091003 59
    0x29205071000d00302c190013021051080e00008126484900d400381c0680d04226440002112544c0000359501e03000d40c4040d0700701c855860110b441d06098101c0140540c4181c00598444a00d90400c002e5400c0f803801d102401c0c0e91234140241400215541030881060161451001d03030391041d00c00540b0380780c035072000e40200300c01890300d45440c0c42c0b81000300313080441c8010340d40241d1900d8800c0c048603019024050072170301c020300750501c594900006c552a640003110070760b040014400c8610440da80c410003070092003405507000102240f0300c81480e400e08095081003070034541080403c01088904e10152040d403904030040c0300056031086180501841c140001941c00301901d400d01090007070004a02003822070680760a1a003c0c0c484680743c44c4200c0803030b45600000e80801c42445203040603100d41003502e1082c02c1c050703151250104001800c0f030702290174610010031420000411400d40041c2c40302c0240540d11026001c00030403c0d0942d402e1920900da00584003d4080f81d80048042005c81c003c540 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 963251996 1250 963250746 963250793
    0x50304060b0303160302010f140105010c142d1f0207021912230604060e03090a08011e1107060c20010c0305090f1e0c0a14012712 57
    0xc2c1c0d0704076104c40c203000c0005600642c81c0040650800b80d00f842500c9c045420700c4140b10007a882c05004684070311104404071641030006185080191040000807036070840f40419071900f2201e001c02041c14101000c903444903900c0b601c85d06140e6480c50203800c1d0b020514410240c1d441c074980c00410b03420441a070312141034250640300060144e507420039201e6054400c091003880004558034900045010622103000e90f0001408200041c200303a00581c0c950591a0a49040003141000540105c807554010400c03070351161b410a480903081d0183c042140f201613030400084504407425181401000d0000703000b2580c2c0c2d140b071380c402030040c130041c51108811100c0c960445203100199000c2e03c100c9424002107814075020607248200403582c0c144545810b402842c001e00003102d402105a0044e42c107504030700807142c0720708964440d482d190002d000d040700e07148000700c981c200041030f45092490030340b1001c1c0e00d0408000c40d4003444100d98226105010b042080800a05006034105a94040300800c8017 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 963253246 1250 963251996 963252007
    0x618120825090b0c06100f180216140609120412110102071208090405010f12060902150409140609041e060f05130c0b0f041e0503030705030d0f0c05030403050304060b0303 75
    0x4400217603c45c4910b450001541c2516a03861035000160030174045c491500c410f4144042207134145038084c0500340484603801d44030003400e4481013910441d13240d11303900340e400100070462414000c2056010780403c1c20391241c9840d09c0c14020f0710702121110f60041462494002d5034155030f1080242c400501075290212150702513620304806d9546c4031078403071030066040c84000501c1e5131224070780208a440901501404001d5070380c0f244000c02d003510080340d224400c040c2c8032020780f03440c001400203420302000000d004c01c4000d0190b10a4070008000724814001c210030800007c0700c410b604022462104100e0703c800c2c0803458907101620810184002884c81c000400a003058004403008003075014a500100c00d54444041d90210f204071002c1d02c650b00710808c401c0017401c0c00c0e0303418901400001144842d09548800c00a03040da80a450241c50350b500c045056140802c0501c10110316050301e0134204155000130001600c03c0c040280007030140100440004c05101d00741d0002000080e008007503a0f9500b = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 963254496 1250 963253246 963253267
    0x20d0804050a120c110405040f24020d090b100b0702060a030e1b0f0f09060d0204090203010525080105010f030e01090203070605030717240d0618120825090b 69
    0x1000140380075500310002c40038078080390034503207c1d03280280c0d0040d1030b0010a039441c0d22030300300f031000c5901106d41140c4012244955014244094180740103003000100d200c031080c2c18400465280034181d206559100b1400304403200c9000119078501d9415600305d40c030b500e81010154000c090507010f1003074501a06480b1081100da14100180340c1c001201c00004000b00b41d001c0c8020580c00881e01904000a13401140030340c500381403038083c00c52000f4804510b405050b4042420346005480d80e1450200408010042c1d00c03c002606201c206585403100c840d41c50704000920001203040084145a034031a8002da22620a411600309541c0240482d03240c26910100149241d004071003c200180b075200d8070520305603005450b032b409220403100802d5001c003c000b140c40a04905805294401c403102d0b44200010000e00481c080b1700c040ea481c9180410721400d004443d5071004d0407090401c4442170400c41610b4800f016982c55403910f0011a01d5600310070026500c0c0ea40907080142e080c0004500718880 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 963255746 1250 963254496 963254507
    0x7021603030e12012c03300f09060601031524020c030c03030405121608210c100533041a150d060b04080109031806020d0804050a12 58
    0x3001029540180c512060f10031107030032205404007411200d4401d002c41a50403000c4001624010180420f50745032543c03031861104c070000b070f03195185841d0240c0d0700e140004408890303040b42e00c860f01000440e1286080d20140317403275070030080890f41403550780d4201c00343e03a032088481c0b0b402030012030f0409501401503040c443c2d940039220603d40700522610181c40f14900300800d101601c4400600110300303141c140410802d151840442200300c91068800c000141c5078200130141c010303e0404003410818410900c1c845080401c0f1801e448003a0080001c038041d440c00050400b011011010300240c0c2e5120407220080708545036001d14880f0301514100108803d4106000100100c1103404000000c103140807408034004040f0610303400101e01c160340700c1c41a07042d001400d180c3c96070440012020703241e1402070303600d400c650400c2d41d045e990b40f1071200403d034209200086031075074101340203003440c50000b0080d5039280003807001d030403c41e080340401c0c1080b10800882c2220380c1d12141c56004070740603060007001d = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 963256996 1250 963255746 963255767
    0x50712111e040c09050a09050408090d0c0801140402090115090506031501030b030724050c100b010806190b090103020705030d0c090905011404090f05060411011202041d0702160303 79
    0x890751801502c110214040e80e04d00040b100041c1a01c010305143c41c10a02c0103040042c1f09a6000000700003001c4c4aa40d1494000c00c014441d00d802800035081c000780b41d0848561403002180300794100706000150f95008031460455580c02c4540d150500c00c5403089842100991166030040e00c04400c1c4095412501c040e0301e44010284d8003008070304101c5082640d070308002c0c45090b551619540110008107800c480c03030b102198480c01c02602d0b162070590301034500401700744000c500540d2184030005035a030103001c0782d03004001100d4504803034a0f440512038040219204010035000001607091103a4083d4040d110400d800a00790b0fa01d40f0341429400d0040e14220302610700151085101240c80305e01803181c181170b0303506009080c034244c0c01b24050000038101d81100303868410b1f128600b40c0008404000f001c3c030607441103541c143c440c070381c0b40000f4218080c0b0606e0b0106041c014030040c4000d100a008100419840400240700c0c0d441d4000b0036401c0400050b80141c500d25600c20210a15800041c10314 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 963258246 1250 963256996 963256999
    0x60e130303020c070f080d08041104051819060b040b0a2312060406110f071113020a034110030b0a02030f07030e210d060e0105040c02010603050712111e 67
    0x1040307c4041d00084520300000c45006040d0400500d00c0480d40c181079100c1e5511001d00140f040d200100e0120b594500012101c0492594400540040c00c1264601a580c1c800d20140c5050000c04a01c000140c601202409400780144a4030024807181b148050000790402002e072520200401c4100c04170303100e100c1214151103003400d107150070041034080c50407294500b44d070340070041c1030859031307a590181d4032408441c26611000842c0c1c1c00440f10141e00c020202c2c0041a01c002800e600e0b03040e4000841002450745010004148002104090840700094103800945001c4026595a81c0500303240e4103054002901d50300f00c0700200140d9403101e500071401402c52101c20140c0d507480d5a8110300392081c5c010840507a0700038035950040ea01c2089440a82405268502c1e41404801c4030b2090484404e64400d03078145407240010006030502c0d11442c01058201d03c024080d950030340e1205590364050b8806c4002040300d608a0708144880d0f0745400072a600c005060000052811790003803901d6040700c4505 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 963259496 1250 963258246 963258253
    0x2040f080307020a03141c053106141603020718110f0a030b03300c1c03150909020423070c0203100501080304030c09060e130303020c070f08 62
    0x812000300000c140c0759000c0e40101040d0700141169940c0c10801c0b00b0702100d5400d4440d07440114913101c03422856005802d01035660588641515454a5801c4c100004111a0010344a51810018100b9020409540e483d050191811410210031381141c0b1507204500780d01d13050404000c0030182d02181d44801c44450398402d0050a0303258028008840881d54102c0780c00204020083c0c031f600804d0060070080b102ca090001d401500301c40800d0070324801c07203030440035411400515150501612003104000940c010201e0901c191b4041190391000d0051054982451241d090303000e440c403a401c00744402c075400112012144e51450210040d04140400302e03c41c0b414011400c10405880720360309402d40c80710541615949402c030303050b01e0019441b0300a076054015000004442112130240500074070440340250303580c514604204400401c1c5800c14144035060000811210043d10604c0d070708038030407410b00620900e0f203203002d40091240345000515805100d000003045d68031481d11000721448107003503 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 963260746 1250 963259496 963259499
    0x1110a0305040612060518040f0f1511030405030d091e05160602010b030607140c031603110604030e0603060a1d100b070803010b070f0b0916120206091e1302040f 71
    0x400f050b12818002c0f903130884a002c018039208207034a0090744d04580127500c6d002d02c0a0141c0c450000d0186e2001c4c068071415003054140c02001c41038841d40b11941c10244038181103081c03e42c0e40503220301c15400b140d00802e40340c0c1401000c4c80081c4c2903103d640141c0468040d903558507440e11035114000809002c0c0304030f5541d00009102e600602406009640040141466982e0041c069a1042128000c100031041c14011441c00c0c04040009000072004204101014101490028072030358904550204582010301032000180d0001400180400c00710390700c0351659a408040b90340040c0941c40032150340c4a100300545c0c05030f0550300c01030190751060304000d1940e03110000001d25108030388009048071020070041052a0010015003d032038800c021740c0c00e03020f4032a164248030701d03420b07110b5041a80140070424000d4400000b0400103141400b81d03c6890b1685400141190150350342560088003001c1e10030381408121402290480e0004001c401e580c1d40180c10350b4000d42180c0503134034000f00700210 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 963261996 1250 963260746 963260777
    0x1020f0604051b0604030b042a06080108070b0408100203151c03120203150111100507180906050f1201060905010b0703120e061305030702030304030b0a0c0c15020901110a03050406 79
    0x1722000d5a404c050b2046142d03c0e10ba454821400100035580c5012100401c11103140084d00c1e0300000828883e075503c505941015407081c1020020741c4201c010030f008020400c4082e00109010400c03003c0d51400507102e42d103840b91003c61070051195540d1285100b04884182c403049403103030100318000c0d51a1040804030010f0b810483c80113440301484001c048074038448039031054403100d410710000c10aa81c0c405003001c04501c240c1d1800e45e40303040816444280e1b800700301c840e0b40926000f0a850301e014800d02d86000d0100c1c9003080201071080c02003000c40201c41164100f504503038018440503100304951742c1d51704180081c07030304070307013400c50006484820741c481910040c05070403111070200018014035100c000c400b442004079403800322000d0005010f501c01594051003d00025405040c101d103491400b061150b08035043d07142180c0c140130705116104041405800b22107a80c405012005980d01884e0300103a41072110b040216049103d40700030f07442090b40c02800f50088440c40e40fa0038204200058 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 963263246 1250 963261996 963262009
    0x50d06050613140f010905040b0d08181201150302130e070312020111041a03061503012309040b0403080c131706090712080f0c030310030210020703020a1401020f0604051b 75
    0x4c00c0d1070b00049512809018600d096804060b1035500100709c46c0300202140d54406075904030418643d400c1e0382404024031a41080081021004082c600810403513032442000c10a04010b804042c0c020f14000c0c0d03002010b03804130b41c401c9855000c1e03041141c0585aa074a030000c8110245900800107500f00440d4a11141c002c800744c0b01660080544580c084081142c00708042d0030040401d039006128040080701042500005d5000e4031905000302000034499003034591040c0307a9078981340108660000c001c0410444170101c0d421540c185000d107410303100d01c90b240c0d0b02c601132040104015201032000017110400c9036107128a20301c841d0706031351903503030750580482d1070b03682070700c109001541012801030000b120304000f072400c1c940303145509003400c000c5400586582c2044401c0002d0f910b500c41e0600c00d500c1c00c0781600d040c403103081c07005121080c02c644c08901ea4600d41c3c03240c015405080707000b900582e1b0080c031103030700040c05420803034040d85400c2c201180e640c5581803484038060040d031405001400c5c0712 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 963264496 1250 963263246 963263269
    0x7080411120f0a050c0a0b0712022a0a1a0a0c02040e0d03020319060e0109020a231b0705210a050105041b060804080f090d0209091b0a080c01050d0605061314 69
    0x4071f03185c1089441c0d02c1e200000c0c400384080d00214014443e030500201009880d01081c4540c1d803030300944d08a101d2003400927100f4203130040c0686004c10954015881040e10031550390042900d071030b018001c02c82c030108014100c00000d142075030041c014032440c921b91560185120710201c15504a582d070606510400711420b50054000787c2101e0401072001c14a10f4000f0122611186446019407200000190041c90060741000c0d09800024015190004805002c0b03000c02d90769002c0c158aa14000000c1d054118401d01044002c104940300d061012007881000520350b0400c00901241c80c0c2450034038040382d40300c940341c94104140000494528030410415115950281940d0725200c80c40b0a001c003183c2110100315800f007e4000d581d001038031059000750185508030010301e0002c040f8000d0480c2200b0544616018805056080103440c20005485c03011354030070b003865581e0f081c40380c0b20800a020160031642e048a00002c08450302d80c0820b483c40110b96001c00c007a451400004100103804107031 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 963265746 1250 963264496 963264509
    0x1110c06010501050f12040b1f0e16020703060c08060102070e01060e0904050f0106180b01020a0809060309100213090e01091a10030506131a07080411120f0a050c0a 72
    0x100380103001c41e5015200415107851050400c0b070800d111100081002502210200c5490510600303000b050701030351400042800c0760102800517142854401c040d4920018040007003c0070100200078210700134403501000c4c54220a040c001c2d00c8055401800b032030303000e844890043c400c4010000c0c00390a2040d181d030585803140c2e100880c0354407800070010314010180040e1403500946802c001110000d102d64001071054041250098840600303020494180310a42815500a121024005804241111846001141c1c041d40f2921291140743c544010301540c80550381c80001d03144410002c241c6614111098004148800c1c41380101a50988a54910041c48000d0044010300065681002c0a521100e40c0d10f19180007070b0b99407191854440c00f9200d411500980c862510300384402c02145200c0743d00b140442403001d060088004080030001000074201800a2960b08800d541d000d0b00041101400e400f111003c001e08084103859210640d8101c40d107200744171071402e542c1042012a003c4448 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 963266996 1250 963265746 963265753
    0x12090605040c050a21080c0607020709050c090a0905070201020702100e03062401140d020a03060e011d15013606030b0d03030e07030b040b0906070206040c120213020a0201020a0201110c 81
    0x100101c282529a0340044106d49560b410701000000702801c11420344914610f49c020302000b0302e0402c0400c2210780c0940741080b840790170085c121041d1100d9810104561001000094994035424101d0090048620095001043c1107051954a500c010340d40350018084042e1200d645440c0b801c80315255040c807100981252417030640c0240c1d80551000f40c1c001500410480c030300820510418200c0c0d00030f007030610110750366210a10000d9080c0100c43d01400820381c00080c8056503c5c5410302c9081d00414455146017800581d401991107032140c250400c0714080c8840314200c0712800400760303404440005240c0e00001500281c400c1c424061400a0a00504016010840b50710200d01404414095010360301c2082800400030341412029071240c1d008a60728801d030f04107c10030728100000584200110752210051001060800100c08111941903414690f070300100e10110b40400c0b0f800140940700761010500315109034064000b08950442580201700803818003046c42c016004d40d0440c0c0200e40c2c07 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 963268246 1250 963266996 963267029
    0xf121704030503061305090f010f06261f02031801060e1602011d030a0f020102091c06141503070f3501090305090f042a12090605040c050a 61
    0xd00442c021908408050440301030060902c141001380c60007501c0140b031960095902001c030000a02c10b00150713041c0c01006004042c0b030180008444902e281d00c041850b814080c2c030b0a0703071750410007064004a82503d1014401c3d40e0764202d02000b904115404050000f03000408d550310343e01131141e58142d5100034012405a01c0306118030580041d00759000302559079074100154a0b030b00320b48142c000580243c0055540712802003004000d03c0e0b914800806681c014003d044180e0348091b11300001c1034011307030003246440d481c1c24007a002e42050810b4001d000c01a400b400f91102c40561102c500311410303022206030580d9040c0e5941329030300311300c100c86050031281c0050251450030300d44207881c440703151a04800c400d82c501d046400c49481040440c003007400014913a9840c00d046c0c1e001a040c540c03c40d82000000a00c10704107a013010b610511041c43c44070b5105041010b03000d2140e1030140d00e90701c00100310344040d5107490030045c8820742e03064520b8038040300000b40c02e00c1c00881103425121512464a08072 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 963269496 1250 963268246 963268253
    0x605061606052703311406070b0403090819021509040e070906090605060a230409110c100b0a061d0904060c081b090f1206040f121704 59
    0x3408060521030307041003c0d201c49104000451503107048802c1e40f1010750b60320900d0480c2d0203403011058988410210441900c1070b5485080c40c0c50034202c401d2240c140d1007198042c000201d440c442c8401c020007004044090100340743d8400f0b01a010f41c0d03512011290782e58644010546d42d200311581c020340c05403100060308080c00e80c10028003403007440940041001001080f1250a20800f42c1040e02c4007a80c45104120010403401044024403040d5400d0b031500040d00c03001000c0342c02e00202c0058440f521285000441e40d09002c0700c00600202000f0012021000070b168190b5021f081c4c0d100540c400d5040d11540d4400510a41e4115040100328881081c03030180190340c603440311000c44080808040c6501c0258840d45052446944107050000c3e044511090160880f02d018000c0c6611907020f06001040c1c40c0514205c541d200000c0701d00c403428100c0c84000445010406488280500498061000304001404a00500c0e44190303e96000103c081070b0494400c8441018484000400008500070 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 963270746 1250 963269496 963269501
    0x160b34030e03031e120a1a190b041205120a05120c0909040303050103142e02040302060403060e120903073003091505030c0901030e070f03150605061606 67
    0x7942800340940703061a100341002540c0328885403142d01e4070040020010700d08010804d503954000303114134040249200040301e0801d0032072568030041c000d10340311801c0c2c403040701ca0340d0f240300007490041da000d0354031511003401000d0b0050050f011a46482801c00e000400407c81081d030741514401d6030743d1410305001d914081c0d42c0341e1000d004940c42d54002c001c1085661074901c0100d104034002c0c1c0b804541545589003444d40c40e803000071800c0c038a4010218207490881031340e00b002c800e00c290780303041d007070710110114041d000744560f9100a500c2640001c0c0003080107416081180442c581000707031030110700f040000c900c942c81910340d1242e264011b6902844010722441c08241884283c07460380034051402c14414417900401d070070503404241803010400103440c0320b1452040f50015490400d007036080c04803021004c1e018040e480b5047c180c0b55a05001864003c019901c001c1500012a03227010b50349040000b0480c241c5c00d0300030030b444d08240c80403806007886d000f20782d05a564561b01c3c0203130003010b8460b03900 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 963271996 1250 963270746 963270767
    0x3050a0207450212010e01140135130501141003080d020417060f1f032307062c0f04050a020d0920090702150405160b3403 54
    0x48500c00000d20141c41c0403c0c030160145038609503001c0c00342d5040c01c1004000f0131050b03010450440d200302d603280b00b030f03684200303020980840f942a10104040030106410845a251450164042c03c4000c000c0c220a64030041801c0c83e000c2c20082010340005032003100701200440391a068109000c1e010400a01108014030503000729440c014240b980fa0144100c115148205444159012005000130315540c2c0f08000d82101e08a540d4225805040000e010190000d21001d8541c18042c0400340540da1009100901c4203107000a81d1a03085c1c41319009003628041907065400e5048807011058101d10440c0b524600d500001e005031201042038003000050080140006080c54091100e0703000c0d26560300808086a11503c421409150548140c0da03403540c250780901e21548407901441110764001c5500d410300040108208030560761400c101d0702d800ea1401024120b248410303c0040c001c105000a4618a05419039007406035890a511111300e5501c40252000090300c2944200042c0c013030f506540c0c = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 963273246 1250 963271996 963272099
    0x507080f0412060b06090f09091002070318270f0e12071a1003261911280c0510200a050303061e0d03050a0207 49
    0x28a804280003a0040d540c20951000c100407103040e2460040010500428050040594145080200c0800003901c43e03800c2e0380255000e0483c0b6400300e450b80d0014440d416902440d41c1c070540d0b41d040507207001403881d2500300c10200c118454240100d03200d4a61960b0020303084000c0619484d441e0035502c00e100509600501c42d03815941c440c0c90b02d00351724042c045491418680840191102980e00b0140c0d408070144080c4ac030100e01010403c8200144d01c14020300341c90700107040380303510f202075201c84440a80e502d924011016000c04c14150f11400c18080300c1c10401160f071000382250000c240703241da0f984440a006000d080c4d00d929400d000031282c60116010740202074018020790b4031000b107840003c03003640304000120120300d40c1c5000e500684140300350008400040c4042800e60321003588074040642140d10800012100c00c25806a0300c103034110307076600281560420015407070040c1c003640c00504103031301600840d400046c54020300c04c004111885040d100d0b007018140241442c104003407084410 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 963274496 1250 963273246 963273263
    0x3110c3607051c110a0f022b020f0a080f07030909021305040615020a1b05120d0806030a1e0f02041d0c010c05070302060304031419030b040b060a08060a0b28110601060507 75
    0xe644403000208e00040805556008010400160b18005c0c206121100c2e0078a1940c412408413001490680880352101d120100b480d0f250f50003483d013201d201c411613004005042c00880c101030000d5520304040b04550089508000072641c80114803900300c000714071040540c000c255840041000f000407403001786500329403104c3d03182d12180041d100042c0c0300510a813540c8404240307407a00c0d401000e410781016003200140002c11070350b9184200064054081a28030f085101a4010450700003601000e40341d00400501940e00e04d880700e403060002403003242c196441011003a0407954000d00d00e180f0320540103409048402d01750b40038008039a0003d042102005191041ca80410401402800074075040c5103d83c500b40305504030040581d01440d03070980c419032400811103960390300d20301200c81400940c02c044510b643c81c8400140c800f900340d48854200200050740729216078440080c03280c2008110b1010030507101201d003c444043d140800180a540020010321007240520080c2000b40e02c0388080 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 963275746 1250 963274496 963274513
    0x60f0929040510030207060c05120412140c0c0a050f031207080702061b060718060804020f0306091501091a190f0605030403110c3607051c110a0f02 65
    0x7040f0100000950074000a901250b0038081204a020394041c07803415191031420445c1da0282500d4a9801034030080105400c06142c032600740c0680102c01d505040642c0340c9440c1d0300507000140c3c4030031903481101d21980c98010042440c1c0360070f002c0d1868121015008081e460010086003116034081c41017a120500c2c1840b603440140d90340002003001d15029120078491411801d4894902000a03114030309002d21402460100710205285004440c010306c0d04c00c086840f43c0c004504000c80e00d00740c2c107400d030240300100036440c1d00014440c0e503407811580600000baa038901071401101c2c854a1500521b403150101803140d49004140d00c0003103021010758400d204d80e5015030b0311303091886074486804210f0100422080c5034000b03103903034035009038100500f240f040c3c200001140b04d0317681d11444501d10812401480100e103010b0b021501d1070601c44030f94216040c00e0b0005441908400c00c20007101c6100004d10280324054003071441c0001c104e00d45076082520200c02540c006041d004064218800d6254 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 963276996 1250 963275746 963275749
    0x102010612050705010807030e100c11070603020a0f0e0d0f02010909020301090b0111150103121404080703022e050d0207080a030c03051305030301150905090103060204060f09290405 80
    0x25038154402c20041c4145458040007415403d0018006800c0c540381005805105c07102040326011401c101c0d50000306030460010589407416180c010500304d1168540100300035416a00500c076055558a40107120700e1015002c640080302490038070303000001100c0d580000b49100b10284c042e1407050415807a519190300310102260800da10040841c1e45a869440c0c407540c0001c00301e000700807041c019046006034908002140c4c10184001860380035900810101c0910521507160880c40c680a9a40e0711591313400269038034006070006034450f48190350000340b0100d000400c10013070050794181580c0000b0344542902e2540000541ca810b5540800039030700040c0c5403200a041c2039120380c0303000031854040305004044580042029011078100e117102c0000c100300100303170703811501d5100e407014007010403c0c41100d001d00035501140d00310001c400003004202c1e50303030080c0054030503c0d69100d6074100915411541581d15100b0100302011201c21802140445090420ae261030320040d60702d0666034a0 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 963278246 1250 963276996 963277019
    0x4020405030a030905100302030c0a120f091109060603090d18090e011d030310090b0a0503060106020703030f050a0e190b0a0914040204081509210d0507140d0b01020106 74
    0xb1400203800000c03d001c0c506d400c0e261850800d4583c501141580f0f0000d0004081d40301c1c40e144202400b052100b480748440f0103030040205540d80a02c01d201d10b1a403481e1460901160300780d0a80b007803425000050003400c02e80d058030700c105a400020710091a0340b003020303142c81e41005030600c20460b0341c0101141d400d10b24000d4002496100000060500c420590101c02c60409200d0044c503400400c140300c0940303100c10402050301d200c2000024440360031380c0003505140071980400d815008072400000d806402048010480380a500c86011400483c00212081d01c100c809180c049800001d40c110181050b40114130030f800b482104414207911481e812085030441d9840c200060901801400142d42a4010541c0c824041d6410b50500f401c02136240d807580101c068101950b0314003c0019140402007188800ca44441000700744104441d4025204030303800003484450050406001c03420b0544950001070741b03040703001005414000816a0480075044c500310b4641150340390072001c1000c00991 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 963279496 1250 963278246 963278263
    0xf1507030201231f0e010f06180305250f0f15030204050108220501050a0506130b0306040305030c040e0a1406011b0204050a020405130b09220206280c02190803070803060402040503 79
    0x86458019882c0c404010040c8040012703041d5240d40d13000042001030300000f43d51462600c00c000304000c651541c5102d2044d0341c0e044e0f100300002410300400142d2800f002c1c507014248e50741f10300002440c800c4100e040d401e0748201d100e01c0c0e00294000e00001c030580c2541c4410906400cc42250320162542501c0c0c042c255001a11081d044640c0c80043c4910391070883c44da41d002d14241e510034440d1404010010361200b10041c0080d042c00300010008001714104c1c01200d020300f5002c0c00c3c108060403d160300308014203106104d214411082c7c0003142407136004101e49060340c5c540740b0804c82d0000c041d500740400303488003505102c441c0344c090001146955a03c1c1714400448560f017400110781c1000d000f00500c0d02d401130000c0040e0701e038808105aa510300419174501c29078040e6501c660782c0340d401071441065904000030319405c07400900c90b58003440d03118040f841d104d03008880505c94030018401c0c803c0412124420100a0741c003c00507940001c0c0420051984010020001810503640710003013420072411 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 963280746 1250 963279496 963279509
    0x6210602030c3106020f1213030503030907090b0618040b031c0c0203070608090a081321021207080d0309110d0803091c050f0304020f1507030201231f0e01 68
    0x1c28101c98000700141c030f88000070805440100054039070391906540383c1071703110050302145100158080214500100300001583c3c8141125903a10380000361540361a258059070780d100e410070484800030b00e04135040d04d03c0b211450361904410950303241004010007854082540601601d6420340102c1d0b004070342180802101d0311042a07054091041508005250b040310040c00120820b0151000000424402c0c00380e00406443e81e40c87c10030b4641c40403145550014102c0c01c103504100c0b40f18202c1d1402182554400d0340c10b4042010402d00c0941c03102218090b400076644460501d605141c400d8024130841805002d20b4182c180c48500450b0044c0152601607408440000611076242010040d0b41000008000140700039982e4000041c0981300c0e501040740800c10100c08a025582c800604c074681c0c00d801084007100501c0300c040401c41c3d0300860802d40140d484c0100f1101500641c0270120841194048070a03000d60703416401840b03104651410680c0c1d05120b02010516180300750b04640a17041 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 963281996 1250 963280746 963280807
    0x1110106090b0f180415020c1006080d090e06011206030203070b0307020f2103041e060c3c0c05160e010501052b020c030f090406210602030c 62
    0x100201400f4426000b900450302560110750303418014482c5004407504654040040da090820485041c4003900031400c0b01c102500880f203034960000b035650f110204031101801540d00d08400304405650003005032064081b90550600090001d40c03058150f103101240d8144000761164a82c0c0100385040042d8200304204c030000030900205540402100350b103810040001c0c07070442c0000114201c60311085120a04150000c0301003020003203441900403c0ca225401d211006601605010015001c56110400407518500c43d1268019403104103400c0c840d900021041110414110344110004002e07141081001d14110032000410910500d010b0301c0c403144511409038249000c804c0d541c0b006074442c40c140103040000500c818170b00c0103030340c41c42003c05502883c40000001c0200280c4112058075a0500001504070ba0812060003d410081000e42c0c1c10003c40791907405809041321555030300b80445800c580c2c6200013400c582c0045901000740d0041500300901c102c00c41d00c80311207030900c0416201 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 963283246 1250 963281996 963282011
    0x3010617150c0708070f02010e09070c0201081506070f051218270402010e0301110c01020c07080c060d110d05090c0f090c1806040308040305030310080d09140111010609 74
    0x10308a0100b50001c10908185160071015941c1084500c03600380000e001d40703403c0160406580c00b031081101d400002a0410103503180805004140900c0c56004074003048074800412072210350041c4040c0174200140c0558540030558444201c8014246c03c102c59604c1560801d40304503081d08081d041050b0404031500b60100d0403c02c100c59198500c0d0202650b5141b9049a80d0300052529055042602030a1844200000c1e4000c640948a071822004a58030005000100401c05600501613011050141c0b8a0161291225500c0b6165aa0140d40c8450180700e041c408011039800701150425854001c0c0c03504140e01050400ea4400701d07141e140580001c21450102e09144194402d114421a13440f88140f5040c500c4e1485400703000c20b1141e82c0354000d4980300720350300c8140c101d0f0080c1d90061001c40e21940d40c0d1910039580c0e8011650052904186040002c1c0524001504101c4104c2c6031980c0c4501070901c02c22110300790000100d28100041e90761030342e0440500384160001713000003000104000c0c = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 963284496 1250 963283246 963283273
    0x9060b100c1a0709033815030604080301141516050c030c0a0e0a0e0618011404021f020c04021603180f0902030604021e09030d0503060d120203130f0f09050f06060903010617 76
    0xc1c00d0807d0200e000303403c11010040040c4006048070305440205100c10408540c50010800034000140e8400100c10700044400b250414100c916228510840448450349105410f064940780c91030300d10350304504d003c8801d000c2c940318084400c2d4481c0800400041001c150b80f807461030300301d0541d486081c1e08a4450840d13003100003030249003007002c815501401641402c1e40070619482c0840030003203508050040501c101da02c00c0c07041c1d03030080c00010b2056480360900da0784140c0d034101500c070440204503003c17600041c03519140360740c800b110141003881c481d10f442c0894074000b95000030324044e4050b0b401c02110307103840320800780100816001c0300101d46444c49002490310301181000300200784182441002803550310039200d1186150700c0390200380240c03001e4005914600482c060700f900405000c0002c155042d040b04aa8100e94110b01d00740c1c1c030075566006620465400b5500440d00f2145080003d0039030030309000078504204080d00000c0d03c030f5550401b6500583d28284c015406400480c040d6450 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 963285746 1250 963284496 963284521
    0xc140a0b161d010509040b06070b09011d03030a05180303070804030e0409080d090804030c0311040c03050906040b090c0316090c020d020a030309060b100c1a07090338 73
    0x900241c200a204068100c0341c0b60640c054003031880381003060001d102c504030f490321f400074109440043c24094540d10706180411006004440c2c3d000e1561a2040c03c0024040c8803904032039048420340910300c2c43e110303c04084040c2000810081c11406c4005121b154200c0410083d031051407565640c00b06400d0130b1400038950101648414800e0307041003604004101c500d011565441008100090141d10602d4001c0b240c1c0100d50002d0020341400ca400414007100003202c0c407080303408540070000550794441c15411150140da4074071003a07100c2400140015080805503810688803401c96240c170002d00b000a140002c003d0041350400010101000082c1d143c0c01504480100f50000e4101032440c000000d54550580001508050716881d1201c01d0003490b0303001c418100e0700036000304c01c2c0300710681c2d0150807448c030694121560700c40403040c02244050941224010b2125a0702c041a862031a1174030b44031102d04569407070f10b500c125800c81c41c4c1100c4544000e83c0020180c2818441d0703203030103280c3c07051 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 963286996 1250 963285746 963285781
    0x1060e180601050f07110d1a06010305011a0a090504050c042301020a1b0519140117060111011d01060509010e0108030d02030a022101180e0601060c140a0b 68
    0x2035200c000c5081c44416078010003074480c40b04000510645904681c20a5800506402e454541049500900a0074032060400c00300100c2c01c1201584501d072503040044046030030911800c40080c0f00a2070a10b10030745d0b0000217010802244c0391080340c00e51647d00043c100ca2060303903860080c030000a41006048080d00c654603052044611600b003028240c0000303510781e040e213000184841d480100c00000c1500881d0048084c00024001804907400c0c0030a0300c003500009c0c02400b01240700034002c01119032041c5160015882000b02030341c00d0752209801590400070405003000d240d52a58549182101d4070248020f0300c0480c0c800108000e8a80000e1000703404040c3c201500d40b042d01401400f2900300042160800b003c4000010380e01c3c0c0d00e0a2480000f8054044c1043d200000e083c41c4824000b14141030505031207813140984c0300002540861030480320096030905240d00688010440c46018040b5200c0c0207003e80ca1203d486410304100d1404e240d1441811034010b003aa034248551001e41405417007 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 963288246 1250 963286996 963287029
    0xf0e040f1119080910090311060408040e010b03090a031d0405040807020f01020d09060c030509031f05060303090d2d08120c03042003011509020c19032a080301060e 72
    0x241c9901304460280d80360040030000741645078459020000301032207610f065220705d8020041d52000c0c01d280c03400081c40d40c814420040c1400c01c440012030203141da001282d01600c0014010041e03900da0f40c0d4140c8c1e034440c1214690052092841c070141194036030303000e0a449688100c40d99650303222035104021788014800c02480c11503101881c101c3c841a08009a0010b4a2481c285201641c3c014641129244503941002d501401420b003103e07443d44034200120313102c0d81503c1041c003840c0d8402e010715035a401a60003491f4440c20b0314580d030021402450340542066030000018904204001070b00040c101209421101507500160004040314000041034103c8045a4901d255042540310400e44d403401c1c424900344041d40740550441e90340c09501c02d9100c20403c80002c410981e88aa03c40f00030741020300e4181e154002d10620910300045a02d40d403d9455040e291921000c0340d000e09816416840304030400c42c400810b03240404102e00d00e010754000c0c0f0302a521456080d02c4502406a4403c0392070000 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 963289496 1250 963288246 963288257
    0x90312030636020715112a01110c0303070e0409020a232d06121303090b030f04031803051b0102032503090807060f0e040f1119 56
    0x5100e042180749600811521241690788918076a840a0303103401c0c400301021001c2d600c00205407041002d0311001c0250001018805c021041c8840c030301d80c90f1489041085d052a9100c0390b6001100c071081030300e25845035402c9000040301c1c491a032890200360710900041405900c0402084401c9920080e210030300441568103101e0185a07901181001b0203a00a5580e6000c03906064844144620a00f600f100d00050120148403243c10320992004240f100c4c481d85210380400c0b47e80c143c10140120f40854034007600b1640e940c3d032400a0b000d44166611411001c02c41d405100003141f00241001d5401101c002042801c5814180380280c60003d00b0b200c03119069001d503a003000456000718030b4100341250040388034101c001c6000100c0c210710882c00900100108011060202c182c04100421918826100d514100741c403800300a81d14107031445880000f500d80c0c54660a214852007103000c4d00d145c0a400440c1200a40d104882640d041152910840d01e0200c1c00740d405200c1c07542505c0385000c450420 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 963290746 1250 963289496 963289499
    0x1030303151e030f060207020a0f090e120904151d0a0605010320160501050c0405030c060c0c01261614040815060307330e03030a08090309030a030903120306 69
    0x30522010300b40c4400f0b0030a04002c40741109005a07a0103c030300003580105001c03219074031481d81d20346100c018007454100078541001e000300d0101c00260441054088a81e483c181601641000080d103c014400c54000c260b1400c0003940b060405582c664494006034a50018070304081c0401c100c2c0c1180c3e022504160411514040281140c40c105070460503125120b41d4503946400401c02032407021400074441e40c80c040410206107904405001560030440c140c0701c24140403c1005014000c1810045141d0032945400b54550b0242d09005403040e801c0d5800c00240c41060300000d25203100300d46030b4090100300c0d141110304c607a10510201060702c815500c50304141c1850146543c640d00303403801c42c24100019010039a15a810040d400061038460b01061802d5201450409445030f44850000810b04501030694018080c00c002005044060300131400e1015500c0129200b1202400e8072203907000030490121642c9003441a0809030b030098540c44015480c500c0c0401c00788841030071107810580341100 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 963291996 1250 963290746 963290789
    0x81c021207090e150316091401062c03010b1c03080a0213060e0604090203041b080106050d1b15020f1c02030714010b030d090905090105010b09040f0e03030103030315 73
    0xa0080c1c2004e046051000e44a035940040391520506000d026812048024001840c05640d001184001c2d00300301d094a060340c1c0e440054071341d407013001344070710000000070340d6203410310104002100700280060000c200c00c11100081602c145411075404101c10400380004103064011b455207400010b0780204514244180035520310001c40d50060404001d60351054450f580c2d1880e0646001d0100d844046607a400c192a110200c0000da6601014100d1000e80000381400c041c441e100481c0d201134020f4400000a5580a6481440304641409221503483c0803491042d00c0b102e18a00c00c40783e8005008042c6108142e80c505070784688150045800d902d20f000040d64044103442030607511800040b4011581d819940c050a00d8100e41d541522429261f00302036030303205400740c00301c9860b820204440d40b41c090300706003611024040c1c082211000c100070005400d25030700c40c3c1101841e1500001d0b403814030410342410340d0300031b03402500000c0e00c8840c8250300742c20b1701c8400c00062200c1080c10070010380e20348 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 963293246 1250 963291996 963292019
    0x9080414121b130e0c0a0f21080705070b030a1d070b070c080d05030403030f0b010207031e020603040501050601020c120c010f030605220506060702060304020409081c02120709 77
    0x71000240d00ba0003580c0c0d040343c446a0820000d003580f40814071a02d41300030b6209686070181c501480c410b0903d00f030b00151200080b4546801d552420103d50369000c040160710200010491088520703240070803c00e4042132061040c0c3c400382a011106999074113050250b0350543d800355000500501110003c20701007400040c103081112680040c4a890341c08074200300880c1c2625503c10f120a005841241041507400b0004611461003510108000304003001e619048a44075a6800d0160340142020310200b400b00d0340b9036050031602c540020b01c12089901042480d0002e0b01d00300c0c5c02d03a440d0818402c0d81d68051140312803418040e41c40c25004886561031356510b508140445040c040301015102000b8841d4000780060031018008080340417000c00d001c80048280e02808020501d000e0201d42503103081c40c2241c1415030010106420358613503800304401400d041400700c032410020000604c0c1c0700650035018210070b5081d14010707240e26850940300e45001009000d4001c00001132000d01c02c419844 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 963294496 1250 963293246 963293263
    0x1091d0108071a1c0b1306050a0e0103030813052821050a110307060c020a06110a0f110c1909140c0a120b1c14120a050a0c060908041412 60
    0xd455a0742e44c41007800d07001000f004070112458121038001c610300c201d000c0c25080748044503019240301ca0350954441c00741007856400e000c014001440d11022444411900c0b1303100d0221030041082c1e0b1200b030700802c0300500300f80e66171b5524102c4501c0a0b0211041c03150010442000640d100404544152010401070851083c000399400b4050111009290050b00700240ca40f030070392015007000990321040000c0d5641b0050102190481e0400d100301c0c29030154101502c003140d03000e0326440d06403640188156044c05410b8000b001600c40c4540854031a654040c0100c450513010558400c81401c00d00c0030010341c0d12a42d140d11150b0f04600500800100304402c940409120f8500540001103000506010301501d078070039984540c2d8900c945900302c5011482005452103001420b41d1002160041c6e07480c0c031103641c6085000750060110b400c41078001c00c010400840f40f03141821f03200307030103680e8281143c2c4943c000b61182034021400b400359042c508500341d41606d0031100564075401801207955240c510 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 963295746 1250 963294496 963294517
    0xc030a02040f0323010c0827060c1905040b0306150702150a030f06030f2303030c13060e09220b0906060405010b0c060c030601091d0108071a 62
    0x28440210a40c10768015007855001c5184442c1d50b42040200304c00f400c002200050b1400d1104030014105110345440030520345c07a10303003165481c0d114070030140545011800390401c0c03905c400b402c82c41c0d05020082c405d88107411915143c801440d80c13203000d013a94400d2401801002c00060101c0b09828040d00d6010b08115031003041c02d40da641c0303c01e03050301581400a4100d0002016083c142554001604d0609407176502009461a081000030070344100d8400500035103040404580450045605000640901c0024940054145941c20726581c02290980c66100012400c14610030141c51002e00030803a9180c0b680e05240ba0710001140d03900c01910400301e00b08020502000000420344e2145035640140c4158582c0c54400191074440031f04480c4144164641300020a0a50000d41544c00d0740c0300600080099555503184194107a2000c1c16450511803000c500003100e22000001c105007072040c1c000c03c040755144c0312907180b920049400801c04240800d02c00c0c11114040c10070345d80030700c2e41c = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 963296996 1250 963295746 963295771
    0xf030f18070f150c2f04090314030601020c18010e16050a2a1505010b0408061609150f03060501030b13110403021c171207031d03130e0a0b09 62
    0x1a040003640c411a04d901c00070080016081d0080c00c03c0c01c0501c81e02e410001c0d10886000f080b031508100000ca414400009000c11818002a000d0186881c0510f600910600482c1c809540c040c3c0040c1100c0d031404214894580c0312001804003902e84156140c10415043c01a040301034101e45c090080c1c0102200c540801030182091001e07101c100320021801000301c0040141030607642440d204e00c00c00c0e003242c2a2410304240000a0351007901e401c87e030469103031101521ba1500d030701d01a60340c200d45034199941001075498012075540360703004603112010303495290780302c40085406c4050151441ca83c4080d0605140075032041d02521441d0141c41c15420407080001d20030340c2c5281280704e501458101135048515101040d030259008580d056815000b807000142d42c0c180580194160300c00c4e80488480c11202102007001d09002c0d40050511401c01c03111011018641920396140d9004000c10039400f8480c02c0d0b0802c50448170380c000580102c94110148150301303103400812103002c409003a8172034424 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 963298246 1250 963296996 963297029
    0x114010302132903070507021f0203040b0310050907030e010b1e0d15090609050601081b0d020d12030c0f140712110d12050703021303020103020306060f030f18070f 72
    0x280042042030703d101c250740c0400e403242041da078004d00941004d00100d004005254401c03100b02da032080d14400b0106254011841e01341000c4e03030340c4440e0308094800042100010300128050740c9034100b46101d0182c41d41d000132144e852004507030030364450300711080c02548500319200d81d0343d6840020b100c5645003035800030440030083c0780c80c19172410800d440044051610400008125582e00070b50111402042202c60b0399072520f11150312114401d489546ca5546c5441500305400c0111240b964140000c06083d00c0710764a448880410030b8648a0b100003aa481c05030321b00d115080440c40a203a4003d1a041c05e9402c40c1040c44945880742c81405000704104aa0031040144503901c62501f025141058407440044a003015004543c01052101ea8605050010340038500c44e1007a12902d1400c0d82c1840f110300d00e15001500203600c09803050781c0122041208040c06200302008600540d0030070303034805a074640f08640920f60790071414100b031950032002c1d0421507845202100c2c0b045c2d030200d000c5401703900e = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 963299496 1250 963298246 963298289
    0x2033f070903051213080f0604062016021201060e0a09020423100506090f09040c0b0708130e042f0405090c03010b01020706350f011401030213 63
    0x41c000b940001c00701c1c0f0609a540125040b808040d00702c4030201c6181c100315644440042c0d840b4480d607840785450354442d40002c0c0c041801e03600320280c05200845589400907a00080d620340c0d40c46510f81c007400700d9031609050218101030360440c0d2001c44500003000680c1c24922103021404018103244546d640705c010003030555a80344c4c03000c0021250002a0980030f02006015508810201da600d00190720503600011103051034001c0720b0020340018040d40e00d11084404000d83c06901030000d031030000d00e040001c00c140a0306001414118001c21506448543c1070014100310312050700080c1d07001d00442c05010001d01d01311541c0820110560403a1000750a0902c4003440c1c0c0b01d80c0074044e521a0404007401940701011440b5071101c0320580091044405079001079940740900d10859001540300d51300343c44420154051303009100c4c50060a440c180034036075129000b00d8015109404203601c608010800102e0130b001c00c040e0a042820151304120310560b80c200c074060381d0321511414443c260141805c4 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 963300746 1250 963299496 963299507
    0x60c030e0315040308070306120213050702121809130c0527100302041a0310110408010c1e08010b030105060304030e1f020c01140405041e0c02033f07 66
    0x203480e03088000c2ca006150604000b0314141e02502d01d180030074501007020034160042002400c00c650040d16242d5002c1d4542805401050003c1400c4114007034845c607a80310003090401090340c3d01001c0a50300301c82c000501080401c56025102c810ee0740c00c0d1100c4100015506810342d822075504030791064403080c080c010310395801c681c280466424030405c0200104136400003500700c07d4a0080d201000344000f101c0e070b00d81510707041408459141e4428a80d00d01d0201040c0c10400d01031a0201e404c6050560340e48009094450110002c4040b03002c072505d188440c0070000c1c007000158403514004040f03524005030f90340700c1e12040c02940c2c0151000000101414001c8044084040014061180d1f003e409680310914502001400005000d20700c10341a096103d0301031400000080700c6800c0c581860201000000d0546980c030380d00c800c10485943c2039000c2540302d111041d18040d0059503442c5404136107072805400074101c603240034038049410908148915140c40d09000d41040140e103a407078814003500d1 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 963301996 1250 963300746 963300763
    0x150c03040b03040b01090c050901020619060b041d092103070e12070906060f0e0f01020a02031506010e060421030516030203180402070f113d09060c030e03 68
    0x1c41c032000106010420510226090407280000c50030004a42907120498a0703114142c10726006921070000f04075082c121082c81182010001c1c00043d40306c1c1e41e05007801c2142c0081c0d00c0804494000790b18607150855011142c1c1d400060400078100d0b12099010b07600c201c20060145000b0080c011001070001030164403100042d08005241142d03a1103440c0b40c80e6074a200501901d10050305081001482e24001c41c0940201030250319480d01c1804a0401c0c00ba000c10364228050452182c101c0180260301c042c0a60074010b0b00c1c0e0003070311105242050000d4440b20308081c00f5400345504200c00c00c481c0c41c40780404000c1d0b081c0d4041c0c0340d01345075035802e084455001c0e0f8011803541c400e50b0003d807020190000003c101e03c8032000440010a0721900400080740214100900301083c03e0601c040002c100482c001204407006115461140c2040341c83c20044501c1901240d07031411212001400d82d915500891901d04589070402505003080300080043c0700e100d40040a000a400a402566406010030074 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 963303246 1250 963301996 963302009
    0x6011b060b0604120210030b0a090519050903130e1306020c010908040b0a08100308070305071a0703091407150e0f041109130203040c031e0203060405160602060105150c0304 76
    0xd0b196130301c5005800f5984d2050804038441c070002040103004600038007515035030080c01020710003640e00c0c04080c200a407a0082c094250b0441c03280080340308111505c20540511140b4000f513843e918241000b600414080d002507461045000400041150b1401510010342c2d03c01030141c0c03034103010b016040c090002c900004040020115010410320303081d10142c85e500505943c1e0300d007141c0368201d100340d4041040c00041c0201354100300400119004c0d01c01070024a12618071401c04030310058080f40100020388000c1c00003921482100140721100103121a400d00c1c40c1d019040ba82c0c545021601551064242501888810f1080708210350726220b02905034040030f4030034401d643c0380e00c6404441d0f51207140d04074880e2403683c6040106901c584290382c410350303004007039084031130650300c5603121209016111a080710b1a00100e50041e00c3c02c0c00300034084d9101c0c0c001031854028900c0c0903801c002e401c1d00f00d001198000b400402942d5203201842001d1015104d101c1d41d6007400c104424103501c650781020 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 963304496 1250 963303246 963303259
    0x6110d052803020d1a030705190b0f04090501090e0c1011030c060f090f060406020904061215050a0c09050d02010c0b0c03061804240e07080307050708010506011b060b 73
    0x1155040e80540007003110b10f540e81c204101002030010440c0c10b068000032006d4055009800c01d10603414220341424a9892200c0c0b4103000c180d0b80c10381210070f0f900040c0380b40030341880803800308013130f60041c000c003809440c850742d09010040034a48510b640d01c0b00320004c581f050280d40c03091180d00c0c2c05001c00b001948581c500707480da1603a81136422503850000b07441c1900444202c2000545000740072a40000884d0764001610854460387c94030406500f202901581c495612400082c00c3c640010502050a210302000307900c1407403071465541100d00052001d001d060a00b400300c002a503014800c8000d9900c11280320008110500048500044d10900208030324003080500c4002c02c64100618400d680480f03003950398800320503409603044c509960080c010880101c8100c0109410200c3c038503043e540e50000070745524048005442c25900c1c0c0c0c03020700142c000180103001d0081c18440c4101801d01742c0300a0045080c00720008010419031480c5403512310b84120303000c0030020550050070340340c2c0004140 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 963305746 1250 963304496 963304567
    0x5040809121b030607080103171308010c02070618051c02090f090c040c0504090e12130f08062503020c0a0b0924070522030b060a06110d05 61
    0x50907a1626070b506003a1241071445110001032a0004950744100490394035944640d00e15603400088195403400501c12a400780100c28100902c450200003c190b4640041804901400082d0030883c10307403c83c104000f00700c020b0310940300ca041010421a0001e0714080024030800b03003005c0e11113040c110000d601c11302102c240070203103140302d00d154045e100e004103a620b8082c4110400c81140c600c4081ea8010810a12041008050b15408402e8402001080e50000d090280c0401c50030381c004a1051580c01c071107141070164900340501f800c080c0c00c01c0801403100b400c0042d10b0030b40a2100c1d1048500421045900c6102d44c1d1080c4c040d2140c559010085803a1094a860440c0500100712200354092003003440c000c411030080c016540b5100110140c918a580b40e01000b10f0b50780e80141020b40c10882c9641b81c9160b40e40161110340000d5000e45001c440c181040001c000d21140c0c44d51040017045480c10403408070840204952603e4200307410210741d03490b07025842800140303c0e280d840e18038010b010311 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 963306996 1250 963305746 963305779
    0x501090203071b0c05090c0915190203071e230307120e09040b0709030804080c01180605032d0f0a0b01020706052d030711060a05010506030a05040809 66
    0x1d180038042940710103181600c60b600d41c42621035445806403c0201d01d800800c20350030700c400e40a4004603040316607850001d51902007401610340343c810b420b032030030300184125544a10f9010040208014800780d850200d5589500c078914400441c0000d07a290181803083c208908050500c0080c1c0070001038103200521400d0f4103849401070101034564030f1711800031400d11171095108448030074006103540d07a16100d0751211031003960000c01d003105110001a01101041d8441d010308000c0050a0040c48140c2c40c0c072000402e0703d00d0b82200c2c519a000200c0c0300348a070640100035030b5030050300c03c540640520400540201807038020140802843c00d60030a0100c081e0458100501c6000600d03420701c0440e078140c004903a21405442048002101071203081861506288000c000301009845c00c60388400c3c159800c00036500541e2104046040d203061449010014000f9130780c0011031003410800c41d850140840e0761488028000a03d841d51880050208504042600c070720441c00f0705401e10b045081803 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 963308246 1250 963306996 963307001
    0x9011b0506070f110a0303090201110a0f150608031c0605040603200f01020c010e060c06131214031314070603060e10081e010b0904030f0f0c0c170a06050109 69
    0xe81210010f400c122010a00301d00941203680030402d20001408912220b48013100100341500c4200d0402c208144a442000010003c0d01c403030902600000d0200700b020328010700c04c6100c081036031182c3c6090107410401040d011040d51414a2042e807001c49500130341d103d0700300030030381c603040183c0c424945a404400d001208594040000642c030542045014190402c440c0140c2205003500583c040320120f00c165103c1c1d0500d10b50200080e007010b041181480c2401d00342801165022091240d40c00c0b40c00c00d04c524602c105420144500b01900604010034203100b03e84070003003403800903151010250080104004ca81007801400d00191a482a1165401000340a4502c100c1010740c1c032800100f101e20003000d2101085440042c0101101200d11050588000103001c0d095403e55882c03030844407039200d40d01402d2003144a562491039501491001920449070301d18104d0400c82850a55800201c51041d500e00365452020007241541e203603420386180c4688200010141070900000003003544058 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 963309352 1106 963308246 963308251
    0x1a1b0c03060121141c050c0d0f0215190c0806060412020319030302091003050411150903011a040501050102150a0207110402030415061a0304060209011b0506 69
    0x1c0d00c44403a60f958000200d2605c4d0030400041e20803100b0a18040b400054906003207007080c413017110095441d003010b2541c07014005000c2c1501c0c0c0303c60007004104d56480d01031004010302d10381a0142400d56880901010200382000e04840780c150188103604d1003072001401c0079040510f01001506c444041500580e018000d041402104078900c0d013a04901500a440c0541d03911031110520510922a4240500b01403401c4207000004050700c20103c0401c008407071034540d841002d41d8110f8103105d00e0070095819860402d2803d20b46000b0043c50b86945021542008030f60380c0c4100680c0c030b454485410103807250303c040000e82002c041f58007a01056010b001c103002521140004142280d006490035504800d1808106044000d1806200060000d00c0546100702001d40d00300b021602020300001c2c00140c01207120071859100e06030b1001e01c200c1016944a40e1703180c81c1407594480d01c06 = true := by decide +kernel

theorem cover : BRFrame.Cov 963129496 963309352 := by
  have h0 := BRFrame.cov_init 963129496
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 963129496 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 963129496 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 963129496 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 963129496 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 963129496 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 963129496 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 963129496 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 963129496 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 963129496 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 963129496 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 963129496 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 963129496 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 963129496 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 963129496 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 963129496 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 963129496 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 963129496 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 963129496 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 963129496 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 963129496 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 963129496 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 963129496 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 963129496 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 963129496 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 963129496 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 963129496 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 963129496 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 963129496 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 963129496 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 963129496 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 963129496 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 963129496 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 963129496 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 963129496 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 963129496 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 963129496 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 963129496 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 963129496 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 963129496 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 963129496 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 963129496 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 963129496 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 963129496 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 963129496 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 963129496 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 963129496 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 963129496 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 963129496 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 963129496 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 963129496 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 963129496 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 963129496 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 963129496 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 963129496 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 963129496 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 963129496 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 963129496 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 963129496 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 963129496 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 963129496 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 963129496 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 963129496 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 963129496 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 963129496 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 963129496 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 963129496 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 963129496 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 963129496 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 963129496 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 963129496 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 963129496 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 963129496 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 963129496 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 963129496 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 963129496 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 963129496 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 963129496 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 963129496 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 963129496 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 963129496 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 963129496 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 963129496 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 963129496 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 963129496 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 963129496 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 963129496 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 963129496 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 963129496 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 963129496 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 963129496 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 963129496 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 963129496 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 963129496 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 963129496 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 963129496 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 963129496 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 963129496 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 963129496 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 963129496 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 963129496 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 963129496 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 963129496 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 963129496 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 963129496 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 963129496 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 963129496 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 963129496 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 963129496 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 963129496 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 963129496 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 963129496 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 963129496 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 963129496 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 963129496 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 963129496 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 963129496 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 963129496 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 963129496 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 963129496 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 963129496 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 963129496 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 963129496 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 963129496 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 963129496 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 963129496 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 963129496 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 963129496 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 963129496 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 963129496 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 963129496 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 963129496 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 963129496 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 963129496 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 963129496 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 963129496 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 963129496 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 963129496 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 963129496 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 963129496 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 963129496 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 963129496 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 963129496 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 963129496 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 963129496 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 963129496 ≤ n) (h2 : n < 963309352) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
