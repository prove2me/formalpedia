-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_2418
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T06:39:32.221959+00:00
-- url     : https://prove2.me/submissions/c389bd67-63e7-4b91-8826-081c358e28fc

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 434712230 ≤ n < 434892086 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 434713480 1250 434712230 434712263
    0x5210a0b2808030a12050c0733020c0d0e0105090a0b09030c0904020a030b2a0a03060e060d080705010617030c16031e0507090617160605040302091003 66
    0xc1c41c0408481c5034407010705101550b445001e0340324032404401e0000190060040320b0400d01c0ca900c00c0d41c2014085a0702401d00340355950302d6501501144d24000e4080c00c4814120180382505040496640126015410800c1c407188440d9503081e0615283d040c014042803010355a40f0440a5660340407004020a2940d40e031807a00f038002e540800d0856029004840c1c60b002542441a209402103a01401412501d0310f141c4510303c003440050801a91000104640402c46051079100d00d01003440000b0107684a20350700740a02210807940c054120070501108100e80303640d0f41d80041041a41244103159980158900503004111b035800c103030a05500c0d0811602603080000c0a415900d041004407640780c072151610f850281c4481c030006005c550a105130821640014103c0718070544650101c0f08684d4642008409691054200565002c0782440c1c240c80c2520070080890490f001e2547c0c86645818440300521a200e5030001038021140f12001c80c205084115100d070056411905540655000 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 434714730 1250 434713480 434713519
    0x120e0a142e02150c0a0f0e3a1203020703030f0203010807061827090b25090b0a1407061406090601030509060f1003021906090605210a0b 60
    0x70200361001803150b01551038080f0304003003000d401000740085450829803681000c41d0802c0c1c40e01c901400f0016102400581a210210f0507054004c4840c21354075000b074003050002c50880e0b00d03101d2081c010311111450000c5a80102c0c09182800c00d480c015a071825142016006088003860054907684000000205a0800300d8980151507070390344d8501003490b0100b007007001006c1602078500001d0f0035034941c03d0110810107000ca1f0008003108013041400850b06d0314511050101c549209448184d03900c0c809000c0c207030b250008500c5050070040a15400c0145c20301c058090000350310709001e00d0000051036601e00809992070715600c04000d0105035242000c102d00038105072a00e60040a40c0c00c0401c1d22076000340191403141c0312010040c45582d89a6025a10040002c0d04c01d00b00d03205074103c040096244d13070200c510440000c1040d88240703841d0580060480c406603011000f04802802090a240c40300082c281f55039911a8100e5a0b9031200c18014000348144000d030ba42c002101e082c42c43c4840d25 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 434715980 1250 434714730 434714809
    0x70e0411070f23030c060a230a06050906030304080a1209170109120c020f0d020a08010e03090a050a03021804170a0f090e1003020d060e01050c0304120e0a14 69
    0xa50701d0f421040140c50030440d969001c0e41800e070034140c0080c00081c00101956000c0c1480c0907144011480b80b4502c2380c640c811400095450107031043c0c031000c040c07069041924295800c41d40650007503152a281c52080c0d80c490301c0e5400c0007402040220705d00809140701d0112200039104000c5072a900c0071150700078a000309481078044500d8030210005140300c034001c008004032280c0147c19001c20402010411507445d0001c132049030302452030480450440c0742441011504a4090003c60b5508040403c2011000f46035111074800c994246052006031140090703100e84505021700c41c0b0340c640340d078078140c0b4660b03482e4075007500c04e1a1701040c43c0c0442030744000241054841921803c01241c1c44001c20074a180d000c8440c50411040800200b0043c2041d8075000700050189000185c42000801a6401d50350156020040000040140305c01d00800205031003401c0d030360f03052240d0006003100c04a4409000c521079001c1070300c8070002c4a4280e4455401d01042c10051803446010b40c0103281da058640748 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 434717230 1250 434715980 434716013
    0x1e03070c050c03010c091716090c030f020309030909040303060504090b071101150b0d020f030a0608160312030207050c0d06020c011a06040b09010c141b0405070e0411070f 75
    0x1041941c2c0011608061256116010301682e802118500b0481070254100c10021020b41c64412400b6000703440101c2407041000e00310030440032075118000180207042e80c10f4260341e034488510420611849260020848040b041d00303403451b090941e5581000d031b008280d03aa000c02d420a0406001e002082101c0f40281d2082c0c246888003c1c107003140009603401c8400b000503044c0e02c0c050341380d020307c084511030000d4994090105000b40c03402110301c40c480c00c140c205a95044099461b110140f02e100d0041c04101e41c02850316040d0200c483c41c58481c6103031440c4c403054031424198002030312024080309200b005801007025113600080501460404025400050035040c554a028010034040c60884007076540000002c201c98106420300950503c0c0ea84224a018180029000fa5000046d2200b0004256010b030740060100a030610500c243c011500f00b01c01480341c0e2500042000f40703500080c800450700c8003640c00043c14001109510402c0c800e84001900a10350280d1250810402098661042 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 434718480 1250 434717230 434717233
    0x40b030a0c0513030206130801020f0405010212120c071e03020a12030603150e010e06192313020120100e070609090b0d170306010e01050405060706021e03070c05 71
    0x201029402c482c0307800703150703c001c0400807a40010005890f054001c1d0090500a80c1ca1548982c0d4500c40c83e4220380c0301c1c4043d442a04c001240800c90b5603014888502d2001581c2d03001c0d86030000060314a0300c0e4903c0108102d80d0080d021035120240f0903000c0156145090300d00e41840005407600f40070b50754403160a07085602e242e48400c51100c80e8468010030b01129400450090301000046001c80580801d4a40400666960964400400c01042458090796070380d1141c0880c81104440340064038082c0b6000208a4081c014644000c2c1c0484901580203030703480710180c200c140600c0101d5014040300d0f4030300500a030750800801c9140b404500034908100800d001c0200d00c1e02c0820182c0c444d2002c0c8210404600380c1007080000750420380003001200750050040e51821040d0344e42141003600108036088214021040150b02d5820442440f0004c1003424140c0c1000d1408001911078425010010981c0e5000714044030102e2420811581640d0000c190b151a0300d00207070020710320840c81d902603816 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 434719730 1250 434718480 434718491
    0x40207030201020d060f0b091203090a0308030712060e010302040b040f020d020d0510080618011b0c0b0709080c010e01020705120610150c02010e120a03030b030115050a03020108060d08040b030a 85
    0xb4915a4035581b0221040e110b000350514101204001c103034038040100389003900041000d88086d0b40c40042d5180030b5482050115100e08113414014004a21320919410b92840e00360280b002840609640b41142e504403030104810f4002e4000c070380a4018070450039162030010441d80001c0c01280c020300040710110008002580d00d000e00030030031a42e0303881046820742180e0301048203004c3c6000406041180400049000710003049140035402c1c0c0051100700064014212404110003058020b411001a00c1d100394203a04040c07034070f9100c4c0071810216052011091036a0445e9009009220080000820941f40c0c1144500240e894490444954001086107480498240f01540c12610b000c00c8039522007044da00c2642c015a500e1120640b100c2c1e00c0000d00218842288041040140161284d40d010520300b2a000906080d2002d4052061300e48100d1f260074030060f1550140b00e002c60740c091800e28425103544010802001845002510001001801080100c0001d00450080c078601c9000c109 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 434720980 1250 434719730 434719739
    0x20d0f1a01020102121b040806280c02102c0f0d0f08010909030908011b03060f120b06012322030f03120209100c0b09010c1715040207030201020d06 65
    0x80340f146901170300c00014440041010301d101c101c1d554408100c0054142e1030a5150004145840c100b140c2943c0766124056100541c510b9050448540c40b40000381486034881d44000a91a11490301102e081035940d060b0038070b0b580040780f00100000c200c240455481c1d80140310b83e40d40380d00d6054101a13040c841d010703550fa0b04900c5075441c1040c258081c0d4649a09900f09100364010700060081074040111011010603001000e1081460411003481c001d003540b040c1d5400a41030340d505520841c00c02c94514810032401040c200340483c10b40d4040b035805c0b15561444010f8441a4045065039100542c242c0c44d4448009442c00515200c4500d140c008006003107a0a01070354150f9901005110058402011f00042e0244d054400f82c02c0811300c02504105400c008611f8280c000b83ca401c00050302a0441800d00201000107600306030450002d11401446410141410350009401c11000f2444030004500b034a000b80f41c2c940441004000b9036851075a414003d020350440c80d480311500307281507c0000d = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 434722230 1250 434720980 434720983
    0x50a0b190504050a0b09010210020a030912050406050708091503090a03031104050a0e07033b010902030c0d05150a02120907081002072604061202091e04020d0f1a0102 73
    0xc2c1202c02c000d02e00003809090105256441d000306c0a043e055108001190040f400c5600161042184a0380c00090782045401c0860103c503007104140c0501104000520840f1380c07043c100c62145410ac0411503a03444840e0100d542e10009080c0482000800700034408081004988585010b000e07540c10b1240c0c0b8060f03000241c0c2ca1007903101e00d03a07111081e60006c01c907843c0c040110580c03000e4503040001d00c40e0084400c00e20001800c818074048452608c00c0c504442c4040c0d0b9840b01d801c410340000b04508585540400d60380e4000c00c0c0e005104404501443c81000410049500e000c409000c035800d46060422103080a03400c454402c241142072030001409500300004d0800488100200418100c00d43c0c201410017035226072015200f003920b5590185100c4044c04002e1104800d110340a030b951450310000620030580e81e110a8003244c010030500c640d0385c1d501d40c01450b8a90020302a07600c1d02c141c00f00041c00038803e100e0252019810849204c0f1101d140b030740085848052882c0c030440c101150320049 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 434723480 1250 434722230 434722237
    0x703181e03150b04110d0c0207120204020702030307061b110610140d0c0b0405041d0706050d020d0f050708090703030504090e01020f0c010917070213050907050a0b1905 74
    0x104030392640d050070004a40002c1422102442c08000003801400400c0410b0030366030344101c48009030364001204c815070401485818000581840508511802c1210740451649000400f030b20442d0003190f60002e66409004075400f26600010030001490900c0315113017020b04000c0403a02045400c0300950a000005c26020f2141100312042e500080c00c100216480d4182100c5c100e40000c82d0b0300c031604c00030303421440349005400382c10401501c3c2ca00c0c2400b00000c2e1030100d12003040180741256000a50180014240142c0355141401c9444a45c0c3c0c1850b4002409001c0c25520014104080440b080d0041d80c441c601811240d0396655140d40e0b1460f0003642c07211540b00c014000340c4100320401016825074080e10f51525590005440c0410140300c00c0015041030401d6107c1d0303551111084108410b4070070440e050311440046038202043c540000760701510481c03195038a941c80e040011050001446440b018080c01070003022481c1e00c3d0003420201d9000640005101c413121403202041700c2c001c0058 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 434724730 1250 434723480 434723519
    0x509010f080a06050612090606032107030302130b120601180311191502280605041109010f090e07290c060114011d03070b0f0906070318 60
    0x40020104001004441c9014001c16201c42c040d83c070040801d1594520004000441c002e4060700301c54140306c8074850601e440505070300d1080d0310201c004100d0760900900c660001c64070405143d00c0b1b0f281400d068020348140d604206030299001c6001c00c2c0029071901515810010300500e411654404c001034988415001010118180c4401c0c1000082d03d20714224007004005400e03074015246221101044020503004040462440c042d826a0300b641042100034841da45c1450a0348100c4100f00c01c2c180e000a18406003c8071345850001d000d02914006020004070041d080100307642c0c0d01d030560407090381140540200b0703d0400900c044e102100040210a44400001101e240154503804d0940b10003440c004003403443c0e052100d0001c40505100e914004c000e4400c5025400e4035290006100e00680c0202040c3c55588402040c05a10006424030640c1c0e0404000c42d40c0364080620301c8510b010728917402380d04c447c000038101e00305a4003900c190f4400742810741034030f0003070b80ba0002000c811240c61803 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 434725980 1250 434724730 434724737
    0x18061d01060e04020c0f030c030405010206130803041103011b03050712021c0b120613020109060305040312021308070b1e03090c0d0305090316060909021215010e06030106030e010507050901 83
    0xd019110f860554014a2640056405c480304107885048542c05c40d000b2030410500394002050400507540c040c4515035114807070b59590006040d1031398034850107020142c00500300d010446110300a5072425801000e040d100074600c01480c04c084800100a010300702c3d8140009400f005581180b00414000d882000e05090400704900401c500d0390030003401c98801490340460a80010070130100103206540c01116900040d4a20b0406400003611480460f40403908240c905001c2101290380400b07440240c40c1c51442c05641c964603042c40e071480304461b41103170f84240260000050341821003402040c0058101c0301100684270311120610345800111080c03105c40d00b100810420b1494000e8030540e0035403181c00c03c64200440000840e18205d42c00141000e81000b04105002e03483c1c00c1501c1100074002e003a015481e01b0311014080150400c040d00c142c4004036000e810002c0c580c020303001c408407244050030340ba80f40e40c0c0d10f00004000e000c1e065031001c1c0c0d039460900031942d054840d408503400e818042c0c4 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 434727230 1250 434725980 434725997
    0xc0106150c030c080702030a02061204050c090717180709051501020f1b0105041d1b09010e010503270a0c05150703110a050303010603020703020f010509060402060a02010618061d0106 80
    0x2100c030503445c1c0c40084100c0e858054042024016600c60016214424000c4040215031405142092612242e640e01600ca945090108000207074030444908602154600080c001c0d220354544001c04105c20a81401c140204400170a41c1ea0f45984418800c00142298114081d5080010380c1c135020011182001034012503525294560300c0d5201c40030040c1d040c58000c4c039242e40d0b0701d64840240d14a200e1000781c80050303814041100a00304500b1480034030020464500031141002803c46112940503034107105000c00024601c002441040c501441041714004101c00996101034440c44030720402c5654840110005c42c4c2c1d820220541c8100f041c1c04040946000800c6e00d050341d81d0502031190041d1f034410211840c00155003400554020003207a01c016886009616029041c5483c44410440986c9004200030f04000d00084941e0441e405540d40d9640301841d071000c0f4013408a0340c216a9100c1052500841d95107007030750045040310b0741100342a0404c54840041c0c0e00d00f01081c0714a200081000 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 434728480 1250 434727230 434727233
    0x61a030106180305121809012111091006080f1b09040207060f020a0e09090d08062803031202090a05010f0203070f1506080601120609020111030c0106150c030c 70
    0x810b140140e010640c1440c189182d03982c1d0b1000d18100c156181140106000700724003601c20503050388050690402ca40c2e0410030b43c1461702c4101400c000c0c201d05040b4040d0300400005009121800090021000e03101d0b0380649000c58444043d58541d01c5100c0c00140c8200000d00c06e032640c1c13001203020b110707040880c03141a81500c0030101140c01032180158015420010000001e0103441030502080c0e01500c05a298900307080094405d0296908131405031106404010301c0180c00326071100070f01005e040a8189403501404103c1203001c4e80b200f22500800f43d01d02e145c0d010145607111341280d21959400120001c0d03030b8000001d0380580c0e1111074002103400b10610484d8011a20f02129500c0c52048a05202250301c5060b5403403800c0000f507842065035a1100c444100031702800004e4140e40340281070769490502c2500410001d84009400030343e481d80c03190116032060300c5c0610b11001079401c49803960900b280040c02000240f0403864204142d0b540c660103907009035101420150551284d8000b001d0a = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 434729730 1250 434728480 434728487
    0x103050304210f0f02011427010504050307030f03030e031b0111040e040335061309031b0809060301141e24040e04050d0801140d0813030b09010f061a030106 69
    0x4c02004905000d040f00c0b03146ea0800701d4501070705200c441034000c0c1844032203601e0505c0040040d40140c2d4100501040f003400b0548000078003c0407241d2201c420305104405080032002800f62480e0000d00e804001099a0301105400e145480c03c211035008014100c3c1c4140c0b9071001d480340d031042101050840b400100401d006484290b0510010b09a07004003040c2d10614854020503410255420b44202c02030000c11b00304a44038004405003084104000c1205440280c409071348110a114900e4185082e4000c2255400c140c44072050060300c02034817940c5072101c45030340c038020300310f940d0040404d00100d20b0300d1124140d0400c0305071800303455421030701c01d80c400054070703203401d0421044050400c0000248007a9014a494400c0b402000a000c24103200b0800406d21581070740300c2d0032003403514100080f1a6440b40601104182d11881840d9219680441650b401c030190707001900320005941046042074040d00320034003440d4085000c0151903140c7c1c0e08001c01c0140c1004c2040c01000601c01800780e50702 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 434730980 1250 434729730 434729753
    0x1b0307020111031f05190b0f12010f05040f1b11010912020303010f1a1b1c03020d0e1b060306031504030306030308010b1c051e0103050304210f 63
    0x1520011070401040a00b08070b0030303801a50f201e910124428a42c40d01410011544030142c40e048072003440310026022454144001e9000d40417000c20005200c01c044003950040f40c4800c030040540078003560352001d0052500310544503c601480c100b41d0f040b484d10000e4400c4620000342c0880c0039544020030070007220700072000302400d10300f0765070b4a0304103000c1200310041e103100030b078240e00969480d81031020240d00044164015416802041c1188504284c0c40046d2100c0c13641811110755200030021000c3d01d00810800340345411300702045c403000c0c82036040e002094100304c50386050052101c052820b40e0f485d101c0400c04c0c648645200d8800c51589810320003150892401000c4600f940c4110303171b181c502100e06036012000329a8480003002019000700a15004001c036030754290401c41e0b004941d1040c071107080020643d0340d41c0c1e823001032002615000358203010704840c55100855a103a2a109545ea40640030f00000100490f056503580001c41c845040c41d00e030b00249400c114106a6146100c128 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 434732230 1250 434730980 434730991
    0x20a1d060d02070803060117150121020c0109060b220b180f0709060e0f011404121407080106120f031403070c03080f0c070305090310060b03041a1b03 66
    0x100308006480e0071400c980041c2901d00e005203c0607030340e414070b10005010205480c041450880c1600308000746c005070150504500b413020708061a104807900d402801910924402040b6180b020a40c440c100c101503024080e0b05100f8001045445250001c10142ea0782600038180f20700880320500064440e6600690134900000d4250010303c0c1400d9040c02c54850116240300c0340c0340507802008140c5501c08001e50042109080c20109114068042203600704c2c5080e0071814422040d062100080c0740c0000c58000b0008007920400d4031801c0d1a00c0e040c3c14030b88445074083c1c0d102d941c1002c2508401071160b078048aa0041104c5181c6549a5a84d9030b0003c81000035014050f00034098211101d46c000154405d8000380e44061884045280140c1001d0340945068203400d48902000032484a400442e0801c581504000d6194401040043e10b8484c1c24a40c40803018104440001c0320728440001c4d5000d40d00c1210141d035007100c03012080040500c1210030556401606071100c2c0444c08000c020340e00103 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 434733480 1250 434732230 434732239
    0x2150127021b06010308070c1202010906050702032a03010f0c0e0118090603111239030706051b06040507050904060b0a1e090213061b050105010b1903020a1d 69
    0x1004102c184a0800609900640701d43c03000080100400c8400980316025005452001a040c441900001d05002c0c440c00b0ba03100b8800001140e40a5503800c00601c8030443e5074910ba182d4945582c59411651030408817024025800c0c1000c4213402c04070f45c050340c00081602d540c0c02d940d103410100111800c02442211518007082c107400458041f216005140c0030b54002c03c03041d1707a20750821003801010708c9201400101900b140603250464002032031045c020080c00925400c40517810414203103040001c2c4003455041c8034040d800540d13035406c440a04140f800c062008555080815100758482d001104c00401a4020000074400d1386440081070340c216010701d10004c0c60188590116120100503000b6408101c4d40c403030024000b140c24442c00d0007406003000154148246089400181d0780ca6028a00038088020f00140c03145401c02014601d041e0400024096540c0d5954000140d0f800400c100c00070030900c810a2030554080d008948140c02c20f980c811191078900e0440b1145481452500c0d60310 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 434734730 1250 434733480 434733517
    0x2030d210515010e1302030a051b090d030806030f0102120403030510030c0e0705190309060b030c06040509040609050a0b0603060f13380108010506041e0e0c040c0215012702 76
    0x8170440c40654814100d0043c000b410f8188445030b28000c0110114055200c2130402c120305e2162141000003104c1a0f260520040036158400040e0038191042500c0e942d85d880850401d00491000e003c41d4020760098404001c29118100031800b040e613180805031030507000c84000c200d84140c1c0c290050b07009001c4d14005051012243c0400b00700590071301803800094591214000f805110b1091581c6210210003c0105034240004600140104e00c50f892083d0ba81c00001070502000e5040503083c69444400e4407910241450106403214003500d10500030b00c1541d0001c1c00f103241003c03409001c0c4203800c01742c8024817401e60782d0846240340c401040c003104d01120ad242980032000202030900d40380e500740540341c42d81000341c0c00707003111001846a80300314100350441c1142c6c112001450001c21940e01e0200350318a41e0400c5910f010f078400b8215803c03070715185000c5c4a03d03038081005402021000c0c0500c6031642c2e1210350041c904204000c185901e1b403180c8800001d41255030062100c0206840780294 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 434735980 1250 434734730 434734759
    0x3040b030c1603020a020301110306030a060902040902030102070812010605031513060b0310090b0d0c29160308060d120e13020409140717040b07030902030d210515010e 74
    0x255000141085001d80d0002c400351701103240c01e014650240c250044200c4c11843c00400195661100070005000306a07284540c1e415500c582d00f2011545402400940d07503400b1ba841c10401642c051202240805030500003c50300302e00c104201c0b030160580c0510050313810b072340108000034210440a24420f09a0320980051350900010145120f0f0050203581d918036841c05072810306558591144c0740c4500c0005038407900055105501000313860103d0700340c00185803006d070b40051130781c54654056044400480d42118010514030f2204149220b030b550b21410362186000c0c03095605420fa0020f141c410310202c98815a4800c150101320231348010030b00171000c40740c4040034040f6070040d00000d80d2039445025201440030900700b4150800303032516010b01d00c404243c1e060b006a103409000140b07041034804c080b88141c3d102e40c004560180d00101a10100501021301034142d40560341d0000f500d01201000d080301d00c0407841441c2c0f1031216641041400c1c99484011640000c002803070703a0b8008490084100c = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 434737230 1250 434735980 434736007
    0xa030c030e0d0f12180305032208060112020f0306070c1205210a180305040311040605120c1005040302090c03090a120c15020f120a020c0118110409030203040b030c 72
    0x42c2070500901d1804c00f075101c1c41c64000c2040b86807155005005a031200c040001400c008104d80c2c1041d418440461609071012003400c0d4030300c040c1d01250403440340b8000420100407905000c40c401d0b10803284001c206101c00240b40d140c01003120380340045041078000a010980044880f41d500c0c095140043c5064480716910b10340348144d00d825901d506e0b001d002c00890202c28800d4945140d0300c844121142c60b4140c0e4000d026201e1408010251b0350b400f03d400c83c140e141c2d5040b01000c0c2800a00ba0300c4006030401c0400d0381c50303030703200112407240d1880110410068041c100300c2d03094a802800a00c000c0c0e61b54025948140d1000e84a024030344144440e80c404140100c400301d14003007890f40c40c0000c004071801d08021400c6c03070130049100240f04120381480d44540c80c0485440c4109441040000e81d42e00d6002030083c040c06511803e1542040402005203c00710340075580644a2080c04090301da0ba0024481102c1110100074090380c0308001c1800070300308880107141e0103540780d079003145403150303186003c03 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 434738480 1250 434737230 434737253
    0x1203020405060a080f012103030b03070f0608071d030a0212070b1b0105060f0109050d1406070e0a0b07020a210203010207060506090a0509071401051e07050f0a030c030e0d 75
    0x1c3c000903c00000c1c4001e207000c08080078014400d5115005210510100d02180e1a41c004c20080506a50303050548840c3c5044c03180e0802004000b04003000c4a07030310100500701404c21200320700052181d29a030750010262891580d0042d80203001031806055075401d000d20001a480074041c984104180020030000c0b1400515110007103800e0808a0140044036609459018040c9881a41940c078211027990740481004200c0c0e4040395600c4400f521400c00e0b48045d00c60402001c0180608402c20800036007103c0d2680300074000307640501e205681c0d0801240c5034003a00b24025440f1003504c08c1040041505010002c0c0400790f013203011350903e00c41d0700003800c80c3d0224808a40540d240c004010144c908142075561040d8414000d101924046849645030340d6240a40780c0c2a001e640d10009541e4070030b1081c0e03000032192030240c88070501c94281a04080e00b04650885580c8110700d8032409000d0f01103a6018083d030316881d0044044a1750350180d646490b03a804a540100c0c100003100041403009058 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 434739730 1250 434738480 434738497
    0x11e0f110c070302120c06271504050f0114030705030c0c0f0606090a0b0916170921071113090f0606030b0a06240e030a030224060904120302040506 65
    0x1c0144030703d5841131064800c40d41840e8106034000f1000e507100c6441d810126510001b01c03440d000209001d0f6030f8103e1a03074100102c85508a5194001035100458050040044d91000c681070309801c000740c001100c0060000d41e41c521048420700c0420074040c01070024503003200611001d10300340746819180c14500f4121f01e108012580c01b00c000e001036807d103c003950350880113031082440301800b5480800c1c00349030083c0118102d140e0b51104807002c07502c203004000c122904a07104201c1340c02c00003640c030340e25aa080024251201030ba0211065250f0440171290710075402180500d2101c41d0b28204188100140418180300341c807100c03070100160200081026070342c40358070005200c50450504102000703009118041d2541342000030311203010703039440009003400e02d10407102161044d468211140c40004c46050307094451030340c080c420560003203120a0207403d17600460500c0348030b40950b0071311305100703803012504045040041004294403032581074410f030043c2405403625668401240d100c0c0e008564 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 434740980 1250 434739730 434739733
    0x7080c10170f0708070f050a0e2704060f181e0605040605090609010b030709090f051e0607052104060e100e071e120f020406150e03011e0f110c 63
    0x8102c5615000413140707410885c2c2d864070010b4100d0302c4001900901c5581c00325800d00503d0462540507660304030307030b11a05110b141d801000444c0400c007102500c04042d40c04075403040c208001c0301f01d00160fa00c103511001c5400b001e081219096900c4e0780c02418222440811409020205440072580b60b00500f030007184104e100241c2d503d803003215142005c1020381900b60b03590402c4203002480d580003a20605440303d80302c000946050702e2419045d0390341d56000062003406111071017010303080b07800c001d0202d440280d0151841940d81c00b000321128032882c5621010048030500c0c500c0032810881c140340c1d10078440c040001d440341070040140d02d81804084e400c07405a441d840406000c441c28000320000303001d4050000c2e00301c16074030440d58018505010389443c00449102c440180302d000700c402c0202c160050000c00009881c0e880d01041701111035a1038010031410390390340205080521640c117540d403500400c98105404441d2480c041c0030168010b0101d240c0716068800001c1d40c1400405001c0e11810 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 434742230 1250 434740980 434741011
    0x603090708164506170c0307170d03090204020c1b100207080705060a140f0301061e0e01030c17010e04020306010b040b031b04030f0c031407080c1017 66
    0x55001d100c00d10203802c648003c500c2c9141d0b404600844600c0000140761082c845403030710b407800f0340480240a158401c2521000d2401d40390007802c00421000310140f01502a42c90441e118a000f24a8442c031848a912561001e909221403601c642d20981115200500161800440e85462850031603003411400d900c0c00366803001c45c55840c0200c3e2045003900d150001d040d1183c5020352140d00c410306481054001c2c3d8001400f142158410381d1940036208140c1d000c10780390f110740f4403012041c1d0824084c1e540454041c2c0c801c1c0e40d45294125203ca6418059964030300d048030040011000303040810504d005203d68841032084030906d4103e0240a400303001880b603603034541401094504074043e03020b280302c0101000248070004509048950048082d155103002c00040407060744e04d481103a1000e48007030050301c0e03d41c0c00c0000401906048a0081d123401018200c004d01c80d6844200c140304a07613640c3d202c950800c00c0b900b0a0345d80000300e280b590070100140c3c0c43ca105000b02038103003194070350303804039560 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 434743480 1250 434742230 434742239
    0x51e060d0e0706020f102a03020a0219020f190f060c02040c0503090a1b09021204060c0f0509040e0a120c1401090308010e2806061d0609060309070816 66
    0xc0002c0801040144003c00034070210551098440c0240b45080302856140c1c2060b43c1210f0587d101744030b003808400c401c541c1401c1030241c010700035002122280d0050040300800d980c40120f449902e0340644e0000c000901203008582080002d4040d05003a00c1084a0807000240e807805070003414004000545500a906226104000c1100c88000e40d0405000d0103000748030003000005124030581e640404000c404400c00c003c170805000c2581c1c030005061303000080450a4420421056004a100d040240b20361a01e1900c2950039542400020000580c28802c3ca001450150070100019202d4401e80c4e88201c01615002d003145406004007022072100307601c410405c511070b14900c000b42d141c10001c112803450f035030b0000d0105170180b007120f00c0f6400322008240c41310300882240c80c00d800c0000154507000c8042c00c000d000391000384116008103602071100301c0d181c50388940c0d5010f4018010b040d0b07444c2c1023044041103215040941510994030681c0300201d100c42003000800c1d10380c00c2e040c00503907440345070 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 434744730 1250 434743480 434743483
    0x16081302190e010b030405061803220303110708030a12060e01081e1207020105030601180f15020606030303130f05010908091017220218010f060216051e060d0e 70
    0x180d004d400a848100200004148042801600301003030510b4803021614201b0400e00e0b60040800a9011098091843c40da610740800c059049a1003501c40c600d81c040d0090949850fa2814403034008207070030400050703180c0c80c80f9040308058140d01c0f400012306941c80c0e4540442c0c03040309810403403055100c41c09940100c40d038080d50340241e0041c0401002c1c51300007880141d01901403990020b060090100104003160700542105102d002504400c0170381d60b81d1071804101ea402d583c4a4520550f11000064400c00c2c408a20580b0032400076005600c1c1d0b4440490350301140d00f4028081ea41e1b100448060b80000e0780030700810071554000c000081c0c0b5515110304020100306610040024840c529800318008112031010310f41c00b0900150001400d008001458051205114001e51001c28590000c1c0c10070400c004190585540c108601d0f02c50740c079240c0980e41c40d21400d244201004000b80c00308102c1c5880340035035200302404082076403226402c5004c280660050501121281d85036650304018040 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 434745980 1250 434744730 434744759
    0x3030601020c0a24030603080c07063c05041e14010c1109041110030203040507050301110f0f0d0509030c0c0306190207050118050703030801050303031608130219 71
    0x2c08440341d880e014038000c601c248240101d603010450010300c1c0d80c0010303050300a41c0711400651b0004c50481da200700c03840140e41c840d500c501810700030032070710107007840c20b014102c2e1852004480c0001290102600c80a14100306094203070140c20400104404640c02400344030455030350110401f030703120391420702140303280101e44a61454100282c0e80b00d120003027a140200c2e5840c00c0c5c0141e500310340c0c5803201c5c1010000030403840c00c41c43d0040e441c0314010440d0b503415402140702d540100180c0301e03800d0b181e004140c203031001c45000d030094001c10300241c00e01c00c42c2c0400400003110180001c86c901840450300801342e80d0110f8030310240360008240010302200c03d101c00e0380e01c000e00b20040e0509140c4900c0a03080000140017001d0f246a01161050401c8025403058408009003014003034503441c42d1a000d95a10181d0108500061951000054908001090ba80a06031114440b800000051011100c105d8000c041045242c162100800540c40c0d80141e0012110014255030f0b0860a041c000701d80f402 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 434747230 1250 434745980 434746003
    0x609060206041205031302100c03110102040e0f0c090907050309010f060807261605100c020607081818100f0311060702030a060501090504030906110c1002100203090303060102 77
    0x4010404000024a034101c640f00c44a602d42080d640742d854141890b42c0344080c0810007500540307180f82d2400059001044010ba4900c80c0c0e460f601082c0c5c841801600b030f402035220740481e03000910f000c070b004954500d280d1580a41ba004041d410000c80c5c00c0008c140c40c4d010f03955100800c2e400024010400c1d8280107414803010f1054090055528189600341c0e1910703d485925061a05001554203114901d821204000c180804559810b54204084d84034280180b09661003140100141c01c0c2c020300501d9400780140d0014004b40c00c01c80281c07660070f40703035000300301c86001070110016003030300d50303030385003030b454400f4544130000d0302d0b50b00d08201c00c0c10328031120f0b4100664080c2c1c1c0680400c0000d82e402800c04030f0a00903203015448640c0c0344007103450902c209800401680c00c2000214003070301d066116501c2180295030b020701c0755903928002d0b02d004400919440c03590b00810009603503400d1003640703900e04c100c4c68411190440035000e0240101e81082e924418260000814840d0315a41080304541d602c = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 434748480 1250 434747230 434747233
    0x32409021005030c0417030a0306050a03031409130f05060f12060406020705031309140c040303050306040e43081e0102130e040b0c040f0b070609140706090602 70
    0x2080340c000407140703500d41c8221010000000001070b403040000c1c09860080c5034804849108100500800d6100d4004c01401d1000034903101e0000754a00d0701900070011a601a15101c04411000c480d100ea02d074860010940c01014000c0100051822441014001504101e002856003402e400b00220800340010301c5100701c0d00f0160401d98a0b40102d02503402036401100107a55411701d1a05c0c42c1140030341d40303c0d1035074902c0b803c50002e40b030b0100390407907841502440c155a40546c1c0d00c0c0c0c41c0032203e01a0307001c0900051010b01c0020030505159220520b01000034040364120302518580a20500d1001158581450850380e06070100022800301c008480101418420450901945550354450701c06000c9484000704100c02c06c0f91002c0d81250078990350303e01050f06203900d90300002403012042d1401c0714a84c08400000344a00d4207501503030160f541c0444c4807a0102d1405002182c0ba4000910541d01580d894213003100254070240c00d410410344d50703c05000b00d1031400e08040c00694540e40030130f096 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 434749730 1250 434748480 434748491
    0x50d1d1f0204081b031009140d030213050609010e040204060c201503150d030306231302090109050a0e1605030910052706011703090307050d031101060324 68
    0x80c0503000c03c420b07030000c4e04a2842c3e940366420400107864400c1d58020b0040c1c0c20302e080755510503c05100922081040c000086075a181d0b000c19040301240b0031990740c600d000287c41d00070301841c60050010450b1000500d490200c0140c81e500081c202d038090b80c08103010a95418030b00741041854403031780d2040c0c6252080b48445241c118041442c0d003d074510070748411100000011a01b103501905c0e0210746101404024604030b0314900900105580c1c01080d2200e40e680e040000810070ba5803100c00c0c014400380c1424180d0700303540341c0c3d940a9040702c0101e9041c414100d00110300d54880c000b4241c02069110000300c1141031240c60002c1042a0350b40500130820200108410702030005800c0e40340c505032480008883d6250160680341c406e29500564080940d00a186034000d0001181410f90f8910b00d101900c8461000c100da99a110b01d0b0041038040d00244000c201c64034100c2000380c405400303410028990440da02d101ea08442450708101c1c1c1818010201c1403090b504c5d4005a82c9044960710300b0040b = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 434750980 1250 434749730 434749739
    0x9060501362714090a0201110717014b0216061a01020706021507090f0b030103060b040e0a020f0f04090f0b0a0219050d1d1f0204 57
    0x119400c800403030401001034a54010300410001015001010100b45100c1035141103611020400d10650a40255509060401e00400d01501507180034030060002031104c08886d900644280b089920030b6292805020b00015290100107103141d402c18a2400004480354125001c2c400c1002265078500d00e04482075281021250343c0300100194a92809400500314004103080085d100b04482d40c41319590200c1c05200f0400f05421180b0085414050a03607501418001280d035139405124010040c3e02c412444020000840c08503600030000d4a07101e40c496445e94410b10501c1081d920040546500200401c05c0c080c6a1007031451610f0100c1e03050000c080c83d541c90640d1500b01c0701c4080c1c4101c0b014541d040b03031075884001c1051040c401610031700c00c400013824510030015100c0d0042ea085030aa0b000500010494821541c42d09403200200c0312452561208403019003161080e60050b40d81c6210320281581c520510b420208828070052a0348002400200c020740e41c1d00d070301140c0d1680180428003 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 434752230 1250 434750980 434751017
    0x80706061e090911060d0e210a0309060b0d0c1401021603060c021f20031006140405090a0b030c0103141b0403080307020607081806061003140a050109060501 69
    0x203084482d201408079007491030341480b8240500c00300300ba40c1e001c0c4001680c50040718039600211b24005902041c0e400340940f01e0b00da0326040b43c0007141e40e6511141080080d00c540d01030b81c0030700740e05400f50f50009405064040400e098200c40482a500c00300c60100800038140b5100407003c0100c000e10150180441503500d46441e501c950000802c1103483d02c0c00482c246100308840d10440d641c2c00c08446a80c3c2a0b0b40c403e038010900080481201da5107400c00c24200007990084900403900c2c1d00f006000306c1d190000445103401d4052002c1083e080070840002c0c80e0307995242d00c50060b4140c21000a550381800200341c13800d00090307022814581810645d010068104007030741d5204130b140e091040307020700b070001c8001141f0440d040282a40004401d10091541c005009441124241c035089103588078209801140d620032007180c0e0855000c440000c00c08d003001c5840c045d891000341030100d21490201100d800d61307441150014a510f6884004200c0a207443c0590740080c0020700707200a006080e031800c503 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 434753480 1250 434752230 434752289
    0xa120f020607030210050106090f0807030b0a180501051006031a0d03050c0f01113004030509040b0603090d02070b18091b120708010b0c030d0506060c010908070606 72
    0x81d1007079102042c01c20905000f0f20414481c41c0450008210301d6844002c06003045a040c0a0812201818103010440d05000112402501d4005594036056503c40d580c80d400780101c1401c8a44940d0f0068442c00090000d01940d07000d40c0322128544040d0b424000000d085545100c415100000641d82100701c9403503c0c40d50804450305032800e50340e900d681c07000c40d038540848081c3c110b4a56182a540700c88108249000e020b0740c18800303480c2007110306e0ba11200c0010911041d08030b00700e9960769001c00d000070301442c020464482e014102249009410000800799002106da80a0b51b40208130004945a030510241e000380c203030900010b04140900d050718401580c0191b80601070440740c0045501101040d1440040e030111070081640c84550362803886241d04199031180c00b1500100010808a10341c4090b145c02c11a40c0c00154200040048410041c2c1000b40080b508054200803006841c1c200f8014114214003c8012136034404041c6804003c5038415882070381611200700080b02c510071a050030 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 434754730 1250 434753480 434753483
    0x1505070c0b0a11040801060819120305130c03081908091b0d06020307110c03030405090411010e03010f02040501021b100f02071e0303020f0601050906061602030109110a120f 76
    0x1422a1580d45038a25402419449803032807103c60042000610450b05410400585006ca8140d031100b82d02480da1488507501c2d040c0060001301e0060705c9040c5180310794040780d8030851840503101d140c0c90507220100180d0700e6400a0702d040e040001d034541c0c0c0014401704948400860304d040c461501e80381c28801d85866548140c00b1a10000c40003142c140d60720030b00003030501508050115684c0c00c10b000040c1040700c00460f84901401441e83c20b5000c1c1c074021003a40e0031913a018040c18190390311170b03442d04000c10070480001e040c031844181d4103416071806d00c51019403070001640182d07203904200001e40b0340049490019035102244150240c143c85400d11515000e5031420030482c0424071038030581c00e08101380c02c804250340101c40500b41060f249410042103038084c0e026611000c20007001e16844110900030039410202d1035010896030b050a100400c0103010010030f621102019a00003400d4410700103041c1d40919008441d80c00521300346200f80010040f4a210350304845d03080e50388182c0010342100 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 434755980 1250 434754730 434754743
    0x21b060c040902072f010f0c03080103030809011805071419090504050a1a0103030f0201140708060a03060623030615040207080426070602011103041209080303131505070c 75
    0x3060300400038441c0e035641000c1005a20f5050701002040e4540006002d07a00340741c005184036407c510250301443d1302c5c603801d6401d541c03134030340313903800c503241665000c0001e400b40760341d0b40d40e90740300301d645840f201c0003840c0440c8a48080c0042d0340c40e148100308400c0c001d804542c8079031102c150b10a046084900301e802107841c3d5040100d0580e0721801d0150800f8903011014000c0f2401640b4121172340d90500600307050f24032a80361180c198010320b00c100e08036030124003d10b030032001e5172003c189503030300585e001540314400901d81d60042d6102e40e0f80c0c03410f58017164842035182100018409000040303400b0700703001e074405500520640c0713003258100841d0107035804040d004590000c1c40f4020300442804440103004015038004a100c510003803018007441000310000b0381d020ba4003011030074034418064407580120030580c1d507080da29103498220480d0030743c1c0341350030038021640c1c80018203d00072b10207944590b0b24101030404a100700d060440205440780401c0180d1403500b020800c1c160b40100b11034101e1500880c = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 434757230 1250 434755980 434755987
    0x5101b020d0209040b01030201090909030804110a0b1c0c05090102060403030f0902060a12050c0423060d05101707060f0323010909060605030115150512010306021b060c040902 77
    0x410040d8000e81c0d0007030341000d0f0b1038080005004c17440702c0a90480b803003031342c074010307419074500d407800c00c0f500b0030355009001543c40804503000c00c0c0d0212a942600340c004084907035180d0340e07501c04091035000c1c0e03440300d4604c4080881d0017400d901071310503104202250304200b07180901c0c0c1030001351104001032008051541d698080c0142c86044d6000b160b80a6010f0b04060b1b4660706044090b101100c2d998501c07011500b8000011504d803082c4080c0d0b0115400d11050554070340460f02c241d00c072035074040560b542021082c1300313941c10300302c0500404e030003404031141c2c901c01c00d0308000d21890041d0075100d0400301a07000241c00c000d00369101641c0310020b16070b440c00144401d000c0f0705200c05074580c80440301c41d5019040000c503040e074180d4840c140c100d10a007030401c20150b6640900d400d0728011040c0c507031480818079007000444103403000b0f00c403282203614245180403801585805810400c4c2c0007501c90035804104000b00c2d00484100d02444500c5c2002044035150404114950f4070413801203060881c1c010 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 434758480 1250 434757230 434757233
    0x10c1b1e2309160207153c0c06091a06030d03050106210b030607020718151e0e04050a030305010905060a030213060f0e0a0b1e0108101e0f05101b 64
    0x20302107000545850142c01c06d0300c809509009280c00081e179a0381d00e00306502c442983c00003c150b000041402e01c01540340d081074180600a645412342d07800c003515416210700185001071044400070804804000050074182000b105061a20441c2d0a051040c1403924004ac814a5007140c004006550f0802203007030000c00d80c0d1007001c044c4c1100d0b0000f5406129071030600880035000300e40742d0140d4009500d00c1d604007529408103001c0c7c0d00d0010140103142400070050101511112a80640380440301412500c0303541d80d03050a407488000c032402d0310140c00500200d810580e150141600406214034140581c2c101b880001701050143d21001b84110001c00700c4004000310fa4100c41e000f820030321600118103a4a602e00c04d080402110000715491801c0e014402a20b44240301e1010248045e800454901881d4015203075041c0242c0700e0544940c00850010359640c00e2520300118a6803c42807940d00c074034000e9508075600b4190001403240c0003003045601c03816400f041e125602ca4500240d0f481072000c0d03 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 434759730 1250 434758480 434758483
    0x30f030a0507050d05040b06090a0c050405060a05041d04060c0822050f010c050408010b0d0803040308060303092707020f0a03050315150705060a050402010c1b1e23091602 75
    0x888601035136542c1090100414000021241d0744501000d483d5503001e41d0f40c0c9082e8500f2500c29000c0240440d07000c1c0014021414288050400c01540e418668901078451030002240301c0c0d01045001c0c5012403004100410495001d00303a041c1c1d4040c20961100c1c200780c000c0c01c403541702c02a680c1d040750181300da01c0782c1031080c00c1200c07502526405c07008200c03038200b052004026a1041c06503061541c20440707840218209000b1490680340c125203420704603120b0303236821200c2c4030000d40301941c54402405199450750391040a003111254415100d003540303030000c070310004680004114005542161603180911800450703076070382156040c90603603500d41e99480b4040e0700c00071203021030390031001c5004140c1046024034000c0c040300d070145048516903074900354035500303540040340e00900207124406510005502e0740204854050001c92210206072602e80904c92042c02010ba480324645100c01085102e80300050b0511035004041142d0070100d00e0030100c1c200b40f4010f40701918070200035401038180e620 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 434760980 1250 434759730 434759737
    0xf0603090615080c0a080319120207020613090513080d090203070905010b041a1305010c02180c03060f040204030b0f090f0f0d140a090603020f1213030e0102030f030a050705 76
    0x844024400301c2c15180d040320b9030788090130140700d80900c20031200810300d24000400c1d03940e01503030f0b100c28411350862110102c542010503044454141d8091024000583e82c586c0074100d52000c1034103541c0708030303d0480c00b0000d460000c0d240c480345404040109000c034500404481040c0541400810251440c0c4086403034441d181d4007602c9040d1400c8004100418072070001c00c1250392036004420b94544040b4588a00d1244412101c04900010410417440d4040c55903640607600080c00c0c800403081c0e030740300400125400c031611290000b0001c1000075a140418400166203c151402c509103800e542c1d40300ca503500090803440c00010b481e4009144164100081c940118615081c1c3d020041075181071542d99110350544408920443d900c558161210800d0710b62140480e618180390790724102d0700341c1c0254011740002013503440c00c12400382201864034183c0d00448203940700704100c201a090040020b4140000a4110f4208000900c42c800101c019030340c100d00010000038a40d00c840308141c0305480b = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 434762230 1250 434760980 434761001
    0xb1503010e06010e01020d1e0c050f0705010f030606120b03120414091506031602030c120c0613020114090307050904060212010e240d0203030408100b06040f06030906 73
    0x1440040003042030080c01e03108500603182038030791a20000316000103a844030b1b6400e4041c2c00141c6441090300c00c1ca0900d011040c03519032942044d00201e60180c403035a0801400c030150350090740c00a0010412035901c078109069015244c5404c12200d801d0403801002c4800342c0e240c0343c01e140e07110320311041c1550b0184110121440c40c800f42aa50300d40da20003840001d200884420320a01700c18001843d11902050405016400100403500c0d5540310030b122a442082108001e0031448248000443c0a0b0308000300b98644031045a601c0d04d400030515011b02e00040100032040000b008540540140d030414083c1228540c4803080d542c40d03803032b0400841e00d4813800764480365002610708148010b0003c1a40104641040283c181d0b525030780384c00040c00382071400e4481e10b4290031441004000181050003c0135490340003085942c1800c070b10f400280c6135801c2500101c800360001c03504402c10f10241d12642803c0982035400d10306052804600c038090103060721803541072640b5114500c041041650100000c2c0 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 434763480 1250 434762230 434762269
    0x406020c0a0506040c09050c0a030207210c021f0f140d060e04110a03120e18010e010f08010603030f05031906091b110309120a0f060f111305040b 64
    0x4241c2424550341d03a00c0d00703680c1512218240720307000c5030b1040c0900840d403280403c2404507142c01c1000324120000c0d48194800c0c0d031044104280201c10224010045600c014941c2d90b01001d04440c2c010040c80007280022114107411401403088410780100182e8003509070390404050f0341802c0042005a84104110841614681500801c90b0a4210032132409280070300d03180e8102520f01c00c14404d0000c601e0202518898082040d05000c0340704031b1a169074084041e00c030302913040044500d15031288080c0c00040754020011b00600420280484174070041c4481d00c0240060b5140d0346010700b1010101100b00c04014000000503642c40c900080c03a40241c105250070418555950486001440480e0081e2544844400c520381483e20640e0f248010b902c101c00910300c1c0440d0401040802d40340007800181c9406885581c2022607070741c4520042d0350303014840c0400d280740700d038407d8000c8a5405401d00c1c1005000c0c02001820302d03004800c1d03c185c413816a0005400b540c080c0014800004c0d004207000300 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 434764730 1250 434763480 434763493
    0x60d02180709090c050901020606240c060405010507090605030609040c0e0405011a060f16020411030a020301080c120d202a010302070f060b0f040204090b0114130e0406020c 76
    0x407181c0c8226504221850000c040100d030007100c8007220070340310721003050340180d00100102c0c546141489202240d0304041c9104a0844000ea040c044581c01006800d40f041d00090100300903c01d0a0254542c040032614145103440c2c11b20710003501c80d00001d0500c0d070240b010f1100240030171801c40342480c007602030451172090750f16003132030000c2c041e00f0001d44481003070920341e10004803030502e082a01c1c0605a504001c90602d10b10b103a0218001e60100c800781c0e440b41e2510f40208407011420025406003188107400750303aa60600c04504d19100e610304416014528454a400740401c0c086030404030303956546030082d28000745074001800195030b240f030121240031718a00c0b6141d0014809681c0e840c22803401c0b80b042030f0024030300150220701902c2000341c24442520b0514001810301d0388130107070410008001c200c50103184400302d4102d820640181d41141d0791060f8107419980c001ca084d170040746c80610001d00d0702c0001d0400d141c2840c0070b445500403111000d00850200b16568064450407580103040790038 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 434765980 1250 434764730 434764741
    0x90703021f021005010807091116030c110f09040b0a1b09081005012103090b07060603020906040e1009020609090403021e010c0c080702010e0307240e09060d0218 71
    0xa41e03200044000c0140c803070305000e503400c80694000d07a812621541301500c0b40720300d0500f455015140d0440343e141000c400700003000010194441c215032a0380a40e640c04090303809440d1507511040d40b181f0040c428461115003607030503940e8848856026a10051403804d0780c0f94100520060800d00d07202241c0b000c1c1c00d00c041c0c41c0299020001c4400c458201040710b80c902c400d100c1d5003003169000e0040444035031300804c50f050500c440d0082c90010300c0c8245800903450382c0d6581c0358040d40d0009441290901d8039248104254030b08280d02940040084404102500800c8801565480c51079203801d0440c1d212003003a0b042d555841e017601e40d04240900141174510303240c5802074031a034101c1100c0c0845094080c81880c0b050701403041d181050385548030002441490344508846421003241281044030041c80280b454034280400310082c0444007500700c0e103182d0103a450f01209016104981000a5588142c000d0740d80c0c0581c440d000709e400d03211100c076a40913001240350440101040e85442219100340300 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 434767230 1250 434765980 434766019
    0x1020c01050106120b01090b0a0807020715090e01080615150702150405030f0a03050403060218100807140c0a06020d2703021603080a11030c070306021c0c12020309070302 75
    0x101c6245901801704441c460600c0192421000d90080000341081840b1010b040780c040c801107904100d1074011200710300c2d61010100006c03511108403c0c0042c560380f00422082250800c40c901514100f0003900d4140f8107a0504545a003662802c07901c2010b5400050703540382d0201003261103a81d0050400c52241c501341081340d40592242c450300c1e000b442400c03c1c80c140c402021503003412180d41a500c0c11f140900d1500d81c0800383d00102c5440b0090010030640301002d6450300f0040900d4034450321001101d1500100c06001d001e090450321030303440802c00c100000c15501003540500c151307200d08010303201c50000d1880c0000341001c40c0c2c024890340d0000700d00c5c0d840210040d03400350b40328841d500f03c41c03200c6038448100100611620008025000910000450502949900050f40391000440c8c1c10659101030580ca001040c0d40251044c590026928249880303110b5a040c3d4103205800a100d1285403074401402412600d80c0be0128a50200c08660170740c0060100343d0041d0b80081c220544a001c207910329 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 434768480 1250 434767230 434767247
    0x537020403060203090c0303070308160306050a06110c0f061204081b03040e0115050d050414030f0405090a0c0219110301020f121003020906120703080307030518060408030105040e01020c01050106 86
    0x45c0b00903c50030194001a2600004645075154599640034140d03e44080c0c012101c0d0411a4100034180c0301c443c04102c940312080d821008143c0c0380d445c5280c2412070341050741040c4440c030b007090060204282c01401c030346610701202c07044002e403010300c0140d50300c03400c1c899614056842545000402c282d907002c0c0c0120000060000d90782075011840060342c1c0c61511070340926138801001e01191041c403110100300da40358001a07006014040c401203280d040d00855095a1000c0c400d41140800410280910f0030100559540001207082c200042d09107101b02950704d81d03551800700346040001c0e80c2003081200c1d40303a82100d5120050000c3d0b40ba0020300d4a500e240340c000c64003062510301400e0005003131100c40185001107a80152400089894074020303c616102da03a00021081c2c483c01c01c000000907030382401140b141e40160340c00146424006203030010010700c03068030401a485070081c0808118010112411240107e40c006441d0350000c0d4118003a0207400c2d00b2004e25441d240000521540001c0007 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 434769730 1250 434768480 434768491
    0x109110a0e040b060d0f050a060507141303080f160f0b130f031412010e0402030616120207020f130915140103150b0915030601090537020403060203 65
    0x84406807a100350103050350003100c02400441054001c0794290a2102002d14014098110402e2214440d00c0c1c9030b240440040b000c40700ca030b580310100081290710840c040c106c1401041a2407900c11041d00c9002680c0b031a000240c01074000007880002c0d802c54408480c00e02c42c5200d001d90741040f02c2e06240130700d20358010b0161481c0e600240019000115a4549882d5135440b0748582c9001c0070640b400c403808800740080b0210140104024280402002001b500a004103281000c4038602441410300f400c002400c40071a005619080d03440c41d5400540080001c90700c2040146c40340328a0000400642d00c552519801030100f1200070a052501d8100c0907402e402040080008800c0044460403203045104070410144a1401440011000c02000503414201400030400464101c00a60101030a403802246403803040b80804103428144a003e004180b9440c0412240c603048454005400c1510301d22501c15800c0a00308044a00042c4d2041e02514000c0085480d140c480c03a2a0009520541d107 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 434770980 1250 434769730 434769739
    0x20106170d02100501081b03030409180203070504020c03040314120301142e03020d0603060510060e0102030306011b03020f030a0e040608060709060c0f0f0305091c0201080601050d020408010911 85
    0xc043d65482c885010301c0d4120b607000310041510a031007070300d400300300c01c104801554036000c02c1200040602d05030181da0241080e888280d0b08021181c0b0400d40b0789991a4000c40c0150f0040c0300300602c19101005490450343c22241c12030085d900080c8103030418802807441e010314407004c0000b0a81044041500c0c02c0b007902a80c11b43e01d082c41421740d03031034080070801103c1806244401d1983d1510710a4001d0301103228020310204215440b44d80786400d81e4812944103c0300000f040041062560000d1440b18500b020b0001d5403541c10050002403045a12052008501c0c0142d091803080601c01c2203a54980010442600c0d1145021a0300074848803420703003450701c03c50510b00081100100070503000d010301d02d51f48520007075503c1c041703042d1412464050180c1c0c6091142c2d010b40c000c20030103c0c04030b440354031980d10543c3e600031400801030345010200712610510341d01414400183d0b0807014154001409081c1240c0341c410091249020b841560000b181c075500f0b0140c44030400c010000092020b00d012038 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 434772230 1250 434770980 434770993
    0x51003020901110606061c06051203130e0105150702060c100e0c03010213060809120a020d0801091802130e0f030a1103030f0402010c031124060a0303020c040b01020106170d02 77
    0x5103030a50354030702682e175907074424801c000c401621b01e00c10043c50303a035050041020074030554580008407070350804000004240c00c0003034840c20800b51842c0601c003400c500d19800b4410350610340070803404070b50f000300c1c00e00050340000e1200943d920a01603c40c00b52015040340c450511003003004e0080c21046038038140b14490302d44503144603c0d042c000d44005120302464400340030310b4002c0444200c40090300c9401d01d8051540514400d4070720300c0050070038401c40c3d0000d10140c007907050014051f0380140e0203c1c809030301d001d16150200d070004801010b601e8044400491800302685540c00810447c052800780b889001c1186072882030210140c0307000344094854a50b80c40140200a440384800ca400c4500c042101000034010f46c020742c4079900040c06071405018100c900c4005c1860640c035019465804441c0110001c002d44001403416481001915540641499640c01954840a91404070720450700d4408484141c2d100b50300060003481d03003000c000c090245504020b5181d8400e440400014014031 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 434773480 1250 434772230 434772257
    0x110613060801120b040219031208060a09140f04020105130602060a0509070e011a1e0c10020a051c0f0c0503070206070c0c06081801020d0f06050d0c0b0d06051003020901 74
    0x40c0c0e007000ca0550881070400d81d0f585c8550070800280348480840790b40038552240032011401c0400000120074054550705030f1420000104a00000c02c0d81c0884100d6050113405100c140101100c00d41101405a94800603141c40c401070302c26005620300030025011218000550a500107002030164205072003c20407074580c496155250b28460007030711846017000b0010822010008082008040072008144c104040804004840c958200720450510004500b14011b000144a0202202c1842d40218135110917218081c000340610114101d0940480800301580e082642001c1072004501500708014203192601400c943c0040c0c8100d80144079050005030345a00848500c406182c0000c042c0c402d09280503c1202c20302d2004152740c0340e40000b400c000c5800e030824005800070400740c200116200454458010855401d035211500c070303003d20950100071902c8500703400166400b44480d25680c0f1210403144024021640c0142d4010b02030381020300c03030203504d54040c00e136000003660bc5000c001e404 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 434774730 1250 434773480 434773499
    0xb040c0215010b041d0702010b0402031806060307140d020102030408030406090608010e071d03190510111e0702180f011526180304030506040b010501050414040504110613060801 78
    0x950080d0108215840151710a01e10420096940b00f9000e07c00130605162001c0481c00741c5e00140d50124041c0e40c00c1c96200c00e440010300c0090352069042e40240340c0280b4020040c100c402180031030320701407001c0741c2c4104103592080c004c0350041d00200003213965031540c0c3e0000908012643c0304150004414100208541640100d020301400d1650703141801c43c84010110f9010031840305803070b54503206020555250740301d500500164103001b00c01400d04144400c001d4803e49100100e4000350500c20000b40c001d140b25480074443c40c110202c000c54a0380700c40c1c400716012441001041015404503001c109500d0581c1c007295059901d55182081c02c0055280c06031400c5490745c4080004408103440c0b0280074440350b0100354011084203104a00c2032036203500c20308552060300107890301d0b08a00100018040d811074500c3c0109020f18041e89003902d8000c0c2003005500ea105801d00c12502c65010806001c034288551503e00f400800c01503071074103d841c2d04184016144500400307c1c120b8000041e441c4035 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 434775980 1250 434774730 434774737
    0x20d0818060a02100f14072102072102010914030a0f052b180501051807030203190c0905090a0c09050105010c060203040807060e1b0a0f06050d0b040c0215010b 70
    0x802c3c1c0c009003d0459998001d1002d411303e200203d0103655116180000900700301704680c02480c481e160b201048401d02100c40d09100e0002c85a200c5600401140c4000740d0b0702d4802d1903038808510082c048031000030000b2805094240000362445110900303084444401000030440031049844a440d51803102d40252840e001c2e007c3c03100d00c50802c1c040607503a0b0345517007040e80d0030034610721800142c00306665200c280c070f505030b9500030381d010381d5507000b00f01280d000d180401050203181c00081c003c0603d15170001c0c3d500c1070600842800054842c610504105821500001508178160203101500e0480c8100790b8640304501c00b41e805450203803001620a08a12030719040e81da06030346a91801c0c040e515403102950010700304803401e4100704001d0002c54003a200300c0300e9010049010300400240c0842c1ca1040794070200c0780a118052008040044075000c0c1034000490b406410141c0e01e800b00140400010400300b008140c105050284c075180080e804146d0b1240ca0903030110344581c50342c0f0381d13039030020341e02 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 434777230 1250 434775980 434775997
    0x1206091e1b150f0503070e040e030706060e06060f0c0c0a060f022406040b01050d05010b0316140a0e04230921040e060a030f210c12030c020307020d081806 68
    0x11803083c40600c041d03210348001c590100880c20f0140408091078045000c0302d10004441e10b035031708042210020070006008003801040458810107182c107000c400036140e40700d050101c88055000040300340d2903000c01e000007500d054004203c0006543c0d92031020702054a80058000140620351044543d1054114903140130005c002000d25541d940500703000042600b8410141800310034880d80d0300300c600a00449000c0c2910030026900da06005102414031007143c0e0200007444011420707851500385aa0951b0000c010515050014903065004034000b45140c9401980e10342000311048450044d20803a00e011343c104004440c0b16904201041c0c10310b000e0300b09048410358040008200c0c007140a40201d80021000300500c85c4a139a9955001c00b84d4441c5008030b0311074404c91880404c1115005110080e1141402c103055a0001686c0b2440c0c200114242e180505550740080a01c5501c2007090702d920903806401144001d01c03506012200b908404035588040f00d041d1138101d40ca0405405a07403841 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 434778480 1250 434777230 434777237
    0x40f1401061107030512041d07080a0b0418050a0c08070e16110a030905030d08010509130c120b101a070b07260702010b0a1206091e1b15 60
    0x603400c0a800b2682c051159880091901c0391200120124405105d01e0101d800b02d548815529854840c0010042a5145480c201540010200241c09030004c1445910160b07101000940042a0001400401481348285444880c00c100441004000160b03090014091140700e4080c1d941c03000c0c41581e4000d14090551a0100d800104103800700702e0030080c0040ea032600b080003092002c0151185441514501500042c0010f00204180d0400344001224582181381003221503042c100803441580c4050542d4a80031109203c1e5402d02c155040311102600107a40900642400d500304081d09280a441014102000c08000030b04884100c0004e1100e200d2064501e007071050644480051480080003a414010304030968001403006a106c02000e000110744604d0710705203800000e003111000b103800ca004801c08001480880a070881c03d102c8030350b00c08404601004107140070810002c5c8200aa401881c0204906d42089509128140c0b840c0039201318282190340d41200400c07400d10a8101d6021 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 434779730 1250 434778480 434778521
    0x50d020111010b040509240130050607050c0610080d050a031103191808090f0118081c031119020c0a0b0417030906220b070b010302040f 60
    0x5501a00403440740000e05000001c9281440010400369082121034407940c2c0c000c8040303d0a80c500b403407852040141480880202581050b44110b000041524402844200c100c0140d24085140d925425229481030a60b101ca0400b1100501340381c0000401700c20b82d00a11001800c04000540458101d41c82c0000034500108501000e0380c6030791110070088101503e80030f8400000c0080802035005210f078004084c00c1c18840840841180e640203140310340c54525020407004600c0000c1540d40352001122609103248449006035011228008006440e41403440000703000c82c00462080700c0a01215450300340c000503a00124201c0d0802c1c808a0401e100a200c01844400301c84031440b0480800e004a91032480d00d03800286d0101c0c65a03000200304200003034103100c021507001c00e80510009417401076081014000015140e40101d155140415240d0740360780f80c0b002c010008460040c00030f0b204403940da00c2c2c40e00301007040307034400d0001344d00450608500780140f25680c400c1405414140f60007088 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 434780980 1250 434779730 434779733
    0x70e090c06030903041e150f0f1707080c090306010305010606180b0d09030e130b010f0f090b0906090a2c0c0702040b040b060406091502032b090f1b0807050d 69
    0x100d41113581014038049040030380891100d00a2542c7ca203862540d4a0308000c00d202003c004103215040c803d03103001c00c002c10301c0c10030b032102c0324581d03481d041103a604080711981d44007800ba50240c061046500d9061187d00000801c0c4101907100c1c4060350603659603c41d40441c2c025000031802d10302e1203120240074080159803008115903000314481442480c0205070605600e00103045c0c22600051002c04a5480e40a43c49035038110b0200c07078442146050000b411403009002800b0103d1a125001c40c41800040110899070380d40100c44d180f80008060002c2c0742c0d01c503041c030244c2444030005c05a103404000c3d04403c0750603541d042c1038890390402c003100789460780990a02c000b90165044482c0c000c2e440c0d04110340c09a644030007420103410169a400102ca24220740d41c06e009001d09505000d54108005440480415001081c07000201c80d000520200803100904000c003910800a03041102c043ca0702010880500598190902c414607003a03851074032054480d032100e140344100d583c8206140381490 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 434782230 1250 434780980 434780999
    0x804050d081b0a03020405220c0e010e0d2105070c050409020f190323061f1e1509170c130903170403210203040201020d051605070e090c0603090304 65
    0x3c8075407440d015082c2541e88001c6013025400300c10340c1e840d1b40200c2c905107a0703141c0b0911032406003420610700302001c010300c030300064040300d40301e561103018129545000c0144502c08515143d040e1600c0b450a041707500c140c0005041d40c00010040300ca02504060016162078a8000ca058442d001450b40e1283c041903010401000c504091901c20024031110001c0850b24144544114034112950310174500d2641005604000c002012080c52007000a44410b504014418003002c0c0c40301002c09010000c0e541140390888152a071001800814654141181c20303407281803d002c80d802049510001040e0014590b00d80155100441e0071808100904131819120340001040034020705010854500c002c005401c04c00c82158203501258491711400680244950354540c42124028118114200350340005c0d00c406c00d150b420300c02c00c000410071074180d0690682e10480305500c9000c0354031032941d5038903001001104036140704081c05009445ca2090a0000403a03104584100255180a04000116 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 434783480 1250 434782230 434782237
    0x90a0606091511060c0c071a120403050d020d0906050105090f070e13020d020910050f0f0d1b0c0507051002420103020f0d050d0c140d0804050d081b 65
    0x1000c00c5030168084411010511005000e00d4040801740d5640407146d282e41d103801c0c0f0981c0484010703541b1000001000304100d0548144000b14803c4803a1034849040403507050003031007005090148000b40c030b90268402c0da4041000903100d80740c148500c2e030760b031070802000c1a000c840d07076044210b4000000d41c031684070b1001402070010090120b41c0d45182070f013000c412a0050440120442c2c0c0c00125852145030220481d0f003c3c0c0a1440c010b40b510310009907010090003070000079030701500041003494010009400122206a01a440c400c5130840c10704000c0a10741032210554030341c02100004951403c00141016481c42c4907001000c12840c049010605a4000c403500c52600d1041829030009a60300c80c0c110324205030201c00702c8115415401084084002c3c0c9200b10b2040025801a1000607004101c0c81903028003400c004803403408c02d0801c0451207000c08850b60321402005860740c610768110007103500503400f0b40210f0380080402001501c0c100c2d03040d41c1419110314408241c98100c6c486c030004 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 434784730 1250 434783480 434783519
    0x1409340c0b0a0b010e0123070c21080d020903070b071b142407140607030b031b06070201030608010204060c03080903120103080304150f020901030f1401061115070c02090a060609 78
    0x4070841c060a0018030700b407a0008003085801e160204810000d07101e01007082030a403c400c1e10500d011040c00d9441142f03038420843e0b2603100c9034011442c4100750364113021010041201c23603070050380c5a10500c0c002c03440754200340500f900000100c0c0045500d4005c80001c8100d004098098005095415189400b2691030740e0301d2003107030b80300f0000040082c40d09600549909902d0000f44010b0074104405401d40711100d8001e4001d03480380025503142c210780b0980c21546071041e10740b256200341c1800100c001e05403075002104190f00020300062420752045041c803a040c0281d860b00f0081d1201c8010f40c1c0c8034810321958a0300000c40e0710050000c40c20900007942c01c1407140701c2c0b608400381c00850403401d4920502010030050f43c00300300e881482d41c040c0680703940d400406204101c60035503d00900700001f41801aa000c0052685401010003402c00810074841060010f0503c50300d072101d401450f8501901c41203000d048003101150a80350b40f4045c0600303448040d110141807900700b41c045641240032134107 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 434785980 1250 434784730 434784767
    0x1707210905030a020607020706110303040303020a030f09050c10050301050f060f0d290d050d0f0507021903030e09010b071e1e0b011409340c0b0a0b010e01 68
    0x403150000d40100300820038043c098010b0962403502d008064100401d6900c0f05051107800002c1d4915941c0200c01c9a50042c0d15083c016142c9103100c2c01107009280743c038a0010034600d1f0a01c1d030410b005000811401c0004210b629034899441a00d0480f41c0d80000e20485401802d00c0446141c54178041c0c0190010841c40c0284a0900c4d00541c14401980d806501d010500c40f100320300c4192036000145443e080c074100f5584440007125642d80c8aa40751090121441040071114005501a101d04112040d01da0024070040c100d206800555200390201d1004801042d19201e00e880b160030940905412609600c0c90350782881c3d407589440d215940001c824019420950b2074141c0010034600d40d40010100a1140b0b44d142c0c4110b240540107100103070069500c4030450042c14440760b66501c000c1e903102701c0006004151140c81410351280078009850490311f4a82e07240c041c40c100d5413010135928958022640fa4101d512040e481e141150400c0384481d00050240e2000112075002c1c1c410982c09030044807 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 434787230 1250 434785980 434785991
    0x4020705150a060806010603090203060a0c020712030503150a08210403020a0306050906100f061103040e07230a1403040219080d020714010e10050c071401170721 71
    0x858108840c8401c88000903a141c1da510244010b00f810480d0502407c010b041c1040a48030a030002560380320001d00c40e00394a40c4500100c000c00d4801d00542000700890074a00780d03016940d2501826503041100c0601c0c3c511b50109204000c1d05d003400c3c0300001c8482000c080c02c406404040e200f41c1d101400b045c045440c5004000010058450510b0480114090305000034141000d55146050803c050107000c02ca0f404554140140c403500101c10044540500700a050030450f0501c3d54114055a40880001441e10042080142e0004a00e5a40c280d807a40c41106407030808094080380e00031420310a001441d0001c8006e00c58070381070001c581087c0010420310712003020302e034200741090300c60b00200143d41049080520407501004402e01404640b11209003045000c00000d20720000c20034658400d1650000312207400b4026003c540c0045180b000350b5038440d0b00c2d24818080c3c0d43c51700c0d060b68009201030558111205c1d2540b6514001e1001e0340c0c0c1e40604c03d90101541d080074101481e00170b001ea5503038 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 434788480 1250 434787230 434787253
    0x405180903090d0c0e07140f0a020a0519031b030905010309020609030f010b0f0603060f010305060d0b01030321051501030f0b0d060f0513050a020105072d060b011107030204020705 79
    0x1c0400c3d0018894145085824180405004054000350010003031080000212200c03440141c03e58140080482d888c548403070380180220320340b000104000d0800e0103540400341100015654500c4014040d480b925100c800017094981c0000079000042c0001e4800007041c080d56100341c004d2004640000e007034a00300340038036000905180e414142528280c1d52035814042c0703400d00004244081070201e410030709514010300403880300040660300382d040640d2100010020b5031a0030040c54080e8020201031641d41e128a00603001a41d2000c04002d2820403444501c0158094024148941d140101c1007030000a04001940602804025192550f40350703800b40300c0790b07201c000c50103450500421b000725554031b003d0492801c03590003400036849406040c0703420740400c100044113078490354286050799840010341401c80722441c08010581d96440d002002080580e5070706800c24941b070154000300100018000107490400d80c85a10364511b8020340e0080000d403171f15a0245c103070140940250381040518 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 434789730 1250 434788480 434788489
    0x11010507020c03070605070206030a0f02130305061f1d0a020d021305150304020915060708030c1b06060102210f0318060619140f1c021203040518090309 67
    0x496111005900c50a1900040c1c6030410809004041c1410b100340347c11416004039096120003000d88101d0341c0c0301d01d00041d8900c80f07541101d00a0b14050103005880d074070ba00d0801d8a030b10341074030404100018003c1c404404c900c041e40c00300850b1344011004074020751410310030f00d0464000304840c9005500344210258444240010700c4400002e14056004a080c9000c100c003c00c01d040030000001002c2c410000141ca84041164120100301d40c90560b81040344002545441a00340040001c040402840486100c6e03001511041140101081050105048203661184100c0f201801644081c011407019411000030740c01d21139200758980e144c40f099071a000c03865030042d02d01500c2082c001c0c009400c030003414400542c1082c03080780c492000b00b001d030000120701d0300d13a80503c07002c02c1031070070f003040f0f0319500c04403130f003503c02409000c81020b03d038249030040c44d42d401804141d01404a048071031400c00f00200c1290181c4500404d031900c114844400d032202060001c2c5000c00741c0c40200900341850380d5 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 434790980 1250 434789730 434789741
    0x40318080d02101103010614040317180d0c1a04080f150f131502070b0a020d0b06090603040b041b0306050106030e19030e030a1515050607051c1101 65
    0x111500105030707a059104009280030070380244078a03a03d24001c11022204402802ca038115052440d0409820040000c0b034801403056520081403002090204401c900d01d9002406c1e030328044180040c24031440100744a000100e0440003041e0440c00c07401444501102c4046407000d0460000050601d91110001454a440b2500940460f03001c040441e1010840300500c03a840140585030341000c0c10500480078851994201c002c003000041c2000010018060741a20f140c990400b0211203942041e000f514000e60110840c02c407000c1c10151100124201081200d60688c005000d080c517541c3d07103032252841034601401c2284c8401384c1141801c14403e400c03102c18050b5018100c009095403502001400b26065804110b441781c100381c0400843c03a4410004900c155018200100e20500303440c002418070b009230380010400181071902c18840038159204071101d000d11300401c0a010780340c00c1000200c0c01602c80007001c5521514892000d4030f0030742c00e0758440c03064500300208020f52a0b00f1705420b40e031 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 434792230 1250 434790980 434790989
    0x7050f0d1d0c010f08130212030a0e010905041a060d090503072f010f0c0302030d0c03021306022b140c0105071409060d05061306060f022112040318 65
    0x15540300d0240302244082c042c45042c01c2003420702044c0d071060207101500602000f0b00385c0a1142c0242e80c00c50664955480c124100200c01e010703a95110b22100c0081e000d0181c5403d22800601c10b4600891720341040d2080542c28806038071424014110041004140d5021210070b1130b10f151282213040010354204081e01d8000d101d0700d100c0ea20f25101d4404d2020640340041c50110400044802030180d98020a659921b2001d601e003442150000c0d0070103a1a40c4502c0c1240e4450a1800111018403030303141e4042c1060f03038030300c001000b815582c44d0012a5600c0313000c000021484400b00003e10480d030390075690001071101c4e04160782c0c801c0b900310301d05840e03400406000360310740d4490081284080c5d00840c0801400d203c0301100d42021004804103115000d0101c41944050f40c0e00c021943380d0b038a1000086035402c00900512400e901d480b801003851140c00105030261280822011010841d2081e01e0b0034281c11120341c600340203070740c145a01c100e08003920540601c4060400301c451214440180c02c06803 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 434793480 1250 434792230 434792261
    0xe09010e0d17060604030c05102d1205060918120f040504140f06060c1609090b010603020a0c02100c0c0b0a090608040f06050c0409051e07020307020907050f0d 70
    0x6100105901c0303100b60700824036803240e02c00700824400200c5422000003541c2d07054890f030035000800340c010f441211040c40c1c901c0c22654010f12024401c01590030072458440b082d510140310208911401c030a507002a14255803200caa08002480c0080a1852079110040306040352034403121100b5401c0180c0c4030b82447c07c80301781d0005040c0180d04250146215543c881e400c00005480d048200040d0110040c040501c43d8400043d10304120b0b03020070800310804120085103032996900c10911008150640088580500c2c0c040001400c80c0a40b00703031001c04441e9101c03207604034210784c20443d5000c20744041d902403090103042600401c0d080c800c1d10025040901140c3e5503480703a030070040c0982846903c0b00d820800410300300f00c0000c201c072a40e140314650046001c185501d4010b0b0b100c0441c052030300015400382c0751508012040400440c100c01340a81404081595105c2d20b400b282c49104502000c4e40000006000c21005807090008181001100f00c0503828007039000f102c030058801504402516 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 434794730 1250 434793480 434793497
    0xe01060c05100614120f0c040b0a050315150108010b031f0b0d06090510030c030803090307080d050601090f2301020c100504030c051207030f06090614070909020406090e09010e0d 78
    0xd08102c012010541c403508000c140040c50201883d41d00c0451f101014001d50f00c4912140154030f45a0740d45001d000f00400762400701200b80a4402c080d031007182e222190141000c16101c0039401500094160380c5500d0403e072640c2d0703544440c01349146e44181d82194107000d1b45000680b000350352000e03100c440d80111002c120286400412810340b4000b83c40e030000c1e10b200305410400164088032a1046030751116003292295941c440356800c5029040c009081502e0000b60644481c600b68840f0748900401d1b00e42c07002e000e466408400e804d500d64011045095070210420a130b0301d0307244003601c0e880c40c014811101c0000b141e80104907002c121041e0400880c0000c6028404c21270b240311000b02521050b07500716a10000c80405a980700c0d003070f1001806003e0090309000a0082d00c0d0490b105150b0404003c0c40015950181c010500720115a04400601c00d0580450400301074000c4400b16100e0740c0c0d5113124142400300c004002e40f4040c20144e0559611314007000b880809125001c0b90000c20b0710b581f1034 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 434795980 1250 434794730 434794769
    0x1407150e0a0b18220203100807080c0612091c0f030e0c0607030503040807081201030201020d02012a0207051e120708060a11071b060314010e01060c051006 68
    0x20814441d008451110000d0101c0c80700c0301d4161100400c9030b40f04444280082d440d0305503195078800c103d0000103c41d030000040140322100c00b254401121210f004036401035a030343c58010b441d04c04041015512100c10066440c20540700c0d400c240e04030380080e094a606007141c54010000d40131209a10004c96801d0302c8007880f40b901403160500d881860400380030340c0b160440002e603003481102001014070801001240910628000359640c00d41d02c412004c1c1e03542c0c0d619410301100002440128018803840018809582c8180544603002031a0008001750403180490442c0c0c49070f48884481c1103120340e5400141a82d5100e0b42014103000030707412035243c10185c0092104610000904034240d9110715010010600001400740c0d000030031101c0000c02c1c412107001403902e84200c00020b070000315840c41055001251100380170844203252030400c84044001800407901400740f00da64060b83c03248004128090140c0341c3c1c0300c00f6510810035541400003034208a0115015501b004000c841c1000300c105 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 434797230 1250 434795980 434795989
    0x21060f060e0a18181212060302091303120609091e031d13020d020a090e16050f0c030a02060108061005030c130905160513090b070e03010e0f0a0b06040501060503041407150e 76
    0x4886e10841100780310315030450300494600c2601500103110382200035064001e0501c01e0408282400c1007207410301500d070381d402c0d407200074080d8080e064480c402c0109a41a182030f441c005031300c0d400d42c1f41d1900300d84280c4111803850351520096030706030041d11041191000803041c1c8002c084c1c1c800c100d00c00507201d10048000400941590304180340c00d10b18070f07040c030070f9900349040f820074036030001d1400c1036403200d20522080c0d19002e10004140107200200d44140c00c1600841c07002d050314249000c0f0781c0103503070f80e5201904031341c070903c507498040d040803000340d5841c10844982155820300c0038004c0368519055070394078600030101c1081c80504a80000510840c07800d80c104005001113400d0a2007c02c100781c0362412110030152503201404062040a2005d8600303410820803e21001c040d1180c1324514080030f511101d50703900407949000524002038161500c2d01c03580f03040c1e03092580c40c0303400c1d50345540d9246561070b00380c000c480e146e01c245040014031030f800c09844540c0383e03042d640f0050b02074190340900 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 434798480 1250 434797230 434797247
    0xa030b01030605130206120403090b070506180303070c060515120f0c03031206042d0605010201110f0306010f090306020703090512010c080c0a21060f060e0a181812 72
    0x2d813409214444c803080580e40d81c4044e24460a18454079090341e84851030b044e180c7d59000e0f03101032140b030303c0404c03c04180040400d0203441000088a6401101441d011081c4c0324402111a0170204180c00c4414000c80c14030740c05141d11031400c1d2860000e1214450019100031039082540c0b81e640e100464443c0310000601038121301480c00e03001141040404450800b204a0040c2142e0046a0b6440c9080c18032030200800580b5a40003ea29801c20029041c0b0b400900032a0003084d0140d0b0070105034109c5500030784202c030b10300900c8030849070842c0c60f48001198828607004e551002c0120303190001c0040b07600740c40181441480f94441c4107845d031a05003130121580c090301c401c2c0c030203902d4884002842900304600541c440920100260b85106a020507260000049102d040c602c0301000480081c05056100c9415144240403420f481966200c08450320a80361840e6a000b0b900d041080000c1c20500c008200e0380c0e000c0034400b040300c1c21a195680d400c1c40d2042401d980301c40c444a0b90310545038011018 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 434799730 1250 434798480 434798491
    0x3040b0a14031e0a02071a06011d0607080a1e030906230403031d07080105100503060c0a080a060302061314330c071202100504062003090a030b01030605 67
    0x1290039407070316030094250380c500b400c050000714042c480001d00c0e00c0384540c1103414195100c0864100c0f40c0c21f9400e5161092021902c0328007003001e8812064100910034a1300d1403a032801400280b40031426a40c02c2100c0c2c02664000c420700103956080b8011f00542c40fa40540d4049681d0000340110720381c10034000351005282840c01c004c04484143c2015030003020440e901503018140071481d0310704601d168854a41410074040c450046200100c5e038500190845805071441079a100e600d141c842c0c04054640a080e00c404064070710811642d44018061410300340c0c40103000070001641036684d004181c0c40d5208280d0440e0508a065050005c1045806120049242905c0e090016001840c141000c400300c1c81c4c600c248440c1c060308140600b142030048920f45000301041d14101d5954483c014070343c15042204030300c02c04501024982581c400c000381c0c0c0450b0201da5035644040302d00c0c205810f00d410311164120143c00304000701215500c50b106614010352240c40d1400066145051081c11a10054203 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 434800980 1250 434799730 434799767
    0xb0a030515060c0c0111190602041706060a2304050c030f01150e0906040b060f03180c0f0105030916080c010905060f09011404180504020f0f090c0f0c03040b0a 70
    0x7007040c0354940080e03130300303061078017800e0400c0c54070200c503091490140c0f1590410f1001071603104e40c400b00080c0d500a0400c52310f45010070740c000480c042550b40c1300c10b03084a00d250444000c0e1410040d4207002043d03044001c3c5070100c4c0c141002203c03000725043d10070446080c10f034220000180841c010200030803c2c0100009a24551429001003000300305404008243d8450601000442c80d603a0352503005c4a58402c0041c1504e660703031f69030000501d10750412203028081b05610f600021460201060401d001d807001400604000c03500c40056074160400b070540740341071007006499010100c1038403a90010f800039100800340e0344400800144010181d41040303004030000d000d400c2c0c0401034030040c0c40a400c42400c0c140b042406211081c8140d0045c0d03480b408040c850140068040e0701c03070764001e501541c003c0e00d010b1100e002010510100949070000d0a82103402240000c5010021801609244102900c89450700e4240e1340700c80e15681050304548105100002e450a0040d00225036540180c803d42 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 434802230 1250 434800980 434800987
    0x3090608070903031d0301020d0606020105092a010503040510141f1401110a06060e0f09030705120306040f060e0601080106020d020703170403060513110103060e0a0b01090b0a03051506 81
    0x2503000b000d00b00404820401707011031002d0b00c019a5420f4060340c81c0a00d1490003084100d0380d45000070f02a02060b038031001e031401410328450302c16140c1010f4100c0003400321030724101c0809003c01129a94402001a44d4600903410f144540c245940030342c030030311a501c2c1c420002e41c0c1003a040e0740c202c46484180280035031000c0c0c0020820490206001c1c00121400d080c186503200300203640d40d003000b0051800408151411401250000b94800c5c5076001c4c00150b07252460303076a50605500d98038415100094050350060386400c42c01c54082d4019a8050001703840454400040036081051750010740190461004800400141b0b5900c490102d00409403413008120320424844060740300c83e2180405001c40003800c61001c140c280c0e9800312802198804010401c45c0b90608a0041c1c148504008680a004140c5500e840d513200f030180d50191640c40b90802c0070b54851982484c010565000214140f15001100198120f203000c00360442c0c80c0c00c0c0e1008110f9240180c5108e981c1601c000c00390b07200d004242f = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 434803480 1250 434802230 434802233
    0x501170103021509060f04140402181504080f1b0a24050f270402032e03020a081501050409080a0305073f0b01140307090503010903090608070903 64
    0x510003811240c0546440340806510b050680380e5105440c840d44d005507002910441d1051074400078001c03216a0300418010104040400040c0e10408400a4054030346002c0401e443c54402e400b0000300c040a400c15291a80e5400610b0078540d250003184040d40060a003030208000303091405e2810315040701c1c1c11000504014820050029044c0d408207110401c0c00e8468900c0d00803012aa0902900883c042e204d1116070080300c0c0740418000030803c8081c40b015080c0c080c2c107240c025070303010310816180d814901c00799414807050020040050304101c0c00c80700c40080940c40c1c51002c4e0020740b21903000f500d42c600400303183e80d500d103406a001c18052803130142c151001c035a054065407241407880c0380102d100c0c1c0307422104942061055002d0400500b80b804070440c900849041c60328405001102c61540d0078683c01c1d4001214126120130340842c81c481c440e0012001c07858025903000b81d0030f090003442a034550010908442c500c45003180401c0c00752000b48203254000c144103911002d2840c1403860070742103 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 434804730 1250 434803480 434803517
    0x1021c05042d08030f040203390406050405010306062105030f09010e040c020c01110106050922200a05032d0a17040e090607021f0b090a060f0501 64
    0x2200d40810303540414442d5066440d5024072a0301c403194001c0c0f101a240d0400044044080109960491180c800c6002085600c200c00e5640c1d42040032855031a503543d2210000c04c0f113950501500d456002c1d039101f1000c50160380b14803c15018600a0b280043c0c1c050800d00c2061841c0e040d440c0c6000880840140c1c200010000800c40d0200103446800d641c40d20086401659489005550194424241604008000c0c3c0c0007542403ca00c0d005d9a82d01042c061000000e801c071030310341c0216a00000c100000403200e91050300002c03030510038800111005119a1588460580b18400044189003104003903805803030070b5003000010b420100e002e0540520900305000b903010100c103c18400e088080c8c03e01954440c18029850030a070014100412000015aa60711950250042a9090790560041200a000040d080744a1441500104003c05800a00f04003140f1079908071406107444a400c0802c90300c500074054056218070300701240f414240907460f2110b24050700100c0c10080c1881c150014000c2 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 434805980 1250 434804730 434804753
    0xc010c1409040f06050d06090b07050705060c0a020f0d050903010b060412110a0f09020d05070201050405060103060203150d111e06180a09090b040308011e033201021c0504 75
    0x1c0c1160005682e01c0c8040348400600099481107601900c515413038010301c241d03030308070380041441000304c80c03030350341e00d00f90241e810740180800605564000b8000072200c0b2003c1b8000c000e00304541c0100c600500c0c0e070501e402d10304000c0700314030340c006500815100b1b0182403d0180864482c0102c0f03a26003094200ba07058000315240a2000d40b5640c80c07003907009404d4480301000c40107425240321210301d00345c0310b02a2038041c2d0300409021890a150000085080b8818440e060141c0c1d409800b40101e64a15110b00019401c05003051000c030500900b1a9041e40e540e0028196803441100e0440d600741c5030780b04201010340c142883c40700080390045001042c0d6101000c9828044990b50003190350405880400e6591080c1c0d0441401c90340350500c01d2041c001c204002e90300c118841c1e0394004e4a0383e01d07616601d104c940202800c92503502c0c100010310009460380c83c441440c1c01c561100341070f400f0201100300010300c101c00c07218507207941c0003500c1c400b0600044402006907444203030910203420f00c0da445080482 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 434807230 1250 434805980 434805997
    0x8060103050c031906030b0a02070b16050910020c0a0e0906071805010f020c061b0d09030210121416030c02011b030209060f120f150a0e060d060f020c010c14 69
    0x20300b800d0703e40e900519580050083d47c1c100c24950b000d880c0003103c01c0000d500445003a40c1070501d82000039003414054845030481001903440600b0054030301c050140c1020007414420950203013004210450311540742401c020104048000b80c54100710103030074207100006e80300c2400c214480c01e030080c401c01d55440d91b2003210402c3c03800706510301030200708904118502c00307207030390042c800951700c401442d00d03800a0381d403008240203941040404840a070b5061104c0e200c001c0d041042003560f0b140140c0246161600e2001009000c145d4000c0c88000104600d41141c0c01080c0c042c01c1c030118400d0b29418850000144840d0000b0080e920404854001c80700140080b1401c168001403002e955880b01e03019121303584040300000b5100e00e20040203411002e0b007190030905c00509940000c2c05401801007020b4200b50292800200d1410414000c4500398005e01064000d240e0180040010b0002d1054a4030541714950060311806441c62541c02c4d10300100c030010400c070240c8680c0d200c505140b401c0341c0002 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 434808480 1250 434807230 434807251
    0x5120c010914030109060609051f061d0612090a0501060f05060d0e1501080102040e0c0702010503060d020a08030c0109020f0a061d010c0c0b070210180b310608060103050c03 76
    0x2c0c0d50107000074007620401c54010038484c01d290001030314040940003603000f01c1000c07085207105030700254040c109400900c188000280b0904140d00d912600b41d880b09680e00740a85594980460f074046c101c81c8a0054640d81c02030751101d9502d1080c02420300c2508050014400f54186061801c00080c91500030181400612640d038055002d00c01c0c030411644500454008600e041580d5501c0b41078001c0d0410f105400090382600c00289409102004454203030790b05854083c15500e601c1c060200411a550b001c0760003904100d40850100b2040002e4031464811000100d040409481070100324403030303510201e00404420405210a030f4000d5444408001c1d000e8014030a0401c3d000100c45004125101030601480b00308045101c604050080030940d00a030b481c410002004c140455000c0c008120300c0410340c16504c41404807510ba440101001d2400c1d001c480c1e001600c0008603000164225001c40c60600c2203d0704100154025540d030364811001d007000c2140c0d103004240008680b100070b00d1000070 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 434809730 1250 434808480 434808509
    0x402040f0c27090c080a060b03071e23041d0609070f0201090209041208060a1a0702210303040218090a030309140f1e12070b04081603050405120c0109 66
    0x4400c01e815011000f82007400041c40f5400d500300b40075008500a40d141700c2d00c01d09165001c01c1081c44241117031b0003000350340d0351840c14001100c034034074110400005807420810112040c0c100d00401d03902500c440580811055680c0e403078018810006007098104031841c18a03842000b02eaa0340d1400c650740d1002041c2003286490b00d0310b290890041c40c8070003000b0341c0440c60900744020711043c2d030861426170040707803520120740d1681c004002e8504543c1c49600036584203462032030040390610b4090100300d07102401280000c03000c5c07a1900620060b2414040580d8808400c1000394a0808a013003030341603002102c0446428411101d944661031058040c2c10300d51504030200c20820031440000b40c604246007a00e00755030200594548a00c940031745e914107028040e41e00c5000c0000410038001007102a40c1c41d6203004803d03600e174812a48010800c2e00c484100303001800c04c1e030940c00c82d83e8000d41c1c03003541d85a6503a4141010491b070840780b23009a950907071101c1554621660000d03410025110312103040d410 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 434810980 1250 434809730 434809787
    0x20c2103061212030405030702090a0504121d0d05160f0612020a1101050708090d0504050d060b0a050d05010c0207061b1103011107060e0c060307050412020f180402040f0c 75
    0xf400c5100044920b2409000003080306110010001c3c0803498402c64201620740c135a5540c82c0b09443c401d840c05080404a41000d44510b40a04603000c001c1425603c0141109403441c002030140c0392046040d035141e000f400c03c507451007591850b64009425a4842c090815003040300c020106070040301507452056001540101c4603018816071460a244140203101034900b81200610500d01501c04103182c1c401c3c0790028054170300500c241d40503100c0151880c2409006925000003800200003016044209082d010645450b50710fa40e400c079034000d0002084e5400746000081c5000a280d10031010007001080010855008400400f4040c3d0491090b0003120708080000c0d0043c62007044020741100c001510740204511904501c1c2054000d10549039a02c2c1d1580a00c00681b20440e044400180100f0040c0280f40311010b06210003030018150781c0507049607a000c600e03000c0e00c000440c041c1c4581c0a08200442c070b0302c0e002d0240c1c4004c0c0c410b420b20000c1c04004010b030188105078810b40b82202001e200d0003 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 434812230 1250 434810980 434810983
    0xc070507030606170706031b03150803120415090f26030117010f020a050304020111030c07030308010e0907050a05060a0e10030207031107080c09041410020c21030612 73
    0x3405160082c41c2040000d41d9040501800f08900740100e000340104100000c686e4042e1003000205004000d44615103408014210b0050000814800454440682c0030501d1117042001d419422140c1412104608050426120a40c00c10700751920a80c10840c0050010b0880c041003118a035110f1044c8412a0f0b1700d41200f0030810846c070785070114030400b000000311103071048076a64188003c80004c03c40e10703c1d031400c868141d04c2071102c2d07400032800400c045001075104015191692901c40d0a81e400c00c0040840d85080202962050f070010300100018482390340b030700c070000c4d0f0420950b000038116145003a010030204030ba50300c11544900e1000c46c2e03000c0341d00d005650314842e50b0002089000c034034158180c003500030340000cc5d003600080c074807920b041560100000c00d0005d689401004103103044400f010070654000042c01114021054030b0089100c035800c01c10100c0700c03e906080561036240d00d220707481c64004c25220902ca00340c091550b44000c4e510a001b1a60440000e0b02d070b00340844042030705035 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 434813480 1250 434812230 434812243
    0x70807030219030e0a1409040b09030c0d03050403081f0303030b0109090f0f1107170d0b04090c082a0f06070f03051e040b03060405060a05030f15100e0c0705 69
    0x2980b86854901c0c48401c06a2110000340c00500444001500945074140212025030304030300a41c1100c0d00e100882d010418900b050b6601c1041c01007102d00d007100c448209030400e040c0041140200b0307150400d11040540211040e90301400250360083c55240da10344249002401c3c0c0310107800d0598811860340715910401c1200083c0903520414405902e014010300000c00800c014040b07100d10706600d080514003070104407004150041d54004d080359662088442541c489003000c3d51880c0e0380c000d541e86070b44560003000c080078000ca64a8011600e82000c080c20036490128420010b12161b40341e56000d4082c0b0f440d60780c100000c0d00c140c80c1206040001c6001403003062000341000d40714001c880100b50f4050011300c0b50549945210240352400c0074840050300503805905990074040c00000e005003084d500c81640308800034a05000195203801090500c6002c10280540e038204031100e110f158540d40e8074130780050740d034030302c60400302d2400320141c0a1510162210740c803a2000181c1509120781003101 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 434814730 1250 434813480 434813503
    0x3171803181f0c0c080708030f0f07060e0c01030b0616030e0612160306050f09011509031e060b0618091009050c030603010f06030803130507030606030f1a09030708070302 75
    0x40c0b5603556502e14040c081414602080301c09407208040802d04110100e03006049401040c02913040081d4003101003a86e4225030b482400d640e03c24130055003c1041340c016810280000d00240104d0b14001000405440c02d6150f40707801a4820040e000e40520310b415183d14068052402d414401002800223003a8815007a100c0c900a03204014071690a030f03e907a0505107260740341c5082020070b90310410f0000101c0d02680305907201102000400004801d0071f810303070b6022060305d00302b182c07540c07a43e50f401c5007030001e42240a4200d1041864104020440c0706007003111fa0201d03036940c00d2080c981101810078020900d418000d40501c0f01040c01010340d920011b000c0c2110b010103101c289005800a81c040d00200c400520a41c01d213080740110900a12803941940e80041040d8034550317a982a0200352044480120340e0352040000c00400f099840c45004083d40c41070f00e40c1c00350780d54039080101c4c4e820789038040391030b80310281403c0c401e0505000048480c507691080000742ca420b02d500b016420050348224 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 434815980 1250 434814730 434814769
    0x9051504050106051f050403060534030c03060e0114011202030106031e150905150306010315110c030910110f0708070807051507020f0d0317180318 65
    0x348010000190000c01c20703200243d840c950207900158800300e455000070b00e00004104104003d001140d000c0e000681d00038250b01c103561900c42e2000b80251141402a030000ea44401100351090b4150b05005910700c04a50b840c043c00031501340403000001007018414281c00c2d901c040c40e400941c1e4010b0900c9000790200a00131510fa41e074840001c4c0141405051400e81c00b580441092a0030381c482c0704a1000c08417406194040c1801c241c20b0400818015049001100015032240e00550b02003203110b001c3c5201d2101c18030381580f0f0507903900a860082e180045100004e000d45044900000180e07070302e00504a524882c400340303c8206031141100500b00b03110500948941d250702000014120085079014011202c2030359840391080d4840300070340540d07540b052045840b4130700c078448a8054000a80020203148842c00c040002a24400300c86200b2170221300d1007009500c11081e0072001603803010b00000e045565050150030716071240700d5500c2c40c40000c1c0103061072032116200d1440140d03003c81c0b0040e = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 434817230 1250 434815980 434816023
    0xc030f080408070e070c0b10051003390f03110f120703151406040924241101110c1b0f0604121104062c0106050d0905 52
    0x40c40c640a0340640508100d82c031400400040081520383c0c40c0384908040d40c0d91800e1601e071541d8481d04180090010209003044a502284a980d40d00b0f0342000c0036842d450006a2107125050b201c00c20b0740500099958540f0804100c0701d203145070f000d5820015151410520002608005070001c111700c0c400d4214140c00411151118240c110083c10006046408003000c0c1da1041c00c101d080d00c0380054005c2d82031040071004c112050380c1f0420070f120000020f110f0340c2442d441e41b0715081103581201403880c2e1001070890340c0488040c80c0706410090f20500ca0403405c0100c10344103010f82e644081c907680341088000100c2811080b003e511004406c0e2000b5038041d40ca40c02010101d540383c1801c03d18881307003421007040210301d2070305041000c049103015144d01c1c01c140c904100030303026400700041507030306c0c1c00100c24280c0103940e248a0034010302901004d004410250048025104201002c00410f20948900501000b60884141c6001000f03408000c50901114500a03041c0240c100306070081c10000c4 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 434818480 1250 434817230 434817233
    0x70303120905011d0c040504020319082104032304060f021908030106030f05150f0d06050906011508190b3c151c09020607060e0c030106050f0d0c030f 66
    0x2013a03981c1104031620100c0e004030b149201008101d40055400a40c142d04c0a04031050000002e5245585c00780622039490425000790102065100b040f80500204801c941c00c1104151308280b000c24240c0da415140709454110704100c14091107a40126024000111a2a00403a01c20081100b844a0882209064030501d14100b50f054000b8050380001c2420009880074002261040e0341c440d104c1c003403903002d031060388401b4000c110300204d0140303401003400da0784040400d400d40102c5000f1080070000f40003d41c034001c0c02a40c2c0d40841c072440c008004441045c40041e20b2a00404846081c0001c4001000343c2210b0001c0c0004820b05038150b100b0421451207a010102003e0820010501111608441030400c0420030302d030b85c0c04d035200740e082c9501344001489003070031521041040d0303000d0000081c903107181e400160f07094003c004100d8400303403100340c040c50482041c0002d100310201035009100c10343c14140011074003181c065401d4010139440c8004410f00103044080401036070094040801c81130207 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 434819730 1250 434818480 434818511
    0x10309080403080a09061112070b040812070806150a210615020a0c06090f17031312020f01300b0d0305040f061403010308070201020c06030a15080303060307030312090501 75
    0x11441408007140740302c00d2410742c031840412040048c00514070300510380881540d0381861103030094030941c0c04400a0003a0800d812224004038081c01d02610340322003038a41182045000e01f242800ca8486003410300c03022640703d8000d0500590006e1810424a1700780200f003e440040419500840c2e8180721100010b2003d81c0105400079002c0c0100010318601d80c441b481a80c461000e0310858281400c0d1200c20016041c88890003500024800300f90381c0f0308a441e50610f25040340980207141109a48220101140b5203c003203080b0f046000e085c04840c7c90160300024050407419500c00e240035010030900450183c06070711000000c0d400a205002b204024203000782141c0080c012203060003405800800d07542e0280d001c01c6845c2c200780c2c0342d192070750707003150b80d0702c525500800e000302e05510070061424003c0d61008050740c030074110f00000098141900c0214070000d806a8000c4100380c004105020341601c010a4007000d4903090f0400030204000500314400030302e201400680a03500e80040802607508 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 434820980 1250 434819730 434819747
    0x3120e030d032309030313080408030a0906031a090714040f0f03030807020111041202010c020a0b180402040b12040302070f080307120513140303070807120207120b010302010309080403080a 83
    0x1001201c180c0003401105100c3c2c254010f0b241940c043e4000c1c0300260b2a20007140c0c07d0380420317110301c04050426a545907800e296404ca0018030001c101540000d01049901d8400d00026000c6010241010310a43c000b0070300211016204c0010841560400311550104104450040a00180f6450303140d96406030300c5211502c90000314002200080410550303441402100c020107000b05a96142518001041c0185c911150080381403250600d40c20300541d6880900100401c01480115070750310071410700491140c00004000e10603441803106002818a1409507040103980300c2c40c00610792120f060a901c0c202c400d80c0040545c00da100c1c1c003c03a09800c0400540f1590344150301801070a0440b88050395140131301c5602c085415030590041001c1000d21080c1d41700150b000c0c007968503010f21910341041c5a40100d000b600d60f080c482404080d4070307504002610041410140a490030115661911000324062002038101074903603451505010020701143c0056a0003400c540ea80c4d000700102515114 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 434822230 1250 434820980 434821001
    0x3010803030f100303090605130b0a0809100213030b040c050306090a1104050403020d0c060e01020a0c1a011d0622150503211b120309160f03120e030d03 67
    0x20541012070390f0400340c8040b0320156581031300d03100c40c03075414881e003120160040000c07460b80701a0810001986003070b110091031007031030030f40e03d443c4a45800401140352000301001c1554840c0f04000d500082c0808000d01c0301070b01c0e80f00c101807402da2503900300650b607038100f0b400c12503144c00b03074409204540100140038922144105101141c0240403c00c020481d142104d010307015800001051048501c07500c006646980304050014441110101740f0703007240c03c21640c0001240c458401c8030b0504c4149502c0d4080d15030010040034180d0306007526440c100d1054031042005039032a0000c80c1c220b0f600c40c1c40c908029455620541c1404a50310343ca41c0281112140e55100310b45060360204a5080c080b0340d107101c070800b107048402e10740140344070b46003540d000c070b1a9020880d00e69101e110a17010107200030010420b5001c561504c07030070200c5007079050060b900640051503030201403c0021900311708408045076000f00701c00141d0080420180d038062044841181d0500448908101e900e42542c000846007 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 434823480 1250 434822230 434822251
    0x4080304030b06060403030f050a020f0d090303140412170c01050a050115090b250f0501021201240e0103020d2c0a050a060e03070c06030b0f0d0c0605030601140301080303 75
    0x140c8884062080505c11404007030005000702d0501101d00e40904010311000d0340300e204407100810b5505035181003010084071800040d074480c03010020301d9440710f000c030321420840440c60318051401e41c4020482c0e05a0704020900c08100315240719151107041981d500d00451350080c4080d00e4513203042c0c4001c04090042d60032404195054012052080c031207141510910b41120b80b0b8480c28100d0f000700070340040541101e00303801c40f000e1030000e6088107c0c156828800c1c0c0015072a86003200382c1e103188000c160000701109046122251600401d0010020b0410721818118400f80e140801200a40b18118900da461414944512580c00000707050706c0020702d0f00348426801c0034242c0140c5894050001c0082e08640c402100e00c008640d80303922110f44000301c201124980380032683ea02c0c103801e0a80d0303c8200425038480076110b541c248402c03c550a0f007000c0b0344001d0545415900c0300c8118080e400741104105002c0000741244c0d0058028600e800e5030616a140c6a41e903c0c1601ba6480c1d00c00c83e84215032 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 434824730 1250 434823480 434823503
    0x8070f02190b130213090210180501030207060b0418030306050312032215050411060a080f090f0102130503070b03040206040315021201090e06060307080c120c060408030403 76
    0x191440440e00807203030510405001d4418146490741c0e8684907000d009229010305801c0d402005a079421034040f4001e100c11004612524680100246c0c1c80c0e11000341410301c0300f05080441000d4002c03060200341c480034203005885100d181003590050034a4082d207500280b503c1c44030301041040d01021081e82e407181d40c1c1400340c80e03106c900781900c0346040c2c0c4d600d81000f0014404201c943c1c0e41c565103901a00c030350f51110304040109403281524140350625152015076140b0601c818401c2c8010f81e842c1e511401e50b05030740391021285000381242401030102d59058045400b081c03d000040c8074440c02034441c04020b540710740e042580e07903265440c544200384c440d100f44c42000894030381c120107507446183c00808150030203107541c941000410340b6010038003031544d08002400400264044881c06442410f01c006004a0350401d11480c003034001d4440c5100fa800b4003002c00003000c0000d1074030300b0000b05550b56000c54a1850711170f4a0094070b04001540090301040c00301d8282800800b0b0b00c1241d00400d0b180300d0 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 434825980 1250 434824730 434824757
    0x30a110406020d05250305040f0b04120b13210912021807030f0f020901030c0e0901090915020a0e0102060c09031218040608011d01060509070e120d0807 67
    0x10511440c441c10001d0380180d50310010003401140a4485986810910f60352540c050554600d41d0860790b200f100070400104062144035424450100940369a510481c58281006410003052840e007000400740e0880721b0008011110030000d41c0d10240e8000d6042c1080c01c550803555007900c0e018a90b07880000c00495000a000f111502071464240c0c02614010748940307040310f1044000c000400010501d0b40720030030b200038007c003403240000b00310301140c0042c0c07551000f00004080e50f01c052410010400008a40b010f2659120b035071030704403a0345110024510040e40341404d043c0d6846034140c1481c1c1c2c0702140e0030b0314954204498864001d002d070b003501c18035074848c0c0b01e00225000b0043c0c2d241d0143e01c0039501c90f8206641200810f40c100c00b4144281c2005010000070341900d01079046008180d45980c0e80d440b140c804008083d00c4807001c1d500902010f81808080744441e80001c00c0e03a810010004c2104c44a80c5450780102084501c413420707204d02c1105008040c0403036800ba03d00c24001202d5980b03804 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 434827230 1250 434825980 434826011
    0x2060a0b03160e091f0b041802011403060a2d0f0f060f0e030a050114060d080f03130803040308070e01090312030c05042d05030c0a0608040302160b030a 67
    0x1480907140403100c82850520109061488005011242c40d12407041003662000425958517001c010211000c520fa43c121814031098401030b51001034240381150300680140e806c04940100103a805ca10716880f03544080c00607000c0b030b801307078811115400c5820140203141c1010280d0740850412040207080c155940b400c280d200c0c4402c1c401c820071030207801824040c062291401c1c400c080b420340381007016494a07800003424400c4480049416a6555a81c5240b20011840c4154020400c0340c2c44d981c00e041d035413140e50303c6228000808010040010002e2484a005040e00900765003041c03511f40c9030b00e0641740c0a80203200036290174021528649250782c4543c0319549200681c0d030720022100d0400f40014055010300308000b66141882000c3c000451040c0480c040000384240640c6480314608442a202c601101c4d903400c0580aa00722008503034150311800a81c008841c104d00d4000c450369100e0030100e040414010318802c2c40080318400041030048003002e10b01841440000f040919002036115 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 434828480 1250 434827230 434827243
    0x501060203040803030c07111f090602030901020309010315120506040507051e01032309150108030c0601230d06060e0a0c1b02011e0302040f0b07080d1a030d02060a0b03 74
    0xf81490390040000440190700480034158440c41280420785003c1e0100c0014810b0040c00b1000fa90140711518900300309502c10781701c500178417650019514000c0c0460000b91248200c0005506058480703601c4105c0a24202042c3c1c0200300805203030000c2c81151a02d99102c3d0341c240c0d8240d4061007001c2d0049080e18100251900e00303081014103ca83c50349650055001e807030502c550507102e40700d41069110100307002010b20701c40c10740c0202074188241441200d01e4154010b030440c40440e80140860365000c00006520b5041d100e0021055039124280054040910708d4a02d000c1e4100035008011010002e40350801c400b90760559145c8000e40d40d5864101044508441289002500d1100d810007400e01d43c1c0d02d0001e034540189000104010700c0d800941303040030712480d1400042c0d40001c04001d000c080d603240c0c101418450741c15514105c42525210700314050280520001d580e100700c0c064000c0c091901b5401c1104001d01a9242903c03a044042d441da1421585440c0446c2000c2d04542c0c0b6107004520b0 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 434829730 1250 434828480 434828489
    0x140709050607020f01021c11120301080604080309030d061806120209040b06030f06040b0405150705180f0904050a0201140a02031c141510030b0d021003060f120204050106020304 78
    0x303003810414a80c0130081040c03081d2807828158040c1c0c0300d03e41401e1002542c3e4810329a01603c2e034220f8001c1c540c0303070309160800d10a030400529105000600c142200401c8072034009410800b1107480e5216012600e04520805029035a2a1b01d040c2c3e0014088121150030150901020010400385948010401e031810104000a5200c0321385c0d8005000201c01e82000b07a0091000740403600140c0c01c2c00840e510f0b0040a4905031040700030b031070400c03041100400c40007550710000c2c10204068103010501a049008008503200413103036502150807140c8400880c2012000010114140c50905003441510b07030210810680c00901c04102078a10710424104851130715095500951804070007658241c5596140c2c1080624603807640580c4850b10300d41e00c00c7c140a500d08403009020720403804100145480e00300e161805040c20704040100d00d90f00c03c1e8001401540623a03215400300028141240202070f581c000080e8880c18040210b101100d041030401543d200350340800090741ca5460580c0e1740d0056108 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 434830980 1250 434829730 434829739
    0x303020c1e010809120708030105040b060c1b060708030c12010b040b180604090905070801050f070f2f0f0c0904020a05061312030f030b0111060a23040614070905 71
    0x100728859521441455510802003c2641d0340c2c4904000c0f90b81141e40540d41c00e0302e0070346001c4010b2020b4a03251051800801003142e40703600e00042c1c4070f1040c0c0c42e0310b0b0481d40243e024032591010f13181501c43c0f404590296510032221596443d00008466050f00705031206020b02103248004144c15500c8011142690102c3c400c440c01c000d0000503070722030440003130000350b0454014000000c100c0c5c2c1c5802034030303040341c4100c000c0c00c031540c00c0080301421602c0c01000200040e51842c2403000c003941051540d00c42c003507145801c0d488a00540510004051026609a50668400c140d91002c00021800941c030344001400c0e10804403098040120418040d10040d40c00401800704102ca450b04000a001d06102c8c401c68180d0540d9500c0c0c80c0700d07032480c00720050380842c880c4185215100e5161050381407180742420700c030f031940500107c903035031700d10005000740d500d1540c03080c1e40e0140d05000d8414440041428107410607902d0b141c50840301030320140c055000991507880219010034060004141a02e4000c0e0 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 434832230 1250 434830980 434831029
    0x7030f11030319060315022713020901020c0901080601060e04060810050414060403050d0e15150111160e010e07020a080f070b0403030b1219060507090e070305010303020c 75
    0x3500212a80d00f039401186140d56680e200000140b41202c1a284007079206170700680714031662000b440034034444400f0904070200780d1980c804540e11030b90711001549500d000141c8480740000140e1030301074100f000c83d601c81000000051840e40006505059811550743d5482107102c00082c0000da40543c050302140e50441c1c04001c04c005115031003558044e00079102c4020058400d000f26061001c2a601a00040c10001340301c5410f940e1805040d181c44907003c02041c40c0b0465140e440303004800900400c4120340302812903c207031fa01c07134151440c00070110001c0e22640b4118056160350724140c0e10130080010050b400000b01c2c400944481c910480b095005844a140255100c0403140c3c01498600da2260042c84000049000517000d42d100f1b901c01d40340051140d182e1410001101c00014811540340d03c4442d40c1d0181d00c1d00e48102655466002030003084030b443e585004c0d00e82410300c2e040305846598440401041a5050300301e1412030340240c09503500c980d042e00a010074441545000101c00e076406 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 434833480 1250 434832230 434832241
    0x30c070509070507120509090612060a3c0b09040b010303050313170a02010f180311010b04180b060d03091806090501060c1401050f060603070302040b0f07030f110303 73
    0xc001d100d80c480780c0d500e055031600c0d89654546030304a80307008910f0009500890650420305100c1440c40c3c000d88220303a00c50000040745d80459545000034402e400d0b040c0c030b80000009a4414030180b881441c0e4040c140207105003070b20303044c460190702c002c4071480d01400d00140328141c2c2040c002d010700983d004013080030507a00f181c40682d1154805803101e02d000340c03c6056074001c11400d568401c03079041d000250f44d60350811100c000307003036a0082d500c070b0350395510701a407186074030004061208003998103040514000b130300068000e00600d650041142c0240c00d141c1040c0070800c4410318240860b1003280e00078002c0d03c6a1040c0b144103010804000c0c04074610b0081441300d03921055041c42e1544103114081072a40d210f26190007540c41c280d2060021070201d00225040140c032104c80000f43d98020000c110030318080e03084221058000e001940101000804a40090300c03a4040b100500701c6d003090b0340d55442c21603035003801c50752201c242600040c200f03035440b80c0c00c54071402481041d00203074001541142c0750f8 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 434834730 1250 434833480 434833489
    0x6040b0c0903070e04020f100509120f060405060f0c030402090103031d1005210c0d110c1501090609020a080402061602030f010603031803151e0e1b03030c0705 70
    0x180c6614080c21080c001c441c8a5941046400c02510800c003a80309282800e1052181c20882c40601621400d400301c03002d9505a4090140c40c1440003c0ba5815503545189081504048044041011034000d400402c81803060001c0d016010340960306610b0b43c140e560760f000c0c2c2454001520000d502141c550010800709104500080d540e03401508503a0704540b0900c0040d000d90109150320000c180c001ca103001080001050b0624042d0b445201d40b9080e25140d5001502445241510101d0035a100d84c00c030750b01d480707403410354459008150172035505044c0c003201005540f02c01d2245000300d6040c42d402040d085040d0098500c0d0703000750303113070850642c0340c0750b00300042d1b41c000483c3c2440c1555408044001740e5420840c00c040e0828250000800314298207000740b6650940014a030070151504040002407401261034031800b600800010300c01c1000d0120404030b0000c5403404004504143d00c051407820302207000c4482681d00c0c1440601c9004160034941c4030f00a280e130104c1950012201008103080 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 434835980 1250 434834730 434834753
    0x10c1502030a02090603040b041502041413091401020403020a0609030206071106091c33090305040509070302130602071a0d0608031c060807152d020f0705120604 71
    0x100b4058240b0307a0110101c0c0094000312001c0d94012403810602007440103040000c1e4101e00c0c615402d6150032708080400740003c1c04682c02a000c0e0340e0260108074121040d038410245507038030031490702d510800b4000e07031b03400b0750054001039100c0e240c0300344002000f50040180104490307010b480c0c21301307002c16070300c82000c204207018007282c001000b009480701303e036a4003482c504040100500310003030f041d240c20054148601c00e110501a031880c2a956032040100100401c3e41210392080419034024501d401c0311a07000d0b580c03207142c00c0703803211003030161442d05600035068050b6036215500e1350943d1920101d95544007445103489032407043c03200010726110744c0001d1103450030b0030340042521555100100e14640c0507400250084074508444d03003101c5401d002c2d810092400c40c008001040c100246955050340380f04580007800311034049440b00c0d4201d1400101074040c004085000805200340c00303521744803080f500985901444074042042d00c4c00c0320001c0e05c1800b450000b0f013119541d65884112003c0c = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 434837230 1250 434835980 434835991
    0x140c0108270a0605070518040c141b0a080a080f01060905040e010204050d0804050a0b03040803060621010e0702151506130b03160f02010b130c11120c0c010c150203 72
    0x402c0c450b0804508075005603030255116541c1d0a9464940c0c150340c0c03100f80c11200c4841d1149080c50303240185103901810030700e5041140b00c2c01e19680e011190307a042e016169000c2c96002030258000003014880c0c91400340044c000b140c0c88400341035031130300e400c0701840c1c4d1b09000b00000310311a0781c414005410b05511150310f246145d000185040c1e213500c001641040041c01c119021074001506100d6802c041d8a00070040858200090940c1499a0b0b03551b5180401454280504400b245060b600705a0b503445603012407111500300580d5031a6101c0549500c001c40e05840944190184580c2096008040c0c42c41001e0b43d00d080308150004a04001071a4070081c031010b00400480c00100d103440250000b140105568082210110040710b00907000f40c01c001f80800c00d40e490300102ca28107840d42c400c50601102c0c456400650901d1059003924100d0024000d00340620480c03000c10340d4100010000c02c56080d00303000701d8440c500b404c0d00465500e00300c070000400381c5140c8000c4074078201a6030082d54004 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 434838480 1250 434837230 434837233
    0x8030a06030b0f01090c0206040b0c03060402090d2109030503042603040605040302040c080106081513020f070b130312150308070f1505010f03020f0d02030a140c010827 74
    0x1560340e0320303200d600349410b80d0003c00410724040108803e00b1180b080026150040c0094085482d091b150740c1d05503480244581403500c80003000801c1e03036980e581142c89000004060030070f500c1d0182458200b404a9880110715000440c6c0782103403042c020380780c040890b03500c040150301e41410119481810446941a0440360f500030780602134045091000d00044c0c5500c0d50b1f004e072030754550300420003528080301c121401c0c002c80394014003688e075020440c4c40c3d0043c1c000034800c00d400e1004010482445034502541c000c1031012492500d03601103e0024000d030b0f07002c0d4414003101e4985601110708200506c0e401000f00d0aa6420003a028401d0303000007a054003001021040b40f5a00d17150406a50f01080c0c1c102da0200105084504202001c6000c00303044100200c1040158140468562807071007500019202c0d050440806c156a078800348942c00d07107030b40503041d52810300307a030b1800c6521502d85d405014100c0c00fa0850b480c9036544a501950310038012102d490b92030700078404028118095106080c280d0703 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 434839730 1250 434838480 434838491
    0x20903031608130b190e0a051c05161706070c0f03030e100c0f0306032003120f03041203051e0919030f0906140a0806011209030302040312081308030a 66
    0x5804010f40610024491081025500c08090000d841e8417080001240d040c4202c4c00e0303c004581e11040e504506440b4286c1d01000d064411040340b030481c00110b4070042c2039101e0b00c407035a014003540311610720884408030303843e0010446914081c1d40300c05040302c8190004080c81c40c0003002c80d400d00380c0a407000e0301a003000243c85811095090500c0d8214000a00b540d0b00c5030030081120364412110113204003980380801100b421076032803e10803610f00008107038100d00c0b520085010381d018095030548081c03120392695120090110007000e9001101c0a131203903640c000707608045030b000e4042c0902c00d032101110164840140c01c14101c07102800380000d0b405118054803030034104000381d0001005406a20351480b405021780e0001c040312541d80000c070402c944121040e01c2040d031001900c800d0082414200f5103543c410004840c8800c0d228480341035682080302ea40e06240d0035500030420340340140c81c00741414505003020b4568220550305640b40c400305c4840c200110344c418000c0c64001d0031528011a6 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 434840980 1250 434839730 434839747
    0x80915040219080102120f06010c150f020c010b0102071a19200105060a0609030305040b16020a03060b0301111c050402010203130e090d03200a020a0b01091509020903031608 76
    0x3191680d039080182d044e9070000f0007030000b40800550a90040346071500700e00b40d24200c40000d0020b840280001d280c01c41c010107110420307401e0340000e81a10100c200441d2244982586d0901034240a80268007500880340301154034800300b2059200160000c0080385031070766180c058200e10103020022001c004024075105280c2c501e4400c04ea8030091103100106a604100c0100a50580a03500c207100303000076840d0410010383c00c0301c156411614072001e50b648601ca840e40c0016814241700380254400b010346004000c009250340b14001a40060f80204040c48000444c850789100704180b22601018005082d03598150a80003181d1061041c815a820a07003044042d40350f00300c3c7d98210103034043e6423108100b10001c04004901c0300c0b84081c9000d01c00640389101000c070280e20000f0741040c01ca4001480c4041e41d00801540740007a5003e5400a5103680d80c0f900f500080040c1120115038100840000611081318025031342040c2c0014041c5140c4041c2d068049500108032000712a05102401501c0 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 434842230 1250 434840980 434841019
    0x70e100806010b070201033e030105031002030604060302060307020714060906091311030c040302040b0603070f0c081207050301241b110406140102060901090308070e03100f020405010f0809150402 86
    0x107140720300c00031150401008d0075010210f0b0508541086651800a100401c950340d00042c000111071000d00c40103070341e5100c60300031078040e160b950400794020900100340b00186600141007412180e0a05a66150079100300811800b0b00c20410065440f41d4144a41005031030300c640000c40e1180b034844005216040f02c00c01e241a07401c00c6884d100300c140040360410942c1001e001e002503000003210a00d286180c00c90015000c800303500c0d40c000c100020301d501c00041200110443d58120410b5581f880d081c83c05c0c1400030708950007400313804190068906002d030900102c0c01c0c2c020380e40b4107a445603000440c50715410406541010b200b07980c20f1113040c130700360110344a52048101816040c00c01c0300c0b03443c0081c0c6c006480c1c40000f50a03020140e2403d0380d02c20210758003d4480e9000038803486d000e002104d610000a1402c1440000304400a152001c0107400302c52540c0140225082a2244822a0400001a1074108044134103544030f03007003024801d00102d20021025442407000304420384116148840b107 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 434843480 1250 434842230 434842271
    0xc0102070627380403080f221508090706050331020901120503070f02060708220b040e010b2101120605012117040512070e100806010b07020103 63
    0x1039a2084903aa0350300e0007904120f0351480c40b89a55940c1c02c5224851092400040c8944d2201500c20040807500551040c190300807145540074020f00307444024590107400042c0e150502c180200e0703503c1d50600303490003401030440c11300c0340c2da500d406820f90914180d0300303840382c2c0d0000303043c0402c810304000420b01582401e0281d075442c0c0c1c003030035504c803103002148148a03071504180c10600d4502e503031006803c0001c0b0000308940c001c41d4061140d030000c250754804100280220100185515008075120a003040300c147c946999a5504c00581401641c65201005512850050f8103000f95945c0c0180a00303200000200740c0c06000c403a0b607004002032248028a458000e1b0025030240c2c600c3c0000d00144a00307405002c0c09011600c0140300507214000c2c1a148a042c03001004040e200700c40300800d01d550401003614010000940844101c0c1c000d000d0740f40e02c4120340d0007000407603070318280800d11080201f4040c000b507a11305002000c0030303400d004032602d89030004c6000301d0415484440880006940c001407 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 434844730 1250 434843480 434843489
    0x13030201061a1c090804030305071518030f08071d03030706051f050f060301050405070c14030a2c211504230316080c011109030f0c0102070627 63
    0x100754843c1c480c540b010720404a0400d0300107a4a0501a08102003000d00080f10112545814296a2441186021403c040701221103000962030018101c210304454040c0303c003018030035039458000ca8641075059a0301c003400c1d10708400084445240c1c0c0c03c9014403400c0703200303800e40007400c40b0b08112042e51100c00340e4100322100080b101341c00303c03031650658400c1c5050001d031400b21400000c003001032002c201180814030480b4402d41c2c4600206250900402c5000c010300c0d0000d00020340784001482c040e541e5400050044006007882100e0004400c403c000c10b0110030441030001e089104110401500020882a01501241c2c40e920004030481c2000410f000324039206200b515032526080c15041a080340402100c0000d900c1079080c0c00603400720449160090b115005420907049080c070444502541420808070b40c40c0000f81e035030718032b14007019000410049040301d0568500140d16a02d0f44140c030401400369001142c103000f030078000d0076a080303d40c42034412140658100418a51040301b0740d0302 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 434845980 1250 434844730 434844779
    0x91202010b030f0705180613150612020c06012d060207030b0105062d040b071a0117070501030b04020c010507080402120c03100c111b040f090206031303020106 70
    0x807a481d8141072180106052400303000e411424580780114100300f02040c5100852880d031000a01240d548800b01da41950030b11030100403101c0c00d1060390043e5003040c051240030403806003c58807800d02900032030b42007589641c050045a441e18170000032449000b10320080c983c0341d0b00310502c201054100050300400e02c91f40200b0030340703245040500301d5001c181c11860280c031042114141c0b41800b0080c01d840040d148841d003000c802814a60f6060340610380140601c4070000408100781f100b084070500b0882c4205480750031a907a10440c103650700d1003038070311070b041c0d41c1209204104542c048e510205216102070005481c2400007400142164000c503403100104a0100611044d070504140c1c0709408840c2800405001400d980020745da407030144410100181c4402a445245200f2010840c80c00e0464084504904240c4d07454203e10400304200d5010760310308002c4c039074118103c0c01011050740d0040c1405141d074a4841c030b01c0304141c0d580d4400798299034032980001800510114034891080e07003d40b = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 434847230 1250 434845980 434845991
    0x3020d0b0a0507080420030c0a1410030b0102060a0b01030204031211251215020f0315060306100320030a0b04050a0501031211070801052d0708150409120201 69
    0x6010300d040310b0024103801d040080100c10480040c1051200c030507480b4503854103c0f060128480000d162400000a03950800b041e05000030b504850304501b40d40902045070700ca15105130484040b000c44407142086401a40319102091008a95a02c01c042020042c5805440d0035266180d0038400035100d404580042c1c40302c44007000c02c1e8400e0000a000c007000403c6075555202004400c5184809805116407003c2074040141c100039a01044010020f18004c003035469000001540311181c0003200d040d005841c0000c1d04a40710b18180b01228801c480c01066884041000d00e0202c0060604080031180400074003880381050f0405405107201d181070300d8020449031828003c1c0300541c2c0c005450042514180001032000460301841d0440207121441c155030100c1082640d617290410030381c01103c41b54a02800c0c80b108000c03070820070404a071415403503074520080c02c8600d114680c00310b95180001c0e0f18440441c2101140c07900c08454a10002d0011031246025115004400b25000011025139901d0 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 434848480 1250 434847230 434847241
    0x3140705160603051f150e0406030c08060106030c080c07410105010b0421061b142a10060914010e0702100903170906010f0909021807020703020d0b 65
    0x18001c2682c00303d94903070624080400041d09840506050060910186d110044500d07a03901c2004501030350040100140031540d41d03403c0603d0002014018285540210f200101d040c501a00400f0424402d41d07585111990740c0a40d4555281c2021200b10f0f40c0410360318403007801021001c1c401c03110f0031050315005500c548020b0240b03031408001c80e404025906001c01003050130a41c070309480450314568018400c401d41540e88655010060b40001c080910340949035641c44c0281c6101080500c40c3d880b0385084103140c510a401a01130200d0304996079180ba84001e01042147c40680704151020048802069a0001c45000c0c0d07159500702c03001c0c50740d55140304184c4c0d0003c410b400d07005056502102c115030800d150000d40390240258a401660b40b6a40090708252081c1071854a9a0610207000b6160401c196102c1d240c0d6421b1007109201c040c440d00200d40c605080c441c0c0c45440b41d0042c002005d560000e03c4044510100038015402d40c02083d20000160b04c0c0d486500b44220b216040c22045071421 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 434849730 1250 434848480 434848487
    0x1120510062613020114070b010303080a05010302030a021207090e1b040b09010603091b0e0601030c0206191505190303021605010e06071511120609060904031407051606 74
    0x20841d01d0b0301100002511030361107502c01d044542042180c014003290440340c0c001a2034283d101c40100303440d000002041414030070701c220781c1410399120781e9528115886240788802620000c0c00040d526800c01c000071001803501c0c844050301d03441d420341031b100045d995144401c2203031140303110101e00d078010760080941340b019007600413802c100c112020000c0090407008900495014050401499680e623050028840303100100c0f0455880003070240000c0b80c481c003905102c54010f40c1c155002c203043c140046000d07400840d9982c4210301d0544040c00b60000c00080e10702500c840044680e0718040c01c1004919a11101081c107003420350380c44d02560315455441e0080c904080c2000c1980c503100c1c0b450046c00282ea020852204c00d040841ea080e071141a9400c1c0b0054074420300d001307190039a14111080000a48100240c150030790440700402481c1c0d00c0d0028040c07a9070085070f501d503000c040074000400007400b40810202200c0d814801d68184806d40c3e070341900c1c00383c419254030301c2502a810300f000002d51 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 434850980 1250 434849730 434849747
    0x12120c0a0b161b0303020d02030406020d0e121611030d0806090708152107091b02010e0c010320130f2103030c020a020607060b011e05030402040b0112051006 69
    0x301c40b11240e1140a440c1d004000d00d9006010f02d000d0462001014141486501950107600649200f159070b0700b4145482002580000d0703080042904100401001000105540c0d000400b002482450079007506801c2444400b4800c0407145030040b40c0322456951402c200c0c420701e01c00c464a407900c19080c0342d010410407275001007940c000c1010240800c90315141002c410a4040410703202410300e214558000412203903014010a954450220300180f164a117401065030005016462206001124030885c00c1c1c40c10443e0940f100d910504011b0040c0d4480c1d03000600b103500030b208581040d8910081600d0943c00440c2c00300c0241031005040c4030b001040b4821000802903d083c0c4d9450007001585948610b81c1d03c0c10117030070b042d624800219840d00074444100c08070303801000140ea45100d80f600345d00821150443c1400180d40803081000500140d149400c0140140c86607400c4d0340d00c6500b080007130014003042d5410006003107070607425a50760740500c6000f0010103c00380c0c7c541d42440c000400b0600b = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 434852230 1250 434850980 434850991
    0x7060206090f1902010c051911060a17090102070f0f0c27050c04120c030b15011d040b10080a0c05090109062322060c0b010512120c0a0b 60
    0x2c100b040140080400029603084418400c05900303080e00d12400141c901858044024005014466407004203004068512030041d1140c40c20102440d840e1040c004540240820400420b00c5114540b5041c9068810f05600007030000015250400940d546c410840000f041100c00c0007280001c0f03070800800d968010042c0001c1e0480b0000003800711f10311030341a0515051100410b5503000454690b9071044121009002c3c501c100380011049480c110101d04041c0c801507030001412004103d00d40b4020000454045050351044240440c2081c1250b201000d0104264402d9482c0b1b8803006c01d85641e80d22100700001611001e44e1850300d40c14507800e03100400014810800d0811045103240e03084005002542d030740e460450940c05401c5440c10741f40f51000322000321a400401d031281c0d4202608201103d0b1060004d00043e055503800c81174814210f82c600c0109407a402e2401480603007031080c024440d800b4140e0496214240040c028841640039803e000c540d81c02c4007031601e040c8000000980d8201 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 434853480 1250 434852230 434852233
    0x903040317071e0b010302040207020307080708100509060906070f030605030109080d0c0c0209072708010228050409090618061b05030603030712090315050109051612020319020c0706020609 83
    0xf4120798401912000c14000248580c0e0f01140c04800c0d500e00700050006401c5034070071140320b9521800c240c4d0342c4030740b8544103101032820840010310555000c12650b00134007443c402801030791100101030301d1800104114034100342e80e031100000c95030307802d0080c11010b80c011a080f903641c003221310a00003a00d400c414450144180c0030750100058035000803850744444149000f402c1c12001c8024001e804084103a0310003841e400290110703e890041d401000074680c0d0030810382c60000300824602c881c1c68001140c20116800f4441000421705541003407410a00ca0800058807480c045c800b10b801000d03900040d205656580c1183c00ba0000030a51482d42842c04d050240c198039105000940d20f200d100c4000306480a41201080218082d07422480590740c458136107404201804401c40c010002413042c1e890381800d1002040d03038588002c2074102c00000c140d07160801010302c1501c84029500c007819140c401188041032506000740d0344082d0002600d508050440301d032410000a18116010301410031030b = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 434854730 1250 434853480 434853533
    0xa1505040c080118090503030103080c060f0106090317090303130e1b03011203020c120a12081306050705090301020403050105101d07031808030906060907051809090304031707 77
    0x725400ca0400760442d050803d01c0100b841c2042848409400240002071180c0310100010007003040da00c0107007605800d00d5007164442d84d2807401c44010b0010a101c1e00c004292091414404a2101002d2021a0346814581e502d04a00400802d146070310000141c4590740c1045014881926010444c6410030f0101080c1103070b55407140e00c64191844181700700c00c01c0164209445003018000d21014500b882c00900d00c6d0600b1025124040d21f81e0200c003001c56244c1da41140c9204064019038030b081c02801081050700200c8200d136500401068040e0040091005c1401315180c03d076424001000030318170541c0080348606244c40002c00b00c0183d6004a503003208010740021030305042000c103d9000c03080e13180100c5e001c1c1c01d13a41c201010030038200e405001c000000040015444001030b16174080c020541b80301d8015540c0c40003ca403140a43c2e40109911500f80c48606114030b00807441c41d0b0000154000d4030716096484d621030b800c4603416402403481c0800802d0190910480315040084041c003031404812 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 434855980 1250 434854730 434854751
    0xd0c02070501092603070b011d010e060d060e030408071403011109091b071113090b0610090e0106090501140f0d020304060207020a08030408101415031002030a150504 73
    0xc5840140030702141d00d0f165084034180d9130101003281c3c51812800064a99540144c00e0810350706c582401001b001d551041c03030509a410a0604241c101c5078085000c0360b103522140304000c40c10705001e2060ba402500d803000001d00c2a0f040c4001c00091116000918040c1c3ca000140c04c844030312400014441c1c0d242c002c00c4140790103010102e801c19442100d1740641070ba94500d4100000304980140d40b9070b0301300840c43c0410400a540c03000c08410707044407442180c00b0300069070740650b80030000040900c111000840d0741410940304100f4102c2e414207251940075200c01075510038034000d0707104900144245104210301d58221001c0702d820300110071810310f1315460800c3d00007944030304000490038580c004002800d01115030b0680e444194000e080340149030b61510002e507250080e01441045d07002c1c905010940031154481c41c0c0e003401d049141b5105682c0d4161340e19902c21255411180c041c0110030426000c400b00d0b200440c4100a4410002480031091488440600c519008580034502d040300824 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 434857230 1250 434855980 434855987
    0x20d05250501110a021527030f07120306082b020703061104060905120a15021902060f010b0c060c0a0c0b040f1b0e0a0b01050405190509090c06030a05060d0f03050d0c02070501 77
    0x1147c0d03241c4001404443c90b0442001d03c0c51066809a11441c0300c0440d00b501009400c06150310000303200e940601c83d440d240d00206807650600c41c0c4212000c580207020045185116100d101004d420303005894400d5031f2921000242e030f00030072145251400009040c08907a0f008000705014042c00d9a201e1100c2140c184d01d155030b21036040300070300f1021204441114020301901107402c0e0502c40b81820520421524000e5070b1450b042e44c951503106010800864640403003829aa0402000e5000f800c081d00c0b6100303030030800d5101025039410040b01c41844404180170011250141d48904052224080903042284004840140c9200300c800d00c1502000803800300d03241c00ea041002607a001816400e140700685451049030b118a070445504c1e80713003250700d44c400d50740041160010b850b40003903a5580481c1a0300c4601880c40c985e03006800b0710105083c81d01680c003e55001c03201420300c010045258680301d0b40c100c080d410880004c1c0c00000c001d4850201e81c0101210341c1c80500041030a6030512001a = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 434858480 1250 434857230 434857261
    0x60303021002031f121401051605160209190506010806091611010c0f11010b010504030b10080a0b0a0b0406030203120a090b1315020d05250501110a0215 67
    0x21410981c020010403200c03030315074100800b41e803030300e0110f00343d205c0d92008113018044500000382c503d0030741c54428881c5a81c060251600c20a10a0403288184494007001c0d541600080300c0f9040c0d8241c84841c600040e211100300e140243d80020140c06010100400401502c500501e050b0400c540101808450380350200380d240c022061640c020100b40f40001d04031003400780701005070220742c2011802000c80340c03c400d0b030a1402c40c1603590427900a0b0000c258900ba2004806000d000610401c82040070940c030a01d841c0c0c008038080c071242d004658030f44040c2d20b0301c4500442600c0d800c0d0903c00380704020400d40b01d4074220b000181c4050240a286400080e105c0c5407510358191200e03c009515800944103040c000c01034001d100215807114003c0e400800014514060070700e503401001c880301101400050a0321010b80300d07581d024a0580b051303c145181d06003140300c400c08044c08942480000d0001c0c0107800e62607000200c800d40307075110414000d01d4031101d00d418030187d0f410036040c4203030a4001d17401e1 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 434859730 1250 434858480 434858503
    0x3090c0b1611040207170a14070c090c1b0501051e1b0f12040609050c060310060309030519080a1b021504030c14030306012303190204050d03111006030302 68
    0x40803850416001183c040e00c00d104004003039130b00c4d090781d542401c03240502504000000769600300444011048071002c500c28004003620761100c0e42000c11582403150441030740c202982c0380c20004900860407c00010003502c604170740d103945a00c1003103a500070b000004070030141100300d000b8013814080003c0d4009080e1610321a1842d80000720460303201d140c0c2044564521906544402514090406800030708611404031035034000d5080107890740c0b83c10360940b801241d0741030300c402d00705280010940040074505801c4051000c1801340e40c05010380d603000a10994a903480f203044da80b404461060840303581d038000c40340704083d1103405508160700045040180b080d60000c01082d0300da60a0949603031025602c01804500e050710f0b01596090080b025500980c000e0320b4018180200c2c0c0540c1c2c43c003078241c00a4140d09a41072002600c0c051303440324080e078406100c11005241c00c3c4c0318004280d4101d400d4406030040760701c842e5000c0401400f0009280b4122224504201040c155a8020b45449600c2c04 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 434860980 1250 434859730 434859743
    0x51008040809180f0f073005040506151009060c021503070c030807050307080402010e180a060f0801020705060c0c030c06070309111f1d03070603090c0b16 68
    0x40d00304050801164805070000b01903100d20903c120707800c10100030440d40003002c0107414010a0642c442d40c640d840c00755200740c451071440304c0d0707d081501c28100704203200c100e400814000c20441c00801e11980d40640e010710058607561070095a015031004120049501800301c94158113140ea92000004050382c056103000c00e03014101d4000034910600a5100000b241000014410015000141801c900d4800d80341c01d00c00e41e40d1040107882c1d40c08121503800100c0d004000090040d0700c2001c0180380400002e1050b100c1c036407200403104000038200d440707039420b503600c2c9028804ca107900c420f00e80091881c60f0080d858005555551a1140d030050061396107450042034000c0c00b03050510603200f40503c2c3c6421904903162202e8010003400d1286825250881c9500c048400ea050800e6002c0048000980c941c0d02d070034503414100c8280a0190b60b0107d217403601388103615596428040400201082d40d00440d251045003081940058079900c0007900320340421201c0070019515013442e540c40d42056 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 434862230 1250 434860980 434860997
    0xb01020a0b07110c0a0603020a02160b030105040f0906090302010501081614010f09030609031d0913030e040e16090608150105130e100f05090c0306040602030612030a080118060510 79
    0x3a00c00d86040c0132407413850703408070032001c000c54441da03d58043c2c07420381403580c01c032904c4051038035090440c00c0e02070103a11062041000140001d040c0f40c0c2050520820560300011401003544815048480c040d03011030060351150010042d820040104200042c042e00c01503808030b14048040d0b40348030308500e60a05101c81c420603c01d036240950350b068000c5802c81014460f0b00a80d1a009002000342c0d419000c0c00a0400b00004031820049101c61040c0c0c04009041207084541c2c4043c0e6100402a1109130300079102c10801428031401d000a0309c6075186c1000b010310040c20450a070f81920407070b8000694540c07082c199855011417000403d81190700652b0070494403201954400c001d0510350400d0801071050170800d403030030b8095030302500d0040000c03c0100215107901c00c6c019100d1403d8003586600d036000001043c04146198011504040014010f055031418404000d080d03800a00303600e00456007540041100e4140d0791b5010786440070480040120505210001d0800344090100008010104 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 434863480 1250 434862230 434862257
    0x151011030313031403280b010c0209040602040b040e15040203090a0f02010201021308030304030e0319062c030703090906060f0c050115090902040629250f060b01020a0b07 75
    0x2400451340c3c8208101d4410b80e64945019040b40b050b1400d9454012803010113000700424461f8800d0000c01700c0140c1d24403058803115002c11510031006042520101c3d42004002652035444000b44004e000c0303546000c90a1030004101d0101c40c00c8165032a004600410401c08441c0000c2024a4110360080382c04400d8280d600040f8024040c0002c005401070001001050b4804000041c40c0702e00d100c0d03034a00a2050f541d03800d16485240c02e40080003401140440301c400214150800a004a24a0410f00409480c9418055407081c10880020660800500c450502d0380c44502d01c000350504d05030501842d032030218014103844001001d401080360203074030070040000a40050581200594111540b6a01ea00b4240014016004102e200c0c80c50203400042182104101c0b24051802a02c498141101c400c1e400c00c2d0b907802040030441c4180402c3c43c0060280c50048504000b900508a052a5030001d1903c141120364030182281554070485e094400902c401801c4c6901c00035034940b030717900320601 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 434864730 1250 434863480 434863487
    0x30f0d0e06010303031d1f0903110d05210402010c031101021b100c0e030c0f03031e03040614041520120417040b0d02071a15101103031303 61
    0x854200e500340034030700001081c5030741a006107900103030203140c955500c400c9001c1c40390380d0700460740022803d244500011407400e030759501100450b40a0300b40890078401c4d581c40c603401e03d15a0070344c50001c6030001c0fa02c80483d0103801034242d40c1301d040c00400c80341401e041c1c0010b441a0401c2800808102191500c2e80c9250001c3d01520102032801d0301d051085078001250a4030f450580342c032004800e00c0e0050700c40400d4031405049514950140280601c0d9282c0d006106a264650811507010301c41000010004003c054185102c484106e40345a1641818500202038a0701040600c002002ca4018070000c0f800c01001001c0103000c80a0010309480130315025040c0303148104c541d04500c007011034005038641e0b10f03045446c4034030f114404c403c88041c483c080e1482a402140254104190288200c0d2155422980101b1516014600c03680c05480001c02100c1c600c981158003a80c03504521104c00c2441c1400403039540540d000d4103021903d2841550110390360b0200400250040880c04a134005041c003 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 434865980 1250 434864730 434864741
    0x90f1b1d01080c030d141b01050403030c021c21110f040501127502060c2821021e090d020312190207060801170f010c11190203030f0d 59
    0x7c9480203001078070f040d040260003401d082c00d9040c00b6008200c81c0c401e64102c41d07100840b01e01c2046d114224545410204443d59468207500000e000d60748600c180046c80b501001740030084108200315581c6c5050100040201e80c1070544c0c1c0c0308040c00c0a902543c0003511600d40c010010036102006003041226045504500850604c0600948038022042c0100c424100000c40a51040c010310081c2481c41094480640f070007000f0401604180b0210b61a00180d500500350040ea0034201c008103000540b6030714440c01c0752000d03032001c9811030800c1c01811080070300740da041c00c014002c114100345041125560200e044d0010541c03401001a0035402c0b03523160b10355802e403e6005070441d104650701403000728141d401142481c140c002566200c0398500c3c40051039070150340040d0703203070782e2164a484900c159074000c440900801d4080c1a0450300400c10901c520582001d0583d141d00300f121031001035900707010388911400c1141c0007801c0101d000d80c800008030358a403c0c1250855030f540d003d5140c004010007 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 434867230 1250 434865980 434866027
    0x4121107030b01081b03161211090f01031202010e030306010302090612040c1e030f080307231305010c020d030503071206030605010303080901090f1b1d01080c030d14 73
    0x1642c80300089001c2100203400202c481c1e43c0d03000429100403480806070742c0d0000c003080d4901c50710794010a010702035111140c00e034600c4c45060300003c0500e041c000108081000c036503158081da007490041080c414a0b02041d40d0480850000300f000340d041c90411754503848001c01c035174141600000c0380c107810b44a9108030b034030358540f185840d00ea604240c0791088080041d4414000101420300c0e42d0103809044100c0102200e0303000d180841010213036524030281f60401841081806101404810300300d5001603e0301800144090045d0f4038220072240c0480390300c05401050420080c40b0404006803140441c6060b030130703014149652640e40b2040c0403540e12032290b02c1c0300c0c9042d00346500001004603607080746050f82d209866128095032120702207030880d0004203000d041c0f04440624040401c000c801d842038810307050003100004070f4640d041c242050291651045036240310b0f0004101280c410702c50101c84403001c60240c0580b1880710402041082d000c444a90f8481e40040c000d03074103034690a45d02503140c = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 434868480 1250 434867230 434867243
    0x14070f230712050106442e1a1203041208090a090212060405070516200102060402010c060f06091d010b01030506100e0f06070c0f06080412110703 64
    0x781c0c2c030346000e10b80400b11080300300c40c02e42c00d242011075030f80003a0b0610680c0c42c0e41c074203564404000c501c0c1c0e112a00c944003004d41401c0d02c0c9500c4011540b040600c02c914004003654030070035400c01913500a20030a8144000707004c0851406a2100315181000c082c104042d0703045901e8000c030b4100241850541c4240d5020254000782d42c1e900b078041100b03d40140820940c00c6445101c0381c0d035945542d01c160300c14083c68400e101c0b00301c0c0004425113855802950040c4042c41c0240c00d00b40040c40c0c42025122092080c1c91282541c400300c0440615060081c40d0004207101030203540c2801c2e4000b9042400e030300d100400c0507440e08007031800054950300410003480120002c1c080d5407112403401241c070603126001a203550030619420ba41d9400b81c042c2d54040d540180010481120015049404441803031102d03030701040c0c1483c1c2141c5651408040d00115002e1903481c4449441d20007400c06001d89680300700180038651007044042201619600301ca400c4508000c03100d40c00c0c5010880c01e066440d00000d000 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 434869730 1250 434868480 434868493
    0x203011d06030c042a03050115030c090806070e040f0605150315130e16081c03090b0a0b0102070905040807120507060e061918030e01090b03040308060114070f23 71
    0x8030008182c80c00d003182e0303800e117900441c0c9100e403821000c0d034100f4000c4000150012980720a4141b1990000803602003500d85111003944801c207603810403100380d58210020b00f5110050681e49018030541106070049542081118a80004140c0d038001c0c940800300d0990001c000038012800c2401c64450001000380868038882e0203055000c0180b00010f407a80301441006001014000c00c10281c1e4150360304080140641840c010044900c00d451694002c10503807564904400a82c055080f01e019200b901c401207010000c44000918140042c0d001806440c245000c0c4030101e00303048200c613082038024090307415402c2c01440c10b560510440030b00803c030038a041040408040c02103103d9000780b510311250b58001b02c002d42200c0503100c6d400700c460000c0e0015030003100000e0103001800034040044c1000300d42d2320394a0116901d0703034004544c15030114048000300070703031581d2202c81070783c946c004035500c2e6043c001da64464408101d0081070003449096060900e80c081500410780c20070030020364088511 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 434870980 1250 434869730 434869751
    0xf03190c0306140a0506010e13050c04050d050c1002070b070f080f03130212120d020c0c0316050301152402030c0a0302070f080a1a0408190f0908010203011d06030c04 73
    0x40300800c1358243d0401e89080c001c2850796104641e10341c030541c0000e11000000085080b0076005003006403a94503030300000c00c0f0009413610780d40c58280c10b450054020b004070300e124000b805031581c0c4e032041c00b1045400440c01840042d4040d003d881c0a1074100c559010340381d6680c0303005145c13072041c000c450400729004010018541d21409607503a42900c290b03000d840501c041040750350766400d003082164201c4020301c0041c00980740c0f903000d04070204000080354440407035a07010038284801c140d000c0c0c10940080c4014802d500342405900d42c0300e010000e01041081c1b51070340c48058000d0a420001316030344045080044103100300305640e00003240005071102800340f880c0280da42c0800d4030821140c080c03449000982142c0101e54642c1c1103811108450141ca24481011500750000304112207400c030a2010040da2078124403000390300c1c80107841d080c4114900050260800721a03601104050b801000184a01d440354140300032107000346403007640a5200d283c0001e003040700580202d600309113000c800170b0 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 434872230 1250 434870980 434871011
    0x30c050d09061b020c0105180301060312050d05060105031009050a1d01020a02070503030702092a210a0606050d0b060d0510061709070b0708070c0609080106050f03190c0306 76
    0x1043d4642505060800180200c00e036120b0341c0341c0504078046042481a0013411005901c0c8110a080080000840988030755520f003042c41d948104e540050700104054040100394410150803c00909040d401c528014800002682e01c1c1d00800140710303150004140d407044070360428500b03035910760000c401c0e0f505448510380c000e4116550340e00051040c8140011f5500740402281c0f40c1c3c0381c0192854802c1e0b96000c401415805d1104a0000300c00190381403170010181c800e014000c1d901c01d42c008918043c0340e61000074044000a0310020008e480e0100411541e60400304481d00c2c04404074011a801c051034001600300e00400c080105003d06000030081c0da0240c81602d00c00b071f103030f07503803114184000d2010302c5a5038400116070500e00d942c00074205001540501000d002003034803401d02c07146480e540d551442d440003c035510900114221400900041e6800c0c00b42d0b40c05002c06403036444050754002e00190f554051800c06007440d2a908030b03440c05200a003030048003d560002001c0c44091005074205 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 434873480 1250 434872230 434872241
    0xf093304110a050f0f0910120602091503090714030c1507062004060c08070f0b0103030e060a120c0212070309061e05070308060a0807030c1508011203030c050d0906 72
    0x180c46040103035070210f0a4602402e400d04059000751440106512007014059007a8000d40215400000124000b6060700e0051007011002d10460025890700078020611058580d01100981c02100620420080a000250754400c07105964910b4098550f400c002c80c0c01e0030401030086412540e0321241d1040b85189000034840f0070300c502d1040102c200086c26200741144151072145191400700302c02c0001d2407050f2075610440c0d008102041ca0112030f9580e00350b40082c81d00301141c4254a5100410a0513000b0f0b422100f8003009480a620380000c107140100080c0d1203481c0d107101e49e40e4400c41c2403000d51003041b40e1a2111080d00555588201c1400c02401c01c14861040c0e0000807800e4800031181c8040411307404880c885e98854504084042d0307802e5600e098001c180c2c0f030300001004000150444c0810410000758041d005c141c151506000810600818854000081c032000c18010410308240210740d841c1181c042c0f600041c08485500f080b600c3d41b140e5490291600e0a04409405119159010 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 434874730 1250 434873480 434873513
    0x50a120c06030903050a11010f090f11030c0a0302150405030a031101051006050403081615090b16020718090501151401021f0e01060b0a030209090f093304 68
    0x40d1110356a0070049040e01d909101c01000600300b030116698460003450035000000c0d40130004150034141d0001d000c1150300020040d169003d401074640c042c019550150007a0705016800b03404a1581000894038008052200034050b5180c1d01d030702120018032406072030140c040203041d6820300707a40d410005c10644030070510000651800c008030f411080345245000854026440b003030300b407914544071200310707400501514074a0410098980c0015a2107000203106202106c2c0000380b45109041195004c40000d041c42c0910310f1041c51009030503000030b4180c04a07060030b540d01020303604010f86840030b0540000d0040040d0300f411100401303240740c50440b50564141640c0503c0343e203000300c0120380e610800010716440f8200386100a54201d13403500301d502903204020021907103980d00c851207116580030074042d9001940c0800d01d49024036007a60ba40740c001204028080f401c6c20844016501c542100030485940c8482640c890040010748812080120034000396410a00e40342c2001d2440380307146842c = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 434875980 1250 434874730 434874743
    0x409060504060203060a120c091e15080d050309070e090f0f010c11060f220b040606061e020c131b020a03090f0e0a02070602040b04181406010503060f0406050a12 71
    0x1000c207d004e03e2403892191540c00508000e501881c100ca50402000b01400401c010020490850701199090290742064451415039402140c0780c01c8041e801d12200f200d44c0c42c200002002400300070748000031008281d0b500000d0481c850385410310541c0c9065070040a8948502a00448506884041d03000000c02c4200c0d41700c3e01e24003100398181603220721003201c20100e640c0103100801c1903189000050505034114881d1107001180a4071110411101202d00300c8140d40c0720b450500045a000161074601018007691203901d55118030041d4840208501243c0640c01c40c507012281040f0b00d4010100c0e6500403a40c3c003102102060b8000c0d103a0b500b204003030f8003107180120006528940c1806c42ea0803a6008200c000e010307125510301c000a540111030076a0740c4e0f5020310011505d400e40f64002c01c024007180c2c0007001c1400ca036030460815641d04c45521940c1d4103500c0308009890342c0210440e45d1011f000c40301709241c455010002002408039402503504015050000300e501040054004d0145001c4c10 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 434877230 1250 434875980 434875999
    0xa060b09090a05060f06120615040312030519020a0201140c04060e0d021f0203030a0b150702040b0d08030a020702010219020105070311010e010f020403020907030b01080c09040906050406020306 85
    0x11409021803162545a41d040810341c0001010308840d50f00440c0c200c1d100610700a82c0e0700007080081d00039001031220111610f62202444076510301544140e40064102010900785407461300e4a69000c01b80398240c03c241512000099000c581000d40d0324944030703812070f045407604403d0714000d0080c840000c0d02010002e0040104850503201020349003114650b42d1000070b000710303ea00f0303c456032001040403600461090200410081c1c00900f50a40350342580c01141c0300d280029141050b030f050011158005ca044c440d4281007000160100c80075140c058a0200b82c1d103c00c038000c0b034034002e50140003030b2414402005101000d03416800810419000b6422101000801d007150014582245c0000740842c4040002c400081d0140301d21a110700290302c00042c0762407100041c10700f92035181201410f11a400a4240114506000005c0d040501480c040103018501400648418400b03440041c50280200c0e08502603039864101b246119802a0b0500042c1014507085010b0341040c0e511521a06c0c104 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 434878480 1250 434877230 434877239
    0x4031a01140f0402090405131e03020309150d0905011517031818040305041a031b13030807110405070c110f1224060103020414060d1509050a06 63
    0x80151905981110078600351065210741000040342c8041d120b10b402680074003a140440d6981d21402d84106d080c00704110000300c007482d0484071100414022180c20540003908008254000251041c014041e00d00098511000e800801c250042c0001340c40e00070b04000754601003040640000c4884201307481307000c0782d043c0c41e204070f00440e20742c80d0114a0309620a110713200040c140d103010301c04440400303410400010184030302c140070348204440070f03808a035002034200840110204400d28400c0880c01c42170071030400b960400c040f052101651854a0008101040141d0001b00110300841d400344040da40e419480c9441d0129241800066220701e1800340040d4405000760f801c084000e900014203054940813008016021701d0598100350440010384103948107001c10002d510b02842c00050300c00381ca0300d40600540c1704c600e0041580341003500501c401c100c5205903001c95901c00d0001c03215140c039110242021401031074003543ca812a078540200000d11149141c1c095802080c0c0c100060201c070740c88 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 434879730 1250 434878480 434878523
    0xd03060501020a020d0f080c03070b0a06050906090402033d0506030d0c052a03010c020f0c13021909060201060608042102070504050910050f01080d051308120403 71
    0x184516800760f0081c034041001440e00c880c02040c2240700c1c07400ca644590003501c4121458200d80e8140c40c655100090000a0017100c9511035030040d41c40e40b090060b9410700000c28442500601054044e51003a4003003003c66606000785001c11440304444500c655100802e805030300c0740d1006251400551408d01d1001c1d01d128050284140341c0600101011031074201d04660340c2c2e0200a06540b940030b03002422041c000d400b8002c19011101c4171440f15895840d404150840b01309039a10400e40d07100341500300b0125404516171040703500468080d641962a0080c141c042e120388c2000084a1140245030407c80390004104d030103030b42840d4020450385031280b4068450903810b40d40a400411549124108005281c801c4000719002d4810340c0c151941e103030042800c0d44c03419100000d540e01301c220306007000d03a01442159401880c150200f2015450300c0340d135948a00d1592042c1c4e04202e00080c200d5660706c649603504004000c1da400f1030303c2c240c3d0200843c050f60f40041c0811035641c8425540b00c01d03800c22 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 434880980 1250 434879730 434879741
    0xc08030a060f0503061b0304110306070e01110c010207090e030c190b0114010903080a0507050706050d0e0304030f060506180103050312070f09060e190305010e0607050a0906030c0c14010e0d03 84
    0x40c2500440500306c031501c2519801d402c000c1045580101c0500c8003c4161400d000d454002c1d0f40c03035154040d02460100001d440402c00800104207940720303008400880c3c2e0700161010440d20381c8a40001c03a2142d0340c161a0035882148001246031103843c2002e081e402482c0300c1403960500603246685241d0320b5511a0080e04a44070284c1c0c00501030a9051020a490740300610780602c550a00c2c0380b80615565825003044419803007840450070109000c8015402030140f0078144080c08003451800b0300795664210440401803000d400c507907850300014850384884020080711755a10300190701a42c1e4914000c0d90741e03800100342428150001c0007058410f4000c0d11400c140501540301c1d282d40d5401c1c05000c603200904070031202d500ca0789075046003074001c0c0320000c07210145001d84000301d18800340000301450010090f000c481041030400444101a52113a6100150380b00f038030740400c09004031403003110507104110002d015a411303c0074011401005606c00c5c1e28110512003540e202c1c0380401d42c2035003140c1 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 434882230 1250 434880980 434880991
    0x606010f230310030b090d142511130203091606021f0609021605150f04110307090c0c05011103090a0b0a1d070911031003060c0c08030a060f050306 65
    0xa00100000c07920403114010310fa0041001c901161400c0d42c80c1c80321540181e054a44040700c1e003100001c0b004880e40042c88106400f604803049240105410030314030301007613800d04940c0340d0380340000c40303010400d10309180c041c0504002c0003240d1031407594000e08001d42c002c2c0e80b6000b0741e01c0b812001d82c070380c160603052140c100c44087e00a0400c003010021510786034071680010006140d03580340080368004041c03001d400000c03014150703010325507000d20340070345043e03141506450405008030400581e04031000d080796205501c500050717404950140868913011043e0003040d00030741043c03a010350303403a40940440316aa010f00020710421484d9031000f0324a04c400d490804154100f407442a001c5190810306d1500107156502c0010002050304001c0c0c1d0300c50050f400b4140582241c0b00030028410303203001d0340c40f40c6080640c50910314184141001c81ca4072032884001d01403070721428880352803406800c00c40c0207150061085c80e620b01c0c100309000d0090805000e4400801c1d4401c0c2c021131181000500c072031045 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 434883480 1250 434882230 434882267
    0x406050604090b010c1202030405120c0d080c0f0607110c0f060306121c020313091109010e190b0c010608030c07030b1b0a0504090b040e100213030606080606010f 71
    0x5040070b01010280c42c4070408903062194002410000949400c5c1c3c1c0010172920b40c2c0596103480c14035007000340c0720710040c900040541c40a01c003c2d9040c0c1e5440303035010205912104103541d50b00d10f80c000a0400c04280c50740152800b92004000110750410700f0052030000140039589071119403020804545a40b02c000e6802a4003400041c2d003c1c02c0201800e902c2c0d1081800b00c60306000700c602d000e45c114003c500ba50300140c0000c6040b0021524208458000e0902c0c0d44051048500c044070a00c45030040440460402240c0704900d8a51341300c510180c0703056800b4900c201030450b11240d1115182c0c1c081000e440c803035842d1040010b2649000b10541f22070610b00c002600b119071454544d0910006c029000340524034008884913500f02c01c800040c49902e481c0d4031856112468100600d040313408000300b55000786c0c01c02c282807506003000300d00824043d80b0030800589400d83c2c002140c1d02a8065013004001c913140410100300d03c0b5001601074451034099880c0035944945400c03c40e4203040400302c1e140781 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 434884730 1250 434883480 434883487
    0x106121a04150b160308090a12080c1207021507170408030c09130921050a081005041406030d0c0807030c0201020a060f05040b0708070f030504060f0c02160504060506 73
    0x803840e00d0742008540380300d020700c107003005903c03042c3c00b4800750311000000c5211030a004440040503007040200b98004c0302e000113071004801036111480b505c140d103042e040c01c004050001820f50b050140944409000300003016940d0310b0310000103541d882d40005900b030a041d1040018400780e11846107414041428012100320f0744840e51081050b81001c1d02c402c03c3c0010502000059484079000740c501000520008590079a41e424081070000341650103800c403540400c6240d014a40041c100c421001d1186070a08a55640e515010652080358000590050070700d00400409420040054040e00c000c0341074400410300400e003035403a0091100e004200400600091020a000e55a545612030040c010f4840710b40700755540da0b08440b150107900c1038080da114180b0062110b10f607607981c2c0c01801801c05600d10f00340700310060920300c1190003c008054854000400b00180c0c0e800a1917540d40804080c0032140d1415006910303480c1c6020002c003c0702d0071a0700003590f4900340c0607204c00c80e000075002d02d16 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 434885980 1250 434884730 434884781
    0x30b0c0a18080d0c050309180a060509012303010e030d140a0504030f1124010e34052a0d021605010c0618060c030c23071a0708010612 59
    0x502c1c4e51070040544050005000013a01c1e601d80000480081a0240420041c1d20380b00c0003040480d0f46036003009001e0040600140154410820546060b000084820b032407406900c001902505040c3c0d85081c441c0004203184015503d0f42d00402018803120407410183c1c0d50307820035042120000c890240c0018144004600d10900855034034140b1103010064941460901d52030300b002d441c0e502d600c059294404001041011404900f464224145c2c420340500a006078082c0703040000003003070b050000d51014102031036240c0a401201c465414004100c60344003110017141d5030b80103c00d00820300c280191b60025180754404a042007004800081e46c4020600701001102c541c0028107046560300e50b141003c3c0020034584954a004030f2103801c003c20841c004035402004d80e00142402d00c1030220308600d119046000d01c032440c100303105e52201d0796240c008905184071807001c0c656942076a042e4040500c0b000a42c82102e40e41070780c0d619100c0e00d0390801501c01000c00c540c1c00f00301c2009016001041c0c4007 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 434887230 1250 434885980 434885987
    0x3030612191b0f030309030c120f080a051b2d0a170d020d05010f0909110d08190e18040503090f130204080604170301080712020406030b0c0a18080d 65
    0x40a0b900603142020201e449035140860000300360002e42c00300b45090010010085030002400185c0414081840502000d6071070407500040a280100091004030b010f46580b4480d44c1a10240c007403a1030b100e0120003c1c0121a902c1c4d9401247c1404502c2c1c1302c004092414081009110302d01100c1e07801050342e485144c595080b000d0300200d40e02030041c03003006406082c5816002800003c01004400105549000298080f09289901640107141000c07180e5010680403040c10601210540da0b09150b001036141000c503034840e03d0244100618403500d0882200d600c40c50341401000295450b15420082514200007240c0407100284640e0080000881606003200c040180d14030140c9000c024010740d101c40c0059800503013241c00c042d40b140c0100005d0164401c0031183d10000302c41000e02d13550500c4621911885940103025030a12a55032030411511380703078004001907402880e00c110504142c4403150030380e44407410010001d0100d20300b0700701c1d5402040c00481103508900c014043d4001066040c0c = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 434888480 1250 434887230 434887253
    0x307030309052508010b032e0902120f060f13020402030c04090501030f0309050402271201050c0a020616080403050f1c0605030c0916141326060c03040b0c07060c020303061219 77
    0x2003102c0b89d244c0f0300740070043c0c540d8038a07000710790945c10207071041d05e10364548980382c01e10050125203410101003c1c400500d40058042580079010307034000d6640d41d82ca0384100342c140b1465010034006071400000009122000d00c000350075901c02d940c0c04410319518400c202c1a409841030b0720980620700100300110f00260301d0032007080c03107015081009c9065011011030071290200e0300990790100001d050500c665041c0130666104a00d41520540212400301c0200305945c018401401e008000a140d400c0020b48802e03513081084c40c018082c58007143c0305890b0054907440c4159802486010340d001039030314082d0384892085241e20381c1d40b085149142400c40d80d00c44010750b2203000e41c2003009980310455009030b034003018010b06144003c854024903048000c401d61000114040e800540a21882026546c1169002500001074050380d07229090030882903c030b14180207000d6072810078004a81500400958403424044854011210750b049805840b0707510707402c400b02c2d90038140840400003401441c04 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 434889730 1250 434888480 434888563
    0x111005030106050d09110909280803010e091608030a0f17040b0a230114030312010b090a090203071d2211120f01260307030309052508010b03 62
    0x654581da84414041807c0b20025100500b15401900c0414496042d0031000b40f04403a0324500131b0540400754a0354240b500040c02035296581d181d80110300c48981c10801101240c00e55160a801190380d103803140d0790f90340907804240100b5003145030059400d0254610400ca40440f0480080696450340e0716804410010903c0031025a1881c0324a00170341c0f03901d20905000101c140c012400c1d410803000c61441c0401416961295004025030b800c05000d1b0101c140c11501c0c901c21217030b11100104005284410190071806600e4030100401c401650702042855a144a8080c1d80030108814070511440d010b5a21400c040d4152005060340da440956122084000c05107150504011181050055800060700c42d04109030840005200e019a11806090f0116070000d0828804035403018150f00d07402413a001038145640d80919100380a81808203904c5007007858805095400e442c2c0d0140d6040c18180555400e0b986007141c9002503090001700808640d0b01004000400034100903202000c800e03c051 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 434890980 1250 434889730 434889743
    0x40b0708160e270a050f06031504020d0227010602030f040506030a090507030c15020105011401120e0f1f02090105040e04111f11060126070b0403111005030106050d09 73
    0x2020b560320843c2c09506003092000c0004190504081d0200e00c02d41c3e1000c2e1408903840d003088180300c141e50340082c080f1810302c080700051a465a59000081128001d420007a4000711103141c00c100507000160b10b01201d288241d02d112050b41c03100002c903560300450340c04c40c05058040000340f0640c64010b01035507000c4000e180128140b0750a9079601c2c140502c81d40111220003080400340815040d45950340c91404807880200b04940c9041d02c41103a40e241088440d052002e601802001180503400207081c0004000495410110f007070703035160755400107501f051031829102c4078400c600e0381c0500844100140581d101800d00d030a009a24a07000c0c0302800481e06400c000f40000340a458401500340c050f11860341e2040000f400074000707010103403240c00d100c2240d00004014070000c0e40040f815200091504c854007689054a01d0141c6011025040503442c040040b400004010403c058900c0c80c5100741e95503c4800040401550740e4003081c018180070400034488110b1005080d441825042c0c020007 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 434892086 1106 434890980 434890999
    0x201080a0e07120f020d1103101a0405101a09120a0203070905060301060806090c0307080f281529060304020402130803040e040b0708160e 61
    0xa10481c2c40303160f84482e000d200107140040a0700e0360103007a810002400b0b00708003840c2084884043c0c4a0304c1206c40c0c14001013130902413003c020100b06050911000240704100c040d010040c040d06205006140000d03100268120600f11421100c007096614000c082c01e01108920020190304264001302155006803400181041100c51592000507251603207400207014102e642c0c804901846203806100c1003543c0400d4051502504404903440581d584805a40b40c4200100008598000942d0b14048030000a0707004042c1c0780c25007084200070040e980b1500380d00c228100700ca01181d641d01800011140a842200400c0600c0041c03a00314840400021a188001000203014035008500d00d0906901c010300e502c05810044207803500d464a601c12140300b10402c550a540b01a00d0201041619005920305030045000da0801c1c0401144604241c82c0c801c00d0070446904a82c0a0 = true := by decide +kernel

theorem cover : BRFrame.Cov 434712230 434892086 := by
  have h0 := BRFrame.cov_init 434712230
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 434712230 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 434712230 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 434712230 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 434712230 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 434712230 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 434712230 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 434712230 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 434712230 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 434712230 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 434712230 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 434712230 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 434712230 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 434712230 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 434712230 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 434712230 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 434712230 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 434712230 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 434712230 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 434712230 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 434712230 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 434712230 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 434712230 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 434712230 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 434712230 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 434712230 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 434712230 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 434712230 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 434712230 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 434712230 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 434712230 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 434712230 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 434712230 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 434712230 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 434712230 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 434712230 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 434712230 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 434712230 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 434712230 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 434712230 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 434712230 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 434712230 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 434712230 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 434712230 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 434712230 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 434712230 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 434712230 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 434712230 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 434712230 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 434712230 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 434712230 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 434712230 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 434712230 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 434712230 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 434712230 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 434712230 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 434712230 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 434712230 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 434712230 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 434712230 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 434712230 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 434712230 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 434712230 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 434712230 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 434712230 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 434712230 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 434712230 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 434712230 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 434712230 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 434712230 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 434712230 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 434712230 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 434712230 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 434712230 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 434712230 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 434712230 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 434712230 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 434712230 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 434712230 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 434712230 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 434712230 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 434712230 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 434712230 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 434712230 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 434712230 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 434712230 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 434712230 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 434712230 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 434712230 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 434712230 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 434712230 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 434712230 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 434712230 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 434712230 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 434712230 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 434712230 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 434712230 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 434712230 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 434712230 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 434712230 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 434712230 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 434712230 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 434712230 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 434712230 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 434712230 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 434712230 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 434712230 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 434712230 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 434712230 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 434712230 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 434712230 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 434712230 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 434712230 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 434712230 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 434712230 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 434712230 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 434712230 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 434712230 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 434712230 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 434712230 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 434712230 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 434712230 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 434712230 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 434712230 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 434712230 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 434712230 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 434712230 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 434712230 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 434712230 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 434712230 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 434712230 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 434712230 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 434712230 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 434712230 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 434712230 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 434712230 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 434712230 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 434712230 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 434712230 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 434712230 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 434712230 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 434712230 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 434712230 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 434712230 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 434712230 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 434712230 ≤ n) (h2 : n < 434892086) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
