-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_4991
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T14:23:09.038509+00:00
-- url     : https://prove2.me/submissions/d1f3a85a-40d2-40e8-ab82-aaafd6d4942c

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 897482014 ≤ n < 897661870 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 897483264 1250 897482014 897482029
    0xc14061603060b03132d06060e060f010f17131e03120507090b031f061b06020f091009061701080a0b0601030b040f32070302070f0f080702040b 63
    0x35005440c0c05820b42d1100c04c041400503010040c216a4000700340381c0000c40098020840b401b04071120401c005600d001e261060070348025038031925204558500780503441e0b96030841842404000c0c85c1c20004403149010031110440600a07584500120703405004501000c0c0010b4185503020b1510f00c0ea0381140d0f20ba00c0c5001c00201e03072000e000141254030340c80a0f802150051504034a0071724121000c01c0c1c40e202c013000345074010f5403030a4881308a02103036105204040c3d8400003c02d51802d1018990001a04111810f9600307100103048560000f50200300d0a010001d0f662030040141c40d1100c90040908042c0c01006203000303e802017809041109103206210480c1c90503a10964050440b5041b01d035030b03040440c0350242c155814142c990541515075200e6102d00410000880c070040742c41d003a50342000c403951400301c0c0000154042a825202c0400348002c44039000314140c5030040e5107501500b4405403649014400805800a0008a2061281a40c054208075000300c80030000c4403203107410011300c03 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 897484514 1250 897483264 897483269
    0xa0c111206100e160c050705041406130e0c040207170c030408011b17061315031406040308060123030103060e0606040603150207030c02090906071d0108060609010c1406160306 77
    0x720044d40b03501c503609103d60314600c0094490401c42e4800d60300d03680080d084e83d15a00284c10348020900410400d0301d0545007581180f0003044003000003200c0702601607103e49011100da40600e4000840008001c0d0301c0070302801c414140e69449481d40030f0001c11780d4403640281300341d812640c03c0146d030700301841d013802410366040b516440f02c14610300c84c002e003202c80e41c0c0001c10072a031082c550368890400c003030140604681807034101024103040d8118601070091019a05c45c0315820b138001d10800c80001e80143d040b64009609080280c0d00c10035440b19aa403c8440032404050072001000020400049401a42078000c003002598143e544110a100440302d85110243c049024420240d0584209034020044030303000c0d2a0442040f0607e4000c01c0c42c1c101d095072502c0c0180c2c441010018444e0340302c00187c40d079100b086244000c00c12510b000814a44001d8a072610070100059412030680c010600c1d44083da03840503032280744800000816448040c11104200b00710400609150001d100384140c805 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 897485764 1250 897484514 897484531
    0x151514091914010612141b0702030f0d09170f06041101181d0105010804050c01050306131805060106181502030c060c130b040b0a0c111206100e 63
    0x1240e03981c0320303000c400d601c0d2020381080015a14020078501c00186201c550103800c0170b44480c1700c070b00c034014020021201e500048002145000040c400d040302c0d0203209685402200c410365499000c01d00000f401d18202100402561290501c003c14060f04402c2a10481c2c0004404400016403891a56107458603150000080d80001c07001034002000c0c0d070803002246606140001100c204803003610200500d0760007001560808a401d100306521180402d0701401080c07808090301cac205540d41e5581e80c00c4c0c90341c04a06109011001540e00d45940c0c000300c5504061039001d02810308000100d0401400409090b40c1074000c1d1400450420300440e103008074003400d4007106003114039007084d40c800340e03443c003c0c14000c5000c200854503010104100c0e4601601500c11280d589010340154000945000d0b403001900c5501440100b140e440c210081d0b4042d02c00a04100400c4240382c40c0150304c015013120f503035520580d0000304001c5101c000502a03c152441111404010746560304d508403c14204d40300d00c0d = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 897487014 1250 897485764 897485779
    0x7030618020c1507021c1e020a02060d0207030e04140709080f03121003020315090706090b070807150f0906050f0103051e03040f0e270c120307151514 66
    0x1000c240c403c581c140d070701548601c113031600100007141e0300c0611000f21300b1700d00005001c480c00e00300d0b401000b400380c10300c806980000c0c01c0000b503690103d40c8a00864881441e4035a0100e0382d482814060520381da44000014803c0222400d07e9503000f450282c00d94107030300054a400f102142c0d80300c00040c1a100100c0140007036050900d00c000601006c4d1008040480e240d0040c1c0c00000141c84c20440218103030b184822501d194030b01310500610380000c81e44664100300d0180030402c001e403c1d41e0b040307824481e00003030040d5072040e00341814062154280e03541000540ba1100f00d84941c176240d44840c42403031090700180065250904101141c107403c1c08050060b80018144000f400343c5030041449600038601902c0c100703607490350050030071001603114502c00811041041014810a088113503504030100d00403100030000a405039868004225950160102c1c2d00c034040c0c1400100140e840e541e03031000707842d8403203121641c3c01030140007a104020079a00c45013201051001e0842d021170705551001d0100d1 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 897488264 1250 897487014 897487033
    0x3080a08102d150f260f060d1208011505030f0a0905120a02010603020a05061804021b0303240307030302061b090d03022104081b01110607030618020c 66
    0x34180081c81c0e01c0809040200301000203c0121444994040940c00c0c1c550b030f00b43c0c5002d03130000b8040600ca221001030311400d0100743d0036900c1442c400c1641040f81d034a100c06950b84e4150104010350702c0b0301d401030b00d0303222700c0c8106114095112001a05880c0900484141c03040b41d000152001d0009072a20121121160700040451a0503031011b4003044c000c50844821403001c152503090b9500c44480c040050351104002d00c01c2d8242692904004c1c80180c82240c81c2102d0700d0220004040022140ca2056070000b4003118a00c00b990011000803a0040507280d813418440300402d150b400c42c841ca090b0841c000da2050714103140109244040b02c1e00354000c4e08184c1d41e008040f08203000c098001ca007548005002100e4070340c95031640ca10b49944250024261821200c0281540b14101b0a42052040c0c0802081c49100e8001c9000e03100f42d9410300014060303400c00001030b20103404049201e00c1512801040181590b4150041ca00700d0f03148ac0c100c41c40761030242c0d608400f42d00c68088548840e51214080703 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 897489514 1250 897488264 897488309
    0x210a0e1c0512060f09090a0b15100e01022e0506010f050403030e06160f03110303150d0606091e06061d060304050c0405070e01080f010321030b040603080a0810 70
    0x30b4a40c0208001c109038600c0e4030031400221441c100f51800c10b00c0d42d1060319103000704901c0240c003640000c8105848010f0100200000f502586201c03001400c0080038040e9402c2a402000f01c0c99401c02041001d03000075040b9071621501e001c503508440d4510b170170400410301650180501111040540e0f841c5403509046441c2a1922100041c060f07402c894100101c1801c502e00103981094107100d2003a40098010600f4010700c0c00f00320250768040c41c0c104006008040c02503181c604000c103410b484002c2181c040e814080000c01255000604007810462482011890601c0410445881d280b0400c481504ca02080b5840124601162401c1911444184a914111010b140c4c494414401c44034001061004202074030000da40100128001c0251313401550307046007400c0c1d440102c200c2036083d21340c0b45440c2c80f240c07000903001411041c0c99002000404d28801d400190344241c1c094001d0180c030f60340f4641482140d00400800f0001703241940441e02503451030a01408071012000420703207019075a01d1 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 897490764 1250 897489514 897489547
    0x40503030301061b060f050718240c020306070f110313231003021c0b060a1412010305070306111602281805010506030912210a0e1c05 59
    0x3880030481c0c0f41010a00300140090003941411000c0d44804102c7e82044003020704110101140102005a0002c040c0318001d0301d80c02c0300c5140720200907100280c60b0240c0c4103444403544144040c0d050301802d0104000d42d038114144500001c20355881401d1400b020040355168000d1410403406000009420030400c03540501100d0031010100360b407c2d210281400003a500014a14418080b80c1c02040400100c2072866549203460600b90050010355110000649944920303100c1e14203100b540c0070342486034601c1100766016840b400000c00f12550312800c1840e51201d07a40b00071aa264103000b410440740113510241c0d80b28081014100000a4880d801c00082a00d524004403a003111000d004a034039001040384801014a2002c0301002c0040602e001d00b41c0314160841c5005600030000c0c09000b0780c00042071184250090300f51b5485070031000c6c003c903288002c20401c1c000310110030140813807210154458000c003c00c0b0000c80399114461248404207852400707085000c5807040c403240303c94812420 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 897492014 1250 897490764 897490787
    0x1030b060904020a0e0a1e03060c0c1a010812122806060309141203040303050a0b1806010206010501021b0111031204031709070308040312020c12010f1104050303030106 74
    0x80c48a82440760744008201260050002c820001e0b80f01c12a405090400c50410300140115800c0b400804800c0301e0340c09901d02c3c4030320000388255a1000e81c508042c0c4100ca402c03d0f0151b00105490f50104516189403a001081c01025254055452040c001c00c01c5801200c0b000e2800044413140c40d43d0b000d001540010031113200580c5000090700d02c6910f00c00e40d10652016007060f840004020f503490810f1681000700102620103540300d5201e04410040700d9050300e078020351516001c5510f660b242003080c040c2c000703104856003000c42600510158030302415018410070080c2e0854541c0ea80c2c48004a82d1313004420400c07200702c501e00341928025441131081c40e28803100f0700c0c2107038601070234109000344810080301d083c4c0025400348100c40340401c81004258010401c5001468401d003103031205200380c85584402000710010240c2c08203200d0007032100d000203070001000400a00166141c17503018083c2207501c1c84140b494800c10541c01901c21083d1000c0c1e0f1b501400850450b0300f4160107480700d60b80702 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 897493264 1250 897492014 897492019
    0x1e19020901030b03060106030c12141f09050f01033003020c0f0f0a021003020f1903150e100608040b16180b0406203004081507050a020a0201030b 64
    0x12011143d0f00d0300c0c1004402c0c02050365030b4001030504510703034004080300d10f040304203810681488900030403900d04a1195401525641d80c02200e0300c001c02404c1c4035400158420f44200381040100030000843c40403c904990148003d816500b114111a907108519440c80141e000c401503401110706203c2d074042c6c81c9002140048170f502d0785882d20b00303d15110101f00c181940d58020791101086041c501000080d04005003800d6042000682c0d03071191a010f0080c00031100030070290f202c4c0841d40300341c0202004a81610f00302d0b004a4407100356024503c0120307400d051405101d100022180d00c6440c03040d20a5802298100c0305840c1c28a001008425020042003044040d81d4201c05031101c10198900400a56078030700d664524109028101520007008600b1040d0340185c820000b8101042030a00c205a049100e0031b2408105100f042c00342c041c1500b0501941d003c60003203958a000580c1d81d1410f00d10b40142021a92411000c07105440b80101c484011780202e0052170065000b43c000e0030802000 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 897494514 1250 897493264 897493271
    0x421120e0a03020d11040b190501081003080a09210305070f21020c01120504032f010c0203041706041e0f020d12090e070c110a050402070b1e1902090103 67
    0xba50001900c01d102e4650540e640081c0485010051401e8030480000c41003d0310080360100481c01d002400c04054420141401034072000919040e82d20040740010b141c0c0908501e40720307403000c00014020115402403030200c0000c181942a80b072001c91285610700d5041d030311649480c0440d61b0700e03001d0f0b4551000880c0c594400d0129000094008140b1680484040e8010300205a1040006141d103003100c1d54805000d01d01750910000c81e600c9030f40e580c072403800d0501504c00c00c9000d6101e46034022460b40d0046143d440e0113245240c26501000a01c1100e00c2c010707441100305001c044194840009490003000c18a00741e101e221400703c680300c07500105014041107840700e490b940115484501040045504000c14104407107401d40100321240580150300c03125400303242c40320000d08204100c1402811180d282020300e04150780b038151031009072070b010b4801c1d5140d00c110303e00001d10117426500c561140c0354282d512000d0744445e54803507104640d0309200001c0601c020303400a00a500c01511203042544 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 897495764 1250 897494514 897494519
    0x501180503060108030711061c1d0f0d1e0c12090f03060501210b0c090a1503063011030a0b090c040c020102210603030c010608030421120e0a 62
    0x1c0500c44240201040c0e4040c0d036591846e03151241480803c104954420603050000b070b9101c1142c61090b1506030403640001449200400d0030090205001c031718000305206940c0c5820124101040e1a0801c844a840d00d0580c95048c2824a07402c1424203003210000e40303882200700c0481d10302d56030a00301e860b503410020703003880c2c48000b418240400783d00180d40c01c64403103004000d4000c800018154044019803174606400003603540c040400d00140500110040100c1d00e40040d990b80b82600c001040c2c40108803101551155000d8040c0038a48240e100103043d60006251841d405200e06a082100d02e02d0651244140e54964100f81160500c0c16014480d1041c19000681e54070342d03040c0aa10020018145400a201040107890007040039004590040c011456003100c2822665001400a0b0724000c0c1540d948010034550b006140b0940032943c01c4c440b002414140c00300050040e1986800720040c00014a0055007040c9400d03100280b481f4803240004503400d00c00e080e1816141c0300180f4090001e030703 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 897497014 1250 897495764 897495769
    0xc21012601270807150504020a08010219141309050708130302030a0f0504080f21160206030c0c0a111e0108040b0c04050d030207080c0f03030417010b040f0c090503070f05011805 78
    0x9083c0044103403246c0d04c6c824041989070028224006011050095180c43c64410625074060300c0d407840c1e503007448020381b12556000703944400c0c1c80e40d0065176100d6180c2c140d920f01001000e0034003aa40d040c0031a44c14008100f0400c0d6440c0c1c0302d8104c6405030019443c00d10185000c880780541c1c03003801c5040040900002c140d000d01400300700003204004005020aa20500a03d41c1d002001d06a405658100704043c0829040c1c0c0540c5901c00c6030129100c907100d41d515040b01040b4441c04071051014007039400031404006180380f9078000d00300c05030750740c8003803041d0242c2c00b600441d000b0151078007240060000074001214041016400b04c8003c401d00c3c1041d9883c40443c20740b0240c204c003100542c04c080c00a000c5c8510411520f098904100c500b882d0146401d000700e42c032071141d8003c44502804880c850284480d094021010700c0401400c00c200584002a0070740041c00c101c0a540b0002e068044001120720700002c3d01750584803121940c101c0300386448010759011441c9081000240108034000800c0d6 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 897498264 1250 897497014 897497033
    0x614031e04031806030b01020c0105130308210a05040f060905010b060a050a030e0307030f08040606050a03080304021311220f06210e03030c21012601270807 69
    0x220b129446003801d003c4404490850303c0b8460f00900e08240c5030010750070307250b80d00086e200f00d144404e00f071403584d80d0204103600c0e00301c110075040075100404c00640700c0c40303841c2c1840300c0740b40c1c81c1c07018a05d640c10b81c0c0b940116482619810381e009811440100e0600001c0b42169000e44203140c4960000110304803c1c00200d0465080342c0303030203404900c01169071070305a6098010025018001c00180d86001c071940c2c1c2c0540340c811802042b10411800000050070000b240d0300a00141c24014107500a1a03900d29105c9819442140c04034083c0282c1d02100c020350b513003800784202c3c65000c00d825a0600c032070007140ba14000c03008181307600d0504141400003161540805802c0160416a484404000004080140d01c00320620b6000c0c0c1c0c04d19000200070340e000042b040e41d801c12140304e11156034008222000a6881e66a141c0c00c2c0700100440001860385100281090801e00304d010701c008500302d240e003817803c84003500c60701e1720601a0303040615120601423160050180c4030b1070805e1304100081d1148041c4 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 897499514 1250 897498264 897498271
    0xf0301020c070618140319031b1529060f09060c0c12060712050a06090e06012d05040908251b03031b0c090e250614031e 53
    0x401e268030309005003810080c00010252205000741d8503544d0540011071f13130b213003129500c081019021201d104c040600c0b0700e88106a1010f1080304890300400ea04103480c0b18401071224034403043c90440018032410403c0c03000c09201d10341c01001c00603840c4200900c203490b444807021064244003000700c002c495550601804041c03071880024600945250240450079110080302c1e80e47d0f0740450200f00c641756000c50b0b681e00455800304007080c3d9403a800700c114003a200e59084488114181003c0f5070310a400040e02a040380e0002d0700801030f880a01d24801100340d4240b11030251810245400d0000d410300d0b810001d1114462100740313282c99240c01c00c0c00e500e940450b42a900d8841c0250500c001e0007105840f01c0d0200c501412080090313491540c0141c100c0d114201280d0310b0780340d80c0c00c1d1603080c080d40b144182d00a00d1085030074000510340c1e0342900c0e103441d01c1c16003c10f00b204160038040032400701c160044055900640303c01c4d000c50344101503c082d9400040c00c06138003803407142c1c40d412084030902c000d600 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 897500764 1250 897499514 897499517
    0x510030e19050f191101050c10020711091905100f060e060f030c03010608090303071b0f050303161b050d081312051903141305160f0512060f0103020f0301020c0706 72
    0x4005098908174007070302011100301c3d040100074000f1600c01c80e40403841e555804581d0000594a905600c0d045200b42035008500c2c2d40300040c1410450f4074a07070f0803140414044050000c10166403040219002c2c22094055000c645640500c10b000803401203299884221005240a0038606004d518151581c400c0703490340d07a689800300041100b80d402c000581d401000c040045c5045240c8030400030002800c0e1340c01d1140d401c60b07010900081c082e28540c64030303440340c000c42905e0352850015100000c0f404204ca01c180058500442215203008507070340c41c1c0f815035000f00507215402844c2c0f02101c04020107491000d50000c900c004800148040d8110406541c0e01d0720380a4803801a8500c2d640d0705001e0004a209240c1441c44d03d03140311840c1e000e0301e54858440500c85502d01d2042c1070180c680f294060017030350300b00385c50b640108000a80100329011507804403030240c001c5803240c00c099145c070410b0b038480c400314880364018030052406480d80600354101a0005003813506030f0800c0c078600800369000c5030 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 897502014 1250 897500764 897500803
    0x23070c080f07030213021c0c020c0a2c190903030f05060d020d03080c0f03010305151605030c07020f0405071d10020705090a1407090510030e19050f 65
    0x429400d120300760051401d80e001e407a0032450340d0003040742c1c800514a900302c0107a0000e00482e1441d50442c40d60750303a0003050001c0042004188000e582c0c2d0100e204910301c101510b090014510a002c1c0e501071001d03030f4070008961003883c01c0c9510011030001505101c0a03501c55000381c4651841881075038507950180e42c001c10300801c034049010890314080c0c03025001c0c09030f000b840303409a10f40c1c0004402c016071518151400b559501762400702c60044450f04280d41c4400000041071040006141c81c12300041d1916000940b1071080150308082181c4040d004907409100040140002c031000d040903a001416400c0c01c2051300c000101241c4080b90844081042d030b032040c1080202c915450310400c0420744400e1503200760094060b42d59141c0344101c9103e510140002020f80d1807031f03000203080700c0b09682c0c1c120903400c00c1c00d405403c0144e2030050034020302c826602090000d03c6400380c444018581c1c03001d00800c1000e840040310340c0c01115400d0352544107184522030b82d00020014101c4001d403200551 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 897503264 1250 897502014 897502019
    0x180406052707140a1805010f020a030f1214240310050c04050901080f251a0f03090708250e0601091a0417060702060c070f02180f06040501031223070c 66
    0x175240940350050317810000329807070040c0b000d900041c01c00c21203505401c040e000f44000640846081c105403ca0003900e80c100b8001000c05103d8032034943c0034940042c1450454144400c07240d00d0071010580040e0f040c2c1c80407900d00100d0160754011a00500d4080d606854240c880d404940002c2081e0f110324803a90102d1a0400300b240c040c0800e03e0000b900e681040641480044076503140d90240c09406160075180b03040074081e450b02d008481001c0c00c8050410788a2804002e0303a0f45800081c401c105c8a0b0080c0d05000c031007200012000c00d00c2c034002d41c209551083c20150044030010b40282840c2c10311044110118100b070342d0010640350b4035200c4034040d66490600120840034488410440c02d03585c00082844669500465216030203000c4844064481c461411300c0e00413880d800d1380203500702c90502c105130004603005804501c1841d80d43c0a60080740c88031014841224024800506600e6031000ca12100c1031140b030f04002c5003021050000d035040344502c032480c520340c00400120352045008504 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 897504514 1250 897503264 897503297
    0x170415050415150b0a051803010c0c051509060c03040618050106050a0602011a1014041823010501030c051b0705100503090d0c08040b180406052707140a 67
    0x83c01d442c080c0b1014480c1105180003a04092802050141424080d001c600700f00203000300c0301d082013140741c0200244214112084040d0901c1d207541030a079842d0161001d1103000c2562a40c0070f500404040d40100300940c3c4010700c820103a000a07000721102c0f078a9505c14044000d0b150301420525004000000c1c10134603050400070482c400342e200b401964100802d42c2c0800042c61000e50788503038149e87c0d40e0303071000120004a861000400030a200c1c0d090104020940900100c1c0c4001c1e1292120010058003240c841070500c00383d402d03001110070007603110042c0080e520a405c00d40b070302441814954200005000444001d5034040b0002c0e0746540720390003c110a140c043c170708400480311804c11610310704040729500d4071400850294028006180c40000c2044029001ca030018040303441450346801800704000d4a610301500414416400c040b40440c2a00d8424144091b40042d9074841c3e10420804235400300e203c800400d6032090210420042d142da424541c02029454940e0f45da81c002450300800 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 897505764 1250 897504514 897504521
    0x12010509100905060a05090c0a14030c0604052404091d15071e18090f1d0d08060f10080f01080c06030103150b0a0b0c0606060a170415050415 62
    0x10101d140301d0030300280401190340450b41903000103c084000c00c079940e07803955051900f80f030700715090f0300b041c0381100c002600d10101c4414013a01c0c00440503201810561400c0041c0c038001d50103800c0e40203084030110004200d803c80c41120100d001205507050036503c40b014011a001c0c03149001c00010038040071450041d040c090b0303c9625086002d201e2090810040080944120010007580c4440c601d1002d03c1c030a01a81c3c0200f8041e0380700050300ea5054440e45600003074007039491101400c9040c04000341d9400d01e50804882d85904071001003091081e004400c03035036841c010f804581c2200c52040c01c19040d4540b0342d10801c19004503242c0b411141025507034144800016030200c1c00b43c2d084030700a0350581d40c51104490450303400910b034046c0c4480022030b4400400d02c0c00c401907030040da001000141221207502424400346c10f0401c0c0e030a203030341c0d00050100c644200c1c0310400024141040b682003d20f4250b0003150428084d20f0328054030800000c10b003003120000e079410341d042c03040c1c482000d04140c0e0901 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 897507014 1250 897505764 897505783
    0xc09031106040b0703120207120c0201020c0306070219020409080a0305041b03050a20191e08060604090f080d020304170703120b0d08070b0709050102120702040902010e12010509 78
    0x70364080c50039240032801c6015006509000f020050038030080c4005000c103405581c4030541100c0d10300c00804010310054600244614200d001d809186031540b0a0318011a80c284542c0c42900a007860146500f803015501500340d5040743c1c407a940b0302551001c9900709000e0000320a1980380018542003d007030080741c180525011704001c1881401c1880001d00101e00503114a9201c184d810300200f100c9020000503a01e00050307a0809070058601d050058044948030480b5007100c842440306280c40342800007809507004030303101a4031210101c0e1203410564860001d0a00654079001c80d001c01e9580d245c001c2e440100c0010703034650040103100900900e400c1e0f00800c2070501c100c0078540701c4c055602420f480707050000640310b2a62541043ca841c0c5521811482083d803009500ea600c2125282582d00f040f01034032121300081c41008c012400354000102442c40c84080b42c2e0341070800b0b00c0e543c00c20002e859404802ca0400c086084034107501d440741d0541d05003001d2801c0000c11646400700f007040c94240d051 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 897508264 1250 897507014 897507019
    0x100509010b030c03070b2d0313150605031518030c0606040f020313031808070b070b06032e14010603020703020105160c1b030b07090e13170d0f0c090311 67
    0x40c1c0208082030001b002c540d80c244240302c0046249460311845201014881e0f01c00d464481d0000410074035241d00c2c078002000f24452042d0300c0d00c411502c58828204c600c140502038259002014085c50040340d200200e40c4210301c01019451a03400300c01042c2550801441040c1d070394841804d10680b403504e070091040c005051002142545444200d0003061940500c028040c8800e002110b000311301800030f0700c0003a0000b4400c40c0c40312582c41924420a41c440c1b0030644021414201245040c0b60100c1c45108445140c004558188001c2900106000100040041156852000c03074104c0d090480201c2c000c02090320016210719284c02c000c0e0035110300914a1800c1802042110700340703070304000c4200e50582c00101400450000005943e01d014980d0406085003520038200314040341d0000450341a965682581c01d407603180d101c8140d05482070303c01c0042c116220704034603208042001025194501c0440c0c030118054200307800c5c40d011580d60302030041c009130710340c5001d00a1080d116803110f2000c07402d = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 897509514 1250 897508264 897508273
    0x20c0105120a020a020a020a060903060e0708120c07150905040515060301090c05040b0304080c150708190b120708070f150c03051b010f060605030708010e09100509010b030c03 77
    0xd4a109901c00070001d0103484415030100c1d428103c1d038400c1109030f107059805000790300610b4a03040c014003213807464441200c5403801c1c040c0301d0302c1030a000302d0a802216400001440410200410214250070002c581601032041b4000081c004414202e01d00c00c07024161507034407503a4240701c1404141c3c0c00042544401e0a00586a120b1940b50381c1d08076070465490a01c0012091003001d42140c1c0b80c441c0b584840301303010b4044240418080020000d1490072030701000c03200c050500606880820350b0031201600801c1e08140011041c0302141d040c00e051043c990070028003400002d0005420381c4001100701703411342c84107000703004181080000e0000341c03032642489454985008900300b01030b881c21082804002c04540241c0405010f04141c505405001440c110640300f00e41c0980d000f09481824008546d0405d40005a81c502036030444e030190b640d5642c0d07000c1c40e0b800d22850b25101c20018201c1c0469100e51181c001020540340300d0b0500400c0c4400001c070700401c40c1410145400d0448084a219811 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 897510764 1250 897509514 897509527
    0x30f01151b1403040e011707060206011d060604180527120c010b1005070606050604061209140f030309060f0708041113060303120f060f0905040807061407020c0105 72
    0x1501d40004400c9034000c40d030310642d08040e032101e402d5006551217801c0b140c803028000319a41e907c80c0c04103003c500900080b15072150761804100d075110400e224a880b12011420031440402c101280158480800380c0014a0299101c8990070000c14540000e041c031943da8051040341c0c05504807070313039480c142000c400105110150800d82c40d480603040905a110000030310126915003900164070701e160003809071400740c1c940100034003554820b603403c4840341c1c5030000204240c94000241c400752035441d070b00c250000205201d000c004092225054446545141000c900a00c08000203d030300b00f20900a1a1242000004c0d036140080190500d80b180d03401d40c0403c14141d9001c080303550301a401603030301c001502c00b1801141e8151b00150300000d907203040c03c07808400d00d078000c182c4040495069800300b180310140d00035a0b00b180d03000c6c00760110300c0304c0d8524100302c1002c003501b0807904140280c91491818001da43c404007110620100d12000d8100b0b4000c000002d90140944ac00d00c940030301b04141f40c100d = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 897512014 1250 897510764 897510797
    0xa08030a110c0f120c03010e0a060e01050114130603020312090a171515060f04060806030a03020c0f0a0509010906030c0605070308071d040f06090614030a02040c14030f0115 76
    0x8038201c00944c010315a240f01c2004074002044500c620f210094000c0018401c402400c40d15508030003420740d0317001d0821000400c144014480d40c0d049481a04a949130015040c04005414030b0b80301728107a50700d0f203e1001002690f424800d0210105031109515624488a42407000e002601c1e40b12442c1803c83c1c40501c82e600002085c41d028285000c107130103005a8a0350302a08a041c0190001d642040d8003045203000c21610750024403d4454644942250b56160020180c0ea00e05094005005030842152014203013400300154050507001841c034440c854898002c294000000d9100c0340989407100c4040040c01203264000d00501110302d0020b1402100b40c4002d48035000103010b0008204401c645a5034817441c440f2000c2460000a0080c40b00c03202c07034448000640031a0240500390b52801d080040c05c288040900b40401c100500501506400d540800004041c460030200601403117242045088204000851042036071058540e01035060101444403100e140c4413007414403140c03da145400d071 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 897513264 1250 897512014 897512029
    0xd12052136190c08190605070509030f07050114070804030b0604020f12010603050601090501140a020313090c0e0108040809040b040e0a0b0609060d150e0102090a08030a110c 76
    0x5224140e00100c1800c0401c4168010075555504003840c010a4030b00c40c5071a80581c401c103002c60082001584041c1c4a80803151103104110b000d0310110300944111000404d1500520342c414002d003045428000904003090608204c4503401107150421501800150f030482c05405202c0c0c0110540f80c10160f4540e9128040c0c0f080380400340c520610000000c501d9035480d0112400c911003c843c5c180c5800e0140442d0b10f40c7c4e10300f8081c140c082030504001540651007180402e00301c400594030502c80c08801103990b00580e0080900c2c4c400c60104018820601203000e501d100100301004c00082d8100d404070b0001d1000000143c40c5041110360010f02011a07802400d4031081242103034001010660700d0b001800a140901408081307010748140c2005001c140c0345200e22803482540c0000b29a0f451a040006403140311100030300d076820707019192a1908199001010380750800380014508500036000920401c20766002d071055510002c3c08000c1c0c80d60281811459410f500c0091024200b45070000c0d050 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 897514514 1250 897513264 897513301
    0x11060103030c02031f0f0c080c090105070501060506070c0806010504020306060a0305131e02031c080112140304180c03150b070c0e0f061008240d120521 67
    0x10400b40d200c0080c15540d041c4403a000f18520203031040310642540410310040c0c1104258408410b02c0e004152080c03500401c040d500c01e0044080245c82d00100f5401919103030806242035031a0340d41c801d004901c94549000520b02240242240000c0c82d281141c0c061500d00140c220780c0c0118014400e0012580380c2409884858000b0300300812580e43d002c02001c27481c00400f0010b885c1d022050000d00110760f095030344041960007607003902c0b0004038402400c00301204591207140003440000041000000f0b09102c6031403103110b10003035001841c0d42c4181600d1904a03803c0011100480712070760500d12100c1c460a000a05682414010f40d000342a45181c007001c07610444190240005a907020040c0b2541004040c3c0b450b06012116401c8c600040c000c401000c0b0342940c081e007008049880c0d1170380140006c61040300c0070342080400034100c0c000041c09424180c0295040692090724100084e40903d40d40e28403e65036035019103c44c107d070384a107072611003480c11380e50301d802c4041840350030032008411000 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 897515764 1250 897514514 897514517
    0x9080616031509020901090b04050a03080a0c080f1b0f10050a060504061503060501140307050d0e010e0a0b06040606140f16201c03110309220c1106010303 68
    0x15050039410260301428203449068401451114007040200156000c0c0042c0f03c03080e40c07889001500c4020105591040d03005241d0302048040017007000408a0b40100541441841c00c242d00b0145992003004a400403900c04c0d0000a01040b1440c241d6010851000507a0001c0b0003070428051900e141920303040c10880c01140c007a00d5800182c0f000c070702c80d00500001c003000382042140c0b60707480c0201c0c400107014a080324000713820040001510343c802e030081c1c02c032028014882c03891515442c03c2951b05a0001c0c104c001441e40343c81e10040c46050a03c580f04001c542a000f23040014024940101425001000644100c2c54001c052290769403054400440b1111540210781e41d002e5502c803158103000e0700c7c032400b01c8511f055500e8420483d1f0110055100621540c02c214010342c42400c10100141010380344255460355202c0b9000710b8411070400c000070000c08241e0f49841442400700e9402007525071032020851403c01100c490b507205110b008403c21041c641800103e00701c2c82c034107840d02010f210250 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 897517014 1250 897515764 897515791
    0x402090a1a0a03030c0c0806040201090603020903070b40120203030424031119080415060803040e160801062102280801030203280501090303090b07090806 68
    0x7250348a5401c04541d00d003070010800050569685402443c640400a00b161070104801001441c0200000c0d000d0007154161668089a030401d0720840c029044051070300c2d858807035044001030154510300100540034081340c2c8503503420500c6808450014070a01450070310301c1c1000387d252a20841d40341d43c500780e0316105504c0d0745203071803400024914013886d040307884c09107a0847c1114070310510411b900c3e0340410a03142401b4290644610f5001c030300881003814104c1d10882011043c50b07120b8038000307038010b105c4c00e04050080d044080507012603140b0340100505030f000240500107001c051306459400441c00c0501a5416008000141080018440c0d40c1c01d011000300ea811001c100c0011060310000241d00440d16401d003840380940a221028211100114a40140860318400d80b44141602c1c0c015000340345117692000001c010149201d03040d0666501c1141d0100007a90a0107a070036642d00070750700450f07040b080342801840d4490140005003401100c1c0ca00704210340c00440c1195100c1505100003 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 897518264 1250 897517014 897517031
    0x11701060815010c0503030f04030912030807030c111c120902030a060506060c0a1b06030507081b1c050a0506030f06010905100815010305060c0f090d111e0906090402090a 75
    0x143d0301c404c50510b0003070083c0400300400c60916047c5840a00c0faa01a9851006042c0d444001224600b8111001b5001480b524002001140603800c0718014030340134541b103452000049a02c0d414080b51140c90100f04040501c0c0758400c541c821504400180081010071501902e603000941c3ca000c000b034028450b640780c20000d49240e4806060700d80d41c49004040d0b9010b0000341c07a000c20624201c080004030b4420f000008114248a4441e103403103070840d51100d4040d500c40c00b5603006680c0c080c807022000d0045c10040c018100a072101c1011441606002c0031402d420300c0d045582c25100001c1c403150003a0b03c103501031101e080300010480d0440c0d0307002d18000f50540340d500c00411366100700d03001400b0921991130401903500c4840c1600307040741d0203038040e1005601d43c61032110051040760350b144078a000a020450241c03902c0f03800060200d1040b001107103c0c055410110320b0108542c000c4100d03d0703031340c4024511f040c1451568545c0c020741c100e038a903200e4903003540004c000703910160914031056500c41303e0 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 897519514 1250 897518264 897518267
    0x30906091410090b0f09031005090a1b0b0d14090f03040b0702011206080c0405150a0509060d0516061101050105060a0503040f0506012309010303050703050c100f0b01170106081501 79
    0x44000e411044e0311560743e4a40107031034840c0c0e41c1c4900500c80c020320509412040d07101261080718003440092015040070300c855110100c3e90110140744110005503e0400140110307041e00504048902e00b90115120301694071101440d00c009110b030251b9000214449640d150110480e429111030340c44140e00c0fa00b80f8001203a507104c40041466115241c00c0c00490440f200080c0380d028014202c5061019554002d5030007103c1450003507481e084000070005000328903040d230707880b60302580240408102074159114a440c006206103045091110103805111096111821020104050009000951402010400310b2048190083c100034012011030108550090650100b90b0440111052540c40d004441901580c42e084030504522000c000e007070905200c0c0080381242d0b01030310340b2130505025032000d44a59004030355840e51801014481d1b041980c842c4110a00e81100710000181c1c1041c4400240140c6000b0100302d0480d5640001041403d501203040c41d8132a505488082540a28400 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 897520764 1250 897519514 897519527
    0x3090b0a030f020f07020f01230901020c0904031106250c051903090f050315010302060f0d090302070e150f0f04020706140a06053f1009030906091410 66
    0x24551045000085030980c0c4410000548040c5000301c4661222103c1f0030015100480300c407418208401c8403040070306c8100174070300240114070b0040c01a1100b07950410000f03844840c9c111003c60208100c00d04422004504001a9034400c4c4002440d120703440c1a036400709071749480c0350b415008200600a6803010804280032000d402c1684001c2e1001d41e41340e5107005040300d011030290044e80c111240000440d4900051003d1064112000909040e400d40c2c0900605922860711014800c80800800d0f000b50414400c1a49031806075001d0055281041580c5840440c05000b00c150b44c0b2840b401c01c0220394134004241a444000ca603030722941841c2c000414041c1c00b03555000f800407442c201c08240f0f4140c035480a54420442c000040006684401c20005040c612100c4005c07000909102c5205449410701c4540c003070f10f000700301840c80070148900c913032600c82401d646198041d241d8408004043c1c000d140e1001814450030305940203030608031010100544401d002c0d100c0c00c500207441c1c400e42d01030403 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 897522014 1250 897520764 897520781
    0x6070f120504231003090b0109180c06030615030501051c140129010801031e110409060b0906100f0311040b040807213210150b0703090b0a03 62
    0x6143c28031516040c1c035600d002101c20100e18080c0c0c02a2a003c1c40c003074400e10500d0036043e4019003c0d642642000c1081008044507000c0b03054034450704400324040f94410030140003e000139034000c611141841e01e4074800707190003541d0a0506040070010310035903031041c904c0281c03104c4440400c40c1c204003506100944100009152500303510f0201d11109001c010207151103801080d4202180c0700030a03c00448120100b48030240890341c41c44143c9100281003512044224020403101e0000364450340090112545801c04440c1d25a8aa004075428249030440591184084130000035a01111002409458480355a0420155101d901c03500e0001e095041d80d0281031280500d9444985944529583c0c220b03500031041c60380c01c01c507032420072103032002c1d0460134003580082c116413620841620406000000c005c0d440c440800d00090900c02502080070030764003030410340b011891641c404039407060382e00300c0e42100c050400100003810109800503140300840343c0c2e0345038456842441280c214010030040 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 897523264 1250 897522014 897522029
    0x1a060112020c01060609051f080405010b041a090a1a010f0c050708060708161d03150f150108011211150c010921120216060207150b06070f120504 64
    0x225460342c0c4404150301803001c1d40e805465440c0c5c000d8942c800c1000c0340d01c42005070f90400c0300c42280040760903c01d0b206150001c1c410400850f4003a209000141518001c10f1091060300b40c0401c0c90096241400301950001e0941104204901c070605c042d0b01d504d442c034a000c3e4140080f540c40c03946000d104406130115107802c003090700d40250720b03007007115250131091310540001101d00000c20004030f0781d0995400d10a661342c84a091491101c41044040c4508801c026414010500030f1300d605466403400501c9100303a81c42c05000780c98000002001c5601200c591810060303d00014030a000341c800800600d16003003002c2a81440d1904005120107400a109010106010400402800e030541040000c98840c13100078000ca803129070714950b48880d4000c444000382140c000640720008030b03030080c450aa0004a01114030203541c55290907a0301c401030849a0701011704220311003901c18401c0210001c03048440c00d140500c5500d035a41e01a110303280c081c2c29001c44422405103240110200d4000b81140c = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 897524514 1250 897523264 897523267
    0x61c0501090602090f01020d170402040e010f090c14090105060c0102090d06091a280b041a040c0503010605030c03070519020604050d020601230301020417030310060c1a06011202 78
    0x60b281c490080d4020501090046940c0144285198004a4640c41c005032540d2810102007070003007030f10080b8102078070031b9030801d03170340c00341d4184000080c081c0311a0205203900c0402c03061001c0c500341150020652100c002c0c803044060542040d41d81940c118110354040701c0c4942c0f949021000c10b030080c410720307000603400300d00c804c400e100308000c0c0c0d0012041180203030425403000c4003a624078801d08204841c210b924040c1c0d030f1042c44242da03140056414980c00c0480000e01d184450020030119000016503c541401000300d1251034a058040c6070031520b02d03454800d0440d49020809802800064141c84d0406000710004011038418401e440d030310551800e0700350304905810030103174507441d040da816610f0340504600c00946500000e00d51341255501800d0b0650000703140001100f845040300042da01d950204800100d214283c038005103824003070009523907a404c1000b500791034800664000428031010030300100101d5041207620b660a01110000412a500d000040350150a042c0308810114030 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 897525764 1250 897524514 897524531
    0xc030d3f0903181d0f130605011e0b0a0c2a060503010305010f0b0102031605120d05190e101107150c0f020c09130f0b04050616050a08061c0501 63
    0x1489002100e58080003503115090f5529599440c0c04400346950032200f00c1c0c0c11801241d0024007660205501c070103012000c42c6a18a20780c0c509003602c50070392103c00d40b6194085114900b81c0344020040040c1041c0380918034008031040081d1003124041c601401e1280c1000342ca01d465a484010031400715500611000b00988815018103a40c1007070005079844cbd840e05070b1458029003181720340403080205800035401c00c0030013403207500020300d0020210f0799409008210b400e5603241c034020300704091a0110114103880c00841c80011410034040c1061210f00341300d80028003400c0402c1410080c000c0e884c000c104514621400b118521480344010801150005201d2000d003e941c088103521005950700c01480043c42c400302da81c1e100450300f50b58041081e90105044140c24002c0700c4a040c8918109154002251260b800302c0b01c085809039095040311003049540700300d0182000e9240742905025040500200000f400d9070780040a141c041c0f011a0f481d180c041800c00d2018800705c2d8050001d01c1641d8 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 897527014 1250 897525764 897525767
    0xf060f09030f040b0d0b0402180f032d0d1805010f030b0330040b120a180305191b12020c030f15060f091b070b01080c030d3f0903 57
    0x1740000c1e80c1e6138080e803400312039803824a080d00072940e941569881c83c1038805403003803c00031100496088294140303e1a070382000c0a0f00d070b400c1c0305070107111150000f80c00300907142011418401c651381c2030070402c1507032880000c404115280d844150781d028600210034068500b001d03402043c0700d000143e030602ca64003200c140418512201800c580d40d5814070170072021340c00c10400c01030140d40202600094244030003032010039254281e541c0407143ea030006c1a0603910b4840c1005450035440c4c00c1d0002000040d21042100803030b00000b510b54a2032800001402100c0c1403000b0a480d640d42c02410380300216900020f4501c00c00c0380d8804442c004060ba002d01c40002400383c1d075030099552842c0c5120540d00010300c03c1c80d00281c0c400040174043e240ca4400d545140784a11015205d044840d0505020701c140008039810380d0030240600300d00002480b0070442070003050319121182e4600001c001c1d500141d031809030040ea01c820341d04802e490103847d908400110309240d12003000c51600c400d038034040e035080515 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 897528264 1250 897527014 897527017
    0xc0216140a0803130501030e0c0d1406062205150a0603140c0313030503040807201305040c150e120303061c03080402010f0c120504170f060f09030f040b 67
    0x10300003203511200301559101c005849000301c010800001c68a0b5030104015402a0402040501e21600f52007a0072100300005800082028041d14801c9110300c3c840d00c9a0004c1005a4005600325811f245a201a40c000d0140306803803000703101c1007900d0304040381505104010b0000c041c00020301341c441042c1c81d01c400500030840c50150746810901c01021407c880504412a80100b0720301d2003500301c0c08007586040d2816070001d0011103c082c1c04110001c00f1a800034018101c03012a05030040c507426140e030400c00070031074a0300340c6008140b4202c01d2000062112900c04122015824a001003c030041c00956201d4988000140c001071808420340c686003000c002584220012500e12000d80c1d04014042070003681407030001d002c510380501107405036005401c8070071442c510b45424204040c1035580c000005101e6070919000c100041010303c004003507500e615103600c89010080200300494004599680000f0700070790301036161308001c902810000e004840c2081c5440c0c94441c2d032150b1b10300381907155 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 897529514 1250 897528264 897528299
    0x405150307060801030209181002030c0a030e01050f0a0e100f0504031e0c060b0409140105010603200315040b1801031b080c19050a0815090c0904060c0216 68
    0x280c0250706000c00c1460040010034144e94003c0c004014076910100b40c15820075140141c180345218008041350101514002580700d00c036820351040d280c292a54001c0c0c03d40d40908540c8240e641410100030307280714452801a03001c100c4a20100e010140f0010403402c4c00700070b15035140c3c224100007100419a0300c582100f07015a00c203a4030824000142c41803018032042c4090100001074400341c20f2000f2800075000b4507540032004000140201050340c0e118800b090300c8685e0b51599440c1d00040090340d82600c100d4001c4610f4122082d141d04070b00c489000c1c0c1d48401080043e4140380c40002c666241ca0b2580040d10954006d05a83c01100049c200d01c8003150303003488101c50180d00300b002c200c003001b842e09420781155102c60042c02480030920030001c0e00d958251150180104892000900303986201004005186100241804a040030b0140d803036004c0080000b00903a0010400403400d131105281d4076407103074002000140210a14908034141091107003160346001d1b10240c04a00300943c403041c16030 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 897530764 1250 897529514 897529519
    0x1e032403030801031b0b0a03020d060b0304140d05040503210f040e0411010e060306010e240409060b070c03020607060608010c0e090a0c141e2d131a09040515 69
    0x1038250820285d0b849010f4900a16500751002e001c015842406500903003419400c066010070034544400c4820020b81007110305689100b880844002c1c4980c05000303400c0c000d4010326260745007904000c046079aa84138132101d110b0f19407202c01500c220171144010b894007031000382036095440d039039850881070180040c0c030255124440e00312410410360068101c00e4544c40098005821940c80e0001911902d0702c243c4d2031600031401c00301503040f02d0030410300100340d1185980515151030404103984200c9120b50000300c042d1000b0030484002c1203000800c441126412034415a0301d04040c0750400c003400755a0302245d0190700707001030310480540000d031346001600259001c5855560300c4003c00152000410100d0100708c1802c0c06402c482441801800c140c814520380000c18283d001d000c028aa118405410f0007110320000301031404507180a1001440c0c0035044541441001001104400e90910410f2040b920f0503948014800308007095800c1c11000401c20003003481c004109110340721503180d2661 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 897532014 1250 897530764 897530783
    0x3060108011e05040302030c1005182103070c08070c060807030218060a2a1a090c060d0b130b04050a06140d030504030203070303020313061e03240303080103 69
    0x40d4403105204000c4048000c042e41d44126860401d2a070040c080a031081c0c003140020000d43d050400c0c2044186c9041d4090300c4005010700d0b0000d005058500c40c044502c07ea40c0040740003240c520316402d484d901c8041c20b41e40ca913a5035100d4270310581e48140c0e40340307004000c00d60201c0ca40c414480d0440300307441141c0154950070150340d18142c0440403480b40c50210300d01691800c0e07228110742810702c09041000b9050501d40e60000c0c01b995040440c1340c41a1804a244c8150b010308810040300d801c40c100701c464030440303110290070418811503c0e940c000031118024100864081602c0290b0780246410420207440012982c0c00b80c049400a028032254441c0500d00744004500d00016511401c004c907414512641404002202000028000b40100b507040180900c000300c0584c0d41402400025441381c0c00440c0c1d248960b01024845a1103035000d08280324002010301c3e50404165400c003001d8000f49000112007010030400350000a1441449040c001030380c10100130540c02140581c1078900900800 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 897533264 1250 897532014 897532019
    0x905040b0603101103040b18072c040f12031d0303100603050c0d05130b0f060307080c010e130213120605161d0a030606090e190221120304081209010e0618070801050108010b030601 79
    0xb0f004110300bc1d1002008084400c80c07100100300d0140c80c03121031100518000c03400003e09100400310581d05003030090315410001c2800245c1c401180e4107001031019040070300c1107203007440f4403078840d0251030290803626452390005050188050728481d801c80e03111030a1800c0341000358400c544241c1c119001c90103032042400c00f048104000807020140c0c03c0581d00c080120184034144150061002601408503800340701008038502124240000307003031803101206540341641030030800c0e160080c0408015100a00150702100d9000d01e1841c805002001c50200c0100d440011800c0e04481d40c0c4041c0090707140c01d4000c80c007c84070790050391150741d44c0011030b01c204101d20b010040d900d50495000398400c82c10a08075071509100b400091b2002c11040550740700e02201d411040342580100c808032080710740017480c00c04210304891940d40181c00ca200810000b1181410503070307136040251404021070070b2284104041d038001c01212024259003030081c803c81d40d48801c680e02804a40314420310a01850002 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 897534514 1250 897533264 897533339
    0x6160804241e18120f0210061518080d0305041e0501060510050f0a14040b0c030901110d080a0519110918090a030c0303060905040b0603101103040b1807 67
    0x2801542d0844d541c440005055a0280d8a6100705070040c000d40c040e84840030040c2e0294404e9100400540d6200c1c002d042140400802c41400150020381c001c0c0c140d00c2c01d016400002074100c03174014480c2400102501c0e18208015100c6c092880b03208103a40c3c5040304420058103402410881d80e042e50040c420541c041420389260107101b1825090786c10a0000c500000c2c0306400e200750001c00341881c0f902c0d064440c0c4002a07181d001c0c00d98401c2c150f000050303d03201564007030340110140902401801c50095810070080c111031000d807070071a0301c5071281c01051480c1111a150344040604041c00c1082450640380c4082030b0304086e40303091140030480c401c410341c0301001e40c0b01e43c8500d5800c1c01070b0134584060f44e000d0368240e107030b040c0a070304042d0b40d65408a0000d41c0e6205103400fa901030800d40c003071460242c0c00c06203000b0f0140a5501e04506002848528041c690141d0340c10584c0101d440e08580d0341e00084d039042007480d40004034284141c1d403001a600c006881255960803e0b50404400c00805000 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 897535764 1250 897534514 897534551
    0x43060f050106110c10050408101a0114160602090a0608010302040b1c24020a050705070f0b0423090c030f01060e2115010602010e06160804241e 63
    0x425141d000a40500005d2510314402c0700c2c00a0b090a00300e0503e40c8481090785404091090b80800e20f582d441c8450115000c48090480d0042c00d20344244890440d43d90300c0507501440200a021140c90f0700302904102080d016111120350151520282c00e0762400001c20204d001e1000380d016a00d00b409030000ba0424050041041a122810b1018100c50341e5604c00c502000303610802e4020451800e1a940480a000500195200d942c0d15078035015075003481814440c090380720740c4504003d00810001120004152011103000d48211524014031220b0fa80302c580207150815804164541002000c4613840003842c040c4000d045400c1c026031700d80c142500c41c0310000441036401000c20640310081e03150381440d0495441048265903410041c4d078580c3c0c02d14034080c0c000d90b001d07075100c03081051280d108115841d03001052103a200076490881d00d000d00008000380016022804603451040d190701580e05040401414030b0007007203d440d4143c18017030907410584041583c01e05104060041b0804403d = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 897537014 1250 897535764 897535787
    0x914060319060e03040e04121701120218040503071e030504050402030c091002030903151603090201231b011b2313080c0643060f050106 60
    0x3401080c0c030a441101001581c169000c080710403945070a804450000180080e00060420014552550802d468205030200900a1070820460000c039010081004003040c241151610b50361703400b00c410a400800c40280340c511001c2d00034881c0000384420071000000500a8600031f400f40d4904912207400300320300c06460200900050b400380710510852900d58010f41e04021007507a0700313103000031107408601c1e17890180352101c001d6000821070f8074250074140440081c00584a103507a94a180010901005071042d0301230404041d581c40140741164010403034070411031001c509600360a81c800d01d00082d07a07030014031441c203120494041040c180300140510380c1c504034400140c9110940c1c4074030448158a10b0384400120610f641107078401c00d5008001000961080c030ba04004503420308070103910301211120607a009a00400c415480071a82540c0e82940300c100303084000e44429074219101e03403c02d0707110b428040780080000700000c000f0590321800c08626005d038284400d82e0382c1c24007902d1407200da0 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 897538264 1250 897537014 897537019
    0xe011e0e04060209270712020a020a080307020f1902040b01050307020a0b09030418020c06090a020108041202070b040b07030f1b0f0c030b10140d020a0b0a09080313091406 75
    0xd010800181258015002410300500400100c9001030031540300c22500300600c1011050070010711002d286e1000620040d084480d04c103515008031204001d54403134170503001603d802d9011000c101083c0c401d0040070700c0b1501002c00c940c1c0c4103202404601d83d205051100303d00c81ca1824503207542d55400307078064900c2941c1c2c5401070040200b103602d4420032710b5401002c5a0083c0003c1001040840c0308944002d2042c01c60b660040e02c030050100c040340741120141c0a5542c561241c0074210044c0c3c1d1040d1100d41c8550300c00c580c1489500600f600b40c0c9025040d4114028a910118011178000300b41005403020a0003940c400c40324041a030b40c140d404038804852103c0b241e0315241c1303044c00305403e2441650300c00e115035540042c050380c0351940c0000003c260744450286000510800200d01c3c0803038161543c04045800b138803145010780c00940740040f24451610f00082c04a52002158003a9074207000418000055aa90380c540d01d070700e042050307a90301035401c1c02860841910206a20400c900c2c0c441c0401 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 897539514 1250 897538264 897538289
    0x1060e01050405060a150207051915120207020918010c030c050a0e01020c0d030305061008070c0b0a0b030a03031b0c080403170f040306090b130b06120f0102040e011e 73
    0xc0000340b0000e0140145a160400202c2a001440c00412101c0c503044c1c1a05902030030b841800c140070400c14003480165400c04200d2540c09000d52140501c0d540034010341d80c101030041c4004884268064050074401a600200141c100220301c100c1344d0110241c01c1c0040000c0209100c0c0110a90844043c106c1f4800050420710a40c400f690090580c00e600e032405004650984042000040812454000890009849105228007030038460021031260b9000e0800d0040c17440c001000134541c51800e10b014008114100c0070610090b4540d0100d0100c000140903510350007600d00340580984842c6912035400c00144028000c51489034160200a0303600a1200f441c00d8030755240d845011100c401c40c4010290700300540303800c01808070020030065103c6c0340c002c40c4030581402d003691000d000170b01d074510080240000c900024502424581c1c4642d007140c8000341c1802d034a41080c500300040c01700d03030316540c4001808100700a80302c1e400d90490380e00c821001c40c000f0b00f08500140c034061030703c20b41e44000300 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 897540764 1250 897539514 897539519
    0x41b030b0a11160206030603100f02040501091d131103010e010507020f12041806120c0503120708030609181621080d050912071109060603010b0405010c1b06090806070201060e01 78
    0x1045001940c21407c011b0072240c3c10341041d9912000c070348031044884082680041c0030892540c11a610900800701c000c8007403000c4103113000321304500c080200b0b050b100d01c046810040070000d1100083c0400e07007028008201c01151028058020941580c200000d4495208411003286001a601217105040025603003458540140c0040600c4039100e41c00c5c0140e00c2d0f10f00803840801d04004009000d0088007480b502610f44004e0600740122600e40100b162001c010282c041400f41d421240c00c24015202c08144e035403081000440c0980625001c445c500900b01c0c04001b12080c141010103403138645c800b811100324026148208003802d580014925901803160035422852580000da10500920a40d004c8410920a445450f80818022241340c02c4044040a42c0d061041700315038018000d680051441d410088420340302e000d41c0c490b890410145207040820020403103150840305040a1500300c9040d22650003801400030f030702941c80030388181070000e141c1c1032050080340300301c400100d2401442d90 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 897542014 1250 897540764 897540769
    0x100216171e03061305040503030709090c050418060506181906020c011d10080f0f0907170a02040e1e0c093108090102071205060a05041b030b0a111602 66
    0x108020250340c0d21001000e10002080414040c891081f40f060b80550b56030300c0d19140160407040140c00038401d907490700303507455113840d0880c0450b0190790500d0040808101c49002500251071b0a8010941180d00802c8401070b601d00e08500c01c0901c40211101800c5001e0038510070000c60f00792244000607480410025000d5004aa00900c0802c1c00d04c0c0482c41c07a1041004101c803031200c4010321000800b0305d0104410402a000641d810090400c140700c59414440849030703641030140540c10780c21281d44544082c52408102c244a02513002d001803081c0f12203148140e44601c640c284040036041001c00c600e02d03c1c0d1020841171000000204450655200c000245d50640a09540480c0202c1e03460441c11300c000400c5400700d1000e03ca0040160349410b1440024101011917001c20b004541d51442480040c1d000718015910030b01003040041c00d41d03158100800d00a07a10034503008050500c1c80080140f01e00f801545126008840303083c0144d488103030101e6801c1c03044078000c3e41c0300d140c080241401032 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 897543264 1250 897542014 897542017
    0x30c0806030c0d0c030c0b07030e091302090702070e0903120108060c0d0f0605061918050303030c09010921050c0108060f0f0102031c0518010c0f0c0203100216171e 72
    0x180644c0b0090301c0d071516a40c502004540680102d401d040c4042642c1007015800052000c145006541c800041d0425243c9881290140c4c0c0009206002e02c0c80002c81d25482049900000c04502405003200e04215209075120346c0f003040311400c20100000041a100300028030503001740a0415924500044c01c0b49400051a13500407440e191600ca080008071903580300c0160900f0104401002a1002c1095018200d0300d5421500d0402c0c0d6080c4104209a65000c010b90b03620001400704290350740910001290030200a41081010030000789901500c00700070752198503500e2051044950028500300159000c0404445aa41c0b007003038900c1c124640d0411860003034001906004890030071041c40703555144074a46074202c0107004d661350104500303401074001c81082588864020010551000001070810807c42d444405200380e000b0368100b10744040190440141c8110fa0854589044120404072040d001030242c5030340c0381c034210041d40c0d04003802c225442e10030794003401c401c034407034083c0114580d = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 897544514 1250 897543264 897543289
    0x10f060b031920070c0306090602180103111602030a0f12090801180f020d140307170c03120c19030b01030e010b01080604090c03081b1b0306040321061401030c0806030c 74
    0x50705c01c0b000001c00160340e4058104000e21461f00940c0340d4904101c0001c81105180140d0304043c24640c071600132080e070408803003000998048820350500d1500211f032030000c036031307200070240c0c03140040010a011400c54450050740c1603954003110b055440004600361144211449182c1440c2981303040042c81d01c08607104ac0510103012406044600d0300c82e10400c1c0140c54090000381c0000a8450030400c00e42080390040d0855a0130b0743c1054031101c0302d00e5890269500c0c2e24200c981150200344041c55600541d014003130b075038102d0a02000700c84001405004444100c41c042401c10508a001c0720060203105102c00041c6c0d03480f89281da40c0000c22019000691090326031410150340440400c0d0f4280003881315030480708910b41344e8504055180d141c01525451036080c016200380c4440c00e0790300803942541003078061500ea102100801520254000c152081c0000b040c50302c0c0c400160a584003829048441d800d0720204072840002b8410380d0b00c0c520031640c16034150062080320004c2d01d4100c94180c007 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 897545764 1250 897544514 897544523
    0x218011d0a0e0d02011d0303040b010506091323090a0f121b0b060108060a0b040501050f160303061a1c0213050a08150a23060102010f060b03192007 65
    0xd402c040c940c103060401c4039140c4a900140d44901e080d124400000e00a02503402c1d411004518610382038075480c2d429503040c0031307041c410303c070001d03151407240d6420340080200280e8103010801c4800c00529200501d0551021403020410708000412442d0003081c1501132a80000ca03040010b8140c0c1d45100c1c0500681007500f090045501102801c10700ea108004280c1e44214a00601c3c0d060420015280d0072000b00101d10600d10034400b8003801ca040d00603142101e00030f080c02610f171030500c1d41c48005030050081e2101001219580442410f90541100702107940040e501e40a040c01402810030034403c401125032400082c05030b14002a40303560081084240b00c45000720b8450b16400003404a0145510038920b9a202201085142c000240c000d504203460b918200708180088052a0f040d6420300156444a404000090240e900079040518000b0102104000a54903038000098540069400c0030007800425035480900a0f039200c0ca04480801c04104207090900100710005d9038002c000884 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 897547014 1250 897545764 897545771
    0x90402030f24060301022a0102070213092f120c030a0528020a03030302030a0e010204090207140304060816031118040f0915090218040f0218011d0a 65
    0x40c0a0300388410401000300d0342c080c005003001d020b40003030311a1001c1c0c80e55109034810003416000300c1c1410044014100e44403405400d40c1c0c640c1c842280207018280d4065008140101c0252640c400c2d0b911014030f0074410b00c2d15043c41202010120145080c2c00543c62811912088000040c905140003101941203d41103644007194000032170305003a00705074100c1c0d2540c80000b440444900c0c0300000c0c100d5850903141681c442d105600081ca540000748000f41c00e01d83e0000218450994942141c8000400180203550300d5980c1e82c000002980a000181c0e405c42a5004c00150044040110ba0440b9225a42c06007152628000445400d14202081d41410755070300d1210707404040c800240407841040d0088880090b4481c00f0b100c10707107544952001540780f500310203000090b03983e40f00c1c40d40101d40f1000012956442e101042c40507108004040303a0b17403070740c0c01004104011100060f81c1c05209031510300c0301c103c5480042c0c9072114203000e00b130404403e0b06090211b00d1541c0071070550112602c807010 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 897548264 1250 897547014 897547033
    0x612030403050f0601230907030216021216051f0807020a0506010f060f02010504050d12060b030c07230307020d060212070c03020f0718022218050a110909040203 71
    0x3840c2031000011034038aa005800108280552102e4981200c082e1032000201c0801c0100051070a01006001c0404e15901044410314020070481c0bd01c0425409040304500c15a1101041d581d84842e020501e44117070802004182401e0071600610300b071880e1040d01c0101860150184d900010041910003140700e0311040e500420010000240204407181c1c5008040b81004402003616605820901c203680c146428080010000030f40d000c0200054036002e1400c07a203140280c00036000a80c00285512002b1081c080d0450142e0000c0448520030110201c1901c8401c0160308044507800c800801c50700180824009801c08200f0000780c9440390200504c1e10500e00400b07034050400307441b17000c0040c101045120806404110001155007100e005244583c9003214000c0100400d4020442d440c1e000b0500c60b40d980127640f055103400081d2548000c141361952410203a030320a4a0000401c6801d202c085071801750740e48a0b044040c0414030800d441c0100396000d03c00b4034200640202d800d8851aa4070 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 897549514 1250 897548264 897548273
    0x90506041103010311040c0c03050a0f0513090e07050a06090303050a032007021203160201051b070e09010606080c04050622080a02041a0609131517240612030403 71
    0x158042c5208005d11074071800745006000480d030300745030b0311002d0103005441040841c0d08801076a911004d24a0406060084000102c509025001b021160035494400c0030a0700c0150390046a4005812421110240d81c0e0707400308094108039100f0031000c200d0705401480404d100714024510030701d290401051407400c0c400c1640d111141103e40c1041e40e44041207150440c0383c0f401e9840500d84c1454025402c15034801c003036817500c40b6280750082c1801000107000030702ea0040b4400254004c00c0c90155180990741c0e9000c400d0440341211616165481c014001c940540660300c61401804803020780741c1403900f04028010240d0250360160310078641800c400140d0baa5800d9010040d18001340039055500080c070501c0207980c1c02c50104500d5039406800e08256481d0441a1155074a0490b08000c00035480300e6518010207108040703031840324401d032020542210440700542c0c103902907403c40300001e0f00805000c105180c1e1140c07400340c8000c0320020502e81e103001c0384040080b02008003920301e455034a544 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 897550764 1250 897549514 897549517
    0x906190513030f050607030e0d051828060f0801060f03020702040e030a090902040806070e0111010c0f270501050a14070f060507090b252405010503010b0102070905060411 75
    0x10884036481c030341880c201000014403c0c1c5c1d0b000b8240d03080a0180100c60b4458a03116007040030400c0070054003041c034034844941500d880b41100c030302421f84a0051031a0345402e200003c1c00c51003061100044900240f0f480c45441b0a2034101c0c3e0039a150788099003010703411100f4800440c1c1c10380415030203020340b0015a8591103480402120380e8025039039020f840700c01410000c050351054941c180706000c10018040c0104500394018028a441e10580101000603100780b8011442010700350301c0c20041d40d0300c0381d4001c8120f003240e0308a40c45102c40c1032140448803000c0c5151541d960030700c9112410800455010700050010040c0d5814114685c0e4840d6400080c6a040b180d82a54585060403075a01031011520030341d90030123182e00e00a0b0f20a4149020380c0e07102d200b1014800841d5040c82c010f003043c00c8108841184203035101c03802d00b400c00d45c50f202c91440b0207200072071017001d81e20f040000103140c81d052043c040030f00d106801401106160480c080b006000c01440a80c00a8450300801c401e800b101e070 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 897552014 1250 897550764 897550769
    0x11406091002101505031f1401060509090604052203090b0d1a0f0a06050309011b030c0f020c0d030c05010b040507020d12020301060503040206030a0902031e01110906190513 76
    0x50040001111070f500300300aa821611145500c00040074090044d03840100e05181c44054400d030303e030104013040100360010700c00a0900c2004080321000410503680c040010050300d042250759036100c0d103803141000205c5109594040e001000c22103203401c4001c80d8912041d1050107414403000140d035801e522072342c541c441d0550b111030b41d950708410030f4100281503d1030b0385074900b503c2e07500d003100103034020815000d100d0207400c003030210120000b912603009400c039401c0031100801302540c0c10b074180000b801910b0300c04400300120309900308a6002c980300007240c00c5c00c0071001b402c02108618039201510075500b000c82c15030b000d540342c49094205454a00546020300d50703a60040604860080c00104031218030b00c0300161250040004000690344003041d6500643c04071841560b80c1caa41c0206402043d005070001e416000c0c1401c03940b0072403120f0a0900e9280c120303400900c05105000d4440c600da104004c0007946c4100240100740c484012401540fa850807a03052131031820305040801e15a4042e180d = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 897553264 1250 897552014 897552017
    0x6010e031c08090a120c151103070e0907020304090c030e0a0305070b090f0604120e0306010b0904060b12070e030708190c050103180311160801020301170a0305030114060910 76
    0x503651501e249500c514482d90145000024010740c0708141d9a9807000d071041070b0321310104102c0d0003104051006122500010180c2e102040280502d145001c00380c54004482040c04910700e1140d49000e070504004c1c0c1c40c4110040e0b03018504d06030a0844143c020400d0700c4242d82010365403c62800400b0041000c03614541c020b8681544415280c5445000c0f51002406c481140d0404024846030100021380c09800030346c0101c0c100340e0f500304032100f140c60003140c1d00755543c90b1148000024003180c2880c01040d1199040c1c50901006480320800241e074450780c01285c006509040c00104010300c2140314028a000060590740480e58441d11076290201c1080f404000300c9d946c20301d0904105181414500600702824280160006907001003510f2954020150900c00b06400345d0002060620003d100900c5058480c0ca4054803846110300030b4109001d0b2003000d800c0b5a58608514400090358070003280c0c1559414a9607003403181c042e03055203450000c5600a0010310644e130556540c101e4414006c9002d = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 897554514 1250 897553264 897553303
    0x901211407140109030b0c0313050d09050102011b02030714011808031e04050c150c031b06010609270b0619180503070e09031608130e010f0e06010e03 66
    0x10a0000002c01092500c5141808410202000001c00b907101c025404000160000d89030b40e9482e58502980b665620014540c1c001c07981d0701a44075030803415900590b00300f82c2c004c208030418050401481040c58a544015a02c00c1c484640041c4403c603d2452010000700007003116169000300f00c0c0750b011125000c8501c114040108000407640e0801c80d00c1c02240424142014242915503039118202407200303a005807800440e01c01c0c140c4190040319103038407899045035a0340c0d803100e4000d4500078034011040c259009030b600010741240703d4039a0b101a41c9507040c0c0400318569800f802107441006048138588251190302000660f55658094201c0480c003130148602c0201440c2d0040c4900b264034402c00404d50030070414041903c4c0010f050040c6d500408400c5099107a45906c9440d5005031602120ba203030b211244070003040b5500c4054101060a69030807035182d52900700c003c015441c240251603030f240b06003504000007a0022243c0e45c00070b4041c1010540350900380d0119003041500c000d1410091030 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 897555764 1250 897554514 897554519
    0x1c090303030b0307050907030203090a02091326040b0a02100501140f040504120e0a0e0916152118061b02010b0303090f0a0e012303010b0901211407 65
    0x4240c0a0b482d0880c10031030150034105c0c1040c00045014001620810400da4040001480308008018070842c1580061060465113021281c800e245020254100c2c0c1502c2960501c0740300140c6410041c0600300c0300800c090505041404119254011200c1c4604520500c100101d48104a21a1130702a100004010b00b1341c41140b81030080c00744001c0c2001d4060b40c50801003101154040c04000e4600d511803a000700c6407203107540000c104800e5504964404005403050058500c1c1c0001c42e444010783d03c82140a005680d4031800070160b00a141d0407021032003130701601c03490700c80180c1d109102d02002c20000130803407041c1c0c80203102c4201c80030040301e032a5900e40c0e00140c1000c6951815031803412510090000340f50480210b510781c010400010701498107484041555540c103100350b40a400820140040c0e581d5480114099140703c4d4032043c0c0c440c120760800265400c060160224410001d17090411a901e004589029084044d41941112800e01e80c500001110081d8580c0c4100003800141207450 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 897557014 1250 897555764 897555767
    0x2030f13051f0f06140307030803100f0e06010906020a0b01060503040606360b0a0b070302030c060c09041104121121060103150203100e0c07150c02060106050307021b031c090303 78
    0x214580c05c10031007220642004c001c1c81da00000e202040e658042c0c00c2e1501c070b072902950191282c9142c0c00400184c0c20440c004a003650404030300604c03a5409a0390003511aa40320310990301d80038021409010f50b101c020040c02624000c40046411500c6160000b0320b841d07903103040c0c0e0710031044e900040c0c0600404c0c440c001400100440c0807000b880008408022160004d40000c141120300d20441d0f09002d400304142e001d00d4001d0082d554240420025940c840c5405801d844607580031003283c1e880f0703034502144003010b05060001e07903094a41c0320744e10303030040e80440c1c43e16141d401c4410b00c80c1e940312a00c69081348002c0e1b18500d164503030501c002c00400c0f095040d450040f903d8008000381c0c2000d10310510410a6420b41500100b01b11800f04800c03500d5a01c0b03403008003c05114581c80544041046440119003410a5110841e2008280d0a864650b41ca400040381c80e44015130b0428010b80c400440454681440c440404202000404071407a030704600c170519211010602c040741c013040f02c0c0d250810505 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 897558264 1250 897557014 897557021
    0x1503030c110f10200c062502030105040f06060f180e0708070f080c04020f1213020d0b01050112090507060318021908160b03070f0507020315010501110102030f13051f0f 74
    0x40d0b03410080c0c4400680e4030b02280e40c60103038102d03040c4280000740c850f00c2d042051203449950248c000c0c0003881f452030a404d0070740f80c0e1107000400300d6005103401000903000b2082d51042d02a00d05081c440d020045201392880b010748242000c00249028800340050441e60421602c4010901c1607100d4200c07a1402c2282070404083c40c0c500350159004102201c03644508104072404d05454030020f103256203c1000080101c0450000250050b04401c42c9500b80491050107904035a800d03680e140209020503a20801d07100101c5004003d50310040c0c090103e82c1c0280c101c240b6100a010407540d441d0032940000340118002c2854000c94444890240007590003400015032003000d0391208415641341c052518801d04c402000d00c4108000e018000300d09521440072541c03103d400800b10307141c541c1540035051406000b031103090701003407020004460100040c001d480c4115030317281a0104c0c0741d440f0195242d040040135405c4405000b900c2001c01801031607500e40000c06803110001550306403400310300c000c5 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 897559514 1250 897558264 897558317
    0x1b0607020f1b2205010801090b090d17190219020c0303040b04030b070507120e0a0909050307080a1b1103120c060a0c0e03070602010f1503030c110f10 66
    0x190004500400c9026280000901ca0b03441035402c2c40c3c00000c108501c1c6290b00c1000180e81c0b0043c203101c000a01c017003054100d50106405214450200d44600310081d640e209a03054480104d107080491000410055403074a41c8107098100c280340e9070146041410803603020001c10180d130f0704103401d007121143e41003200e03207140d00042e002586094107006188009000d540310040100c007845000840e0b0f58480e2080c1d403209a4807002109070200b840d04041c04c045102082d550040c4400240080d03c40d03024012019410f40042c003451414250351103008182e4040d040e80ca003405403800ea4a402407192045204695016803190300004040000b0141040c0c2d01c0040740c0002c41081c454a1107451011800e2600a100b00e5000a6200c180c4074090710301d241c02c544030340d0b4907025141c1d0010b03206406401404c20f00b00032640400c640040c02c1c0c2d230903060740300d5400050000361b51075040800040c588a00a0082c0000810341154a2030220010380481c2e258050000060140d940501d4141011f81a0b01c41 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 897560764 1250 897559514 897559543
    0x10080309090a020705010b0616030f052109010b120d0e10080105010305100e010b0a0e150403020621130203011a10120e030d0c1707080a0906021b060702 67
    0x14240340c00d03000580c0510050280b000301d9900142000c104402540201c18030107018080c1038544c0002c19458041c402c99480c103902143c8152100c0f00d441d031269046075a2007600b420f0071042c01010080c00310f040070b8010300521041d0b580384000d041c15501c010b01003d4010104006055404114000500c2c2000b01c4c200c0d10701074080011045500c1d40c0120a02c1d054030310a18000540e640d9100900d004118540c1c000085100c060002182d40da880b2001450a141700c2c1d120400c803d14600c050244a0651142150140c0d5052000f40700618140d0b00503d160b0b41e03800310185016000c880070f8103281405442c40c2c0008101c10f001e00c411400d0a000d0900e04003422080700354004080408a80080038085256080001d0112140650301d048e60000d030503080000c040780d4071208410b51900081101d400c418022803440024400f0100c144d0000500c00c0516540380c1d01c8503100e07c041c01c4040d02d102401218410780a0001c40048028403462400384182c000040c80182403810004c0c1c04c1002c03c940080 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 897562014 1250 897560764 897560767
    0x901180303050403021c060e032109030f0a050408010f06090f0504150e0313031202060624072409030305090c0105090607050322060f1715010e0414100803 68
    0x109402c030080d1411690140c5849031902013480c2d00c020170b6091050001c000d10702d002c08460b203001001002d00030b04000440680d0241159100c0070925140840d8001001d0b0f00800c5115032407d502d4015200d4140181003150a040e00c8110441c00e640741c41c250509020741e6000100680105406840720031200c607841008a41415100c00d0040035650f640140c8003a2103030890b01011804204440c4402040540c80c5490358503480d104031041c0039018900010311601010400740e00c0c01401ca021140501114200b4149000e1070b041e05541040d0070595211401981e0041c40e0301107030700d29200a84010b080050560070901d4044d08a0351701030083d4102d035101103031024880c0d030003408560040804a640c1030711500146012441c6201b8030106100300302c507402040c0d08e4062030103030705001d841a81d214003595000c1c201c1c00302c4000c40500c405509080309030340407400080c03c020b440d60440c1c0e81854101142740900000c142542c8009ca82400d001c03000c541000002c4000580303100143c0079035400356 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 897563264 1250 897562014 897562019
    0x51e040809010f050f0706060812120714090409081b03040b0406080a06030f1a0a0b09061009030501020c0a0c05030a080301030201110a0b01060302190e06040909050f12090118 77
    0x126039402080c0c2001d040c424a41c0c1c000540300e008030240c1d80380d280c0c0001e01035903803081d910700240549000d10178000749100b010482404595440e0035070b1000e81704a091807030b841c0d0f140c1000314bc17040090b031155020725a0805c00041c0300e4403517010700460103003d000460f903243d190402c0703140c13201030342c082e4200303103810900051022207901401c490841c2c07000e1410360060780303c0d5444c0c1e0008090547c0000c043e80e040b00381345410010040650f58103865a00014000c958074405c060090321951001035600600e224001035091512070f0580d01c00d1640c510740780c81c0c100d4a0365683c90890f800410248c905ea8800b10303d400800151005d160051701c0294003410b1004c1003a69800400c0c00b06000080c1405003000c0d145005907006c205250910360040402c01c11540d491502400035440500c1d1b03008040c0000c40d08030542400b4140300c00e0b08405c003030441403425140c00c50500c001c0031b10b06400c032194091428032801c0d407401007100f010b191144104865842e00c40e50000b40101440c400020781c40304004808 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 897564514 1250 897563264 897563273
    0x31026030d0b060c15040510060b0904091a010603151e060507380a0203060306060f01030b09010e06041b140d0e0a06050a0b1c080a020a0510051e04 65
    0x5032031400300d01c42000705040420600160890160344801c1585100b4004641c44804181d0222805140904242c41504101045000a480c0c0740d00807903c50190400170740c070b89070400b41c2c0b0650699000d11a0a080070303000c45034104a2100a901480c00281c0321700800c142108205038140c014010469121040c03040c207a00010560502d20450701400b2000c120b6070240102c960100c20403240b1034131080c0000f00c419681c68800512004c039010044890b200003000103035075100300d82c02030030001c00400e140e503115003c01010070302c5101001d0405448201c5c084450f01c41160341c0d80a0411030303600000030b29124050008648124020000911190300c94051030398106c500c13011005122080307640d44101c032190369800340104c562424150b2048640103010f001c40e80e4071050080310700f56002e0055046c85e204116503a10850941c0c143c0816601c4200001481b40700100401449401501d01d0360030340e51503260a00a0008952903c0c070f4842040040381e20910072105a040c10031441d005141c10310742c98 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 897565764 1250 897564514 897564517
    0xd240503072711130b0406090b0403021c03180b1e04050a0e04081b0a0203070f050a1e05040921020d05070b100902030a0609061a031b040302040203102603 68
    0x810152543d5444468400c007031a008542c1c1a400460703a818519542e07100b5103a855105114020000740c1f200c0d00403e0324800322086030201da400401d8600b402d0346080b2013800b5605000f034100e040c8984120020118480810044010080c404103144c4401940d03182a5a03001c604960741d00452003004180301a80c0d9005503c030075503145e00040144c0341c1e02c602d00f6114a00c00c0f6012081fa0114450105151113030003c1c42070050361003075040d1415a60346001220110300a03000d242c0d0711002c0c40e84207120400040744420b030a401c140b00c081901d141ea07030012900b1144010001d84503124007416010742e540c1c04070141d10b1403400700d01c002c0810030303003d040023030042c051200006d2001c20144042641ca51100d07998101501b09994115078905000200100520841c03065001c841d08001001036409a8161084003105560b4019440c45d42c031481041d8800e420043c038500903480c00d10010016031178070300c0a0343c0b01d0807200c02840c6446041c9a4091210b035440307244000142c12810381400341e0b080200 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 897567014 1250 897565764 897565829
    0x30801171203090102130906031401090809011202070606120308130f110612010f1a03010503030306060c070e10181a13060b030f07080601140f0d24050307 68
    0x301c08a8598442900311400382c13094044030b2076500003074a00410030306525400740301102e21a5844000302ca00c4800040c0c241c17925010b02500d00301040c00702c032911354040c044032031800a85000051620689a840d20201c4025410040701c20181c03041c203c04040d00420348507008010102007002428450761035010000310000010903811691150200d1a11080d00b911a2070b0f04c1002500695a103414908002e49028401d50300822072815400100c542c28400b124144e51002d0301039440d40d40c5440600216620200b00c202851080f001c0025444840f00c0c01c0c58000c0319106500e402152406800c4140351203030062124449243c2100078081103000645446145015140101000401d409180c001d10440e80564061103001041280540d210714002d80710380b02c9500ca0080d1074503500e0044076011091032a42d215014104a600e00344059007001c0c28000c42c0740b40c8081512051034400100c000101d03641d20014004400b024001c0303240c148141c10140010188404000400a00c04c0c0d50410a01 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 897568264 1250 897567014 897567043
    0x311010309020d1a070e01050c1b15160201020c0f1c0203010f060b0d051f031b050d06143706030b131a070f0e04061e0303080117 57
    0x781d0503031085440310705603a040250801e066044948440c01c90380107184040350341e4000a1242c400e05003080d8003400c1980d5100440c2402031240403074440340310711044140d80e0103030f03408940d0843d00740f600590900180302d0003d03c201e09840780e03c0c1c1351001a00c0c000d40c284105d4440d84003030803030440c2601c424004004030150b0f44a2912040da4034000300780107109040c0700c001828102140441c2c1c200c0800c00400510f42c02180800899032021545000170140c044090707000b10003d05c082000c503d9030031030366480b010402a0091220b0b51280011041000c0210032100c441c0c60700e048540d4141c50604d0280c2c810b219404203c1030a285030003034a0444498030000e05210f01500300c1099020f11580700d803001d03560003840d64009052031036694058808943e41194642d428500780380c2e8214051900c4c17401008951154510444082000c1d143c501c09601c00f2900030f6607525000680b0080100200e101e0044a42c04642040c25410000d29012058000242c4185403007141c88015400140400d50700d07049 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 897569514 1250 897568264 897568271
    0x509010933141f031e0c0e060a0b0a0e030105040c050103230610140417060a020f07080d0924060609030c060f0c2108070c0b06011d0301051f080703110103 68
    0x12800203d0b115540c0d08080d01144901c2d2144400300c3e548200341c07070414040c2070075003001030780e400402d0700301a03003140d1540e0003101c040c808114104589002c0c1051002e01c0c2403100c0300b10581070110b800c6800c22074040d80c2c41c1440344010855941c041c89140c0c0c4040c0c541035244880000f40f60f403800b0710b41002d041d45010f65514280021038510030107200c904890503690f07407556155602d402607603110403902ca091040c0144c5012401c00582c0e4400c07144171104400441d07091114a0700e03109600d40061403074000098680210000246001c2c0c0c0d211000c4c9580d602c03818442100031103450481d01940c020005011ba2448280017040e0386c3e4007610704a80d103e14022441300e1034100112500c03000311100414204004c859625242c0710b550361002a0420b594a600040d501c1c0c0d28216801481800c024000d0000308003c107865520802c03260200c02448100d40f440c880b00440480c1c21548111091080c14030540070603001c88601e2442c0e007004242c0e5400610246095032a03c2842498840d40759051555 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 897570764 1250 897569514 897569551
    0x120a08090a32120a0602070f08030a0c0305011a0409050c0c0f03040305161d22060f0c050a05030106081b0712121e050901093314 57
    0x1610590607014050030b90500110145400c0031400801070540003800c020a1100494003a04210000207501e50340c15000303100c00c50254071800c0003503100400680b144904141c0070340c0402e095800950003610f40d014002411701d816003000701120f030103030041c00c46c3c0700c1d4401041000111510950b019100d442c400001e4030345a608508001c0c1c400c100b804030040c010201ca10b03c0c90341001c8050003c82e0700070030688e01400780010400071041190300600304048a40c02200100c001103a56007079002d414080c1043e03081c02c06003101c6540412002e41181d100e510341302681d091395128000c140115040e03081c03050521404080107480c0340814041c0204000d41e90000407149511511100160b00324603040c555117610700e05209900c3c0c04a00300c040041030180c850703490203804500c1400150740000300d480701d504c681402c010000d07210107440c1040c990340f1088400045203410a20340407d04041650102d4a03900d0300c248903910a101511400d118500a1301107041c03d0102c29aa602441e0b542000c0003405 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 897572014 1250 897570764 897570769
    0x1020a031407170d0e06060a3c0f050409030512130f080a1701080304350a020a06020607021005090a1a0601020c030f0c0f0a0b0f090f120a0809 63
    0xa04640944807401d030702039807800740000000900d42e05241c1381090040d43d8084445654a5030181c8005400101510702004041304d6541d07020003815a1948154440b0034294a050445181031035011030700d20340f100d08002c080141e003070420041c03400340c4051011054949000d4141e0080707603500c1c0c908004034000030305417003101d07400c108104d0341c844800a048859828001001d401007141c640205d02c0c4080b0004103040054002812210060011443c05040c05000981e03c034a0700040d106042804003003401030203046041040200c0403000078032031a000c3e40100400c1c203540f030340101c0a540148082c040c10550103e01e1140c4c1500c4020b01140503250400c078180f0f8541c4c500400740c254590400440c25100071034120034040d5909034211001360351010201911a0703001c80c0811101d40c0704445815003410312020704100d1810041c001000e41d590355481c001c49074401c030032401c1e107900e0009608405160610a400100106135030320a25110464641c503a03a148100024000380b002281022480d03 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 897573264 1250 897572014 897572017
    0x7120303020c10020c030702090a150b0f0903030715061a0315060708030709060834180b030f0106090311040504060e070806090705031f0f020d090b070909020901020a0314 75
    0x200c0340d210f0110340c0e80340300000701ea4030390304a0701e001ca11402d11400405c81946ca10b0060100c41844000090b100511300a4000345039030040402c28180d0750b0501c02110340c3c0d03a0034005080102d0240010800d0694440403c0044072a01d401242c0c14000d07414142124501c00c8041e81d502048061300d1a50140324100018100c4c017403036400078001e2000200700301c6001e034402c00c05030171140c260721400816200e008801410100311040400c1280080701500c01504503218003418817581c2d801c10200c2850100c5222000c025039410403410180d0020030b0050000c070b0005614010040c901e008000641117683d220b80c101c0d5914069485030340c0303850101d800e00a05034400e5096040303030700031100300c29a209891501d905003120000107074020400001a10300300071900e8a5130081c900c00c08914800f414884a0003862034100302850340c0d9091000503403641c0d10348510a0160b01401441801e880c15100040c0080140c1e000002100d00500c04c01c081660001044078885602d8104a864010408814501d0303 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 897574514 1250 897573264 897573283
    0xf09010e04020a05130501050406021b15070813050f0114090103140a0c090905130b0405192d08190c170c0f2a1807050a0f0207120303020c 61
    0x2a20003e043c00d94a0f0700301000b004000680080704100683d1080152041e01442c070035027004d600300e442424000200c507180c10207a00001803250454402c0b101d00042039400176601194500000289031005c160304140f8440200350458040d52200c9618000809007519104000e8072054042030315032442e806500f000d40024071605c0100c025180404005024085550511010800312500861480f00134000c0d07030f00c550500030903408070481541d65441c566400600070f13240741c050201040c401031807690821080038045e038100601020325038140019503c42e6400200811420203140380052080d40c06c0c0d0700c50010f8410a0038002c464003605442c114800c40d030042c2400003a0700756141400c2d0758809002c07203050b081c0440e040340c24036039000c45e030783c50314254070f01c0000101400103100113000c0c41e0042d00d0b4001c090302503445010043d01f001400030007911040d0200d83c000c2510441d5940c01a81900d03c03412910092900c01d24080c0791003600501ba0300041e040640014400d9403441080204051 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 897575764 1250 897574514 897574519
    0x18060504090e1005040309050f010215040f0c0e0c09040c0c051e031b0f06010e0915061f0305060f03011a06210702010915050c0a030506041b020a02040c02030f0f09010e 74
    0x280717040e10307008000c440c06006162040f0491030b00b40045520026140b40d90764104044a00140c41707903103440000036802c10302111100051000444d8030310326100072a0003510403011944d141d216502c00c00094038520800d003000c001d400c0c0d001d10003203800040e8801000003c94900c1005c06d003021211f504611803c54908505e0b8070080440003107040015031807842006042c05e070351a5903220031403202d070640156500981903110001021041500702035054000700020420506851030004d00c4051401406c000400710340c0c1c4004101450030080240303102c90604400170442500e00d100c4150a2500b03866080f4040ca8004c1495544100440420484007100860401d200d10b8455002800b0700342229045841d003600308a42200700c03070b80e07025007800341500580315402d207502280c04400801004120030340c081e86807441060741ca0000d8440c1e441c91074281d070251200000d0340c01403005135030941418008651007042124070741e280b0081901c18024401350500e82e100e40340001240c1095410355843d6 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 897577014 1250 897575764 897575771
    0xc030d0222092a0e1e0a030c080d180902030606040f0e04020306090d1d0303040504020c07140d1707020d020a08010b09090a1e0312050a020307020f06060f061606050106030c18060504090e10 83
    0x14400c1c0f0402043c116030902c8101d4079102b1031814100c5540c10180c507403e00705178100d0001d01c030082c101e4001e50390004010340800d003010342d544542424860250301c01190340108005102c1941410700403960312141c1c0900078210312010a00007001d40f112a2844100c04841008607902e641d02070044030000d045c0200203649500150140366201c0c1103d00ca03086165070166200340c01d03410542955826030f504081031043c0d010b40d940080c181603100e07040c2260300451030382c0c00c107005a0f202c1100b00003030030180c400000e18551000c00c0c0980ca10380a481e40341c00f90700c10480800011102a064169030007510510840c1c0400352030183c2d1426111283c40008a092000700000c8914590195201c2e50050303084601c40d03103400c1d80c0d090700c40d6030568a540e000311842d4003050060404000a100d4143d12140400c0b24440b503440300d804513030082c0c100c400001d44a001c0c1180040d440080d04420020001040035503900e0560080c01d40d110324801c0e9103160f07850703d9116140d12001d005802103c0050344090 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 897578264 1250 897577014 897577019
    0xb040b0d0b09181c0f080601031806060801060902030112110111071517190225050601050a0b120103060b040b0415030302120c030d0222092a0e1e0a 65
    0xc000c00c5019100e00521442416044242520807200030502084141c817a8986a0382e04a1304948010380189018181500c90a0001300c0d62000423000820030b008000000703881d4100701005094401560000c0034180c01840140400203a01c1516420340d540568241c003800e0b4001c0059848908140d0f0f400034500070468001000d1510202d0000100005c1d0b480c0e003915800d10b0841907500c1d0b02582c00480c8440b100d1a02c41461569074010107402404c5120041c0b000208540080c01309480c100442d416045600104002c1c140b41025030003410071542c2c010306150380c040d807040080c0014800901840e80b01c80d0802641d4403168000002e00e0400b8005001d800c1344005804100ca015210440040c031603461400381e101070043c16941d60040940140d403a024030308202078044d41040c4281e1107000034015440555440c481400300043c42840c8000c5004207410a446007440075607000c981c6982081100701c07511030f070b10030403030710f402a01114000320f00c40380f000b81c81900144a20300325402580d040e101 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 897579514 1250 897578264 897578281
    0xc05090703140a0b042a08151009050307050d2004060b070506150306090a030c020411040f1d040f0318090203071205060a0b0702010807030e03070606030317010b040b0d0b09 76
    0x810300241c191400c2c85061880c20718400c9601c4000c409940780c045454003c00494821f01d080358000802c828503e6004800700c0000d50b007074400004000200e95508010403c50a0500021000340300403511a5010f84d043c0d01c48400042620529080408120307441003031941da40d0340f2141c09480300200840d00c0d1002840c0155940b1401d640d0402d40e04c2944aa80016150024600f84691144005803008104a80c2c06841200110318203c0e401038550f2000010b131540040078100516501e005560035504d00711300f9881c41e10800400c031030b202d0003480810000c00c0c1c0c140e20060310700390b061030000054081c2201c016102e5000c2d40040f84403900000901480c2039001c140c05142c1b84003007030204a030b0748509080180d015250301c01c00f542c41c8024002403000d50300034010281c0c000164200824034104400d131190559200b41c00c12a00789544800c00d00c24540d0100c1342203500368000c0700c0c0103a1941443d1003022b060240e40f1850180b0303c00050765104044490300100103110300070342100d0550070542e00 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 897580764 1250 897579514 897579521
    0x7051002070201030f090c170a022707051201052701090c0e04090c030f080d05040506100605030f0103081e030114040c05040b0a2d0309060510030c05090703140a 71
    0x1d0680c0043d00f48900040d1110f804e205a01c1c585074004070007000b861030711081d28000e10080200c0e010601840304610301607150151049810b0480051064031102c0c02412690701360f201078102001c2010a2040f0188100c3c25084a419200c0c101e034115840801d2060420b112504003641454035020500002021909604030aa40c50019110f0b2490b401c568028401111084040940720f45c4c0880c10030000724201d6128041401e01480042d4540340b0700d1405a010386030150b4007110158000320808c040c04103d45c80d1000505241d2920a2850500c2e190005401c1e030f06010207000800d0005501c451130721098903001081d56104509910b07907948070000c81490429142d068002ea04004058445500c101e0495080c0d0300508030b0513003401c0c172200307088030105905402c4000007a004032000c00700d0b0508680381e44509a680d03a010645002c1e80c600141500d401504805490304002e005000040100b4031170025101c0c191141e040558030a00700f02c01a1070242d41c4a2442100340040c0145403000381c0 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 897582014 1250 897580764 897580777
    0xf1e03030f0b1c06050601050f2113020904110109091d0d0c2019030615060f090e0c0906030705041d250e1507020405061002071a07051002 61
    0x101d081080400754014401c0266295010104200d20140b1000024009a10031a08030b0b506161450808000407081d44280c1d01580d0003008250078449405030285021400d268060841c00344140c00c4541d5602290140d180a0b20080c14051540207401c803a03480740c00c1e00c8008000d058000c0c0024144c0089000b44800c609040c0c00e118054014446005030081240a00ca00c4d40f002125400f03107a800300f031034150034818112507800326040c8840780e400750351494044040c60103107100250b07a50050522811258060b400b04060010075a0340801c0103800007204001c44c0c03c100c501694030341d075510306040d052041c4510a070b800074002c0b007449005540480a4400d503400043c01d1886005200500751000404880c510f4140f002100c00100d090800c4503988001501420560b451203004c1e0001040480382d814201b82d07100c0080707680015845e142c024545c00039420340d104800c0e4420808001c6d2281c40c41e0140392410300e90301c0e40f210809010242115405034010040ea00111000d41420b0082d60200 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 897583264 1250 897582014 897582041
    0x7140d0807061b17090105010602120a14070b180d140705010b0a060207030b010801290607023c03030a0f0c0b07050d05091b13140a05010501030e03160f1e0303 70
    0x144002107000345d0503c00e8a0581e200d680007000c5021000800c0ca209a101d20300c5101082484e2086124002444002e02100f80c0f1901004820b03262403000804a121801104030481d840200000d80c603c0d0041c0d540c823403121544004070f03600c40c0f0508142c0e0142046584880d040807414400041455020a1740f00980cee208540071001640d03a4122942604c2d81180d08001040002600000c40d40c91500d00c6404582e0141c0450b0402c5084d80000b46140d0600b100704000b041e1080c841c01580d40d641da486081e803940c0c90f12800760382702c600d80440d0f80c9001c7d0b605640244044c0b94000c981160141ca1000e00d02a406449010240741c10b48008101f41c00000c80c5080c030a007040d010801c0d100d00031882c2580700d440c4a0000070b61803a00c0041112800c0410090100e465071103044144049001e6541481a2903a85000c5050351509000400706d6009000b207014907003052000000310420b0891010a0030b030403100701c1c1d0381915070b410802115928058640f41c3d0002c082904401c054140d0410004415032 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 897584514 1250 897583264 897583307
    0x317031f03030e060307090305100b040c02011404061802060d090308060418171306050405030607020105040b040b0402030c09041b1a070312111b07140d0807061b 71
    0x403020995424064000200450030b001d40007540c904104c005035500c88844c0c64084002a502d89030a0300b06540344254114403034a602c120200c90510780100ca40b000d1181c03008200000000d240300848403800380c030061105e901c0d0070301907000c0304000818140850300101030654480240d240b81c0010490303040101c004c5618007000414903d00352080d80254044d0011140800500d03565031480c212039032001c4c910440050100d0b1070520391f600e1101025200c15100d441e42d031030402c410180ba0100041c003860440e81030008000002d0701040d94aa000783c0d0001981002c0e486038030001c0e0a00e060b042a031500003508000308001d1046a030b44401501d0403a030316045403da103414415042034002c0e45020001181008024000ba2080300100c00c3c99004800015a0102140c000d0085034404001d00748001001c0c207241c08054414841c0c0401442004a4807035048504804541d4541552130050107005012522106000154120202500d038070091106922540c040c050f0448548004035031840b8030 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 897585764 1250 897584514 897584551
    0x501140c030c0a111507021002010e0706020d1403010501090b07050708030d05160e0328080f070c3302030d0f0204080c0607020d0b07140a0824090403050f04031703 72
    0x43c10010356029920550517985492095004d1003402c11250200c0c608540d601c2c05600107100b0f088c0400c0014040982c00350580c114901d8000b441d980c0b020740002500002000104000c6c0c1e0040420740480e80c51901c0e0980314403e0b0304240d4149039865000710b00c00d0100080084d1a94241c0c0e2200c0d01c5422285040c0e492114018401c0326500c041c05101509035000c0745900c4a55000a158046058100300310884200540e5440703001641080d0020300820a0203c1c01004012240b44218080e241d4401c801c140c004030012940b81c0c0e010240c20443c030021810446c162a14424011071300c0060610341c0c148010f4030b0b1610140004e51084c80f403042540181e981e48402ca00d0700404481c03049400074090740726401c05445800c02c100c0050240001e00a01400d416502a03405010b00301549554a0310b4000b40760607920482c000941d0300e81226007039000c3c100194581c0c1c60115141e041609450003c1c2c440401d004036142c140700fa0341014044102a00100c4100c14000004500c00c0c14070f00200302212a = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 897587014 1250 897585764 897585769
    0x100f0213080a030804030536040e19020415090513050f0a0305030a1109100504031101260a020c070308030406060f051c02010c060e0f0c1005040501140c030c0a11 71
    0x20b40c0004010001140040403a01091250b0040e2101000040c0ca0141e241c180ca920481d41d2041d80031214004041d55030064990329051203000c1303118031900041c000c420b016a40270310002c00d10040007845a40d4404076101841140c4200e040a050202c0c0c041245e41002108060960502c0c4000c071802d2150704070910012002181e8621196410703280e450441d25a114810090041d001840c011310f60240002d101076a190000000300504644820340d84900b1800d000c42030b401011b03c42030620400b10744164103800048040b0306000b0818070b0007505602e581010340c01a1186100e0028103105000c80401846904c80046026602c02c60003080030300d549420807003c00c0380c94404e00342e100780600040c00c801d044558840d002148145456600303130030340d03554000c1152030500041c403c07588a1101103401c06e03410403612088110031200d45401070760500c001441172203a40200e0381000400b80b20031140c8440c0380705070785054691006884c0c540501030603503561041d072000c0540c0e103144030f54400c0400c0e0 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 897588264 1250 897587014 897587023
    0x40503070b2e05100c0f12110708070303140702030c030708031c06030203070e151e010e1e010f02030408060103111e0303042d06030f0f060521100f021308 68
    0x310303c082c0907260700c03040e007140540f82c5032255102990400101039002d000900ca40404100c031030403030307250046040601050075180c1703141600964400e5002040500c0400d400280300350700500b54005003a80d0321610f00c0030a0804174040f800320b03054800c64501042d012008409042031003000a1010f41c0c07183d01880880076920548406505074100c0f56051000755088101c2e55444880203c102940780100d40c085443e040b0f1001090b013410b2900b0084100ca07680c42000100c00350b8003143d15440302060042882d0304102070010700c0e41403009a0ac900c140e501e0081c03064030020640710b001c2d1451980e50f414100240000303c0340d6640310301c8004843d04649004410381801b02000900110306180c18100c201d005c480050070030313000140d41c440d0151181d185640340180a40100e41d40810204074410000341502c0812402c0c000710b0b801c0200c14001902c9901c14819003804100e2072021a0580c0c2001c0383c100006a0180c01c078860401c0e41294008149030014250300707403644803042e21642d41e030300e407244c44 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 897589514 1250 897588264 897588269
    0x302090103020405040302030c1605010801140a140d020d050d0e030715030b0a180e1216020d0218130201141c0504050f010216060b0d0b010905040503070b2e 69
    0x848159001840541015403142d035101e80f06c1d00484e4034000c4180811071030504c100901c00006001d69038240301e41d580c000c030341030700401c3c1128441d40060458000218440352500800c0780045450319028401ea903020010300300300741c020340010107440302c5003051030b21003000010070004035600c2d05e108540381c01c0008880040b980b40040140d15110551003c5010b018140b0590381d0001c035560b802706c0c81d04000501300004410480c40004d81c800715100c05414400e030366190710100b203028041c0351550003d10403040103099045030440060443d905c0040c402d00b14845a15403445141820407400146041c0e13039408840c002d07281d90112000414820346203110740c207108140011100940303a020700d0766400040d0002d1050003a11690031400841a003240c00803103007800c410030205008000e0215510a01c0d4208a0a840442c001549501c800c1c90140301803080803069a9030348005018000240159989c003680482004154100802d00c3c0f0403182c0d0510103995041c030080d842c000f100c082004034804 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 897590764 1250 897589514 897589519
    0x414010513051b030a0e0105070e0a17070b04181406060d0c2304060914030d0c14151609050f100c0804080610090b0a030f080c070e0a0e070302 63
    0x481c2144030180002d44000b901800d01c0821958502051440090156100310941d0038005a0ba86000e900203003914000780c1600c040c07050441d03204801e0307210b90b4a40b0042d0b4041200550319000701001480c9070690347c3c0d1280904020100c0c0c0825201000a1800c2442030012418418281c9400c03182c80d00010540b6040d5214000b001050180c14494001003501100f03424031180620000d000f40d51119000c100c0c1c2048010001414003010f9007101e030314405001000c811400701a840e0340400d0343d85a42c88420014004100201e804100d19201d106e920022620f00f41c3e00c5600c2101142243c00e071090341c01940c44120242003608491281c0e6030b4a0450b01c000b0042c0b035030b415000040c80808100d004641d803c020007801841c01140e9000002d0000b4080301004060b9450901e8060344030b160380303030040d0803c0c904020b42c00a20795500d03c44030303084e40d800c010360300070726002840c0c80012885011060308a502600100140d41500d541450380714010311401802004d024481d40c0740c0350f030100d0000a5 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 897592014 1250 897590764 897590779
    0x11030306010e0d020301091b051c02090a050c0c0a030c1211070306180c0e011a070c05130902300a0302030f090d0b010b04030302101811060d02040b0301030204140105 73
    0x80c90f01d000e00c2c48214950000d000010701c008144c0351004c074091407001c0540c68800348d5904000307a08003500e081210744404030800351410615800140011400380100c039425886201150a0030750382c3c0210f560101c0324004845403120303603141c0503101011051090718103071160640c030b2038030780d02035000d980402c0c03001c00250107820f0850780c0c1c03031b001450f15200c080c0c180880c4002c2540024180074009018103041c0030320009540c50226040d80380c124150561285450a100318070004450100707640130345004660010102e404424030b640100000d9401a42c4860114036006181a211303041d00d044104e01c092040c1d840705070106d07403662500300d1000100142d10030001c944100c1444400713080d07510702c020000101d1720110b0320f40d0324940e0400c2e040070071822000201001010f404010448149080280901642c80d221071041004c50844101400144683c0b01540d034a40da01012168101d01d040c80464a40e501e61503501c000307070001d0108a004518044824419138025018a8100c8000070060b0703 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 897593264 1250 897592014 897592037
    0x90b09040819051e0705010b100503010614090d080910180603110f19022503031112041401090503030f03220c0603020a02101b032003040f031103030601 67
    0x30440440022100b02001400d1014401d22401c00364122107184180103059104c10407410200e007103400803500c0511540004021909a540007401cbea03044a1440c00d003188040b001044040441c4602250765070303c4000d01c0c01d00010800700038040c03c40c080c0c00342c90107140f6801c2c0001c16200c0429601c40d1071799114200d0004c20886101e6000700f1422402d41c04101d091054501d444040d54004080648070303201090700e440300341c0d031b81002196051003150000310210070000107508418800ca00024040081c6046902c1e6901d100700100c1c444544400d4189640390703a01c0d001940211042c4000a00081150030f00240b18078000007661848404182064030355190054103011001000c01c1500c140e514850081000c50088a8010000c1406da100940d0300e100980c4000d0401c1c8640c19614002403814400a15501011800e62100b07035a6080004194105034400500d8114202a03e68070203c00002c1004110852804201c524807984910460000818041d0307213038001100c40c2400504600c428 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 897594514 1250 897593264 897593287
    0xa03021f090302030d0804260306040504020f0a060906020708010e0d0e271509090c1c20010212041a0d110a0908071203170717040606090b090408 64
    0x303420015800c1e0034001000766882d400300707003046960f512010104c5c15020401c01808040240c0c4840500c1c43c058501480c0c0a1188248039030001034007450146580c0c100190464956124618800c0002041c2070302c100e0b91078100500101542c013404e401070251050009502a0500403460350315450b40c090b0000d803544401c11a84012140c502907440701440a80e2810f13142c003003c0c07000301d01c45901002c1c911844c025183c1b90f01c280a0071411340c001c900d0001003000e8118003151403d81848202e83c002c40d85000030f8000d4200c2040c61101400b00c86418081c00f06402c001c01e100182101c0c2170b020781d40d0000e02e01d0503140b280d015600ca500c00f5080d000d1000c1c07812014480c0100080200c510000820b003074903180c4000340780c0240604401007a40848207000c513400070860840140441030a80341446031b640d400030b10002d14001d1030400848548040340685005081d071000d508403d0032883c0d034600c0c00d4181540940014032580041c0d510300803d01e00242851100f161041e41c211126500c0c00118000 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 897595764 1250 897594514 897594559
    0x70203070512210a030c09081c050f0d1a0a0302181f140a0f12020607230615010206040308010b1804061409062e031103040c140a0302 59
    0x1441c4450141d4004030300d0407100320180c415a0100741c80c0b0300d41c80d0035540314040c045481b041c2d1880240802403104011501d4005900c40d030b1200e210340300b8080030712120820f079158042c01401c0c0b2410500814240a607a4155221010440000e0b10568070402ea9170700740003115240c3d0001a401485080788031503800162942c01d0340145424001540c031000c00700c2200e140a1458118004885c4030a01030700d01c61810258000c05403039546140c042503484e0183c5070000c0c601003e802801541d000c80d40e070060200d001d0802e010031065011515411342110400c60b190f100c2114540500d01d5400303844107155100066843c86035900da1075014440e404c1200102154018407401882e88481c1011000942c4460040000910034040d1200c12400302d04100001030000401203401480c036041071801c2600e0308140050165524107164440200c00d0004501400c1d131070043d2a072881002081c04100300c140868002107519100b001008000f80104012004100c0c1c0310103507100210350265400e60b0322010 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 897597014 1250 897595764 897595789
    0x50306040201200a0b0403080a0c0525060221090105060d060e010905011104050111010b060f092b02040b0301020a0f0e0406030f06090c06020d17040f0206030a0b010210020702030705 80
    0x11200c4400c2c40c20004880c0381c0149040b04884080c031000031b202c10150446880c03900801d5402041c00801010308000300b540c084c445510002c560b15181c1003207640c42d100e0041c0203058100384299500c0484211107000c20710b40070107807070341c0200c0c503000920740100c1803207070314000e100050035100d8407800c1d51a0349000d00480c4880d0007165580351002c20000c0c0382482030710b06001c868048684c5861404002400510b11540080c0059040c00a044880d6a8480803111420405c20308191115000c5d008039419144c3c0b0100302c0d00320940071400200c01b02d880710480110390f1003114140302c442c9124043c1803d0b0b000700c401c0c900104080c05840032005009640f48a05440081c100061042e960380b260314141442c0da00590b211a561288882840745c100144d8003c0d10460000f090b600707106d1123004100d4000b07040c0d0541c0c00c0d00046c000c20100714a6484c5694026001080240c4904101042000401210840a000d8400c04106d0350f6914000d0007035803507542d0000e008d8103080e498074050045491202 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 897598264 1250 897597014 897597047
    0xb0a150b1201053a12020706090e040302070305060c0408070501030e0c04110c0d051308070302031218042a030b011d04060e04080304061404080d0c0c02060a0e011206050306040201 79
    0x40315183c10002d01107074107060341090707104d00036200c410a08111085c00410f18080b021174106800c18010355402160040407516001f4441d0f80540e05d5080480c1490b0300350700007d0080c000d5100f48038402c13074542c000e0011390f20b080040c0c0c0d441603075850040d81140c9110760920426082030740484800d24156000803880e160f83d9810510b0550030b00d003a0707070803c0c036482c0e0541c000c1540810942e418400c2c04070250702804100b00200916425a00000e41d0b03240d21420300303146400000744030840b40b42d841c0051401401c0180c03080c0200c00d40d420702145044862000c11440700301c00d8900a420030f21901600d100c000041e101d00c99084003250404a0300c2c0100351034035030480d0b150600040c02e401c02c401c803140300d140150511a02c0c1c0c24503207403003801c0c0d81c03903403000325226201c1c0814400464022001c82d0301200403020000303480030000505850240f05010b010b544004081034140d40d5076044550244045001d0361003012191074992030740304544990040b0380c0c26501c01c1d40000c0040d40942116a50308611 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 897599514 1250 897598264 897598309
    0x905091017011119120501080a021905091005010201140609070c08090607060209030616080610180b04150503190e0325150203060f09130b0a150b120105 67
    0xf00c00d0b44002e558441c1c0b0030509040c000312006107403a6071240820242c1c00800c030042c0f0032549041c54240d5101010440a80b141c04101c1182000c802d00d199851300618014100700c26600c2e0000100345070030824030490740994204440c51105000f4841e1281c070400340100550704a440d140000c0728506070680080343d1641007040130049075641c2c800034140c000d00c43c200240e0303a040e09000b40760410002400000762503a100c9134503a83c1940241131140d0040b02611074055100442500b1640d1040c0003079014280c0450340c401050301d0103010020015184000030f4043c245400c1c99049030188412100d25020b03081141030424004c0c025008080500912002c481c107150040741d046215418010a4005050701c0c0c1e00707107108020080001900c441070b031a80460a518110000c11703000740b20f003144030388545035241c0040c07a5951003484002d0171580107aa480e1280c9441c002d0b840040c920b1900c45801c051007280001100154041200d40100100002500b51b03440d1100b481402c403451542031808001 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 897600764 1250 897599514 897599531
    0x10f200303010b09031203070c031209150b01030606020d09050607031817060109090201080406050c040b1201141c03080603010623040f0b060417012406090509101701 73
    0x108050342c06000300c039902550b2400b44404140c90f04550030440b4103501410710070041e002c0d8010f0b402c51274160301400c024a0506040741d504004003444907006101103c0e03024813040740840c5038000b2800c0c000c281ca08102d51a1101c40c140e0360389621844200000390090400d01840c1070860180040382d1103810101161008076216440d4000c0e1504901c030b00e110012900b102c03e0f0340c20000c00d801080114801c005235007a9800003407041c3c900503c060807403529000403030070081400e0201d8000f880d0440c0740390703112207400c0f4804400713600070b1141050045030318451002602d00f8080c5001201c034402c02600310100d40356421303101004024004c5516568845000030012030813050007208101040e40603440e08082c1c003c00045809a06036074520a16100e00e42d6a29242d9108030340c1035616a1303141c040650307103c0c0f2816014126110049003c0c10b401c46c51043c401c0d0502d5444004d4801c96141c0d400407948074030a120200320704541e42140c9040c1c1940800c0505c0999542005c420500f10010542c040e = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 897602014 1250 897600764 897600827
    0x1d0c15090a0321090605040b070206131e080709050106051c15171506101206031b05090c0705060f06011107140a0f03200105040e0106030204060f0e010f 67
    0x44910003602d0160421800010229480404030000c5d01d16420031504150422141c111a4001c0202c002c0c01200300060f61825480310340032140082c0168a480f8552100000c094050542c451140c420705224802c00496207034024019241602c003130741d981908000c402210401314000034001229516550f1180a40c2881400c2400b006003007145000c1280410f41c1411070718004048644c40300d8440e40320140451551b0300103001d10a0381d868580781c2c030b6000104e032821700200260390004000300c40403410302500e200c1a001d01030461303604561750081e9a41d5910581c60500c29540d00910079040314000414000944d012907401c124185030001d00c0e8801c0d5100c1c1c92034070050f5000340441000d00240554103182c070000c100050100038111380c40c0301d480e594803602092410041e01c0e520212040b064001a4403c0c411f03140200610300f81d032402940e490b070024000398014094440003404014480365080d00a184012001006940d002402c080c1d42902311242258400c9020806950040580101 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 897603264 1250 897602014 897602033
    0x7060b06040b0a021522020105030a02040b070c05040c080c040b030406061203031a0a0503120307030e070e0406050a0207080306010c030201020927090f0d08040201050403060f1d0c15090a03 83
    0x4440342e00108170506040721000c5080600800489080c00d200111071500e0740540d940c2c0308025030a0a18503181e41b10008040e02a014981080c071441c480815484280406102240100c4600383c17030030001d00088200440b1100340403a010a0140800c020820200c0c10f0100210360140c0505000121103485280044892240742d800f540025241c030003141c0d8070703005080501084c90045031440b0891b4a0803000c40d48030524040030064000000c000514102d010b500440260150030080e200c180d52205040280c625054805841c031519210000d01d10303400902c21110800d4014601d076045558080c011074840c5201c58040341155020301072030090340c03181100003802c40d0340119110f80780c445802c0140b15035907000f4020a140d07401034105906c0130002140c100300c076444510b082807080c2d42702e00060301c46204135400241203d03c0d01e902c010b5000c007160712101d1807074621004ca062000c0245203441e615841d9420307036039004281c007490500054031200100307031070036018120340400c03a82c1e5207408050 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 897604514 1250 897603264 897603277
    0xa08120705161b030804030b0a0c0207051003230c0304211205100306020c1509010908040314070e0c0d1a09061c06050f010302090c2a0a20010201140c07060b06040b 72
    0x8107207408d003440354010f00c6019165241c0403900c01030031040e00c0c043c0058841d0740901502828540c0c0d600300031100000f405640450fa00710754407240e005040100c00e00d2104c3d44212401d403041c1804d990303062103241c2a0200140041502d0795290030b01a072a4148000410000e050003100c0111460000006166800900354809154011303000d410300e5503d0341400320400803c010700c40d0349007210550002e141d54040d1400e980d0044040302d0204005409149491030503040891503007201c50800810821038030042c090700c43c9000e01484a059802c2a5101c8440c8550ba20740d03024030044005482e90400d4455926500c03540014081c84011070b0f22500101c3c0c005840401c8400c95210050046d030901c183e09035040350840602c24540201c01d2458984403144440078041c0720722190510088043c10010301803d581c01101c46060042c01c804038001c103094000c0c4041c0554200006030700b056500b4400c0d00c2c8200c2c0444401e0b45000b0341c41d41d440b40100600150180d00501c280f001044049002001d881d0 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 897605764 1250 897604514 897604523
    0x180129010909061203050c19030e1503060622030f050d0306061115090304090207060c1b080f07080f0d09020910030c090c18090506040615020d080709080a08120705161b03080403 78
    0x1090f00c504070900c4220103041c50702070303040c52f8100180607081e110001202c5207101052080d100042c6074000b004403488883d48041c00300c4402c030b091807080c40404910301c80b07800d4182e1010419030781c2d00e5100f40c5d21101300e58000c40f060380180c0d80d012007410000c500143e1050405e4152482c240c3c0b5500680c2c100c2e00103000645405507030780660301d1856002850000542061110302e07442d24042c2e41c07444140d105491100052181c04120f503400c000a11007641c107801c500982450300c03401c80910f1a0700801c629041684121b00d0729002c5280700403d0706c2d092060300c0c1c02080c2401c80f0b504003903010000c0c140e00103c01003002850440d08002088400002024000d0744401003594203114080000340c03581a0420318042c005d00100403d01500003804e02170380c1c00b49081c19410382c3e560f1304003519403e03c55800500f1600841249a08006942004002d2408403145d10030130703501d64038402c4405000745146c406840d02484424004901f5940b525000e001c401e4003c44042c0ba01d0355a92256504103030700440c1d = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 897607014 1250 897605764 897605777
    0x8091c03060e010501090b0403140c0603040539040509070509280b010c030c060e01020a020a0308090309030712050a120305091b0603180129010909061203050c1903 72
    0x8980e102e44100c4500401c42441c0450700e460411400b46000e10803440001c00c1000c0b91814050504d10a105499441000504140d200e14146c2812511250034140d042d500300004071700205113000b2044d480416522050641d10402a80c500340802441c01800074013803886494400105555440c4101d881560032121404102c042140d00e10480c40c50030300031540c2079041100b8170310266400340284041d19054507001d402d211490900c00c0080c03214910003001c40d40002205501a40c0001d1103200c4030317100c2d0359061403070b941e000d044a449010b2804180c3e41034000c032034200300c0d5901d403441030b41000e4055025201406510b0707480e07040c0545400c100c4801b0a4071001008010300050020051424440b01a02105083d50300002c0407840020061015464011580d120320703102540212448200c0080000400301400003851009044a1a07540002c04403030300801c199215005020885803603148881c940c03201650141d450b608068021a80303441100003407031078072800302e8902c51141d0080c0c5800 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 897608264 1250 897607014 897607019
    0x105101e020c01023a0e03010608061b030108060109091a10030b0a020c1c02011808040e09030a080a1d1c030e0c0a050409030c050d051c1a0108091c0306 67
    0x6818044080f00300403900300b14940c05540045085c072040d05048000f0b40e400d45200303071100d01b511700c64200e0b90307056015840d140020440c100c000034841e0045c0026028803a00070740b0f502084075688400d0141ca0078540000700100320455a0360400000706200da10400c558110042015a40400445001000c15082c040400070302c280b01c030030303e500314401d0b003804c0d4075100d00f03a45402e9940c0c40ca01801800b987c08280c4480e0390600c00c1d0f004c1c20803c114507d1000c030100840c241092550042d01030490700520a4001c50200c450000031540c48502e95290852640e5400281c040140202404000c1c1188018540803641e07205001e10251100405908030704015507000050854000c5580321061351321003400900203648404c070140448004440100706540d40c2d00d4202e50b00000b0340c500030400c2c45607051100c40d258101014003001c0c81800403040c1c18680322800c030300540d18039200d0828201c1c031070f070080000c5500c15a4402d07030000d81c0d03d045030102c040414070850004200000c410002ea901c000070f = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 897609514 1250 897608264 897608267
    0x424020a09050402030702060402010c020f031e01050c070512090a030204090b0702010f0b032d07060c150507080c030a0618020d0501090b15130b13051906080105101e020c01 76
    0x30078040d0209a80c218150328140c10f0187d6107034030140000c2c1c1030006058202c411035882e0b524102182e54050155005031101900403c00002200350800c1b965081000140d804c0300d01000f0364a5283d0090009c0c0342e9522844040c3c4101d9021000f503030380120050001002503280c5016200e006071182d403070304100d4a88903000a00711098a540c0d12034003420825056060750300080d012090034031940c600c0360160850103078801e20103550401d882e85802600e40010741d00c1d40003118401118040d6582c0924049094074000031a00100d80354404241c1b060701042525030084050340e8881c1d085000000d503140c407000b1504070045070302c0004070a80d40004103000c10002c00d01030740f070040c01d110006222510aa00001c0c0d584603803c0e4088501440c0418109075040c41041e030b0380b005000c81ca15007940c4030007080c803006227420b4074042c41d03004e60511512502c0d50700f500b01010040f20400c2e62041d5840c0d01b400708002070020014441001c01c0844c80074240b0404902e80040c20990180d0010030300021038000 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 897610764 1250 897609514 897609527
    0xd0801050906010c4e12060e0c0d020714010c1d0d06050903130f050103060e06011e020c031b040c0f020a0201030203043305010524030424020a 63
    0x1d07604003d04113a051000580c0314440308604d507400c01c401580d11802c401e40c4111460ba00210304030f080042404d520414141950680b00c1c1e45045e501c913804503c9600c659000d96071984520350380e52080303800140450780d4080160290070b007014405880e01041762201003400c020100e0041d156551007501d80041e98000002802a0441380c0e10041c0580c4c0c0100040d45400000c500075040e1a00c40303000803a43c040910407a54413a0041d012240911746441d040c0c01c20b08154011640070a2910202040c2040c520403c50f12461050350303841121149180705804a580070380d113040540c800c0400c000000d0b503044c0001d404290810b400000701c8540c007820481502c84021101092000041603420703040c0d404a2100140c540a0030096981e89492409030b20a401210060038012444207402041c040c03c01c00c880300c4600605400e0000b85d0703e607410041402c080c074024240c031118611840c82e041662201a5a00c14091142125408207041403020300d00300c2d414969090036400602242e00d035800c070b00c = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 897612014 1250 897610764 897610771
    0x309070602072c04021903031d04050402031b060d0204091e0204080d111501080309040e0606030a02040906020903060c07030306081b0f040902040c020a0c0503030304320d08010509 79
    0xf0390601e007190900d02c091502526502100740001464030020781503403211000c0064407081450321034600c640d2420000c00c90b2003450245442c000703124070740324402d18081c007035107001c1d640080240c501804000c20080c1d076139a821152941105060124240051091000d00001d01c01e1040200b416a000c00d00300c01c0c140f54011007a24240e10500042c804060001003560380b000301410400d1441d800303c01700b9441c000c0218080e064003500d0500106c1c41e08004400703000f00480c20b481c2881400002d0208076142e52049503080d0b09a030129104001601d8280c00c0100c650f40206001458098140d010074100541101d10380c0300060001031041c1095890301c03d807402042d200c40035003110000305c144000c00010720344a0601c20513904034045055078817035118a40b040e60041c4100816050700b40080c0d00c458034180f080c1c2e843c00241c030340040c09040110072030744202e5104005044202c41c582d001d00c03144408055403000d0400309170321491024002c001c0a01402e400f0740311903d45625160401040c00d6000f03 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 897613264 1250 897612014 897612029
    0x91401050307031205160c121509050613021309050307030210050601050a05090f040f050603010c0c12051b060f010e0a090c0e090309181e040b06101103030907060207 73
    0x420810110b04541154444e000b094501250340b0000310b11280c00c0f404586802420000000c0000a8528102c0f014a100203101c0d060366204008001c0d95074040b10300083d00680b0b00d0b0040c00c001421513061420f00c6142d907100800386040d00b140800c4941c2218070500d01101c07541d00c001409000c0c190100040c0124050401c001e010790724240b00020014090203c103c414031070046040401ca650b40504031709000000b500030003108001da40040040c02c41034800070b000354a4011928000340c032a40d9400e501c40d4208213802c032180d01030070045520760b00a520600c1c505844004044800c0700600c182c1c1e000d004014000d11f541d5040c500240303d4140b010780900d07615480e00c020358000949500d4240b046484402203001550303103040c811800c1d841141101a1b00981e1841d40d85040508510301030b000b14110160914071501310003803001c800c4000c1e41d001d00002100e10008506140001c104280c407141c500d81103000003000000c0c40d19507001681d603c41d2580000a041c00fa0a5040040c0b030000c0c41e41 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 897614514 1250 897613264 897613273
    0x1d040f0204082820062203030f0e0a0e060a03140a030210140703090c081f05062b0f1a070e0603070c061d07030305040806011e050d0501090c0914010503 67
    0x565039205044111001040140b100f404c503d8415a245002d0300c00403941e44181c022100840c41225422008501044001c2280c02c6516005c152003225031240301c0c1005401c8550850910409045d01e610060140c0d43c00344208101200140896000301c041030702c1071009000c3c0034500d241c080c0c14070080d0910000c0c60351a2103100c0c110034021210232500a1550b0034000741e28000c82c180100e00c0c0750303660410b6602e48101c0091040360452004252004191881d0803c0f02c1d48524041110411703c040540d2108070410192076580d450560b942d103641440741816170604c0d51143d6400a01079211080c007410841c0d20340410142e290085618401c031481190101d2031850f010038040d00c4030b51560740180c031407981c60360301503203843c041c8130f000000140311800c4412040e904d2600408a43c0b00d8020500f1a00903a400003503800c1407124081d20400c041d2105030f04c7d05050030b0501c2540d0101d014140c03025902c884400001c107010030348520113080b2003132010909206520f90031401c0141a48014000e500 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 897615764 1250 897614514 897614593
    0x203071a07120c110607181a070201180518040b060108060319020d050609030a20100c0215010b0406020d020a0b0f061201110d0e010c1d040f020408 65
    0x1401124901c03000900c10b0b002482c0e00600500b04c1d200e1910818402040c4a00401e1107041a00102440605210b641300001e11a031144507510a98403a00401c400d00d1405000b20300040d0b001309402c40500d00f100d03100c105582d68940000300c12454010040c02c1d808211414403043c45559180f2030741c810002c1c20104050f043c0280031a0392801240314100c00080207074601d00031940c0d40c10034914a5500081114443d00b000242e082d100e41c005103c0302c01007611400c8441c070507038408800c51031504468000e00b4640e0400708400000d003402c014080d0450040440d40d801c40e40c41c44503000c0c0600303103420f01152280e0420308081e1030441c40130440d1085d903100a008100040c011010954800d0101e00110059107881300420f42510860300c05007490350a140210356443c0f404009004210303055030050040103600c56505081395011206070000488a4800030351441200c54401c00e03200c2c01500000c0d5101c04503544100301d03002a000b110203900038840b4000008120600c244007055960606004050b = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 897617014 1250 897615764 897615767
    0x120a08010302120a03143601030e160b0d0f0f06032a03020d0503070f0b04030305060a1d100f0305030c01051b070b0a180b0402130606020705060304080405100203071a07 74
    0x403000c6406e00c2c03407840001003501c00c6a10994020461062141c44c0346140b00ca54088040c0d83d210812003a070000b841c21350402201c420000312180c1100950354240c0741d00c4d04100503031404c1d50102100821242d25a00c460101c0f050500c1112040c41c0c603007200045503419803130300c07a0860100c2603181d903a01c000801d42c0d10b0740c204010288801c0369412030302d207000340e0142e03d0064158011440041c0a0980420340c407030503c01304007040c900c1544079036000c00c650341c4c44104000d9000a280100f5000100d0881315103070546d00e40440c44d4000c08441442c0b1a2180d4641404150311070540003102d66410110394000c002409010305508903c0c400606440d002c0d060420380114000c815015010511240114101c801107502401c40c603c001002e18403038464a0078101d03144101034408038059404458502c0816285219000945680f54041c0140302e00d01010030080b030b080580107840c2c078241044001003907511440300310102361356a00034540f250080d00b0031403818030703d1449234280d088940c0100300015 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 897618264 1250 897617014 897617027
    0x30a021e0d050c0c0c1c0203061003060c052502030a080d0905070b03160c03090902040f051011100c090f170d0507151a03010f02190e0d030e0102120a08010302120a03 73
    0x180040e0b4902410160281c1030786d682450604010b50140100c1003401166540444041c040e2402640c007071001c6490f8000844062003170800d0008104458168020301d448041e4a00c1c80c102c0c002003c40c0d80600c00d503114981107502c8455903400c41a40d03100507000b04139040c0f060100078541402500e00303604c1c152401500f07020102c0390440030800e180f0078010425010311340b500058a441c52085454980364201d0002001160040600c18048885207480107886034404280d045000ca0207000c4000c208801400505041c00300041807040411010405c084413224400c01052058000c2e0070340542110140e0412a81400d0740003003060402485002c6108c003402c0300c003a00b14030301d030006107010300e0b01052840456131116560315500b49240581890341c81d402408859a100fa030390301c288007820a065446054900c5140d420800115200000ca0701a1040341050351040c0140c40b4062404001000300d580040340d110003040c8188010f00541c1086524840f54409020080c0000e030202c1c1c4024104 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 897619514 1250 897618264 897618283
    0x30412030219030e090609100317040923070f0c121e0c050622021507050601060309112e030f020a09181b05030a021e0d050c0c 56
    0x85001914101040510030001005a40302450030140290309528004210940b4854154483c2c00800c02048042c904000704600402c2c0d41034210040a01c5c1d41d40f001042420b240c1c4400d146003040c040042c00034a140181d8641d00d021420039180d580805506131034825020b49144200803d5401c01e850494000082c841000c0e0800c0c00303260380400c1c40004030340403030412000c0c0b01490004000c0300107468000b250f030300746240b044040d0703100d13961120a044c08000350301c4205500d20b050840310344090304180c1841d5241071501c4900c0c0e45080f41945816141c41d00a9101c41c0029030790303070071010034072100103551800f011003140e00c0310030003554442008581d0b04086846041881e0582a611001e000b41e00042c55008480829501ca540302d010181c040155882508210401c0741c1e496102554184030f01c142003400e01c584485154400c810407102174000030b00c0401e81765805c0051070010900805030308034441c1c250512036512a2015441e07000e23110050040035642c07809101540c41030b840031441122 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 897620764 1250 897619514 897619529
    0xa02010c0b150d081306020606010f0c080d020c2803050301090e07030c08010c090803211905150f01081b0c2508070f030c03140a060c020c0f0904050304 67
    0x1041e031a200b103030004001c4203800c001d600c20080310000040041c5080070b00360032640384c0c0741070f1040c2e6690181641c4442e030440b5488e001404030504006d095024180086603180140001410807030b19032030744012a4843c070501001503116450001c80041c0300250441c0314200c05008d1822943d00c0d03580a00540410b01a10280c2c64542c102c22040301800c0010348015074026000200369a611500d280c02458032082d12800034807503041c046070201c03000044401c0f4020701180307501a1043c6148807001c168001c0d02074a404050f800c010301d0124500c0c000c580c025290f50050f08080108a402c0100c41c0801e9644a07040c48800c20070810100c07558042ca44d18008000003456940500c030001d1800c11205a80098a200c05464051707003000952041009481840301215401920740030f42031810f004c0c900c802030401207a1348081c0001400041451903aa41c000c0427505070b4031039543eaa005941410210000584c003222441c121403510b030090302031040040d1200720280c2455211241c8a1145e0f004422 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 897622014 1250 897620764 897620783
    0x40b190e0603060904060f14060103060b070b0a0b1203040e150910141c120e09090601060f03090b1303140901050301031407080a0312140601050a0e010207080d0305040203010e0a02010c 81
    0x7421b010b1079411880c0c038a007501c1c0c001c00c05812074022481e1000019201180001d1500c900420b0b028028800c5504994001d5450402c59440210490152881600b82a0030100440f070800f014441000500060085c90142400f9890140c0244403a40e400e9400c16124014078010312040d01502130806003500e80350b0718040030480d12200800c00ca80190702121809042c84d04003081030140720780e001106500705a58075400c0d0a0314504000d074645050314402c945801180040107068014010380d403442c81c59060110316171080751240c100b0344504a4011200c241c0d800324110416030721201880b0b80d00c2c0c2192100e4104410700c1e00003040d40c0030502004008216001860010350010003000004041c41c20441c0c50b14000c0e4600208141c8a0f0340400c1304440c10812620103080f4840495407091034103039140c03810015044002c071038040c264808503065002d541c80c007041080c028460305c1c0d00304c40d6649012900f03040620625084a82145c884541c42c4c0041c128100145e9001d0700c1c0d203040c0d581207501c0c403 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 897623264 1250 897622014 897622021
    0x1c02040311131d0715020c100c110402120604050a0e03040302060d0f110409050f151c06020d0c1e02190611040905091e06070f050f040b190e06030609 66
    0x84000303200d00d446411041420380b0f0102103030741000954006079010002d0b40030905e00c0e0058140d0781c0e18144580300350301c1560892200c031b5141c41610380940765800342142c020071079545000b0804a03440140c41182d9102a40104007240c00e00740116070700034a201504010410822142c4c5403a0300503404001d202d281c00252440b000c0e00782d600404102c0e0900f0104028605181c082424160302501c10481098140000119260111401719106a141e215a9507003810403804120300c2072259400d288070711180c2000d42e400700700700e03101803c00a451180009510880010050442e0b40c545111850301541481804092580415a62136107085050111a030440c42d141c09406005a13002120040801280c00181428107810407406041d03008262682d507240c00080032240141c405401c103555000f50007140c11684100d000c42d501c0103407864114101540300720000035a80c0164895120600701064003406400b0318902260100080d040066541510b0400b1440c14000104403c5c411240030000 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 897624514 1250 897623264 897623299
    0x314040302070b131a0319020405030706051c0e0606010207050a1d062101090201110102130e06041503120f0203040e16110a030306150201020708090d0f0b0a021c02040311 75
    0x140c04c0904040003800318101000c000c0724806800448000202e00d841881810742c503210340c802c4805542018010740301c0701e03051101c151610fa203c01060702510048050f54102d9001500c101c00c2859000340140c070060502000080c0b03491510b82065210b040344c1c100c100316101810f448140e024080001c1004195134200010300310210107904000354110000380f04c030f5401019400004424800d803914040101c0b082a45400c0340109100c59442c615544410300c00c0755800b0850300d5100c00003e0000c900c112072203035000c25030000c59104444000710210900c80301604000c000081101c1e81c801903081602c3c000503a0303e00300000e03107403000030348800d210b2411941c8500c0c1c0040701040d01c54100c44800c0441e107402402800c3da03104828178404039a40c0300c65020b1043c001c51341d4958102c400d16090001d41001c2142c1d030300524074126445e0f141001030b8000103d50b2941648214100c3c2001601d40d1008540090780801448a0404892041001b40001807048006008081c0241e034840b8509520081 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 897625764 1250 897624514 897624547
    0x90c0305030c0610060e0607060506060904060914071e0e0a0e07050705010b040b0604030b090f0604050a060f150303030914010f020a0201060803090a121a15010314040302070b 77
    0x2600c41c1c040062104840c00000410900405258031903070341280d6210b20458900200c841a80c0c0e002504002c42d00110b05190401c9400407001800039180c42d54010010301111061352040e5a180d884a00f440072034170b81018110b603ca092402e04001100d20310807007207545191165207009101e003030900218070742c40e2544010090654072100e0007281c100b40c10b01400542107610120b0f0380e50308240b80381d5098282801402000d035800303004c1908003030071a42c840300341420040200000d4803403c0d468000030401001101d003e94091400750006561600313241d03081d500c030707840b442c10aa814000c0e04401005022042000c5035010329000480b0300d03451501c5030401418210f024415800d182c0242d44648450740100401d1031950020402c860741c0303010150303e90040c0303030b41d4980c4014840800c00050b1024014403500303600c516510300741c64002081414464000307a40d00306007405801d444921030758051003440c030400d00003a620052843c1c1075800a645007110300402d0f142500214000350f00d61b15041 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 897627014 1250 897625764 897625769
    0xa020901060801030b060307080d0e061306210605180604020903060708240a0b0a1202030c041d1501122c1e0304030b040f060e01050403120c02070504090c 68
    0x600008803540d603020001e00d1004280020b80740301e00701c0e4000c1a80743c54000b44035012101003202918028000350819a40400c103507101c190401d004101c010b070b42d100403c00d580c02078017254a89280031444000f044152906000c07070280600c0c507016003070049a503403c50304045c610941050085598130140070402a01800310071507094401c2e001440f41c80c1e0f4201424a20a604845000750307030a41c00400d00d41d030054a01c113000d0f007110b2000d205009881c03070030004125941150804803800382e4a036402804036401102d1202c3c4440c2c0215080c841e4071302c40c3c010b1020b41151014001e0141c149000940281d08108030300a051040340c692030391a045480e0081000542e180c007114122040081c1e00742aa82c1529512030042d000c2e0707403c0107c0100c9810940d50b103000350302000394102400c6a40b114900358015105460010304103074008002025030049102c01403802d80081568145842d014143c041248040044c40303050401d2a1201680010230304c0803103408a40125403040c1c1420207148500854 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 897628264 1250 897627014 897627019
    0x51003051c081e181606030501060e091e10050d060f2307030c031401080d09080c0f090a0204030210050a0206010509010b030403050919090f0f060e0403110a02 70
    0x1503400310070315851070a1a070340e607100da01ca031001a40c1d280350540c4040d4142d11440f8030382c40d281003c68611416100908420880d0310100c41020b044103600103651105c035400b000c0041e40f102c00500440f9441110f582106102b41c480d0700141c24208050244c21807a180f22002801c04500003907541205202c4602c0100000ba06103c4a0907960401c1d10181c481d1454540d0401d00f0a0039400c032130f48880d001034414541c1c035220307125940c0742c414048001d030a40240070800c064844c440c0c1d11901103045525402041424002d00e24141142c030090110300482d07014800c590014080c0108544800b1150062540f003111885155600c0368070800003401243c001a40201041549520a6030001e005040040d90780d022205603030b907118204a0007010034001d0006510050011400180c010b402038013081d40c000b400d8440040c4401c8150074607405990102c980c25454501e14441d1841910a42c829060781000c24005242410350060407098050401001c011828a000540300010300c01c0083c141e0f0300 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 897629514 1250 897628264 897628273
    0x40e0a0510172a090711070306060e07031a100513030f0f14010207051209011e020105190203150d0213090506240d060506010e0604030602041e0b0d05100305 69
    0x84902495440020b003141c00f406940700d4101c43c011041420150a50710350040c4000410340d150a81110000102141d85802d0700c00c89002000141c52030213581d020305402d800b408007a1414050003026610102003020f00c00301c0d41403070803420b03482e003018160417140302d0f0414541c0c0340e4450511203040031080c0e102804400c1c44501c40c0003005914040d03004e00c82c2c014555038203000c0f08010503908034440e0190040c425805800d0441c080040e400190441d62014100b4004d40084155440211449500c0c0200141d641d942007224001e0104802d00114600030811425454203080018081c0050140c50344038484c00c030844c00455403080740d504c542c0004007500b40019103141c40e0480c0e44a0056a81240c424003503602c0c003542039214030000d09100c034014440422041d07903854200080c80041e0a5a04102000362403010507101c040c01040118440c134030050703540e451303d804160902d40c5200d0341c00300c01100003c208100440c0780190b41030894407140001c0c03180c403001c0102031051840d030f1006085018 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 897630764 1250 897629514 897629549
    0x150706050c0403020f190612021b010519060f090f110703032901050702090604020c0d020a0203150c040e06010207090f053405030a0e072702040e0a0510 67
    0x8401c1c0281045a2003070b2411146441a08108400c100d0060600b1084110b20030701080b840d44502481810146000030040c40d048002030313030f441450310b6446040c1d5580c0d154400c0c42403251000001c45c034110406107007084140d04104c50f40450030304034480c23081c01c242c45203441026030701d03039078040d40503640201500ca648118906e0040e01611044161401c80b5406200ca0206036800d51961100844c0c140d5603546000c08980c06c001000d90017801c640d8005509100e010b1880104004200090050750014590503507248105880c3c4501c1661030003482104c1001e01c021540c2c0e40017a0b5041e00c501841d00c0010b036a50000403851b100380ea03402210981c0c1810700d0070300710808650080d8020640c00d4510494501000c8600c1c00f82c114682030701011070a5400c03461392280c403070000b940d0802d500c0ca401195600c001c4005600d400c0c52904a401d10094040c602d074010383c0590f91644069600d20020340c03c061030803980984102005181000440c0c0f142d000034000389403d800d0038060003502806801251 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 897632014 1250 897630764 897630781
    0x315030706020d02070602120a0c050708070909050c15071416090504060c020718090305040e090d08010617070e0102030c07080c0f032a0a0909080319020a020c15070605 74
    0x43d000d40c4000d02502400c08042030142c4049900c81c1981d21a0501c00d00c3c142442100700c901c080c990f40142c800f401403110110b01300e18180001c2c00100341e19000443c070f1400e00e051850a102200c1c030401d00c0340400403a0088000380358010303100b80c07030b40058585005040c808101404c1c103000c001c0307141506200440101c0d07103000603400070740958020701c0e00f0031400021900a03aa1000580941d00410013105019050640c02e50800150070f4032925007541415901ea92105c0b0300001034620080326042803a110b01e84903030165500740140b0321843e1542d48007400c00700b8542c0640019050100b048442221005c40d84d0007082210700d2340b695036041301c0364075070741e42e601580762010000e00510a4058030049101c80c900018810104000c200960f00390b001015005403107403241c9000d4a8020a1040001540506501c6504032881c01011456580c2c941017401da50070503090000078003500d05c1440a5140a5030020b00d0800000382a0b94500740c81c0f0030440c1c001581d0049a00c01007545007020b04001548 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 897633264 1250 897632014 897632023
    0x51b0a030605040b190e0a062408011a2e031418060c0901021c090308070501021e07230f0708070314070b1912090303021e03100b031503070602 63
    0x5c40c000c80c03040b00703401c0c4800b8809044d501e10100d491515444100307041c0100b98607034041c81101501c00100c0100b00003090300ca6944400f19882481d1696490080036a00150941110415102182c40d07040e80050b2024802e00360901007101e40700401c46017260503d850196000082c1c078071030707080e44814614115100d20b505920500c0c0640860140380049008680c0b00c2003903628048050700540500d4400c07446026944095140000412817560400000b140e0540010040b25025100250762107881c9080040703848000284140c03590020058100419803141c0100550124000000401c0303094981040c41c2c40400c17a48100c8a000f14031300000c480000280301800c4034843c0d550700445441d03409820b1745640b2648140b1001c44c60410a2040c0d0248c1032010001801c0303503041c07180f10010300050381d00071112086030880c00f280d8001070403100240050319030130a114140841500e1498031403203010508801b840340c140c0e80040400402c4440d40581d42c071240410000d02204d11041da169002942c8 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 897634514 1250 897633264 897633271
    0x150d090c0e091c020d03150e09060403110a0804050d0f0b09030d06080c06190c06020d0b2404180204080109050319052a2a1903051b0a030605040b 64
    0x180309010f64982e80d144440c26643d102e40050300075100420200700294007601b441c800c0401d00001021000ca1b40010400c07940c0d001d41000c2000b400700303190620340a031401d00d407011402c18940c4008408400074142c003040720700380d1310241c07208ca83c860329034500b00e0760038114400c008022114520400c52118400005001d800180c00800e00c03029a4030403280c2c0c1c031032800482c100d40204c401c201300032025401c90400310450541d494450550700740b64450004070381090160134a9962109101e51003494410745086a4040031002c00040d258904000c0c0c0300b9218600c81c0440541c00030401c001d0480c1298152802051080001e0160b91500c1c5001d80d2680e00c03480070044169004441050014812002d4407090b000300200410b105101c1c82d40010724420701740c2081a64420400c50101044030019640c1c03212581d03a41c03035484d40200108002000b46013100b02d8182090b4000f040000c02c40c00a000050141d1704100e52440d401d00b40007180c01c13030f00f40f9000a0400f9007000148000c2080c5050b9544c032 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 897635764 1250 897634514 897634531
    0xc150d060b070b0109051e0405030d06050612161b0c060206010611070306110c1c0e2407021804030e0a172a04140a0e010b150d090c0e 59
    0xc40c548854608109006910000d0110940301c80103021044050b8000381d0003074a40390a1209441882c0805641c1c0320088504884581021904c0140d024013070082601406007119401d007846880c800702c09909500034004d03114000d884000840007030003501d040d441181d88062a05440a49003026940f011403441560014801d0700000a0704c6885030700550220100700015108251458031f80c1006000341c4200028030761020041105400300410a0030394880100c404683e01c12320f45040a042c0034050381c03c503402030301c1d04203c0da0284110014104560310407000240d898070b0f014008210540840b203243c03a231501810013171105150700403071a0f030211003084502c819060345500070301a403140b1100488060754040310409005038407502212641000d0802d000b80c0c405200000103060310f0b10b0208c0320262082c904240080c105050269420310140080244034a030101c80c041040007a050310200800310011880601d000b031150481059160001d2031100500c2c0c881c0b004005080c401d540500c03 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 897637014 1250 897635764 897635771
    0x20a1b0503073f1113020c0c1f050d18060507210605150315031204061202091503090a0b15040e0606091519090c1d0f040e0c150d 57
    0x103100719101d0342880209000f00f00c129100049640d0752807510403c07801d1a60103440c5a008001c60840e81c40980641a60040181500d081030010300c4540141d0700c419808e402c10300c0b40c01c14078850b085403c03104000210f100019114001e044c0303240000360031520080509080c0014408c2d1240d100041c3c505e0107000c04988114036000715095030464003144a0130f030700100b084000d04048610340c4091540881c41c0e48074203680360290800130341090000200303c0c0c0d160b1000b040c10b0004990003190f05014a5517264110f2901300c000d00003812110503c0f01e403a031100c000000103440031105200f40d22071160f0051500c8658200900da8110741030103507100c20f018a03d032201c400403608002508074007070783c0044e21500c3c1540f00c00d0701d20201c5d8105402100c0c0c02250310b030800c1484000c5550500000c0490000c00140b0030800c3c0c100528180c080020050064609036007104a40e903800ca00c88181c540482d40041e1f82945110003d0408030b49554035613001c020006200481d044003030040c00e0400d1296800c1 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 897638264 1250 897637014 897637079
    0x708090d08040f0b130e06010201090501060b18060f19120f140f07140d1107050c0f1203030f06270906011d06040914060c0c010b0a030201020a1b050307 67
    0x521354060040c80d2451803807001010000444032403502900054184000708100f98241c94090944d081a4401420031800203000c1040e80b1250130501d000000480e68585081c000c80c450001500590b201c940c02494071240c8100142e016419400c1c84082d0000c0c01d0002120354011180100302e0700040450307480d51180011100030004182d035105a945071510112032188464904094000d000040304080d96042410303060f949200141034003900c242c2c014984052050103210003c44800d480900a806c0b50500001c010000300580354450749c41802064035954000c00170f5404915484040008030b241d04142b815841c5049446100d8070211003101d060b40d82e120b00f6120584c6005071041c0e2089040341c04200030786040e0708824509401030300100c0b071000c090544035061084c1a50782e801035480020300e0307910021b0203000e0a04800011030700d400043e45140c00103501e03915a035600034003418244541465003844540400d010344006000c0b02d1495484401081c1001151403815550311948042e0 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 897639514 1250 897638264 897638279
    0x1120309090c05070b0411120303010906080115031203060b03070201090b06090717040215041e1e1809050d05070b0f04080703120608030d0606030513030e060708090d08040f 76
    0x3a01c2d4100002d50340c4514000640c0c90300320317a5440c05481181c6650501803100c03816910300305045000044000a550f40e94074000c5900100d8003503034050b1106074101f41d401c13544854185c04000850b604820848034102205d60100c0040109801c10813403081b02206100342aa41507200010091082d98152165210030b010080b10400c110381840000b18141415110010400d10340c50300144094072034821365010059980c040d8129421044000381d0113135403600c00001191144004000c8002d100d040e4201050745159241e005009440c00355002c054840f100000c40c4e0f02c01c80300c40e50043d06503810900c14802c028100c0e40001d5080e1a002d0a01020a0080075050b07a0303071317000300d074024007840c0382000306d070340c00d840d11008580c81540c800c0d5552000500380303070244001d050b20244030900041c06e504004005d812560041c000c11695141c0681e41d4000030b0300b01202c01070299080b60600c2d2914210314180e441da11809402c0343c0c0114480c11f00c1402c101e003d0010300151000e00c080890034030f072a8400b = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 897640764 1250 897639514 897639521
    0xc0c0204051305030a0f0507020a06022d03090907020f12090a0801110301090902130603081e03100b1602030115081507140d061e060e0f0f1509090112030909 69
    0x80c00f40c8242c10801441c542c450180e045001c0d03d0300207041c05824024950001410200240c4c020409600240c080c040ea000205c1c0c0c1c5500c1070760401c0c0464100705441c0c8500d550728011154900d01612252000c079520600070000704075a403402e041160265400f611500743c6541000282c00e0080da0044c1010400850600a40c07201103806440282142c0c0b030509044060705200b601640c00078003030341075555140303180d018a03c041c42c010844075983e003900c0304209112504030b605140e0050710501c00e101c1c9004c5e2074600c0400b103842000c0d0943d00c409854044a14001c1c880500075410761810350200b1502001310120b10032a040360003580d9410354201030840004000310340010000d10b018441003031059010000e010407103c500f00000c1c201345c03512072001c600d50301040d41c01986541d50004014046d4891079500199500b0350b03880d88082c0012020580e00420a01c2d004e00c581e06200c0748203a04c0b04c1d010240c1d4884000280400046d5940701811004107100380005e03400244002400b2070040d201d0700 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 897642014 1250 897640764 897640801
    0x905010e07081504060906180501090b0604022703160e04060e0102160602030c0405040f0f0c0e01090b0309120a05270d0803071403070e0f0f0105040312120c0c020405 73
    0x180c00010f04d5440341c0e40e040003040c0174070088400e20b83e6545000001074180006101c3c85100720000035018034a810b01c501241002020300b44990700410000800050304104a000135009200c0e1140700481280042e007400480b80440c11800d21400c00011140c004001e11805070380a10002c20032107003201c52050030707441180c50649400955030030490002e10207900a5900010280c40d013414640c4503000241600c10540c8640c20040d116128856001001d1088403c00007030340c103104821020000001c2c2040c0c920340700b410003269001c800034010031810b1007a20009404060f030710390303201240d90014011350030903500145907150b0552078001c006079040b50090803020080221070680a503a90b201c40550008003140d00b0481c00a0f09002c40a400b08040d50080c54180c40d031104040c0180280410002c05480c01482414140c0100d080c590704407040320b0942c1c2d0819224034164011280559416882680c4e9040003850000206d1740c40d9400340341c220f800e40c070827241440581c4a00f0004a02c0e4100d08 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 897643264 1250 897642014 897642043
    0x42a06090806010312110f010c03020a110604020f13090f050a0c1e0b0a0302070f140d05040b0d05062e030e030703090e07020a290f0709031b05040905010e0708 70
    0x25100c0741c4034035000e50f11b0390344250495000c441400760100c91150a6030700d00807480011a801085146800d6000496041c14690301070040c203651070590002280d0000381444540940004201d185d02110b440c0c10550b003d80c1c2100c20608014164542156170f82c5580100f60b40f480c080c0b03007005ca8a0710a03011101190000702c0c0d10814018180b0415050075403092203a2000d00d0743c2000550700146815808100d8940a44048141102014527650406915425400410030108800c1c411100701d041542c42c40090300400040550b86e0070081020b01c501c1a40d52000d40c05203d40d00c00c0307550010081c0780341036211558240f208103c03810700f941d078a001d501d200501040c803105041c0705101c408131415031300030310610458210305136940f108070101d0044210201901040c0714903201c1180041a07190b00841c80751891a2a89010f190090103d465800002c2c0802c60f04880e0744400e50171891b2113405403400810800c0314440c11300e8094000e10000d09640a0390042410021360b007100404c581000f00e00d0f0 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 897644514 1250 897643264 897643283
    0x1e03020604080d0608010519200d020705191103070f0b030f0a110a020a170702092a0f0705070509091e0a060e030307080f060612042a060908060103 65
    0x107a69401c60703150030800008030300c19524080001e00810901485004015603500960121101c1182e601950380400d00803418902100e00b035410241c000341140c1401c4102d03c801602c4010030b180c5281002408a860070540140c07801c0c0f981801044031005450035400c0301160292a030b11480c0b1070f1940524800c0301c45414003480007030032030000001c0250b4400401200011044440c00000b41c845c1c00403404400180d121032148810004c559030741c012840e81c00e07a40c0b00c7c2480081d60020301c80d400010510250345003948101e000e03820794500b48416000c5018100c0352a1003040c040004d1310b412040c0103031200c1c820014001090300b80b1f0050380b03008910200142403801d0030a00a6900c0c3c0d81c1103140b0601c00d00c01c41c0e09004c04035aa07481881020b01d04d003c040d41d941d0806803030080280e00050038507005958180305101041d0b0750503044840c03024034032840f40b50a41d02c90520140b6911010300054050092143e501505200c1074900342c01e55201c1e85031700c2e16040d161003890383d8480d001d02005005200 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 897645764 1250 897644514 897644521
    0xe0c0f1314010f2411100e0c03060c040e0105061804020a032702011413050310060305060a062103050904050a05181b040e101a0901210b1305030301030c031e030206 72
    0x305e01c0c0c007060a594010201c55840500c1e25911048669032049140c4607082880c9262003072070103200d02a001103600c5140c9082038104029a010250107221b40d80c41400000341001040c071103a40d120040301030051046494880340710018014007024070320700400c0a000350500d4a040301c1c1c01ca8101c40c15030103940394001036007035508198640e40f00300c415441d040751100002a07556801c00000c1c0d440090940003086d5640741d4502249407042c0035001d420030700d08000040c4059040c1040e044089041080707100058501e5040994851007a0030800381c01070704181c200043e8040300e41103103000e4100644d882050755a11042e1765107e022540c401240042c0b02c900c00c081c1407034160032440d40304600000b5500342c0c10034100048200c4100d01c1081c0c0c08102444016000f40c5400d9080c64010040c1d600ca046801501001180c403625020000401009034140030400c0300d1712481444c04000d6015045984d00cad40c4074100038040d01000e2004840041d0250b001e06d910120010f242003542d607041d001407083d43c9 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 897647014 1250 897645764 897645767
    0x9010905040c1d03070f0927031407030509060309010e0c0a05130e07051306060e1507060e01110706020c160b030a0908160b04030e040e0c0f1314010f24 67
    0x43c0009095041c403500b6000724820080c021460001c01c07071b9030360004100c485051484207406002450410300c211101c801d80100f0b13007104607034035401103004495944c3c1d01c2c80c5c58240c2e964041c42078242e400c1f402c0481040070514055021070130744082d08c0119900c6034030316010482d80400a000340b581003d050312042c6000503441d00041c80f805080c80598108a84036008504100d20b21405100c103582c54100c00c201a5401440d40421038a00742c5040c0d00211411110380f0540c456181c4c0200303110390b25050071801c46000c0d0300c005000380c003060103507546094a041500203034018140c182d40b6800b8944050925000456a0408070341d4003141c030604540d900c0360380200030716907150240d0314078104104500c04207481a8180082e1032045030800014145400c0050440c210304130705a0160345010100400404002a5118414002c894103a4640150804510041030903014048028209007a4200d0f14103202c4045042c0d60429a585180e00c1e564201d504401c11225032072000322260704007180142d07 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 897648264 1250 897647014 897647057
    0x2102010e030c121606090b0415090809090702070816030c051f080a090b1801051b03060d0212061e0c0708090d0f1a0601020f0106081e1006080309010905040c 69
    0x3495044a02203d04240c958809035141903070207c403510791170420041002401c0c40081d004010940d4108801c409035680c0c006140f04655019103c1d00d040710010740301d1842080581c01034000001078951507002040762050390101808111810382c400c01d404106418021094604c00c150b02c1816544445129070a444100e0081c080e0807030f1a03111032003000410f800d2801136006108075140e00091144040701070b421188058824080d4010340c0185130380a041d400c0590b50081c40c111200c0f0040d40140c030000f005031080f0305945640d805240c040060b02c00882a0481c0401c140300542e2105507180281d0003003074414407000801d0030342e00344a021014101449010314151050102410100881c0c480e0043c00c400c02444e0300d408081d5004021701948d040c002e0480114000000784201810410403e0300ea000440c0c02440259810042c008501c8041001c0b1164908000c0702b000300c65104e0700d80f075480b80e004d900040d01007070030321a00040e541400c0c0310b29030080c111551181203002e1800b0403031003603 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 897649514 1250 897648264 897648277
    0x20a15110304030c1505072117040c08070e010e040b07050c160614040e011a090a140f090705030a110d0e1e06040b0403030f0204032102010e030c12 65
    0x400c102240154a21042000240051400b03920b49043c12480d20410420310b030511310b034110070002d040c005072000802c00060744050300ea070481c030318184543c07001e0101d44611034001480360003c070f82004d2005001d0305410900583e103180040d14821a01d408204910803000e2083c00380b211804c1c400140865402007031160450441c3ca0074600d0146802d80091801c1c40b0500000408110040200711150304986600c800c420350900880c00c00d45401030b01d0301e10480521924560b40c4503440c01c4a86600440101c2e900008020a144803054907200917907410541031042d14060342079100d42003910700c1c0c0900d64070b10480c9682e0701d243c41c50380c980704014060f0500c0100a0100c0304144410031910381180528005038011034010000d0700801c0c214807d120591903508517a40c1c02090500c0b000c03a00c041d401c00d03407180c0c05040200d4080c0f02c1803840c5001f4032465101400d400546c02140e100c1200c6010308e015901103a90092000301104401c1c01d80324031803001c840b6083c0e03000200c803890558105024280 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 897650764 1250 897649514 897649517
    0x3106020d1b030c020d0b090f01060612050606130806010e0603030304020901030f0c0308040b0d0518070509130506070e011805100c020d060c05093c190e09010c0804020a15 75
    0x460900590105c3c035082c15429089a0315452041080440c02c0100013040b407130700d215002400301070325114019103a101401c0381241c200b502d440002e240380e200d84c030444959425810945076001c2eaa140d0041d140c807820700030301551111030f1012030150301e00001620300568004180c0030199196941d540800c000e4404129040544035031f001002c150024054802400d1416041c0c0d40c454146a100f8110340000300951a041e0302c40318400800140050000d00fa500c041d24041d502e51120840b035a070090001200070104d02c111010020344c55030042041810038001e03241c080e5000380703883c10031071700c0403440c029503410840d05004204883d219408540416001801c44848940300781c403400c00741c030444e00450000c00c0000805103060f00708001e10908a410005c02400108841e000e1807406031a0024861203281044036030141940d6070407016501a040810030b0482590b40708120340790000105d950303019951030a40e01c034000b540104c02c102c1c40780c1d6000741408051404c240710000621009206e000 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 897652014 1250 897650764 897650777
    0xc0702010e060c0120090a12150b060714030a0801060e030c011d030303130b070807080c030a1b03052a090904031107060e090a0c05030a0c03023106020d1b03 69
    0x2a410050307040c109112800c2e0703640315549601d4203040c841c0001040d48148c806000c11610800400c44125510440031281c020101d4903000f41000a40305000c0d00101501135480048402e505071000001020b101c50b0540303401c50f16a0362050b00350352513281d040700560160046503d8142075032162084115207500c100c0719076481c28500010070310f190001c807040714100c902c44801c0014816042c580c0b941c8460f162034200b040f441d02030801000c881014000e000250000b02c04184071810755000140f0340d00340c051070403013007842801c00200500400c0d941c44c900c507180c00d5175200102400750a4202180e81200b401844c01c01803d0910404000080017541000389020411816400500c017850050540e82e403041e855010503010012420409880760b0841880c000d5405400c580100903030380c0c00807110100090000d03081200780e01078817800409250b02e0210f40849407043c1500240300458130000c07182c00100d076407910f0003a695000e41030904c0c404a818102c150059806009004004038800d14002 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 897653264 1250 897652014 897652031
    0x51e100b1309110a170402010e152a070302060711060a0903060c1704030e041b23040b0702190302040218091f121b060201020a080c0702010e060c01 65
    0x4416074000401c00a0080d01c0d000080100074000e0088039140040c010340f803441c0c86480c0358050010104c6070340002091521800203070a40e0301407620303020703c0f02c005041c0c98000301c100150f842c41030b401091440844000140c0e00845499816840d01606100400034a0458216001c10115402695003120100404408405642c0311100500741e035180d2500d0ba011020706502e03010301a101042070741c40400c42644000c6082c002902180c0703400603010700b003190b228510240820040c01d8040e03050350003184882c11044440d980b01060481071014401481055014a5600071741d5105034400c07240c000d8020301c00b00c00940340420780300c0000c40005500c0d10711385a0f65808101070781c22544103808000c2c1d8081061600d03081411409501c408a100496a40401003c01041120a600402064940122481c0708000103a8508010f001e0441c0c1c42030985544c03001c000380030b5030107801c508000508220129882d00c000105480320142c1c142c40f211010b401308014003007240c102c140c1081c00756480d41d07940c = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 897654514 1250 897653264 897653279
    0x5040b22030f050d0503041e06090609140705090903030c13030b04080702120c030d0513051206100b0c0d0c1e0b160908190c080d050a0e04051e10 64
    0x180c10007148a0410302800e4862420700c142054000004031092100c02c01c20171000520704010783d006082c19058450380c0c20458207021004000220f0010401803a01032a0414008a8011603000c400310740c044400854999090103c01c5005460359038440d4000c4c030104054100d0003025280818603503040d0100c49551352201d0000c4902502c4c10340d00030300e0008011040d0b0030038031411811413841c20300401140d80d401011940d1541c001440104014002ca5480701f03001c0360701a100000d1000401c513142444502140f152644e10503104035070f0486400ea400241c0c141d03954255843c00c401a40902180c218000702030391000944101100c003500c48a200f14020345444203020a01d40c02024039102034644580d082004944140d00a4280901010200416440021040d840c10b06107410000316894a2600b01741200b859001a0000e01885010400d07255000018102036001c0390350728071a210070f507401d00c401c49030192946074140c072506000b00c41d2a5121141c0c1c03508000c400e00340b0721002c1e44d200207 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 897655764 1250 897654514 897654577
    0x12180309091602010c0c03020c01080a021603020312160215090106171b010905030309012303010e04050c220903170910050c03102c0f0603160605040b 66
    0x108624806480c00701c0661150f42445088150030807402c0900c50b035070060300d019540c0c12007160024100300c03000c00000e882c8802a01a20080d81381c1c0740d1403110300f403d41d240194130b941001c05e45c01943e540c15400100114650080303907070118007640180a00468101c50780540c8007004100300300940d201c07440003c2c0202d40d445408072030102031005c0c00c03101e9801e000320105001040d1a80d4104245c422050150751f0300031007111030b108001d00349100c009440f03030045006400003095500e0311303042c080000600345102e84c0215100303500c50b070151095030794034004000300141c22403100c1a10382d590f40b05090ba125460390040c2c7e9480d0180c200b00c0105140619044082402113a00c0e0105800c01100c6010a5510f8042c1c190060104841c050842c5000d5442c0a4601c0c2d146c86021a4101b5040811015080c0390700320b02240300c1010f24556440c5000001060452000e0710102d00074403840c09403003040b480c40050601030b244281c2d00c861510b854640b030391130300c0d801581d0702d0081c101d0381c0c109600e503e181468 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 897657014 1250 897655764 897655771
    0x10030f0b1e042901060909020706060803042903070c02041112041101030e010b131e02070804030b010602150c0309011e0906060f06123210050301021218030909 70
    0xca8801c0fa80d448a60400c50b01003180320300f64420010b0780018406242c105a05105841445000589900c81d038104a03018264662240d8071a0000040c00304101c40910115100c43c031500c9101101e21300032003424000743c4000c580720400901401007050040ca85604070362034044220100e141000b00d00da40140c0c01e45c00640f01118030700200f03400040b065170580590203c04186a00801200c0b0820000c505a080c200c090005007540e207000781e004240031903d05a03111a01c0c120304545a5111349071220060303216000590350f00101100001e212840028510400503074861070f031101e61104008107005030806070110100d5501c8a450a03040b1048161486805103540404101655582841004c8aa07a0b421504495120480a2140300d4100101c29400c1c100c1c40b400185d40034002c8803446103046002810342802003000304080da0b4004861141d80980745414007810003030795504c105402c0748924240c40c0010b52150000420042c0d110051b01c08011120003581d2070b0205960010301d01e00d00c103e = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 897658264 1250 897657014 897657023
    0x12060b04050f0a05060607020d020d0204060b120613020309150a1b12050f01050306070503100906180f060f051e1513120f060b03010e01020d0e010510030f0b1e04 71
    0xc100b101c2000d0f0043c0f6801150680c6c00a2400e00b064000c608180c0700484040c0c000d074280c1042000f152070f5680108018001e0091842d103600071344407a548440415961b6910802c40310440e040707444840d03c2141d0150302a82c0003414202e242d054018018400241040806951801c0003051000e01405c02c0408101c03e640b0143c0c0044082e8900044074009400c0340c0200c1c45030001481192000651a40c018003142011030701c03aa184140304090203420b0300080001800d000c1c00207541d481100d4602002c208a02d01401580c4a81103407000301d07102c0d481180c08900030901d0420032400c00040c40c2e41c1c168280b00c0c00c8200b0013040000700398082810b020fa0408100001024800107441d02c2148020306100d40e60030300c0c000c18580b5424491020740030041d0620b07507100b0303800390141e80c2503000d41c6c15840020002e6440b20f80b0f100b050340c01000340c2c21510388907500703041c000340e80d0320212442e400070350742d01140b1960b035003200d500c0e0441d5000c002031005034110400000860203010345506a441588603 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 897659514 1250 897658264 897658291
    0xa060c0302040302271b040f0f05010f03200904020f0f03062b0201030e16030506070e031c0e01020312091b0907020d030b0310020318011d0712060b0405 67
    0x444c070620030000f01c030b54002030207500020b484400b03510041c0026608686800e03185042200311a0070480ea81c130807940128203000192134002442c90090101500301e50b001d8840c0c0651310450750003078064030185a0400c0e0a914032070031001540507581c001e40680400a0701c01414102c000017171068580c403428518030302c000044200300303081c50300e40d0040440c000201406941d003c003160740f40610f10700d0004024145511a1018080d00004222130116012500b4040c0102075403800c2c604c0e00c54006454040010f110001d01441c01d0400007050321450b501203038940130500c3c202008031807020f611030b04541103000812501003488056000307940a03101400213000031000f000071400c440002141014000d880c0da0041010054000c07440007035080460501041041c202000242058001d0a1550755144044140700000e10390604010045c04010000c1118104603100f100303090003a1405110564000d00e0240502003801044c954204e110300700c04500b040d07840300001c040e00cac42102c000c0c0900b10f1 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 897660764 1250 897659514 897659519
    0x51303021f0e1905210f0f0702030a15051503060112050114090c0a1a030609091c05070b100b07060f0204170a0209071b030e060702120d1206060e10020a060c030204 72
    0x3428440c1c94003411a003598804500200303130203d170b001d015010089594280c0410074203011603141045071a1158002d0030f8a41c0321704140761509010520a40f05008603280000055960111180e11500b0910050041c241a071a000881610504ca48402c50780d070354171100201c00d02c001008032140580708900107081c1008181d8280100e0740c83d19880100100c2c43d419441e00c607008079808482d040203041e10000615503071481d00c98a405410001e00c00b04491030404030700c22503404000340c1003003440b4000440040d1a01e00003103c030080035001d0301c00303076100c100015000600503502c0b1202804203440007508080e52a207500c010302c499440d441d401c940000300e8800442c1f902c031a070581e005046081030440c96003001c2201d00c60700c080074001402d008000025001550701e0600b03407003c4540c0207050b1002e1600e0000703003584826104002c0c03004510b00c0d40110682d84030500030030003a98966680c6280702614001002116030310911401e095001d030030344c0340002c2040c07401525112111a00c0240c4d550f807 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 897661870 1106 897660764 897660773
    0x61308030f0d18020916030e06040c030515010b1902011503050304050109060f0206040b070507061103070908070b070303022a10051303021f0e19 64
    0x4404541c22001141c050010214440c800380240455250790220314800c8406030002540461100e00003100440083c0d2082c80d681110718010070448150341c201810150280c400742d83d5140040014010310008201c500c00c407800c50102d48000758502000f102c0d01d40124150780e6918000e140490b00700324402d402410100f84c400c000881070941d00c0c54461341c0d87c1e00501c2464085211184001451409130704965081d0941c1c0d00604615902c6030342e0a0f00340d040003048402800024002d5030045200c9101d07014000c15505460742e501e0520500107403601d0040e40c4110210b07031000c4001c0c81080d13407040540c0c1c030701c0303906040160705c4d0458100103d0110410f4040d042221a4001c1c400d55420400034054880b440d0482040003282c44401004408140c103090142c00360384243c50b203100080440c4c20088000455406c0081c1c0d1000803d0140e040c0b03c1d045c491943c14400b00c110200038007 = true := by decide +kernel

theorem cover : BRFrame.Cov 897482014 897661870 := by
  have h0 := BRFrame.cov_init 897482014
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 897482014 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 897482014 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 897482014 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 897482014 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 897482014 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 897482014 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 897482014 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 897482014 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 897482014 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 897482014 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 897482014 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 897482014 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 897482014 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 897482014 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 897482014 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 897482014 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 897482014 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 897482014 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 897482014 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 897482014 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 897482014 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 897482014 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 897482014 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 897482014 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 897482014 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 897482014 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 897482014 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 897482014 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 897482014 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 897482014 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 897482014 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 897482014 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 897482014 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 897482014 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 897482014 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 897482014 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 897482014 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 897482014 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 897482014 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 897482014 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 897482014 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 897482014 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 897482014 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 897482014 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 897482014 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 897482014 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 897482014 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 897482014 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 897482014 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 897482014 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 897482014 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 897482014 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 897482014 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 897482014 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 897482014 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 897482014 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 897482014 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 897482014 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 897482014 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 897482014 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 897482014 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 897482014 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 897482014 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 897482014 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 897482014 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 897482014 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 897482014 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 897482014 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 897482014 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 897482014 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 897482014 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 897482014 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 897482014 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 897482014 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 897482014 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 897482014 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 897482014 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 897482014 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 897482014 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 897482014 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 897482014 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 897482014 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 897482014 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 897482014 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 897482014 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 897482014 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 897482014 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 897482014 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 897482014 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 897482014 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 897482014 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 897482014 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 897482014 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 897482014 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 897482014 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 897482014 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 897482014 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 897482014 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 897482014 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 897482014 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 897482014 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 897482014 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 897482014 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 897482014 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 897482014 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 897482014 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 897482014 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 897482014 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 897482014 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 897482014 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 897482014 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 897482014 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 897482014 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 897482014 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 897482014 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 897482014 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 897482014 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 897482014 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 897482014 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 897482014 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 897482014 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 897482014 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 897482014 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 897482014 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 897482014 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 897482014 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 897482014 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 897482014 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 897482014 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 897482014 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 897482014 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 897482014 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 897482014 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 897482014 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 897482014 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 897482014 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 897482014 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 897482014 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 897482014 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 897482014 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 897482014 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 897482014 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 897482014 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 897482014 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 897482014 ≤ n) (h2 : n < 897661870) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
