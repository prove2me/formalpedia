-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_2254
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T06:08:24.113122+00:00
-- url     : https://prove2.me/submissions/ab9fc062-7ea9-4ee1-8d76-3680ae34c7a3

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 405215827 ≤ n < 405395683 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 405217077 1250 405215827 405215879
    0x1c0c0c03080a151a070212072603090411040803271504060f03060504050106180b04151101090f14161d06220903020c0607110d0606 58
    0x25600e0003401038100a09506002820950700703101030000b82c3d8a600031a100d0640315500c80052240c00c02092103407a401a400c0000c130725030628945000102481114050741070107115040310b2080524540011815820641082010350600e1500341c001c1e20100500ca0105482c141c4e81e000314a01e5507011160041c8c01c08040c00c090704109404016660340000281c3c1d11a40d150000010454244280d0142c4020f00c02182d44202026110f58080005850040e008100b03a58407240c01a05040d00b161024510f9031b031034040030648070904019682220520600c00f81c000c1c01150302070b10f107040c405600c41c9040d9a0f84018401080d028200740d07542c180181c2c0c0c0448901ca00c60b00f100d04164000d00e40c20545011a0402c0240d402c910b00c1d900003064100510018039118003001400b03901c0580851280340209019620340003074640c0c030201155203e03408441ea403008207001d00c945409111809083c0a04520a2071080d0801c41c4040c1e40e080c2c400e000c001002c5490340e8040c00e1505101e03030754081c020 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 405218327 1250 405217077 405217097
    0xc25080a0c0c051002010e010506150403030f0c0507091406120c0f0301020d0510060906030b0a0324060902090a1d010905071806050d06050d0209520c0f0303021c0c 72
    0x12030a200300ae402000580d03030494404001c02e000300c4544183c1c8401010021403441c15450180b1405040031000da00800352411250750300840c201034241c02c5003080e980495400490261301e000f50303c00c2d180b52081c6000d46540c240380010081056000701c2c805030195000c11644100da80c0c24820544140d02d0028611101e82c1401c0004010066541002007454070f007030320072991550349580e52002c40e903200150028802e44541c2001d03c0300b0280c0949201542420000304411000b40c001c2d220703400050b00c035170400c10794418207030000100341403103505540184401030014108540025600c4a81d038101500703182401c0c00c0c0318810740c416621100c005903003c20762400712602409400c0040c0000c40d180c3d90a419140c0000700807802c0502160384100111040442824213400c5400c1511b00210040721564600c004682c0284452000581d002080c4840c5a00135406007000030040b54020302c03c52455100b40e03505400075401504404603011b0b90410b6881c981c0c4580c042d54210595641d9032070015 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 405219577 1250 405218327 405218351
    0x20909100615110304030308061c02030a0b0a110406090e040515010803070614060102030a0e030705130212090f190f02130e010c0e060702010309020a0302090c25080a0c0c05100201 79
    0x40faa10900c08000ca8008020400209500a0285810210403980c80700004c2141c1c82407001c0c8410700d00000c1d090302840015005000c0c0c00c0e2000b42c4200507805040c844181541c03004203480c031480c02a0804a121b940c02840507140701102190710501c5041102e04a441c241c64a909005c0f090b8400c903101c0e8000250386003004114007404400315038205c10303181c83c2e042480020707440e8082c0410890030000e40b980c1c8851295020001000101030240850010008045080b4081d5010021401002d119500410110351300020185500200c3c80301034600b410f0322010380945074a2002c0c068400004501d10f010141e82c50703a090346110b0182c14400200404d2040e000c0b82511800441c83c001e10640805100c4207840707120407200840c0e42440c0004a4041610000c0c0313160b0302e5500065040301041040002240c0708800030300240c510398203004004140d0358441001d81c0c151b000c005050766028041c50144038050f0796400d445a106039a103004035034450020404100d60f108107a070060303450310144480 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 405220827 1250 405219577 405219587
    0xc0306020c061816031b150f110a0201020a030507050a08041502010c0e01020c04020a09080d2c011d040b030d030f0c08090604080307020715020706080109020306090103020909100615 80
    0x30003400351015002c0d03440e100500d100440780510014113000e85005000032081e148080f118050107d0748801d112071604c940780200003000e000621390126039103581070b000c910000a00040c0b0740790b05078010b04e580807080e50100e40b5174100d010b046130a40303d0310202200050110010307002904504c0810a60a0385140d0000d081d1141c07000c081c3e0034007071442c1161901d80d07400700380b10308060030a460140c3d035030400d000110343c681050761180c02c513802000d0a5120321075002000520358100d000b40c0360500445428008513541e100c00b0301c0e42c00324520402520385000c10301c01844c8425030081c80064110310480100341050320700740c451000030340d85400c94080e9901c6403048030010340b40c500c2c0ca0303c11403516070f402c141d8628020f03001500703d0b44080b0008124610030400715020b0580e02084080a100341c1802075503d482a02441002c280c2e00700000c20700f0900340c801d580c80f80c0303401040c0c600b0a03481c40c0c080c040c041402078008650380c01184092134103040140508801815140e034030792000c1c000e1070340c0101 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 405222077 1250 405220827 405220861
    0xa0b0304080319050f0a0b060c0a12021204060f0c06091a011502010209130e07030f03030603150509030a0804020f1816020c180603030d0c020f06011e060503040c0306020c06 76
    0x101c143d00e0304e010301402120030030f0794a522160b820000500303043d04500290250059207d0340b4800d00c00c84104804001580c2c100c68002030040d0200d410040e00002144c046010314000c0ea0b000401c0c0e1503c03602000d100b101c014035018094800001c035600151200e480440c002420004114050300040000c1c84e2423150300c3c441c1c0d020340d100031418603078254001110b001070004200d00040e21341403035100e000c3d03050103110b0056503c0b9074204200c845600c1c3c060060040c1d84815513420410003500d003864503403802140d03c65006940a10300d000c55140e002c5c1d820303080107402660040760000743c40300983c44450000044006400c1140b01a1400c080424105e00d84d4640748011504000400095a121459282c02c404041c918003640e43c2c0d21500401e180d8001c8180805405040034000c1c1015500482c003004d01010b46801d480391030b07032290410301c6107030a0303205146080c407041c4c801004828810005550880e22640050b0031151303803a2200d2081c1d0b001110171100c1074004405100d640282040441c0c = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 405223327 1250 405222077 405222121
    0x5070e030d1e05070c0e070c03091d01050d061103010618050301020f0324061201081507050a050d0f0e01020913060803160f06050a05090f0a200a0b03040803 69
    0x1500c20208264100c02c81104440390a1090104820040180144410340a03003e050030104161800c10001000012103241c1540032419031180070844150702d904030540505003400700c11300c84c1d01e800107004101da03100300140c4810f9a520104806100448010760080007290b0b81c24201000300100728615511551107588030f680304104101188800a0a07a58030107101c009a2035a03615a1341a1199004040c100b00c0e401900011041894211191054142c51a00d800c9491a50624a02c8140e0725001da41d050041103050006408031403003075004002040010b58045204545002e802043e585007100f0101f03140d401150700440c5003449035800361400811441400043d1900400e10348034480c061080c8107811410740c01100340109480c5280085510050403c958a03060381c0c0000207107415580d0304924000d600d9503401c8001c001030003a1019810411305400020010b03a2102c01d451500d060540125680000042e44c94540b00a548100d0141e400e16640b40351071712885e4902e188480c800 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 405224577 1250 405223327 405223337
    0x90f070e04060e07090c051201170c120c222007030e0d0b180c0103020a08010e071403040813050a061209151104050306070f0c03180905070e030d 64
    0x10032500c44645816600950403240020350303441150803150410000c0d803ca8114203080c1003010320341a9100c4020404d40d05209103d25883e40c80e039121394038070441010b01214540c072004400000d458800c80344e47c020b00c1d202d02140c0e041d03008080443c461241c007020403c012094a80242c1e001821801056001c0f0381c680c052074580510001c400c842406100c00190802600da9001c10a5459070310a8aaa40f904074405070300d00d1400030791041c0701ca21115172440c0700380520b401100155019000303171541d94846495564507603003880f079500c070000e90080c144000c110044002e0429258081d0003540100c0c0282001c564810302c40c050043d81285031340c0458001c45142004010303580c0e11130710240404400d8803000c2032035a480e041c104110605018100340d007034a480e09141074038000c040180200d80c0240e090721815130f103110013541c4016440c01c880020621517200c0a000074450804a00100f540320100c450307a03038441480000f05c1d002180c41202003003903c4900c2d00385140c2005400b0010b00c2600c2c0c0 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 405225827 1250 405224577 405224579
    0x306060109030b041e0f03090506130b0f04030f0c06030c0912080904110a0207050405061e0d0501020706060e0108100507052d160b0c070f020108060102030d060e090f07 74
    0xc1030940c40b0710000e44070381e2006000c0340c20007842d0721001820b03098802d04a103030320415007061421040c0c181d208070040383d82c0709400100c0c1c1c1030070000d4500b014000660490041d14060248105a02c4210f5076600d02c001004080002513036462000411402402c554001e2070620101504480c03007160408144444408208002126180154003c6920090301da8036140d030b41c0003003400b41191402e02c0c4030590001c14440314a50380010f801045500844082c070003511140e060002c205211030841e6404400241d6080d45420f01c80091482588030305c000514260454546804a8ad416000104205008030042103078010801203c140100c88040400032418640000b40c16407140da44480c0e0183c628603004921210140030400c000c0d4520210580c0c2c170840f00030900e60030a81c0b60021200034a00714049401c0700c059000740c1d918194801010000c40d04c0a800545150000620702c0781148010003a01c1e40c0c11486004100003802d0703014089029060421413941081c050103d01c1ea035036405500 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 405227077 1250 405225827 405225829
    0x200304020609060c010e07090e1e1b1903050102030402010f05032a1b03190c1707080408150906060105120408090607080c0a03180303050a1101020c1f0506030606 71
    0x20807610103910843c3e041e680c400340048440c0c00341c5000c2000001500502e10005410f100c90b80040c44c1c140820001d80e5445e01484084409600990b0f05588043d0f0113415070b0302e000306a2401504a0860003007450388041c4d8004083d00100b50380750404c903580d075000320600c41156007108500d030200d402130030068254038100009070034075101d44c0c50001501c00307020441c0404c040c88400b120303400c0410851410202c020942019035940c00761140c12414404004c01b907801ca0f1281c030260072050740c05407404d20f2480f8007507107400c2160000782003641d180310108000a01c403402081103000306400d01c10454018540107503094145000101964144601007000ca641c250001003065440741e80903201544a81b9000c003c1642801500f070010401d8100050440700d642000550724a124402d58400e0346045000811140c1820244401004a8014002605068020301059803100c90701e038001401d228280014501d009480e80100d00300b041d29004100203a50103009555111800703600a26090600d90 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 405228327 1250 405227077 405227089
    0x80712080403081302150706091a010608280903020d0807110703020d051c02060412030c0905120a0c0b120901090c031704030f080301060f141b0a0503070620030402 72
    0x4090444460880903084c0c110360300e09001c284590044050283c44c0d10103407a00380d0040c01400f00c10303038404800728000000c031080c00c0141030603521565620280c54407001e00903102503803071126501d5000d800c80c0301d00091410512500600300d000358003c02c02e0400c0543c020b002980041c20f44000c1249485104030540d03000a0b07020200c960581d01c020307854032a42040c07402c0c1442a001246040c60251302499016400501c260140f8011070f0301c03820350410f00b681501160b00700c0e0400c201003498084100a0351520304040e40c01c809509041d0f070102e41050341c1e00000d040d940d40050b003040c0301c085003076251860810040c0342c0c889117241c0204040d01440c4c5071942d00f4841031000134050030100300450030803101c1d0b030107590045900c0f071502207244c5075501d41100f0030f4009000706400a021001c03500c40c1d03070740f0031000017030140c0d4025006481d205910080101552000844184d2485000003620003d00208000d1107070318000c1d6000100c40501600f040c0c400d060134105007004100901c00d000142c0d40341 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 405229577 1250 405228327 405228331
    0xf0807050a0c03021e010c1d030606010c02010509040e1e0c090c03060109030c090204090e010213180204170106030c08060903040e1b070308070e010f050403060908040509010308071208040308 84
    0x141c01d00c0d0322500843e1400b02c0c42c09a01120088603119001c21494003402c054111680d40c1c0715680320300c2c141c0505d107241c0366028280254801d81c16170007400820f6041d4007544208070070f80e0040c9032140c0381c4084130340401c05aa088205c1d0589651100503006d92840c0030200000400c40d0650280c0350420300200051020740c000f41a0a0060000101080711680950980300c02154010503805040e40e907141030800035045803080548190030031401450791441031080b6500d9032056040758240c1e80c1030a2610b058495440020175120760700300301c08100d20ba201800c94040748801c10010454a0030761403c0800101c16a0100c4c2c202c0d442a018058106400301c169419203600c4584e45e045907566000c81b2040002030300c0c2c0240e00c10b00005004041c158089241c61180405440f03441c400080e4000454240529000c11000a40203210610010b46d0942003180070a010b0703402181403a460310b00040d00018282c0c408c4502c850b00181000c10080d054140c1d03501c0e000e440c106002940b8140d200903040d2240 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 405230827 1250 405229577 405229597
    0x60601020a0503040918140a120801180b0112141015050f09010c0204050412090b040f0b1309050106050a0906080106050306040906090c0620060124020109210f080705 73
    0x100d400005d030000106d8940503046401c12409540b01d15040c1c00c0355103400310540d041d81c2540c480304040342c0c2c032070181306980d0480c3c010303406044603441c0c940f80160085c4000d0301082e04004040c00c00003005c0100d40518a0140440041202d25041503541c5550030609503102c0c080314480581070156094102041d038502c030015111a0790386040900c0101d8a8000c403200c02940245404e00b4041444500105502c00e010700b615810021512060f418646001d44e00c90220054904c000504c09020301da005409107107080091070781205c0e201d004140030b451098004900040010070040c90791640f102c1c0940c010040303814445140d506061000313185202c010308075809592640103881c100203250307006440c99a0407000240440d511003400424050410f81e1203a0074031458000d4007101d132070110391241210003102c03c8054102181c0040801c0100c039924a10a655942515a012600341801c403094114210048181104400005404d08080040c030760100600b100401003a90b03045800c9595091b0 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 405232077 1250 405230827 405230831
    0x1b021e18092a060307050d0506010c020916030f0203070203030603190201080408070206071401050a0e0318010c210503070f1b03051c0603080d180b011517040f0203060601020a05030409 81
    0x1800c003480b811100b910401c03103a0400000402c2010665111000e05a40d55480c4ca040c800307078544000444140c010440080d500031100404030b02c030f001044008003041040c07820003140708141e410b08482243c00445940015070000001c02007a4501800807113607842129161035424180c94000030014000100001c00b0301c1c00002d660b00a5540c0c0c602034500d644d901140c1c114104500550081c06468140ca81da010325003030a007242c20900d070100945031242d9901840c009505040001158401220341c1e065901c011400701d01e13030103460044411400504203480d480e80c0e9040160b002000c0441081c10001040201c1403070328808104000d00a40c5643c0600d0000d44235100c400381d81c03954420109031207400c1450564000104960350001d0040300003816001c201e11409401201800000f02d0b00080c1101030840040c840e00100ca28072900d1040a441d080300000c0759650600c004c0d100940e429600d06069040e41e10031841d00f0070081c1d600901c00e2018000032003061b60317400d90328001d0f4001c40d0a115 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 405233327 1250 405232077 405232123
    0x11070b0a0b060720100207031e0f1712060d08161e0b060a060516060e03090616060b1c0b04050c270705070201050a1b021e1809 56
    0x40e8031101070b0740403103401515000c1c8800042d4060b820003040504894010074205d80200900d500102d81501126000380b5105484a90140c80588000100c202100c10a5018a1180c0030800c0a0441c505646d440d4091540d502001c0c445a480b0940083c6460711a0089101c0da20000749400252000984982030100905080d0310f415641c080780760070780c11555400d400b20312080c0310188010710700442090f1844061151500c0007114103100b141042c01c3c44030110303802e060010303805074030a1105001010559041030400c4000071031a80c010403c00c80e00141141401d01400030703138419032542d0b110454409024404e0021400f10141051401421008810001805000041c4110100c071040100600ca4496046015401100c40e05010b0f41e41c0c090b0507000100d0031170181003100d0f02c41303805854050a059440008a94121091440d104004400c42d207003c010388421755103803a40e60707450031901180a10041030100145400040e00280c03605081404151200132441c0800c11a0f0078141403032350 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 405234577 1250 405233327 405233329
    0xa0e01090305010510050108160801170a0b130213090b0a090f081209072907111e03010b040b0d020f0607050d0905120c01141e040b090411070b0a0b 65
    0xc0403aa0000d03045500344410804941c141d10450001c1d107109032580c00003611003804400404004000c00d0002ca18000014860252a4541009200001c00403075030f60f600242d13968070100200350741c0c0d00b10100c0c19106200031841c0c0704840107155060242c04100740c0c0038076200c07801325107005050f0300300c11030740c40e22100240101212035000e9281c008450507034921001d1650344055600700e420380340324011400f02181c001c00e51404140185030000060000b090488032480e03e81e4454001110060340710701554010b80c179400d40303000b01040c4843c624103d12080c0d105041c2503401c800c0400d8801c51601e85109603039521601c1e03221880360103582401045c040c020106074944940e5001505920840c1c402c80d040541c040c04810a641d03064034011a0003171a10412a83c941c02d2003040d0340462064424120080f0141c00501070081e2030300c1090038941d82440b500380c1d99602a801c80d9240800000708071301300781464051340080d0703501d0b0040c4920b00180c2352504010408064801810306480704501c000c0303 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 405235827 1250 405234577 405234587
    0x1c061a040e071401091d1b0301030c090c0e1206060316050a03150b03100b031005130f02010207050a0b0c0705030a0c092c01090203010c180e100902071208010f030201050a0e01 77
    0x1400415856000206440c401e1544c1560100c40b50198000d50580c0d2011015911048c0c0e812241d01c0115171210900341743c2103038003801070f400e995000c02c224804404d60035034541e80c1d0320190901d6000500301504011041c03506164210324000403031502d0344400c1090741c541d1106023084a400c61031400fa03003210307081c04002400031211140d03850303c1600e2413060100c40c254807044188000320100d0302d030760a4452400003600c2048501d0700180d252550004081102c3e000d44407800f900c144140c1c2c2146440e81c0006201c0841504810300c3c81d8004158242c9000b420031013100508012401000341080369540d031141c20445004a0843c5512422060807900ca100c1500d260f46000c00c651800030b80308009118000d1680c5003050b8407c0d805c02c04c4c601c100c28040c0600c0c82c4040d01000491504031b0034480e601c2c080d503a02a0556800300b070681400204803000384080c240c900e10404002c8c00c40c0000c01c41c001c0c403210041e0045416038030301d4982000141c1c1c0002c1146c02400300e42c00c103040c0748100c07400103a803 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 405237077 1250 405235827 405235829
    0xb010815090417040f06020f0a1e060e070b180901120201050f090604091e050106080105040b0d06020304080403050708031908130501060605040609090209090c07021c061a040e07140109 81
    0x14070400450b01061007001c10f000401071b50000e6003140c0101c0041c82c4c000d5902e0000b160003401442242901d8030000540d9400801181e00071140840c2180c5a004103515003699a40311010956022502e80a400c03500582c0b0042400c04550300d0030107504010040c1c00066018074000d040c448001681301c5c0c000c00e241e0a550141c80020802078585035078230304140c00b6007074410180d00400181c40310000b91002911030b06050f1b984941d82c0d078029038205014817005100f0784040c950b1140d030384200070f4001001800214401e503c100c5801c1c2e01da900d14504540340c040c0c02d810448003504180403403070040e92000d03000c100c0c582c03180c549100c80f5124958403c404010005029003d94280030000c41c00170b1f046001401200d05582d10a010196603010001c2240108894a6401000c2c00c0200b0bc1c0403102101514082e40000d00c8409041400d030941441c00840e80c40455199446190600303142d002492119071019040d6014840c0381640c100030b90b00c80c542401099040c0081c0141e403406a485401c02c04 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 405238327 1250 405237077 405237113
    0x6010b03090715170a0c0c030f09030f0c050f01110c04050a18051f090804050f040b0618011b0b1311030a03020c030601050a030209011a2502040b0108150904 69
    0x99010000c80390700074402c0100b240284d0310051081c1c0480c0c4080c400c4c0c814200c0c8405980c1ea201913960300e641e03044a8a0841204400810503810008004540100c5170400c10509c140c030200303201d5141005001186062000c02818001112031a0204003404621540340480c21103000405a42d4030352500001c207449000352a800062743c800100300722000840c1000c0140e016030880030030704012520b409a40704c0c450010325408040c80100902e040002c0800310104005101145040c1d5103c01700e000b941107000147c0940e01d2403528503a503960004d00c0b1f0300d00c04420060144580520303880700c180009024040c0465990084440800e110000344091050b146c002e0070749032540310b1030038025652840107110034424000c8030700006013841c141c0002d108983c0c5c05002c2d048168a0880c030504461403d82a025034603608102d40a44590550007207007040032981c4c0d5082c928001c0c0e0045c001111003c19010707040c0120013060007020101205034403244c0e803040b00c420410f40d0381c41c980141030100800c159 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 405239577 1250 405238327 405238349
    0x60e130b060d12020606130507020703031110090f0606121703040c09020a02010b090c0c0604080c010b0a030c1404200a030209030f0a03080a020301031a090f0601030501020d0b04020c06010b030907 86
    0x9820f209a0103d00540180800c0b01d0308010681c01d0000720f411140156800e80140c2c1c000001000013070300038203c4d0568180d00e501541c8100159140d1f41c41903a040580444003080b00071009000c0081d00d10401016004000d1400103088503550b4405c640070440728480074000000c40042c003000150381c0e842c0045d00c0f002c0c0c2c056448105c0b610000c0e0107480c426501510502c41c0b01c000900e05541c8500f0794656151410003043c054407252104565076211035a07645084d501c980e031507441703070711100c5202008610071159070040078902550a07581001e81c6c04020f10030343c20804040424040186503010f010900740b0840d3ba00c00d50000250300a00c220051507805000e950a240103208001c6030300c4c41114000d403980c214036070310791503068100e00c000d02000b4040c190010001501390300c0001c00301d60050b020400c80b050326103207030382c079502e000002d903c222500d0703400044200140c4110b0248002c210425541981403090028280b5150401405544a00d00d804400515a07035410020517000306010782d01 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 405240827 1250 405239577 405239603
    0x50703060509010b060f0d0c09030b0f0a0b03010513020f0d061b09050d050a06180605090105100f08070306230a050601020c0d02031f111606060e130b060d 68
    0x190207010704580c0440075501e00442c0c4481810004100da0721244031055007132038000480c550100a0400311200420003a2700e03040400021000014a401010706112241183c50710b00b900300c0c145c5a90001c1c0328080c0e4103180c03e00c2035400c4812103040929a046410140e4112030070b0219426412400b00500f103d400e01c0e1881e007400310b0300d850f940c00b01c003419901c00c044240c4882c140195404030b0075004055910881801001c1242a4499810040501c03a004d200131155140c0c0c0c4150b50b81030b9080d18680c2d550307500340710a1750348207030144009203141078928400381c2c680040103845034a18032004c0c006c0c54482d905000800f1000c81840801018000c510031030741000e03400301c801044201d40b11400362041c03c003041142d107448051011240d9000380108010094944070302880b900214080b481291141003c09520900c84003902d41c96000d0200070ba80c40c101401d00c44191001d590000c00104007030814017a6404022402148090300042440d10b00d4031000040f80b04207100d41c40150083d004594 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 405242077 1250 405240827 405240833
    0x30915060605090f060702060301031b0b0304210905060a030b040e01020a08070e1c03030e01111b12120c0a020a12030605040510080303060d0510091110020102030709031e050703 78
    0x101800c1d801105139042c03505400b000341804024800d200029611030001c0c001000002d42c10310341983d05108000201880301e0341c0b81503c82d079540090306c0455404607242c1a02d54101e00c0ca0064004c8200c4c1451b01401c0c0034034100120740c0c2442503182e101c1c00c058640c44015102d03102c9030448220b0041d901d000b11b58035110501d00a19403542503d61400042c8104001c1c00b0301d28010140e008840061881c003003000035030384c1e010f40041501c001031542d69521403074400510035030100500200080d200c03160381c01e06121030700c66040c011481401e800d0f8460a01c206201090440c407400d5000f4500120700e6074440c01100c0070f902d000383c0318000803c03540000e240b00c5c0c2560780c980c1210301200d90680701405207403504202e401c001e540340d026030710817540b0500000d6690b00e032542c00c030348400d4060381c190b07444100c0600c120000d803250b441043e640c46802c080807500f1342c105070000640c00b115a100071411814401c40080c0000ca107440054003150410314000d551761a0802610307504c5520804680c8440c0d030300c0c5 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 405243327 1250 405242077 405242087
    0x12102070b01150f05210f01050120030403020d02120111181c02010503060402090301021b06341101021902011b120509010b130e0601091b0309150606 66
    0x80c0440d003494030034000150300d070549804540d003d900c1c0c0d1600500510049000c50310341d0028420f03002c1908215964500301c0481e44485d0780034009107940c80000e90b04000014100d01c220460210380070410712401900740c0b00c003205403810742e941203036a44490007943c0005506002c890030a010343e540381c10120050344510741c0c02004070b02c04124500c200c00c880c5004001c405140c0081b000001c201a0200c10010340c8948001c0d80d1040b001400103080907030748400309089800540c020115800e41072584d8003400402c12002e0350040200d040b20588880541501e40502d84000400800c018290101829203001e06541d0151a007110021922120751440d5041d1080e481c6181001551070f08020300044250001080700243e01038541c0640321120300440d00c014007004040d0700c500e5603250740f11038096071562145441e54003010808a0819026443e2a0030800180c2c040790b40b003840d2036a50400c0709404a103403407100c40c9508002500d03951300d051050303c0180c2e80921030000d91802c8404a4116044 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 405244577 1250 405243327 405243337
    0x90702061609061706060c0f060108011a030d030903050d0c08060a050a0b0909060307030f0b0403090b0a21090606120303060927110301020d061707180209012102 71
    0x200036240c0c1c1c12206a401a12404500d0140000103070300d0b0074103a034400c05110845600480301825140c60010140350321410400b480c1804550b075009000100301c008001d000340040f148454a26290303160b9094000f07036840808446000c181a00c0c2e803104002d05010340c0581d00c0d08030119405120110340d8000040011004442c064854206e031000030803270b81824140c200c02c1d58240480a440c0c208544c0030084020070007400070798103210f6020080002070a1002d188695031203100040d982c0c0c106490040e120a0302c540015a21102c2030040c0706446a000c491a42d200320103100c0100a107855207045400f801c0c2000b00a0103031401e2020005204c215400e40c982210f01a40c1c0c100620790300d0700b039940305417085007640b401e5002000083c004c1c02c0d1525044002e0445c454107164009280b01000b180c03c2e42c000548100074a40d84143c00c000030039045207041400c404900c05172a86e1418852466100c140ba1082d10301c826601044605190b40503d8030102a1042c6101c03400030902286400f001a6101d = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 405245827 1250 405244577 405244591
    0xe1c021e01080a36140105070818060402010302031509071d030c090609180625020109020108181227010915120b040903180b0f190201090209070206 65
    0x112400041c0210264440c4c1c10350854020079100028407482c0c2c0c41c0c0054840c02d80c402600142180083c03000661641700301c1c2e01030110400202d56440c207014041c05241c0c005205141000030f40c00c0b541480c12001c00c0c0713280d103c2c0d8242001038503612207491410303620b40e0310707008141c2040c410424004442d0300820408100802c01800c05021444402450f4452101080107500a441c1c0c502041c2c42d480d2413640164002240c410f054204403040d42118607121003503030300c84e40086400c09040d4520046107003100391a00c3c0390000340203001c80342d13000a1040ca40180348030304096074480e100c012500c080c000c041004034601a0281c8441812011841480000d00c180b03000d41c15210840300154041c005000c115211190082491103900d50180c441c800602c000180050ba1043c40b4691981d85105000506010303130f40e204800c414507c85411112040e402959840405101911103940060101c80e07852001c2100415292141c02c4142d0160a803040c009521112010411a55079400280c4900c1141 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 405247077 1250 405245827 405245837
    0x40204060506090607060209040b030a0f02030d050f19030e070e0a0609090f0f2d030206011413020d0e1905010c0f080f090a080c0102070b06030606010e1c021e01 71
    0x141d61010080503124050040d50010401c2c4088000303c0d172190b02400704040040c0020412a20b0702c40001e0420034003200458071045020b42c00025400c1c00c0150031102c0d00581009031601c0820641c0b5240c0303010301e41110380e5a1411445136000d451103174006840d00d0114008a4030010f4580716401c0c507000c0110343c0b0031046031820000203021079003801101a09608042032045aa4094551041c0722500a006886c00c0e00007402c0b8002d090302d0a080c500c1c00117207401d11041c00804c0c03840c0090821703406a00c0045242401520354400340c0d03c0d412038402e03036816a0401030340c8182c85608072010b8812110380345114091050701910795103200c500c1842c03d41c400d400030031814407080400d4890f202c19506000009600000289208000d10300180d048081c0d04c0c110741811146a468110990200307039500e01e641d401148481c200086440f6442d0084800c40240c292031415074002807179104405440c6114114524500c140151306d20501000590090030f2403031007064951507001034000d003210b04c80c0029 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 405248327 1250 405247077 405247079
    0x6090609040c0e04050a0c02060c0f2208070324060f0b07020a0801020d020307020709020c07060c060216050d171e100906030501060608010b030f010312050d1d06100308120712021204020406 83
    0x21200004880f8040341c0c180402d420442c2002003603500342109841980c0cd00504180400c07a04010459500110300c0390886050300d04030248000f64405070300b13440001040c1000340074803082000c465980e00340e410007217038a600d9681358000a840d04007968800c207041e51002035002100e085580046101c0c40c23241d000c481c07040303540c0c2e800001240304850b451045500034800511034144100000711030b140c0500c07009030400345124443c00c0e4050002e28100c0b0aa446141d44415035074111104c480810140d50100c501d9180c950400c1051030aa14541e074555640c480004890740381000600c00500031450042103070980b01d180c910f0080c003003409510b012583c40740000a000c01044210713841041d14504241199180d41c0d28054040d000400d050203121043c403079200d444400344110740b5000ca0b0009079221445181c08070b90b06000010342400f41c3c13800103410503c0807441072012030f080000c0c8100f0100175603503003000454004529503c440c8031f45000061540c1c110407820301a601450080701c0821841b = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 405249577 1250 405248327 405248341
    0x40506010e130b1605040b0a0315081902040905160605040503011a0d06200d02031503120f03130c0e0f070305010f030b1e2406090609040c0e04050a0c0206 68
    0x18104800d8003e106159080000d94414551060007000750f10a0a1440c203064907800307160155004040408002239842401e29107c03807038a040031004040d8040504031883c4800a0203003100c81c1240302030302540e111650481000301c00c2024600f040b10820084103000d071503040003052070780548183d034865800d01c441c0000006004c102d00e1042c1c0d200902620062600b5074500d40500030080c03111284040c07400840002c0303400e00c4020714001140d00e10040c1d40b490a20703120a0200408480c20303000303900c000c507003200d410780e408203da05600c0184c0ca001c0e00c9580703070001029240070440700181109100c2ca00051100340081800c0d000798040c024006290ba20b40c002202250703003d206603506049009000c00128504082058120040c0000c0a04541600e000304000480030740d4868002c85134030540c03200681e5064002031040744112580c6140101140018809000e107400d0148100e50351400b50038100e001c0c1141d13624500000d070003849a0700c0e10b80c1110000300419400a00507009440c001240c03 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 405250827 1250 405249577 405249601
    0x40503150a14060d020f0a0e1317130302062d09010e0102010c140c07080d0e09072f0c090a0b030d090f260708010207020406060c11040506031203040506010e 69
    0x1c42c04024220702615804c039020861113801e880c96203038005400440200f00c01070030303078400d901c641440310381220300d18604d10b800402d100140c00280c00490041c0406042d17034120504030001c89404803003141d100d1b1a030144000280e04040e140780941c0c0d11003d01c01064403e080060540e102c426280c043c89846c1e9017005a0070381d29049001400101f03890b4a2040c452071001c090315a002e080012142d5035a1a14940342c68600c619041001240c00007400302980e04d807100303800340d002c2401d01d41030183d0f0460ba401710b00c08036102495200c2074201241c01c00304078078040040d21510038006044c5031507030034601d16141c01483d0903c402c078003138020755443c10075650140039610112440c00d868100b07030701e00c2c145440b442e0f100c41042d11001001c030380881111110301000000081d103101000140d03500e1041c4104030848105511880c14044003440c02c1002c1001403843c01e00200d001d4801007a942c0e1400d0001f41070110040184018900c044103000a01c440094583e060350520950280c59498188441d18 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 405252077 1250 405250827 405250831
    0xb16060f050910150302030a05030c01200304080a0309050a1a01080102090105070b04110a06080a06150e1909110310140607030309110406090f0b191406040503150a14 73
    0x48680e12030540c900201e03140e41d00c0b60240c801310040b1418003a45039400a4100f40020600790f807a641b010994225520080c070515050040701c45440807550200d0040c42800d010080000d4028400411102c809030b00039001584010303807280030364440d029180751681c1401d9000c219150130351094000850300c00c00510850300511016102c00e410440301c1e41c1c440300d1200004000315129000050380c140706403102018200601480c1e180c0d000545850b4203d002250300702d502c03c50f080500388581c50b403090b4110303200c0d040e010300950f040c40c2660315151006451000a502002000b4500b0300c580342814440b202030f500510000d6440746141c1e9071903100c508040c20031600140d115804000450010380a603201c4c9040600c1600000e04207041a0300040c210340495008500d401c1e200d4861074211240380c890001040c000702c0b4080000d1002400d0348131905500c0c0035060340d44980c2814840c3c560790f4207003690014007004088400400381c8002e203038078000c001c0e0351000000d4104000f80c500c2c691000c010b18 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 405253327 1250 405252077 405252091
    0x1a070c0602030c1005130c080d030b0d030c0803070e13020c19080306120a0b0f4804180b01120e1c050c06010807080c01021204050d0503040b16060f05 66
    0x100144d02c0c0500c07010001c5c503015024030292100c2815003c006105080b5a500814015020302000b81d804903010f01034070100360045102d0042500344100190b0411100320340c2681003d0303141c1d140d43d00c2c101c2c19103510781600b007200d42c0700c06200d40b03102d8604016001040c075050391720241d030802c1040e40b01103a5849000d40000308881030031b01c002801810031440d10300c242010001106c000807181d440d011a0030307005a5481d100701c0084010020106400b070046000b9148204a801e8450b01103403044030080001d110410804006031031444044c0b0048080d0340c05000c0b20520140c650300c110016a005103056112140480e54064400c4000e40c01441030030980b00000014296040710f110341c0c1390b02c0c5c00c6600041c9050103001e100060b072062007001400d02030204040280101e504184100b8680399071a80d8081c119801a07110301e00c004441b500b5201212400d50b401d0943c800b0380d29000e402d5000366008010442c41c04a401c5400501c206500e10a40703000d418100000040461b541d0300b0703200304540e99 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 405254577 1250 405253327 405253333
    0xf181506030207080715050f060d03080f07172d04080706050a110705150901020f0706051012060b1302073c0f06050705090d08131a070c0602030c 64
    0x800031103010750010901680301d84030030340c5407900660b941448650881c2e0181c500680e24402c12500300091502c8640182c021100071411800ba56030003440f0b114010409031074207494201003000c0c2e60003941244051070740c4010100e42c038a00b544500c2c404840021500c4042021080e520003103002f0b4916050140703400c8156103142003066110340020b484003400c400d040c26503c0100d6240850b03001c000d001c074240300d08042c00054801c03100100c1100703405400003101c0c1c0d10400c031150305c0d16005401c84000544c403a01c013040079620039a114014400961100400820203080c0c54100820b5501a010448046808820030b5000640e0041280035002d0010207070344582e502c0301d0304c4c10704521044408048a882c2480340e00070180000c0500c07425a14110390ba40c1203608a0800c00050307024455011059140080c28070040c180003e00d41e500c010005000a0303000100c4400300c10803460144003822000c03c2507140208800790200c143e510401045d24030b000c1c51140072928502c04411078400803005001 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 405255827 1250 405254577 405254579
    0x1e11210f0c0a0216031a0708070c021309020d0302030c060f01150e1f0c021e0604030807030e10090302030c1905060a0207080114010e010b070b0f1801060f1815 70
    0x402141d03510a00d03a50055118401303108072011012100c800181d84559408003402e1099646a40000300281c400414480a00d0801025640c051b080083d4a0b404131750082c2c01c29a145400c10080c8100100a90480a010310241c140340d0004010560242c80c0c40c211051507807a42e00b0121072180a00402d820040f049401c81d071001d1045c410046200401804107251303481a084081100b40410601d03000715641082500079485c03c1072108042c0c0d0350700030340008070040c50000500f00d4400e50100a10590001c2001c43c2454400c444030701140b40e002e443e050a010401c0c4020b07022007858401284030b0720400301c860b205800c002c1e589546400c0241400d40e000740c1890100081178101e04a603000b148546d01c4e0000d83d05400340910b000b2001540c00111140d410b20f0700e08840b4941c16040a078984104210503000214000c103646d1740511941c1c103500054172120885803002581041071035045d030030070b1004150101181d4030039048480440044100386913009040090301c1444a00328012010450 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 405257077 1250 405255827 405255841
    0x503041a090a11030c09040b1b0403170a2610080a0c03060507020c180108061008030304060902060c160603050907121407030b0703021306140306041e11210f 69
    0x103424061281c0202503405c201c004e5004646c15140031502aa500300c07290301840300501c0401e100800700015a07070900d10340360540d00c8100c0e40240264030360455000004a21203081c0c45080c0b41c54885035007040307152100041d8826515071034420b0350408803a6004005c0003c03501e0f400180c0090041e8040841d44040f0301e0754440c0001044002c003802c0a500900d10100341603590041d408048089440c203030b19195041504961810400400404100b040b80070140100f007000400c1d04c0d40117074004000f0400071054804281213000d0511b00844070700c9103040c0507101d0084c803a5200e00740e07040c1d82c0d410041651102c3c0d20b50360b522084d204d00300100c41c4880b050340209007680d0100c844500203c048a01c007565a45d90481060030490b1804002035001c02d1888451000070002c00003088249044481d814044514180c00c1c840580014411030b070710442e445804103445008520118041c1007000f034007500d01e420303142940c80085031018100081000cac5281c08940e0f01158010145800d548046a448503 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 405258327 1250 405257077 405257093
    0x5010e010806150c0111030a050f0402011d030a080a02030304121b14031b0d080601090b0a0309110a08010906051b030f0c0909040f03110105150105090a080d0503041a090a 75
    0x30440d04140c2c00c101300e55181c50300c0174000d030001241c105000039501c0c54040b4a40044600140401c2041c422420501c00943c0e84150002c414122000c880b4100380741c51400246400034101c401040b048010a1217074980ba000b001030351169028005003c00150094021610512090380c4182b258007a6102d0b00082110100012032254010b0100c910740f0700310211030785101044544468031b0384c1c0440e55014560f80d0100c081034003c01c007030811f140359a092004052560080022060415a0f0380f50103000344000401e07281e0762aa406050009110f0b1034420300c9011b270410030426640c9a0038107001c02c11b004100204075101d44a21705090307083d500d55042d0410b054501070480c4000010500650000ea0f41d055461030203a803251401492075103a9141c0a8102416040301d0007050340340804225541205076008540380809207010f50f038900003080003d500080039004054148926010403003804d130007100850040d0300424070701c0e0341d645013214040c5580c80101d0b010b010f03e8000521202c0018446 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 405259577 1250 405258327 405258349
    0x301051816141c0b2410140915180a0905040b040b0702160e06031e070e04030908031c1a030c011110020d0e011803090306020313020d060507031a06091002030c0f070e0105010e010806 80
    0x1d01c0b50608449c0341441e0030181e00704111a41300300165007855003031850440b55140c0201941c507070903ca03500c2c3c20344951000032070060000d00410110070000c1c811a200303003c0700419072110012010072607211424800e003201b045403098000e1003010120401811109104411a6011801402040d040c01e0040120440c0508100d007446403007240403d07403050600c06404260341ca5001e0708012080c2d4506581501c0c0c9050181c07084802c400795442c074980380492507464001d0282040d41c0610b010102c13261811a211070152841c91000c9130042194000d508441c8642640100a02101007400c120340103100403150f0040101e10751000030000126240c004d554880c0d00c5405041d00741c0c103980c021959200051900b12425990b40041104c1c540c2c00d803040f86c040d03500f02c00e0340e00d9802061001080d40c91240700b030420f00c13400d11000f0404426100300119491805110250b42c50300508081a035900e8115005140c5181003182c00404e055104410341c12003014140d4030713820f280d1a12401c0c0114440d074 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 405260827 1250 405259577 405259579
    0x5070c030809191215050c0d050916030309080d020319080703020f040b0307090e0105060a0804080c1516050f030a0c09050301051816141c0b24101409 66
    0x42c1c08010210441c3c0100315074010580b010414a2880c598a0f203043c001c8044c2c050329042e585000b0600080f08002001e66004802d00000082c0385d450302071442d03190000d4640408800307a0306c6180402056440041602118100000c6507122008900266100c0c0201d04549010304901c0030f021440398462844540c04c03000f6403c6c01481c00c80410480c50f5147e200e5040214004000401d102610ba4001c0011006050052800c9400d504010004100d4480d010640c0108980c26001c1760500a40c00202d400d440010000c0300c1c8003006d0700442a449000490340103a03403514802650508900409c01c03904a01c460246503481c40d40e4144800d00100410030580c41003100c981d0000c11661802d20802c0d009070845202e41a165038407843c41441d1641c21204041881504041040b844900807135500f41401d040b504940080c0800c1c98555041800c003401070902c0042d4020b010701340d502c190459507441d0802c05000d420000882c2400744517200e040269000558110000c2480e010b0b04000e010103440c = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 405262077 1250 405260827 405260839
    0x6010f090503010504081210050105030604090602041206061e0806073002031008010e0705010c05150f240a03060c030b060301140306010501022a04110c1b0105070c030809 75
    0x40c032200400d013103800840301201c4000000900d042c0790302e1752404c420350050031070b98041951130612000034403d020103040503003d2030703c95030148104001d94040d28050021950003e00c995428241503003d04505d00c28030b49004082c0090114101d8424111416100c1480040005031140382c0300b1143c40e842034406100800c41c0300003c0035000010240b464100001c548096100c0c1040303440c008a54540340d0295a45030325281318542c0054000c68414120350003400d080350742503e1400c2c05401c0c04061503030109400090010440c0d5031400406450103400c0c006176160046000c4040d40030405132048071194071501001c020800074495070403084404000c0c1c980400c410b801130b40800c5168100703811103030b10340700c00c210060311900701000b50358010007003440200710080458000070301c00104801d6640601440c81006903603a1603030f40000361000a10484542d03546600d4003819102d920203550000c50441c5400201515881030b4251018940c1089480034004c0c51079407543d14540c419091550025 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 405263327 1250 405262077 405262079
    0xb12190f1203090506070c0c09050907030503040e042d110604152c0a0b0a180e0a05091b01051806030f1609061209020a0302121b0402030f06010f09 65
    0xc0c80c420810032000c0c001e51030204140d99985001824414010003a8007008204041000460340d880904400c80c2c8161500007402c0d142c0400c91410095950409400391200150005081a50761b034803611450152001d0440ca0010100305182c0c100d080d1a1248014003a05611006c209500665a410034004010920389645c840311220b9101010b00d0701e0001c030329140c2ca5203112221282e00301c0410380d00900b10401e42103070013002030f881884a014040001c1c00120740e00d40b0240c01468000f10020507040508003c03540c0b030030118883e5100b1a0501aa0342c203140100d0001344000500e450a40d4610b05400b807850300420045079103401c41310071860341c414504030316411529018001e40c0540d8019010900d24581008013112031240061b07250708200c260003040041e20742c1706400345030700391135940045028041d600000e601c0e013001d6007010b9031001a4103d01681d031030001030a1600e40a011814429040c60700040004901088804c9a02220030200050300c641c440e03c3d119540b000c0b02c1c14010798503 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 405264577 1250 405263327 405263333
    0xf120601110d110c0402030603120307090e0c07030201150b1803030d050403020f0f0601060909020703020114070f090b0702180c0706090809040e1f0b010903050a0606090b12190f 78
    0xc1c061040902c040741c8100640c0c980540706000084203604162829850b50806901003130365050a010202034955002c00820103061065000c680281032a4401000e20b0070041480c11302a4460007048025602e8103258805a004840c000b01c00c0707c0b1803004c01401c14482400c06c03440311078520800c9034980010052008071445910600b40264040c1d4018011038045000092510380c0c0300c40490340d05d1b88200010040160302c0300489068840300580982c44295528007640540301c0b20340392030070308510f900421202d958411510301302c3c04043d40d44c03c680e4550301c480000d41d0b84140c00d000b0750041040403491481307005c040c0d69190000507104510b86083c0e055102c2a0846041c44400c0b1010b100c001140542c03441e1501406800c0840031000e410f15a807020148145104440350744c2c04070310345036004070a240e0b00031000b030380056800c50291b40602000f46400030040680c0d01641c0780c2036240c00700c010718504002c0a12041000ca275002080a502400c80c2c4428101228030304580020701c030341c410000 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 405265827 1250 405264577 405264583
    0x52211090a0b09131a010806160c21030f060e060d03090b0d0516090503100c03060b0a02031213080d0b0402040506070809040501050108090c22060f090609020f12060111 74
    0x4992480513100304462058a00100500c2c601c50703560700c90a0601d0010300c1030b01d402080103600040c1c1900c070f21090100740101070b287d45d403504074040c000900d50302d508084000286418400f80c085a5800c120300d881d0742648004a91060041141c042419400a021401c0c1071408111050080c1885040151f8400c02080d00d03501003140369513201e072508180f0a802081c108500780c0800242402040d00781000c021a681d010417500c1c5031001c42c1c5602e031814281d03000b9070001c405480385240450352011030b400c01a42d254040405050802400c070006146101502440da140e01d9010860700d1500d03c9529182000d05040c8007050b40c8558200030002d92981c41034014580c2c0740c451002c19880d0b0207208200001c48505174045418040c10700708016020347d0100340c2e0f1000400403501092042e042c2500b214003034030105440e8003280c0c40c11201140b082c00704201b00302228000c90051205546400c1403d0036801340c462581090751051104000c0c07448040195540024180b50480c0140c408521183c9 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 405267077 1250 405265827 405265831
    0x503100f0f18020f072405090f28030f030e0106060c20060904110408250f05180601020a060f020a0906080103121b0803070201052211090a0b09 63
    0x46800405082140c80c242e01144040342902d40c07421400c0c000305400c240514840d1100c010462601c802c48402c1142c45034000a50325103c1c10820000c0d0301d814040c065441d2981100803506101701c5a0703800507104846400d45000700d030181c0410a61a9550b03040d0340364181310741d60310141130b01c0d00c0d41d480069509100c1d1800500f071580d1003103c000e404e4206084980031742082400848148420803080e620368a00b1212500e8041c0c0380010303000c511004030307001c50103141c000b01d00c3d500550b4500c208415000c4101d40c640c4c82103526140c4495170303030104078030141302a00c982c6412940d2414010402035602c0d68503070707100074103006a812450035a84d9000441e520601120909075020406451a07a802041c01c00a420141014165541503803981080e05090769540300c01c00c0100a00c0d541c2d04214000541c01095010800c1916403c2c01c00000e406080d0840d0b143c0100e041c01040d20340701200c0e070720b08000310382d41081c4208040300c0b90000388401100010404402a6100c0301d065129440d00307001a4 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 405268327 1250 405267077 405267089
    0xa03080408041203200d0f050912030403060902030f0f0604110a120b0108010b0f18040611120a1b0806040e120a030203010905060a051e0f0a1202040e0706020d0503100f 74
    0x40052220902092030141001580c16016441504041c45850b0400c514482c40221404e003181c2700e03541340700054001d64802e01141d400b400041070006c10454903400540001e80700714180c0b0010f001c05070700a80c0c0c2e6202e0000c0501c56510010205000c03a902200c0b83c2d6544001078100d100c1d443d100c020b070701c030402c030304400464100e1201001008164003c0c41047e001c1c15003101e2254045545100065030840104000e0340380c0c032021400320702006820b40c031003025481840150780d217a6101025484011104480d60b80d800c0e800d1595051440000721004c0e202014651108951526560f007403000820155810040c9845000d038000343d1315038882c6c01350610346070680e030161b40d0b5030415422805842c0041c242c0c0b0f024840441c001e1020f82d90300000020b0120700041c0c3c01c502100400002042e141000d40c039190044045075000c6030f9840300c2074120180c0360080c1d500303008007544070b000290b84000611441c801a0020408a1509031080004581191000103584003841d04d82c44131590302d071000d90101c = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 405269577 1250 405268327 405268337
    0x110c0604140103050106030c02030403080f090d2405010f0b0a140309030c07050a0506030705030a0603020604090f0c0c0b060f0f1003140f070210050a2414120a03080408041203 77
    0x89074542c0e040c0107150142c03403035141c1805140c0f4051030107981d9006d03d000062411201203a108240203c000030f071100503100402440b00000b0904081c0740b0024500b01ca0043d80013260802e00218041c1d008141c103c41040410292240c0340c802c07203107210707084181040c080003840315142100e0310030f460241d07000d0051f60000d55610108030a00030301e01800303940f1a60040d00006e404019039500c11041d00e9104005050190b0b49643c0c1e0144200104100d400080d40b001002c500400c100a460740121000324090100f003003c049026015a02c0b000c03058001009805030200054a1342490070580b40554005040d407080c010341140055400c00c2032000340000290380300d0785c00c880c500005401582140f202c4032024101e040840000f902c580b42e540394592000e80b160040781641c1041d5000c0007214080d00b0300007085480c0d03000816141c011500c10401c801e05858144400c03480c20594241d00610040c00504120600d541c05503803c00e8018010340f03000c941801b000820403904044160070510039919 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 405270827 1250 405269577 405269609
    0x50d030e0415172103180f070e0a02180420040b0703030b06072a0e0a0c0e01021204050907030e0a0501050105090c03040b04020906030313081e010207050d110c0604 72
    0xa100741018083c1c081e041c0540c8111403054011048000ea0075107808904e403c039950703a8802502d498501080c0c031514540c0c0c4903c1c19024113403540407030b034002600c00101495880303440d0101080c00307901961217a100740c5034400604650b00d02d4181c0c012207017038074038120f45003d54402d226039841d150401d9008404440001503982c2c2015031502c242d4540d0802200d016042002d40d03191003070f100c115525688811884940358180c02448548239000510305060003008624114258401802e980b80807400841c0c3c500c004030140398004602c8104214100e400c0500703092602042002804001d0206001d259540c07200303c1c11003c060100807501070203500046075552521043c01290700c0002c05110000006000340301c005400041115041a0110386c2005240c580800107815032103500c60046003600d80b6540090b20307040102d401141a8600006072a403119030042282c00c1c0d200350600205160444802d010b440f90081c015107000c00a030f46c00b01c4100010040100705980d0040c0c00c040c41a24101078 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 405272077 1250 405270827 405270839
    0x90c04090507091e0b030105010b04090c02012c010b01090b0a140f130303020c010c0b010905070e1f090803030412141219150509130503070209010f0302010206090c0a050d030e0415 79
    0x176040e5400d42c282d000704840e41c07400d03c4030002409580280020b03d91200c07070303c0030014400d4018244a2141100340c0d00312002c83c15062155420884002c5565400c00303094480035801040001d049418075000580382040c0650b0031201c000708030074840042d501c180061034404800c0800707080356410f04580941510709606000e45052500d42c82d842c10030a6584c40400080e40c55070405c2c2c1150000072000c1105c1e2990841590074605020040b5046400740f500d0026284480d03403041c158010940b58080f001e40c4a15946840b8802101d014200b0420224444400c078851145e0843c990141aa0b00c3d0074a805071a0315141d02500380c1d450b02248101d015841d4040c3c07030904ca148041c0b440d4025100c03000389080c020460000004100034082e8400213464424048140b0448407055402801d00710306603103600d000c2181c1484d60006a005114800010310700ca08000380c00840311000514081d1094603103010402d6114411070104c04000100d5139503e030503229400b9140c007880e40080308941a6003011 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 405273327 1250 405272077 405272081
    0x602030c0618031206130e100c020f06040f0812010f050a15081f050d0b04110d03140318031819032307030b070201051e090c04090507091e 61
    0x2900c040c1615240181100e903492001045400b104d151954a01380303030f40d406000031003003a41c11804000540c145000d055000c5404030304580c042200c0d00003040507089002040360381e20800426001154403210100d000f0901c075810740740300d4611580c8554a46084008d00c110b5050080c1c4c0042101d040d070b040248680d2421418140c00340c8000b2a885500002d8200700401e00b1101400781500700041c801c49188440700354420101400c805040e240c4600002d16089140342c1e02101c050b9400c3c0700c1c1c0000200185051381101554030780695500c1c841c42c80340d103240390032940301500d0900b85581010780c03802c03c40420f001414603114100c1000030100500814481540c000c0100c418880400300da050002031504030b030350034030700008008810100c1c440c5010545400030640000c1d00d03c480320f038100105280c0c1504020301c14042c103015420a410510042c0319048000d076511411604022640d03105410168060740001d030207842200d44003680e860100040326030b03048429070005422008009032175554 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 405274577 1250 405273327 405273331
    0x30b0103110f07060e07050607080c070f03170307020c090a1b081b03270703260301380a0930060e01020a050d0b0907080a180b010602030c06 62
    0x1d0607846103406240c0c40205424800c05000500c99030740d845108a00590400165014120140c8505d9541400c0e040c122a03a8004c001d4203ca148180480845c0a01e410f6a001040b80e600c03820041100c820b9215102c1142c00003445002148151070b038110f0541d407a0300d45113014040d02e090004940300681c080403070b44003140c0c442c032007480000400d1010461078103289601306600b06400940740c0d01d504241480c9007152040c4508400184e501814000002080c035804403031049506e10072800985034a5004c2c5566021541a00282840108800300340711407004c50200e00c01076480310100311268280c03e07501c004001d04048800c040350140025070403034500e0740a48412464003c4070316448030046190031203e078003400008502c0f081c01040010f60b070000b19000b000ea00080d511102031240081c003581200d658071030500d040074066402d07810102c2a40b4040d40c00380d035030f03603400e66140140d0101130552689041095444064403001042d4581ca80034042c0c1712a070b000d0340d590002d107680c40f03207007001c0 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 405275827 1250 405274577 405274601
    0xf0f0b0904030f03090201050f0307050a0807030e03040302400f05090a030c17030f0402040c050a0909020c10020706140907120615050d0c03050f19260703030b0103 72
    0x4900601c004241c10007002c1c070900e01ca6140100c0d02c80141d10048405001c4d01c0618510034601000b44240c2a030010090326051034039580b1000310707540d1680d08405607231b4404c0c800b11140c0c10410050002d030900701c0c01c1303035404052680e46072190301c0d900c0c091191460303001c5018000e10070210084c4000c40f44500440d21b0f24880a142848103080545103182c60710640100102400ba42003108010480090b25911440c0382041c00c00740c807032810180440b62070320101c034101e10451402500d00407281c0600146c8280900a50f1044800d60030294180001c0d40800b94020300c40c41031404080a01250f80018209248240c10224174840d450745590301411020741046003c2d0080642440304a40285041c08965000940800c0305030764082440b02074022030b003185401c5000708c0ca06000340090354080301d0403a0720480031140d20b007a54064150f29016030500855a106502d101880030591111206c0a108228002d0007008604801010003d6000e800101d011030b80f60340038100f441d0b815200c1c00000c060 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 405277077 1250 405275827 405275839
    0x106060306080303060d05120d050708070504080319030623040b060313060209010c0210020c120303060105160606090501061e17070503090c0a230a06210f0f0f0b 71
    0x20405080c0d0380c82c0d0000604583c061b18142d2024018401e0030040d0095666034101c030655214403d06001000c0c00c0700f02d48082c08544c0200c04142001c2c800c404550480e039041c00914207045000f150213194001070140c2c4400c05455510209241c0d10303a008405000c3c00101204c22000441c43c20b000994001e50101ca100c0d6609000f00011151800c7d10350344800e0b0320440060b51040544010f0f40c3d140e002ca40040d41100700002817400c0c444e0002003889102c90220740004451110594503603030ba110450314640000ca05208840c0c00c14094400300001922415002c281551620056411120309038062000a1003180c00690707000842081000d42000314500300880c10840c28000f14400030161084040240010005038414014030042140c10401441c494403d42c0e5420006010512803005411010604541c0c149034540310240a04940e0107072140c110107a8008808556408082140d004450310390400c52501b401d540304419000300d40200c002054280341050703004513480c000d81a40616 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 405278327 1250 405277077 405277079
    0x2c011706240d0311010f020706150302100e0402071202061609030807020108040809040f1a0d050604171903090c060f080f0903071e020f031c03020a09081506030106060306 75
    0x4407004003460101101602d1070103901d5224981180c0d40000c42150000d07a510303004070100d1140c040d0300108201c2d40144000d0050805c80c1c503d180555410303100c000c3d0b00482d0000c05803150b030300840c100003004500400c0141443c440b0b0300d0341da00040440c1c0c04140180c100004008604600861122060741c0a140c81d1a400e07003117640d803d0440c810140064140601980000c08010342d0108a036000000548103100070704032080c15001504542d00f01d00385040140386007551600380780da11005d429810100803c102c0c0c54503190700000b082920222480040100005840d414800030a200201c10300d0f903000544a0300c90405c84501001d0b5000441001003800703190844030b5101d0840c0d5007007801340810114030346030034615a2440c410608002c1c509125180e8950258111100749000180207a40071041000329008042e116682c5090114038072104c50b8241c440030744203038043c07d081911814014070700c40c2c030340c2d060307525008140f01c0050148a0000c100055801c00713010b0030004102606050001d6 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 405279577 1250 405278327 405278371
    0x501092d08180402042c010b120a090f1704060f030209030a060b1c060e0609010b0312090a050a0801050403030f0b0f04180807080429042c011706 64
    0x340c41542d1010b4100d8071103880c1102c15959a504540c000e25018550f00320401e000c1d118544240b152141c001c440c40c181400010385403850720100d4000340c462404641c0a81e40d40d0042c140104082d803001d44480400c2c4407180b0024030006070b858001d28091011765107440c0f9203103000700001c103c0419078081600610080881d81c40016610034407a40c4a1800f090030f10110b00490301104080c8502c19007d100c01c0b00300800d00015a1001d0308298a450a450741d50303441401d82400e0b00c120701d403403903007592010808580f0300002201424158000401c0310460a945000060132044240c0021000740d550b14244010190184141e5480781c40a000900c8907400d0540011003881404d09800d00807904ca036030454200c022a100042c480307620820700388c1c0f01e015a0400c0351054100707008440407486980140c45141d4035500c0900c1840e0005c2c84250705d0542440350f15800c2e05140b0b031501c0103045541c2000c1402c2603203410118064940408004032840e84211403916142c0080c00c40700b0040c54006091a036 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 405280827 1250 405279577 405279593
    0x90303011410140715050711120304030504050915030102120f311104020301080319021204052707030b01020106142107170304150e09220501092d 64
    0x190b281c00306203d0b512036034030381040c2440c1c80c03c1c240c8100d1107a14000c10441040e8021680c40620410174044820758141f0341454207031407005640c040c0100d2800d00040041d0300d4803601c03ca600c611600c03d141e41c0f080800700401c1c00c0ea0072004040615140319010420304108110465a10411051801c580721040700301120109441031503031500c80c1902004d01e003c1c4450b940040c0800348015004541d29a51150113603281e82020404c040a965100c0001050510000d041d10407800700032012072030326280808205102048504901030386c800c11400512212054940c0352054515480100300507121800080c02c4540c181c220790b040031040b000525881d2903102c42e001200600c2055448866078150101b860009594800655207441c01460000c104011010700215000d04203401f10340c030710488042d6010f075141c172220342e0040d501034000359026482c0d80b4071660f64001010b2406809000e03459060035954107481c242d5110b00e042c180e842c41201c07a2400342c02244008420806079036600e07610154 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 405282077 1250 405280827 405280847
    0x90c1a04030507060c140d0f050d06080609030301030203070b0a14090f030a030e040b03030f090d030219030c03030b040501120204052707030510140f100905070f08010609051311070803090303011410 87
    0x400c00c1c04074803681d6100701c1b6403041014041082c11601143b81a581041c2d40c0d80c400d001c100d0103800b0703118000501d0a5100c0035282180000d483e80c04140408034208201d81d04072115044d0703c10312540814046890034010410124041c3d55901143d2000d1070030700065440c0c003820316000303a0040119821424000043e6503040808582014201c442e41c01c0803840c2040e20300580d00811154081d10040540083c02440c0c0c0c94400c0c1c4003403020960341000c00c01110002d109016541c01e0a01070400146455072003a640721062440d03135003900b08245454039044002814101080d84056024000e100e010000c1c40f1000508200031310600c1501600700d24200000340001510040309070201d4000c0d046114040c0280c48042020400c904e443c6e0301c018600c0d10200d41d141c0114443c100080b54251154030f400056410160841241002c140e203184000c10380f08071003034001c10040c8480710000d11604011401010325000942d1a541011903040944030400c4140788074010820070a81c1d0150024a516 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 405283327 1250 405282077 405282107
    0x50d020607060207020916030c080601080103140f100204090605041a22020d02030a0b090903032707080f151e04060e07090501060f03090c1a04030507060c140d 70
    0xd46440e1030b458084040e00460400951040404042100c2a0f050f181d00c103480340d000da0317828090004014400d4601c8107041da405400254a4030052001c84c884103100451500000121240c04447c0e940761820003c01c05070280b0303030940014081080301202d000d8407000e40000ca03410000140741d5a106070385514810f02841c05003500481081861002d0040720364842c0481c042550795407403100c00c06000394412101100c0b840d01e4420b00c244642420038105102e9550b0b040254034544070802d12003168802106810345072038080526440200d410b004c0c64004101c0030004200b202d9811030841c1c10101004152091040280104802d0000d4072222a1f040202c00001c040c098a031810403a001e003d0720084d0700d60a10403c075002607181a10b0340164120b07105681c81c0030045109060840542d448400e010305500a46503051003141120080c061a1401103070441d443c150b40c9580741d5003404081d900200c0440c960500b08428040001c8117601030841e0a00a8480c50310b441d04058440e9080c89695 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 405284577 1250 405283327 405283339
    0x703060c110109030e10020f0c010302030a0b060c01050a060b070302030a0507030504050d050f0d2f1c080a0b06040b1204031b080306040f0203040b0c030c041505180307050d02 77
    0x409031900a14116906078007690080c00481c803542000b60040001c1c14070720380038005800d4601c031520f20104201140c07207074000140441188090045000c0e410282c999030180d9900d441c108a40c1c8da03148001c140b501c0305c0f50000b254074540040002c04513045607205100c030360001c01c0072000095020048410401445c01e24031f448a916003000c41d82d40c010340d00710702d0304090010141ea041c07000000d6036103131591303200c011140050f1048404403007052100071032146405080803010f403a64401400b00c2c0310002200b0440c1c03a05880700c2038070f9400c0341184829a0100d43c1050505c042c100c0c45000c1c1510405064600b146003514040811605d8824007800051781749400c0e004c90105403060441c882c0300d00c0d44820f00c228207801418829078a03801a9440d5202d2840c00b610040540380a00030342c1d02c19a0000711a41c02a503480c4021030305540b00615400400c2410000810608882d14a0700396094241d9143c0e07860301400134006c1d000121100440744664481d0004224030b680d02440100130990507208 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 405285827 1250 405284577 405284591
    0x4111002070329040311010b030706050d09060f051f05091303080a1d010c021506091305030c030a03140609010e160c1e02190317092701080f01020c070306 68
    0x18802941003543d000403803940a40306100c249a03120001040c2000000004c10051660800f01561101c0d98490b01000ca807043c00501c4044200744d002c010003a02603140807407400c00041060b0200c59084814002d21000154015103440c1e03000d036410090001078032007001e41c1c107100c040c82041d4005081c0c014200000107000654402d66a007241001c20189810341d0582d161480d41ca501074001104404014415552944e40b0762100511103401980007030944c0741c0c2c6440c5d11030300e42c1c0c1e408041d00003a42c06d44810000c0010300c8804200415000d54603550003d40448096484440702c080505803a102d20440801406506640c000451700007041c10036682c56035200d140243c5078402950005414402140620541207880412000140f4401c60380e02c0c004951810105207099264007001c0e000040740313004ad50050b0151002007055071401403003400740d101d482803048041e00c2c00c8001c520307000070200010040b540301000091814140540294100008031080701e588800030301c006401c09841d040 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 405287077 1250 405285827 405285863
    0x702010909062c0c3405240411060c250e0c0c060105011808030c030a02120711010c02010302070b0a0902091003110d0204152c0c0706091b0608041110020703 69
    0x1c90720100c81d16110605c0c184015090282e2921107040400308400c03407054903540050304100036284125400350080c6a44e040f83c0301441140d402c0396034181212304c2020042d070303008256079050028a8880350380a094072401c14a1001c00540003512110007550140310211038094040303a61815070310f0a18140e00d0703525914114410300442540718900a0200003014448190080014412411a0b80031281c01030b6501c110f441d007901c1440ca000d0040c1c6270840c02c00c01598440d00000c1010382c014136025040005a40b940042c621040d1036109903141c3d0f0b01520400c5082940080341d01c2448130a2201d0703810701d9230315a00e03264030398018143c1c880c1200c001c600d0115501c0740c0c17001ca030840f10321500c000e495440b41c01210300ca1148a110721807403110900740c40c0c4c000740e909510038410013510400d2800c0c8400c42d6503a1002d0200d130b0038200c85c903202c00042c00981007900400c60004011a959400050400e824041c201030300c1c1002d018090101d0480d01d07c1401d0700000c4100403603901c0070980049014800e = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 405288327 1250 405287077 405287137
    0x30f04020609220e030f180316090519051006230c071809030e1002100c020304090501090504020306040206160f1515050a05060702010909062c0c 64
    0x14007401c1c1d026a010705850b581043d420a88a03040850100c1001180b060204c4507540307001340300001c01d450300c08001c8021250b95890903c401c43e50701400712640324445010561200303456401c4040110f6a89003000f0341402e02e800b00001000d83c0b50310400881c140040c2032030ba800c540740100c8082c89503080401810301a000c0003220410204d501250b10381008800035512070000d4031895591624000d11510091128441d070608503906844e4030030040d03502422321900103071858212080d0301034181143e0501c01d5902030500d429105601465641c0e0404182e00300b01c2c0c2042c2c0007140c0c034500d84010000180c90000300140c10a8044070b02a03250002940740718817500c1419401410014500302050801c40100000c82825a40351000c0c8141c1c0d40811004140c100d05208007503000e042140100164101400208007040c018075240000a071144480c3d019070f40310742c1c440017212419105400a090700480b24814482d00c00203000200c4c141302c4d4001b80316000300b0080407400280c54003c54807048e204 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 405289577 1250 405288327 405288337
    0x11e1103070c0306050403081e0112030c020306070302030a0e01020f0f0f04091107060b0909120c150c0c07050303030c03060108180d0c05010e0706090e0c040e1005130b06030f040206 80
    0x40c0142d194a0307140c1c58880c003c1e2406803000c60204a0400c0800c1a585030104c101c5280464072481400e0340c0e103000001d000c40f6058100c143c00b8480705030740900250b18140304080c414a01910096540d0505034030b1b107400c071021b000d29421280d205020346c03162030240b507040f22700c030042283c00035494001e01c007100d030354a1169900c048841854820b080c40c0503034107880600b42c25402131070100101c11000c001d02c000d22100719101c00058100e890f540c1c2603800405c0207400c05841d503808807425088002d4121311a2403003038420020400c4085442c081104082120b80040c01c0140c010703504606040c4040225800042c020505000c05080000d4010b5004803105602062800441e15003018110000d402010800001d0720306509018000d80074080c0040c405007218400e50300c2d0052149081d0254401040280c4810161581000005094030490702d185000301210000b0140f02890310003089841c84040444e02c180604000f841c0c001541c0c4ea82c2501d13444007006200f8101c1d40d48510004890b8815 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 405290827 1250 405289577 405289583
    0x1a010f0602060a15260c060705031603030e0d020c12010603150e2a0109080102040b040b093006070e0f0f0301061a070507081207020613080a060903030506011e110307 73
    0x61382809001500b4031400204000540170550f0700d400007000030702c00d09210369a4007078030790f500c00c110102c01d400420400070207031030080c90b001441c07280390f1503a10706010a81c02c00c40e0050384200c05454192404a410300b4880100000800c1498035503900d00ea1000140e4403c0f2400750307035401011440150a2040003007042c403c40e03032100040c2d011a400400c0c2c00361000301c0ca00188008101007041441442114281d80f103690200742028a0103948840300d502c0720b811507401016120314045000254070850714002400348411b00f00384000010342c1e181000c010320001c00c00c0712000c0c84444d0342d110310781014000442951903901c2400c40d18007282c0584003560084001a1105e8082c0240c8403030342002d030029511072002c0e192890f0781d4400690342c4841b034407442c08000700100854401440d140005140ca0000c140c105500d07156503444950401c0100d030010744e009512622404200359042c480c0719400802402c148480b100f10350140b4510702134800f00d000c280500860311004c5090100156280c4980c = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 405292077 1250 405290827 405290849
    0xc020409030306090b15030c1c0504111509010c120203120709051008010e06040b0a17011a09100504020f1309061e03320a1a010f0602060a15 62
    0x226514008000b030110307100d105503951034849944491b00d00150120402e050b0040c2c0c040c00c0d1b454204403215582c1c031a00c4480d110703041e62400202c0d402507502075288030b10302841400d4520342ca14002e00203c050070113581c2c40101d90801a808984e07800170741918945c0c0d00041340c07001c0c00360840002d81c82e40c070650740c1025007180504108100d903170340298080b056420603205e100c42e00c3c40c20001540e510a00780103c02c1100d25180001d1814149940003414404008042c50980c550301c941140030b48403003108a1400380d4582c7c0642c01c041e0341d200d16080c948035003507a078903190345005c83d075030001040c540c000d181c401ca40014070090b0305103440b4107442810544e0007a040070710740c1c1e035141ea8004100300e101d080e845282500000030b940c0380340c07403100e1700300d94002d1101101d001c0204051400d5240114105d4003407000c01070300a070b55100422540d114544690352045401e4013140e541d40700450141d1201034540341d4200b091210790741c0400d8050308035044100c046031098188210100880d201d40003460660 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 405293327 1250 405292077 405292091
    0x807021306031b0f0e060609060c0709051303080601080c2703010e3d050f0f06031b01030f180b2e050d05070f0902070308010b0a17070c0204 62
    0x210568800002c032441907481c12861402450121600c0003030303105100d40c0e80c0d04a0810402081919409540040c00601c0181b8040302c202c005001c07900400c032440c13415030000505012000071842055081112000c1c0c0c02602c44196030002c203000c000411aa04201c11040441c4002c0c0040007a1544805554103181500b007074120b0f403400c0d828802d1220b80c82903003003060100180c02c001c61550040f12400e004030001400200d0480e0900038681d16140641c2060320030126084802d00c03d00f4024041c001e01000710303081c090807240d03080742d0180105109400145520300c0f5404000452800d80000b8200421000044202c4100614000030301001506c0b081d0046c5041044c404c1c1c900e803060030214150b5100c0920a803181c0c88843c3d03481c03400c03011080a01000c1c440c6103400c9281d45d2510b44110126081c0700e4a0f51143d403400350300c1d40c1c808100640c0100708032007011b0300480142d001d049012100ca041c42c44080e401030041c0c4100c880040b01290312008207507180e00c990010308a03203802070020300c155 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 405294577 1250 405293327 405293359
    0x120e04020406050a18120f082502010f0e03030301090e0a06050c090a080109080f07080903010e07050109120f08130e07020703030806010c0308070809030d0908030610050705030307050304080702 85
    0x998045121395000918031254080c4181c183c0b4103400503100c0900503200c1326a4641d554880a4a0b1341600391107200080c040e9030f041030b500401d41840034550301400c1c42d140040348001742c00385040003c00d105000c00000703145020780300003090324112010720402054048506074950f04003400c4100c0607112504000800170400c003424014410382c20306841003241141d842c01000d0884100401c020401002002078819082900014200d0b03e4000c541052800300917a00203800c441144210310700540020b5030410566800c030032100000e000d00365094460072a130750f80d009004246120000e20031032010982c1c0728010404c48921010302442101c508460511034006941c1d69200c0c8004c60014110000013000c9511603244514102c4c0c1c10744500c01652504c0c071040c0d038a078200400760712003071200380001c040107440c03070180b0100c56000d08500e950300d0034003800340000c0f030300c0c0d000320346007800340c01c01280300000e41c0081141c0e07003c245403615948a48403881c0412041c8600352000c2e40c01482e101103120f103 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 405295827 1250 405294577 405294587
    0x1020c010b0918030304111f0807120b01390308090c1804032d0302041401020c0d0f02130f02031e270312280b0d120e04020406 56
    0x1600200d400b0b880c0d5940305010054120806150181c0d035400901c0420000744100385005c414800040140c86030340d40562501450700042da26100000340359100340f202841e0000c5965090404020007440010441c1c0006840c40104041410000007240e000000e140012110002452809480748585400900300140100b80640b2074540714000d41400c0900791030001c0c50405418294036210555039507a860560302c03d40005000c41c4034200c8480340011820b00080300d80c42380d1040383c0380184c844c0d0400b03516030b4162113400901810f560008200c81d02903982c0440d072000550f07220b0008454100c1c1c51001c9446030f60f19544068016052104074580ba5000740c010350700c1581c1c42035030401c000352003401a4074170010654a01d0010450304041f0b03012100d900c11405810007000d0200ca1400341130420710104020121107842802400e00b000e40d40d02c501092010b0074102c003120707080c0903411001d00010140d440c0080001c3c6060140102c0311860750007400c00b039000840051045441c1c0d0f540c1c000183c5 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 405297077 1250 405295827 405295841
    0x19020604120c1e11040f0c03050a0c05031603020f0304030905090a050c04180603021f020d0804150c120c08090c0a03050a03050306060706050403182c1801020c01 71
    0x9924032180102850840c0b0402c0d10340c001c0c0350060010901d001c1e900241c460b180c01881000e440150503540901a503856a0107600884140940001010350b0203050050481e02c0c00b50126120a04168514508036400030a9a401c01c102c403201ea0280e94040c2c10940c001e00c00d5070051580d8090110400091640005521048481c00d885140d0b0680e140840801100e40844043c00800d034107010034440540500e00043c40209078180029001c1d45980004001f806008004043d0a1a0741040c40e4515410f1000c1c8520b05407038281315a04d41815550900032100c1c110100310180d0f95030301558682481504081c0c3c0b140131805003000300c40607600780107152844c00c980f500c4140c45150005070b558100302003944d0803070381c00401420341c40c0c000d950122881e60004e002958401d10510010010815620131075000c0d41c400d0310303810b066240740444200001080d40c04140c1002c3d101000e00c0712510041d0003041e060300110601055a03441c07203216004a401c1d0059a4680d40c07011801180d80101580030780 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 405298327 1250 405297077 405297083
    0xa11010305071128200a0b0708030606180907091e0303020c0d050a021c060507030c0804021224061201021309022a0109030f0302041203120219020604 66
    0x210680ea2222001d8421807006000120795074080d040e41c204113580c104140c1c1040c00030410f89201240252100300020704800b00d40a01e0400c4400320043c60703c0c2000508005280302c0010ba400c09449443c0c03844c3c180001000c45001d050300007101d508005080102d801c0c4003500410f0300c4494101404020030640685c000e00700d91010840901d40602025508041100d9056000b482e10b900c03000144600c801e14520100d4880c443c8184c08401a5200c45044401124100c08102c881d8000c0c201181a070f00c0187c50345007414070340111111010380c0203058542c41901070303c09042c000c04407000c541c03801c0b504001c1080e0500c070902c00d04202c03200c41100580100c2040301c458800c0078408448a00300e124515111118116001d402c1040c00310640151000c00d40544464055856041090000c600b40d03285003103150350f580080004058008941c0e9510108610b1700314102418040c640f050054045405800d100e100202038204131a241c048424840300b6626041e85800319800c043d548000940e412 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 405299577 1250 405298327 405298331
    0x6090703051e070e032107020d1b03030518010309031e020f1905010b060a0c03080c07020a0f030302101415031006060f120c050d0f0e0601080c15031003060507110a110103 75
    0x75a903030a40544002881c6c0216901040c07806402e036080025002452074100c90781c04002055015058240141e0402503000c2d0f02c456a4801e0a040c01e00d98841c08540300300d040c90724001c80c010201e03621a00030460b018515808688400803030005a00e40300c00c004030304800303119161020714040c60342086d040c48180b150000740079164440c010004a805a000306400141110070f01001180c8684100c0c0c2d00114030700d01035443d14003141c0200e01400c0103a0420b0710411100c80c81001015410040c1150071001c3c040704101c040407018041c0e0001074007410100140441100c4d0040903a02072100c0860080c9251007006900e030340d140c01130101070092100d00c01240b803880180181140601484d844941695202441c060040c1c2013900241420241e40c1e401d1941c0f40c55000c032443c07007001681c4c042c08160300140560f003102c4e42084078003143d0f01448901c15205205000702d84e44484031a01c140c0c1d6200b0408035986e56030501c2211030b0001025000d0700d5204080081e0300703100d0100c1110050020070b99007 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 405300827 1250 405299577 405299593
    0x40903020c090117191a07140304051b010216090209011b060902121507230c100b060a12090f05060f0603010f02090d0201120f14010503070e06090703051e070e03 71
    0x1c00400800903940140617410803003490f0203c06c02049955030f0004290030902d1203580d01502c0d040950300212012101980210020780030023100110b002503a007424030081c40c00311480c01c000701101d202c61040c0303001140c010030445007580c090b5419200c1070f44c0701c030601100580d140c07d04e54090040b524041c1d0250310b20343d054440c0404046154400c1c1513031490044c106490755503003100d40c42000440c0d94008450545403404400055000306074021000004142402c4801b003000b0450706089403a606c208030400948910641102c14400144882200007402d4500d0707013400440f40c0140030000b0440e014020411141200a00c8042d00840c815402040700a1107003d40c00e01328844c2e1042c160340610b4407010b00c0010340c8201e0300c80000014802c008100c150803498000d055545041c40c6240e481d06d041c0040c84213040421440c001400c41c00442a90390078031001151001c0c401414030790400da22180041c0c080041d00000c07285441d0020792146a5240c0b0000003040b0b8803038440128800d0080c449 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 405302077 1250 405300827 405300853
    0xb040501050d0b011502070b0706021201060e01090e090f0f15060a0308070b060d0203030a09050112020708030708150603010f05040e01200c0a06110703090e07020606040903020c090117 81
    0x110540754964441011030040e4242540000c2031904903884c08214840c01f17a01040c07041008000d070030143d10030714001da141c1c110020f402c00390b200140c228200f08011151002030980c0c2c014414800c0703803220800108240c41c0c0310720046c1403884038074031891a441071940d840d58003000025501104001a07202209545401c400c122980b001484080c1c040c400a018020201d0000b41049800c13120003040c0d0345a520099020a04580010361040c020440d0440c040042d0350308074501514041c0d09060852520805941d0744842e40030141840040080a800284500c0c10039001c41d1100c41000300110348a6a41701103032201c18441e40504c9000b1030030081042d4803400c05001c5c0b081c8810701065500307100d9164145552054220107541c2a035445455484d4012600c64800c2e014890000714035a99103d800b810040e1240079581d109820f0240001d08200291b0380c041641a0880070468000c03034032010b207003012454001d985154562040028000140d002810085801d044000100355010100644 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 405303327 1250 405302077 405302089
    0x7031e050a0f0c020a030803070c06111305031f151a13051f052104060212070c0f020f0a15030b04060f120206030603030c1c18060f0c0c090f0b04050105 67
    0x8070703000b17420070503001042c40000d40800c0a03580c03000492400f00300c2e00406403075807400d94a95070504158040d00040c0301714400c0c0b849159130044c18050340109551122203a455402d03046c00031400c1e8071103a40e0000a00907101d8400400000c001c50204001d240700210350500035603000a41c0d2110740740501c5030005690074076000d04140540b2041e528101021001c0007034031198004035240c54124007c092842040205d10020341c0164080c0000685800d4a80703a0004070f003e01420303079010301074564a43e000052601e24104915581503411240c0c8010300d102041c844003241e0000c0c3c42240e12242288051941544940084002141d09001460340c03000001480e1049011b000c500c0b4404c0041840582000c00042d13410403c042c04803450040099462410111b02c0402800800c0c6400c3d0000384850740140c04498401d164501d48103000c0c0741010140c003020311000c6a100780038030036a0b62003d2140314640000103041140050102e000f901030110024071011511911480c60030f400810070341800 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 405304577 1250 405303327 405303347
    0x3031c050a0c0c031e020c04020a080a0b010503010e0103320a1704080d200d02071403060c0a0c0309051e040609050c0313050a080a080103110409031407031e050a0f 72
    0x40c0c41d039512800c005c003c07404040044481101c2035100351205400301d500c41d880203158980f102d5442c0d00c1c0700d062602c0c101c0195110a10712904203c1c0500041c00002c402401c03070b80c1181d0b8400c3c400c1009904599a550268111001c0f0003200c1908048130802c18001103810745840707209480405a200c40c084016800340650b0140c0c0040b648004505600c00e40601c4000000050410080c103031111040441854000d0801c00a0010b800c09003080205d0106880503051102003100600380b1781c60071410040c1c240c010f0b00050760170841202c120300103144c015010f0300e0203003101500c0e455a04c82c054001501600092070100d01071f03454007100261000391445490301410240200a1850306c030f91a4402248104d130f0000d54040c003423400d090f800541602e0082405003501e4445082d10f61550900e01a400000c1c6084c5020fa410003801a0010390b03c40384014030084072946690725800719050448055441c00c0ca00992103083d40401c080311600100989100c281c11f42c0d0b03000344042c4840080f20501c007a = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 405305827 1250 405304577 405304583
    0xf1303151e0c0801050f030708060705040e0106091202040c0c210f0c0525080d020c040c050903101a030601090b03010b010207030b06090c0d0c090608070f0e06070203031c050a0c0c 79
    0x5001800b0301d2401c06e0360b07502c1804005040352403246d107a400d403604041060f500100402d000143c20011030950011a5006041e07504005541a00d8000c100300340c81c0c41000028442c9a43d40444960a0f0107280c09024058100d6a0030403d421486070742d004043c80140b08001090241024403100e910500c200346100d82d121010b0803035010b0000050803401c254841c61680c5c10545c0c9400304500300700700015048280f2039402440039079425401c0c001100c500c03842100030401c04108a50041d100010407a01c400c5840c0c00010f41204800a264018007a06000f0350b85030096800014038040304e50016119020100e00800001e403135800103a070380700014800149004043d0001070451b20f00401a07035031140e1a00d2083b490042120000c104441e8204480008266514030a010069008034156070203c402e04203100180011314020305065115004148165800201003046413005d00a480c00d150241c66031244a040410402000c0c0100b111603d03030342c51504107680e2620b0302c2000ca029886030 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 405307077 1250 405305827 405305837
    0x152d03161206090203190302012a0e13020c07080703020a080118060f1503030f0807052706210f0a0c0f0302090406030b240301020703050f1303151e0c 66
    0x8925902c540c0580b0858000381d03458083d4245c007442e00c1d2450780e40a80003903c25400000c024947c1950075040281001075a60031102103014840101d400c20380b2a00c4001c030850f007100b00c0750007504110000e88514030588803a0b0248402c00140d4400004001c0107503442156071002040d01d031102da900f211035122441860f50b0790304000001155007030b4043c035072220403800046521419402d40d0414171140d50b104400140a01140683e81e03a8020206900310760149825440d024000481010110041e940e10248511a64040c5801e44c2c440c0304583c5e1000f00d01c18480540c08100b520001c90003012240000c04800201c0090900c0c50144240700c00120580c41d03020f4081c602501c11802074100d00002a001503540401101092854041901ca1087c00c082c44142d40848074071910882001105140268018440140000e402105990399015541603442e2140b16665030345010003981d90000e4445034100c1c000210b02480303604008a0613045400354804100c41c02d002d04111244002020002a = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 405308327 1250 405307077 405307109
    0x51302090904080a1205040b01060f17160507051005190b130504050a0f06240b04030308070212030115080c03060112150506120f01060c0308152d0316 66
    0xf6683c070003070030544503149814450103405401307840c2103031801d4400b40c884ca1a428010098998024000f103071818051070b14045040d00e0701030b003001401e406843d5901e40000788450703194080c42a4241c8242d02d4210781240c2c031040401250100900e02a14008030304c80e14060322105156a0340105003035004081e242201701980450018014000a0000c840700d0284581c500d01040e8401450b00d03800740902e60004810f002601b1103c10b07003015649450795400ca01c1820007041207020140c408407501400d0582180d40e0f807420807070401d4141044647ca022021001140f0b1010301e800039001086151203003512078031031180c0c0001ea4007007152414001440308149041c600d0301c40c0c000d0071000086150892000392110001009500044880c0d81c107042d03508208600d5211440000340140941e00708503001406507140104071990007003691f1040c62199200080c0c0340c452401c5100c0944081c0008060015940340000c0144103030440580310348201518041d2055140c03c0f030200315100b0810748030b132103 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 405309577 1250 405308327 405308333
    0x6020607080a0e03073203041703040509010b040f0f051e0a0807060e0a090603050d08091501030b15030102160209270303090d02030906040611070b0c07051302090904 73
    0x106000b055441010349807060b032080080c080003d0b0412520421304c840400800711810284000c80c0521117507001001306a54203400c00200071542551200190b020f45a015940701515600c500d0380303d00d400001d00c10002614454110141c0151103848210343d44190b6100762030301000d800342c0901c607880040c0c543c0514540184104000c02d614002e01075100040e503c00050303007810426406200800c2a02e40000d2070381c41c0c10151800a080d2400d400c0101905580f1940d43e2901807665190501800c2400302e5201c0000300404101e000e0b104051102942e181d103018807d01009480e50070654540d2040c0c808140380c10f0086c5c0b1801c401c03400d800b0710091030319000c2008451000c0c01d40f555604080071402c0800c0101400100c03280944070013156203043c03c0030054600425201e00c1421900144480c00785a40e074201210704842092130b2040d40c0a090322642c9040c50103592000010000000b2107011002001c920002210405c8484d550902c4050040c40240d1040003602c0740c1c001403000000f000 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 405310827 1250 405309577 405309587
    0x7110607090501212c03160b0406020d021c05090d020c010f03110f04031b450c030c02031306111f02041505210a090602041403070f06020607 62
    0x14900308468141c100c0e0b020040070204079140c05010054031041c2017501d580b5101d41c81e802c002002c5940b00194544250010551503200c01900014410f50100010406122032901551410000507200310b603200e4000d003001000e0090300251849042c1010b00180e024080490403807803080f01d0b500504512141c2030300450707900c24103d685906050b51543c1c500140e00711070001d031080c0c583c8801990f03600c42c00c5082010f158540c0400ca044000001030042c41400003622089115243c40703824040180a042440304031007203055103041c030b4402ca50600d803240071015005103c140205071010021030610f0311040307860344601d051040103941c0c3d09000b008810b21a22100700a10f600c03200362500d103190024800b0030380701c0c0c800440303020030303000b10f07042c0010301da0b80412151400060810310319002c0400518500c1c909080414505240c02800080005209400503000c1680c0b0200455969448441c0d6030520542555040d000b441140350100b0380c1d8003944078017400d840c240d40080940d6075400c2c4084070 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 405312077 1250 405310827 405310847
    0x306061401360e0406110301140f04060306051003020901050109050105073507050c090103020f0405060301020d090b011701090f060c02071a12091606030510150807110607090501 78
    0x3001d9200d114414140c444944607034005400c106086110380d04145c1002010f94000707070078807030446038100010000312020481e8403506400a5405018002c0340c1c0001400800c02a40302a0005080200b000005080c03008804141ca10864046200340d89174001103404074034a000707030741c041f8404201540110705028001c1074812448884054081c01d0400c1d0881c1d08000045a01704a10020401c0e0040050074000902041426144400c0d81e40c51038000524000440c0c0096000d01d6030381010801c3c03a142901203035109100c03444280030303a000d23510380440784c450b0920072083c1003034242c0d240240c4034a060155080094000c0290182c07294252a06001003035071004030420340c0305402001980e081150a5940b914140c10081511018000c1805619043c02400494107401106440e00d0340ca076500020820b480a40c46e00092a40e5116070002c445603840d0415410203a90754440700c1c51507030104807140308050380d940e201c0c041000704000c03942e2880c0c2602c0302400310f42050002c1c84154450001c840d = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 405313327 1250 405312077 405312137
    0x307020709020f19020f06012403020c100203011d10050d1205120705211605090111030f040f12050a15090605070e030c15040e06010c1208010306061401 67
    0x151405400d13040b840c000385903030360701400035801100c1c0c1002c0c00801481481d00404502c03010b000c04505207051031a15070518194001170650105d01c000b070703c2004200c1c6011440440c8070442d600d5840d2882185000616400855030b14486000542200341184d005822140007914201c030050465503114004018602035400704001803180e01c003c550591a264000e00c0c25440300c45ea52182c0c1c01004000e06040106500212410000c0c0040115000e420301c40209441c60a0350300c80b600000102c860902d00312644410303100202d004050001c003080184200c441301c0321810b83c1103641d551984140c1410242c0035180d6000902c17544041464038801e19003070140d4010001d145c2c001c5581d4403017100c1d410760b268800110590302d00b014a041c10080c680112400b103802103191903503113032200e0b2644070b940542002c07104001c001c1007559008000300d1406541c0255100f000701d030f55a100800da50030921003620003a091100000b101042c0d1020021000c606039108250360004104c2070050490400b194 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 405314577 1250 405313327 405313357
    0x1060e0607050a030801050a0905041a0a060b030a0501080f1609021c09050a1119210c09020a090b0909040201031a030712060c020610031721071103030702070902 71
    0x700307002860902030002880e20988604000354102402e2121107030690700081c82c128540300034480071030001028008405110420101195210080d05001c0e041c40c0c0d00240c00c240c004001d0001c0d08600d508194143c1e20008102c983c1c64500c820707420355841100c5001c030420141070209101c0e40341c05400820b407a07020b49a1a40440524500000458035590f1061b6a140c1000e800c0380100700d08100141310005003100c0c00d0000b80300c40c10394115901c00c01d100c1c40054032140382c0000118250b25480c4101c0d5500003035880c0a03c4c0d90f65084034040d52003540c0c5100041c02620000c180c02c0c0c001c80581d40c080c02c01402031411540ca0307a0041d0010803140841c0403001d902d100c08030401d035404202610142400707480d94000a0010320740742c0b0540349200c00000942d0000380c10440150750982040c0212500208460390f07010000542000d03d2081e40c03000355004032108000c1c0084d161055800c0c0c00b9400302d980d5169074911a2000c1e0361a40000d449540058001034400c00884250750060b2000202c00529 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 405315827 1250 405314577 405314587
    0x1031e0906060b180f15040918120c030e010503070c06020d0603060615090b0c06130f05150403020f011415010203160b1806010302060403020618030d020f012301060e06 74
    0x100075990b400241c1420000000b0349142d1606007840d140040074908140c0d4040174400c0f1060300b15106d40101e02400c41d0183e40d0303007400103205002c4440d9a1040303410880e41c800304c1c200b108000700340040c82d80081d000b1902401d039413519540f20703200312403040b1078954511100c4040c82e500c0c400603602061001d000303903031198004008201c039031141e00000c2850100e0072007040034811001c0c20042e503660080036054030501c03a1100700381020814661140d24003600b041207032094649448466a041000f070590f11a000d11f01d0301004550005601450094080301c3c0c490480700e19042c240c46000385031900c081404c0000c1480030b41c0380a80100380c0b80781401a01d0410341090030703291030220b2190040c1e030b00d000120700380b1001c4070170407100040038100d110190040358190340103c3c0a6100300e21000f03010710000030351081c00c00c83d140c0d107190348458002d007515484c12194400035580c014140107040207520300224a05e400c459a001040e01c10146d030060002e40c1e18090b019035001c4001030702d41340c21040c1001 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 405317077 1250 405315827 405315839
    0x108072006150103090f030309050a0c0909022b0201080601050c0a06020301150f0c0206030c0405031515062a070e0711070f06050306120705030a05031801031e090606 73
    0x1068420100d2030002040d0070718150000001c03540c0d0740b54100d81411300e415100d0000c504c140410040b050380604000ca0605464a070140c13402c0108e440c0506540700490003c901550702d0307049071400d036000b29622001079188044a00703240341040b6140301c601402c0450304006501400d4525031100d0141443c6040200c031121003810150b0074081140d560350f000005000304149143d0302c0203500d401b450320400b9442400c038050400315005802030b208080c084001601c4074444422074001c1e0201034183c0e4503c5d403130303400546181a01510441110485625041b41500b004801d540d405000c40d01c0d8401010702480c40461000c484071021100c41c0214800481d0030314202c40d40c1c600400340355592000606554484130b003412899004040441080301e0300300202c81e484029070380c06c0b030400c4400d0b85c40c01075105091481e0400c10382c80107070180103040000c07042c8503000c400b0b80500d10b12807482481018403040114100c032900c01c50035aa90310f8079802c03030413040c00035413060307600c03501c80c20000504689410f = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 405318327 1250 405317077 405317117
    0xe06090903091e040c0216171c030c020d0503101406070605010f06120920030705040c020a03110307030818010b04090b010518070f050f0f121e0f06010807 68
    0x7000c46000400f9000c00c00850625200d40245c001d91840a04401d442d5030f68603010f071a0140c0300d42c031042414850703116024041070000302c8000618481c0244688200c0ca00a006069807040000150041d818206103142c05401200d116282c42c1d54241041420040c040e5811403d5514003600003e051240c0000240f080c0b0545020300510b60034a0b40807403400c0c030028450411a0900400d41d42400608000102c80404403950340820600241e040e5200710003003441c1c0100d40c0e000c60ba000d4100b00714140260340104028010a000e0759400d50030b1f81101100710b45d24412000000c001410002c00614669141e4070903032401c00c0480c0011440b21940800501503915102c01690121a010010001840c00c01040c400b0492002a4541c55181290014000c0740d280031194040c0840010407500760b1049a040320002842e4003840f546805855622700100d81d0b0480d5080c6228035a00c1c3d0404030b4004000020713204a09641c0c111113030f540c0d0b20f001181d8400000e00818103000d801c0d00030406d105404 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 405319577 1250 405318327 405318349
    0xc01180308040e040c09020c06010510050c1506010f03060f1e270c020105092e180201110601180902040e0d020a0b0615040509040c0b03070c02190e0609090309 70
    0x1140e0f0324a24241130030b0550040f281940700d202050701c10003082c50340c54004034a660445008480c80000425440c005503020311910414020340e002d43d03c030708840a180e0324042030207503030207030b880d1009000d400c2c40a404480c4a0301503251752000001d000c21402d50360328200783c881c040d2002100001c3c0c0d59900305086051941c100da442d69100e503c01003c1d090034510980d078403c207040c40280b2043c14007040d156111012480d518a00d06182c0c4144550001d2081e9240d140b080c4500c0c080041190407070a0030300403030582d90704a000824610070f00300301c0000012020705031005801c01e003e225000c2000c0d20014081808100d82040e164200c00748954401e00c04110b038201650087c1c486240345290014403210010009446028002800f100c4500d00c1415202907440c180d81031000c81e00d49050429104100764802030000100001300142a82d00c00c00c0d9406041c421740303604100a428025103c403449050148a5840c000080000d2042c0f4214003010380007808081600d01c4c220303840340460410420 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 405320827 1250 405319577 405319589
    0x7020d05030403170324010e1c02031501030c1403010f14040209250503100806130308011d070c020d1713090c050a0f0905090a05190e0c0118030804 65
    0x109003041848203070030f842d001030340090084c0c13403444c505004c900750100450140c446031119141201600b50340101c98900000500030101c6040c4e4540b180300d0800d01c4a83d4400b02d00038056000c810f46040001c14500d81070307951044c24282844d0130082e8402d5620a0b140620303030700d9900c841c0c80c051255154440c24603d0017042103a15950318207401484000c120240c0504500d40c00d4803100407071b98801c45485506099589401070340c9884103480900042000d4000c11000d00820060114000c900c1c400c1c0c481c15407080c0c031900c43c02ea82e64445242094030390098100c0742460200010400c1d40300c0d0400035100d500c002d004400300c035003640320220007211503c6120010340c0b0001e0130305c4d80e030941003a1490080c2030781c5500b4400c8c049082c03002041d5018140c05507051288003003031030b15080d0080300400007611001d4516002d030718001c2d050201401c0162541038151120b012540d00c582210b0160008240b0500300034480b030f00170303100110740003075a24502001c2d4a82c0000003000141ea000c0c018030003000 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 405322077 1250 405320827 405320833
    0x131a07060c03051501090b0a050a0c02150a0224010605030a09050d120f0912030b0d0b0406090606090b0d02060a090506040f050102010528020a030b100f1b0209040803060607020d05 79
    0x16140000e02e18441324a0544c9050004883c1c0800440142c0401c0f540360410070300e02151142c80d21801502e41c9400814003d6009141e1031402d0381240108c0c0c0a0640d0502583c05c442c04003405c0c2120901828181c6152100b96040070018849079006600540e000401540001100311180d102e003410a540d81000800052400c0c54070800f04820b800b4800c0086161b0390108180c0e0542d550380b900c1001030030003071418192107080c0d4250580c2e4861314880e4042c0c0019117407000c0c1c40c242c540500140640e41003200d00c140740000c00718200d04644680301ca8000d01600040900015801b0080c20b5002546481d0401640b01d001080382c2d21000d014100a104840030f0964043c280400039080d54070041034400300ca07080e840d0100c0317810f00030000302881000101c001030f510320013000110302404010b40e44a03049000c0040c4841d81c40d0340000b620b0381e00315084d510115554003030b5990100c01c0c001c00b8000ba6104800d4000b08020801c54001550072110062a29142c0541540840d4540a200806075081e070 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 405323327 1250 405322077 405322081
    0xf0f060f0506090c0c070e041a0403032004030b0406050408130b0912011b030c090f060c060b0303031509060a030c03050a030306080303250e0405010902040807050303131a07060c0305 80
    0xf06107040c0e070503005601c103501d40742005001c4104658600c140c0c4101c410449a0b08041000d012900100c0400381031110038408452401d4240035018220420b461003841e904207640e03c0d0780080103000c0c0c0f420fa035400009041e840d1903036200c440c0941406003090f01d090a04011613a000c4000d881910020b1541c0c0c2841525011140200301c840600314001e80440e9041c000701381802c80e0301380c10525500c13145060004040c0c0041204032560403054214010078401e0600c04100b09070004800b40c241482060144400300c00102071581b41c2c041500c0c545141c03e000a4192540e240c251456640200c001c1c0c608008542d0341d4581c01c18010340c0d5402036178950000d201c92814540e1500500b40074002a000452660070142405031400b030048a0348080003c091900702c205a00c02c0c044074601a01c010b106001c0c0b941c50301c155200950140c402d1400d613200b91880000d0905021060b101c4070503956580210062a020340d404115030f01ca0280303809030318108055000282d0520500403150500d940010310340c = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 405324577 1250 405323327 405323329
    0x807021207171203041101050318070f0302120a0c121103010f050711060f040b1e0709151b02060913090b01061b050619060902040b0904060501110a0f0f060f0506 71
    0x1060109140f140c110381041040042a03141c045d0760800c81080c40d226640796a1401c00f0000402c401070341c4240e60041d003100054200740401e10301c0c16a07008076002c880c06100d40213101d58540403c50000e25040008500300301703d03500c2443d02d0101c80d01800c00d0a60001e22000000c2c03c440003071004000d09540e41e07041c00091580300c00540001000440103114604000284000d1000e000300010b0903044035000003403400f45802070120f00c812103840e03d00c0d5642040c0c0406013082c0c10314001e080742c10790a441001e8610b44102916400b000041e500541018000e8003407100e40d60060b840142c008040c400410445803c0c0c1c81000d5030343c0d0080030340413115410500001c101d207401101c1041041c03502146a400720714040340842d004011b21900da0b210134185c0d000540501001d500900b40d43d4808680050f020304010020140804219006c00c800c0f500c910054509001041488110394810540000001c413080183e00c2100e008882c095100c01d219650a0140c50b68140c22800c8152904240075003 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 405325827 1250 405324577 405324583
    0x609070f0f030803060904020a120f12031401181428020309030307030c031503060501080105060102030c120f28020c010e01050a08061c03022b0c080702120717 70
    0x2500c07089012002072403450f00d075803049000180c07002e442072900b1000b003030440d44c8840c0f01c00c005080c0c070a10340c81c440b0880d08000b50410500c5200382c400c01c5080c400404050310900c1042940c500a60300d00c221a400c0c01c00c48601241d404001d0800550b03510411002d81c0000068580300704000400240c1c12400c04c01c051142e00e68982181c414140140180a4503400120607a54000c240c2e117400189120132180890162404060001c2030340b4110740701206020542c1c000038186c1302c0d240c00078010350300d0709001280da07486117403040c0d84280c1140701d0a140d03143c110b60090440792148100036003040301c1d5141c10030040b00801200c411900e51b03c035010107060307010b00c25484c40311003d007440249a1039200001e0403a10540d141305041100030070016900760f84007042042c400c004002103600028441c60080c0d62500f0f5441031090890401000b168041100d1042d1a0724007400c2ea540b800326411070b030b105841500310402c00c90780940320215072154030f00c1c01c0152900070540348070359888068034000b003a42 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 405327077 1250 405325827 405325829
    0x70504020310060309020d080f0c1b03060402063601030b0d020109350309030f0a080f0a020c0d050c0f1503060904080c1c092405090a03050609070f 65
    0x201460060040080580140c0081d00c00c5039540c0c24042051002403000482e070820308007000f814120041401078241041030040c201c8411401c00310341c8212920184031034115201c4084640c90307844540058010300344600a081010f082411240b2191118101d00d040d02c03c034810708407401414010a4425580d040c002c56019560540ea420b551106640009100d0300890068001c3d0300c0c0d814058800c5020244d102c1c2401c15101420000b4041c10010103584a034460400c2910900c1500c407005540500071840600d426800a005403408429207103441c820741010b954603042d030080620501c181d89860710880b0a6904c210007a00c2900080010007585100081020340620b021411a040400340350007204e130000c0c1c08075a000e910380d85d0307881c1c01032540c0b080d1441e40d0903d000b91307c0c4d0009180411034004101d0401912440130b81902d804000c3d46041034003e003105a003c00200c0d9001950068000f40b2440070058a2640c4494032074413140c0c501141503514040c160701c203610800c041828680210 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 405328327 1250 405327077 405327079
    0x40f06110a081b0c100f06080303070f0f0c05030a0306080f01180b041e080d0b0405060303070b06032a03010f020702090a111b1b0321030c0c0303010e090705 69
    0x3420401d6001005010ba6402030800e1950103806105441d80c084003010741d40740b0b03c0220100d800142d0702c0f2186201408420320380c440705a08000002c20a00e0300031090741d1040b0290f44c5c4d0000c225010311001c481c4c1c009403000e10014040a8102e00c40804c9040c001010400d40549022403218640304506107886288910a40617902d047d41c100c101c100c080e43e10625540e040300303c51940d512141005443c01d234401e0f90601c20b110344030000804002c01d40014091b4404072550811002c07800c94148010f440c0c0440e03031903616410401c411000241c0d40e00a403600904060704682c01e02d142d84241c1c086c02c0032150f07042c0d82d8407900020180300500d000d020f1180388100d1400c0c20350414903035502141400001400d000c40e8a41c40d035520040d04107070b170000da460030f20440d004c0403c56030042d07001a8460085941e20b0498190602882409040005605040000c40c1c03000704605007162460100542010f0f1040c001c000040040c0100c2c5001040950301811884142c0349007802c10104103403603c060b643c482 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 405329577 1250 405328327 405328361
    0x915040312110106140d0501020903030406020a03080606090105121e0a060f1e1a07170d050f0c031303030212040b180d05040509071e05040f080303041101030b18040f06 74
    0x20321103103c5c500c0d000c4041c2c1c0410f83e40070b1160500d42c41c00c00c0c0a0700608813042e81500c00410b0024840360300051503c03446001c0c1e00d42c2c075401d44074441800440e100743c07018140032400030042c582c80d805114181c282c6c44130901d038030001c44d0079602c40210070481007034034100e6001c2e840e50805c3c400012118654002010402c1507000512801c042445158a42d07100720071100490591401d0207600c00c40469090303a902c00d20340e62540c5264411a00c05400888007030424614110010300315401e8011031300d0040390124240f40c01d40e69503440701c08050750030210440415400340305118002902041c050300070340c850050403190b031401507203c00d2140304020654170568050200385064a400a0450b001d8032406e9038004010307034481c0015038041000384800c11003002403400245805600034003400c15034050140e5844425643c2c09829501c0c0000c0d0b602074000f040e10440009a0b6000742d21140c9881409001202540c100b42000603d5100c00c881c107950030811400c02d141008a140f24109201101b0909 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 405330827 1250 405329577 405329579
    0x2a0b06130603150b210601031509030e060a05040b04080706031b08011412100b01080a0b09010b07140727090308190e01020412120302040602060703020915040312110106 74
    0xd4403100c21981500746448980c1c822030113195445a0340c400807401c82400c646070101c10400c803072079900e040c2484280e0300c1451030050b00d001800c0600604540503050b035074500c900301051041142ca0741c80a4901c01c03d000c400c00c40003540ca40c20b83c0240c4010000a030261051524000c405001d4403e02c0c5421301042200e10024691140c002e000c05040d41c01c040c0207000d9090034403010540501585c408031006100c1d1100c15640d040079600000c410740f0f0300380da0746002034407406100410b480700c40f000d03582d000c0c0c80741005000d95070002c2b01070040c0c2e03405451980000c402100c80b45003408000d410010480e100001c1105208440100350a0001030105040000064544009180d0b0740003800101111049004080c03e60b1016000a440d1500400003150303560741c0c8074998056145020341c2180e414104060620145000c0d109403000c41e12650007500e825038030400d0480080d840480c815a2000300c0c40170216245802c4400381010f544208648005c1d6115450301514902d031100d0b14040d50ba0400c48 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 405332077 1250 405330827 405330833
    0xc0d05070f08030402030106090e0f010b100207030303020306281d0c16060e010c090305070504062d0f030605011404090c120501090204051303180602030304032a0b06130603 76
    0x704803403000390050740481d10790f1551710029024041c954029403c15040c04031071002510041381d40c504145102c80200304120060b4240003c2d01202c403040c00140e04088410004030313011350003c5034440d13070052001a00f80040b01b480744404040c0249100e101070b101d4028050b40c50f08103c150200328450103292310034a4004081d1450303124540c040c1404a80e05100481003000d0390b0801600745031420020b0064040c0d82400070002c0507188030545441c03042c4500041c0c2410284156000d540392800300c50301c0c1904082d46440f44503a0750b80c1c1112120341c160000201803a0010ba88000b45210703050101c0d041d494a40c0c00000d440b020024130b03206a18141240f00019243c04204080768040002264540100d050040c01010b5403c03010750824109010440c801843c1443ca00d0103e00c0303030300d43c0b140e000491281c40b0340303013203950044c50003680c0104003050100f40204001036041d140f000585011100c004280312092141000849103d11820103100161900c00642e64020403a000e081101c4e41c0395403 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 405333327 1250 405332077 405332093
    0x317010305120a020a1a0703140402130b0a092406021504170f07060b0103050f0103050705010536040609020c120c07030b0114040506040903021c05040810020c0d0507 73
    0x208000042c90400a0300c0c1203100d00a0101e9420036802400c15a07082c03041050051038004203c2d11000040c0c5410001c0d80d545000b640014010394014101c0c002c407c4234044540010400318400642c8405000c400248503502801580400251282c0300014444518510056170b100c81d0000015500035a03007080c009003094020690060704040c004880051000c408005840786641c06c0f0741d18000011310a080c44015002034144510a90b003c00581d80c64840d0418401d00a01004213190002c0b50108215849003002c0c0c03a10122490300450030810071503440c0070403150001350a1200400704a80c0086140c1071203107800900d0b0070281580f8181d0380d45501d640360110000381e8040041c0120311a0080c8004106541c00b456000046203103d585a40360345004492550111b441380f4100300001d44e182c1014010b400d07501e60725030002c0c000c400704490303040142d450031b500400400c1410702000480c0481005480c0c240e4400e060010b81d126084450035007094040b0321880c00f800300030083c2c2c00000e6015 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 405334577 1250 405333327 405333343
    0xc020d03030f060b0d230408040603020a0512010801050f0115171312270605090108191802091503060606130801050103030905040b031c0318020607050a0317010305 72
    0x540340020380d122007015004020f181540100e1240708000c2081000400c0540c0200c08100380011400140600c00c00c003a401d000c0c040364018450301b41803000f080b8803406a00030b0b0196a5141c2002d40c24003100105041407075000b6849000e040e9113070000c2c802c4500b02900543d003d0808202c40f0300e803000400b0405084103040854241c1d59450400001d0325400240802c40f00095100c002d603180b500b00c0c5100100114030b01c0070301d039180040d00c8850b140014a045404001c490080d142e541c100020200156110302c001030401510401e802000d030340e44c03985449102c00300b0000c614a0a500340c880d0044c440608001005400e581c51b801040243c03503900040c41c180c1c0254200d8549035115080d421040710310515034881d64096083c05c00103c10190845601000d0318400c2d00c0400c0650301450805642d03034608450340501c100f480501124251003a0400a003010300c150000c01d06101942c00700b4440d502480042c0c8081c3c0110911104040d800881c00340282400b0902e040c00b5415a19000c0d126000 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 405335827 1250 405334577 405334583
    0x140901110c0303030703140a020405031002070201170412021e0c150706110414031c11070f030b220510360311010207030804060b041d0a050d0c020d 65
    0x54004851464100700614100c200c0050180c0707441c0d04080308003a0103815003603000c1140f07003103001c0000c41c481c1c0d061099404841c8000c00400c08131500800d020000e503c03040e0280c2c1040603940c080083e6144851401e4000e070711030605050b4130384071500024101000c200d026418000090341c080440d010000e0501038000d030454265074400c0346426402020b1080d0032008103a10700b445d82a12841c200c0f00d01620031244038985881d0348001800403d0b858411030075502904440841c07209610f0391054000240c800e10f50340484210039140c00e412560a041540700329003001c0c032401003000c0c001c8100c031400d00b091107920760700c003606100b60b68607900d48060011518015030b03915201801d01d0074a0401244032408804141356080f44c03040e043c1420b060030300003500402d1429143c6001207005201302c40019805640380d0a04e52038a40d00e9174080c1013010b902541c06615410002e8050025509086076220164005c02005685180080c20400581300d118144a1301c8410f07440540c481710401e0b00c170154 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 405337077 1250 405335827 405335837
    0x10e0303250c06020a1122050604020d02040305060103061104210f06112106010e15040e10080d0804020d0803180313030c051c030c081c0f0b01140901 66
    0x2511524400a4401c48503000d82046002580010729940200b000345032103001c0e00b804a600125202400300d00069004074100341803e1104d106410340050b0711464201200420240c41c2050f004000c9059070050b8000742c810b40c002a00400802c40d42d8030800c800b4070440c042541c2090b244c41018213902d030002c400b42c0c00300350540100e0010000b990700c4003054694400e42c100210f0499503000d40e03450300304c041400204215a50021741000004440902c110016540c04000030398110900400110701030703500829600611000c180090907809441c40b400c00404080c2031207291a80d001d1030700c84208401d50612107007200303001c090303150104c4a0700010b42005c0300c56629225010b46400344945031102501c94000030030b211202e15805c0c014001142e0040d017138081c1c0581c80328100f00304616400d0740760082c40c1d1b0100c802400240264190b610090003403442508050f52800184514000300b4203d605e0203603210503483c13417000c26100d0070000c802e081c80c1121040f504030001801c40c1c8145203d01d030600c2 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 405338327 1250 405337077 405337117
    0x6030c1209080306190b0f0702090702070807211a071206050a05120a0f0b0618010b2d070302011b03020306090402091503010e010902090f130803180f070f05010e0303 73
    0x40b170806210b00802e20400302568450752080c924500d0b07040100220700c0340c5c1c914804145501d10024010303041e070300400040d00f001c40c948002c20145080302801c2c9900c109810040e800400c0c140030810555000c0240d002942e4a0400001850380d50790520240d4202e00e841000e1041d51030310300071001507520076601d2015856074245d0007403130850a54801410346040600103401c1099680e2041c1c0500d009584c030a07a07000c0c1102d140884000240900b03081c404003032100c41c1e200d484003040c41d00345403101a44a0300c0c40f514804106e225500c012426000350b9100c03146150203034464018051102120b150440c02c506115001a6035200007820181c40340030f02402003071911801541d5102e4406004000b00200000300240c640a8510f00c1d0080c7e200e03121407030018108041a60241e0310030340d070200310f0810090f019a6501496080176003003078085500b0080d9000800300820070121800b8001004148161501c03d044095280641041c1c4c104440c03404421a5a20f000054401110280a025101c1 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 405339577 1250 405338327 405338359
    0x30d02090a0e09070314010b0105180604150f09060504080a170c03120108120a020604030809120d050a0f060f050111101b090902130501031802090106030c1209080306 73
    0x1034150840811540b42c14240f01244800264400889214071400d005091400f140c05088401003000140030030010000c4410054a095014210a1004201034145616454008a22100a003070400400d405000d211206a00800b54000800840c98240d150500300750145403120482d90000309805000c2c0a4400300050440a4404e03241d26001121b03159686071690404558081c815038803203004050f400c045039041002100c01a1006400504141d115507404076004d501c014891100380c0120b00042004000220003440e04d2070403544d0204090401c90244001c0381d0400b40c003c07481502e8400c04000c3c00d00c0e01003140c0f085850900300070411001d5943c1c5603082c910050401c010880c0341c2a241d00c101041500c00149440003a6282d280c03007034880240c04102e209034076000c00740d0700400600308440d600ca40c0010459244080307252511410701d5010400742c050a0b000303400402e4071a180700f0085944a004203529081a4a00380146a4580c40d030003a0780c44064169809400c0504556440c = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 405340827 1250 405339577 405339589
    0x71407020d060f0f0b0405042d0f031e0c030210020a020111032a0a0801030204090f02030d0503011415040303030e0a120201061406030f01050f03010b0904110f090108030d0209 77
    0x703a0403642c14480c4468020084000f42510400901454504107101c0d086041501c1090703c1a94020480340c0d031030030403820690000500c07024810301c1107880045480000e400c040e0310200301f8070a807100c1d420110058007a4541c1d403d49030300740741004501030041010903800110307034989040150b001a034400c04a10201d003d80034140e00711100040c000280280e8085c090f58651151700319400081c0364018428041c5164404d289800b800250184010300c00762410b940805d076180e114010301c2c650b8040542c04241404401c14011020074408170040242c90140240151048811521202c51070b0061507103e1090281d400090101640c41c29103e0301d90f5810020b018145400064954000700713175100090280c1a00e0180404401c41741e10f0048842c1003d030103403401007501c42c07480c540b03507070920b401d0003846502c91b410a40c0c15925a0081ba005490f8110014019409186040345000500c41845001503041000b00d0241440000421198001105681c0f001590340e20140e6550382c040c0c00101 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 405342077 1250 405340827 405340849
    0x1401020a05011805210406031503061d060106020a0506040b130f0c06020d0305090319050d020403060207021509090f040314040b0c06010602030f0f07060e0d1106060907140702 77
    0x12142d0729200400510140e809072124100d880341d0110740500010310310842d0200300c201401d078a2030406100a01c442030094011001c0d00d09100601c004107030b13890b00c8400580c1c40c005480d24045500b004480c1070140c0c24440075000d8201d0b07000801075183d0300c0c1d40d210f549160040001e01440844000b150b000d20100042c0101180c0191003100820200e04210720f0740003951142d003000d0302c100076415516500900075540300d04110000b0b142420301001001009006c1d0050b940b0801c14200030881c1c80c250310784003a2010310f0140000585404c0c551050104c0c03003484050ba00b400c418188200d4030940c2d20b054116074025403440300c42ca090384942c07900392180151003c0b250b00070000820701190b1400143c0281440c42d508100311021070341d9502c0260384070300c2a0088030381c00c12002c100110101d8090b0005103030b0148591800a50318040c0200c2c1400c00d001c1550b1807000a00b03054013201ca10404002085c2c2101c01100d2501c400d0030140000350100a0014405109400204800c019551070038010a = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 405343327 1250 405342077 405342083
    0x16051c050c0a03050d030c020706080f0a0e061018090c12050307050a1a060a06050406031a0310020909010b0c06070f03020d09060e2407031104080a050309041803091401020a 76
    0x10b00040d140d14089880719078000c0039800191070b000030900700c10300c000f5045080700c03203648404001e5150880e00a000d460020042075000340c9404080d48140c1c400c004462041d00070f0204c50300c00d542490300e42008100c44801e0041c2031400c007890440454918084001201c0400008000003421460250b06500682c10003404034010300d800c0ca03041c403070800149443c880c51400b0111880d0b42c3c074020405150382600440002803014042030201c41d000342e20680303400c0508580c460300314a240000914145207801d00440d8280c002c201003e5a04201c12024094100200b84034240340340055030569840707000707191604024400e03001415803400307981100e4100000310014000740209050480240030380d0354910501c5d214a61030400a070040e84110341003809108020582030312201400c40190604010443c40700008110001d00343e10108101c4400c28482c0015586447c801c1081000300c9840c0c41c017000d20051040003440000e5800804030741954042031455181c0300160300101e18003d580c460003 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 405344577 1250 405343327 405343339
    0xc21010f081b2403070e09010603090f060506120316060b123304050601030c0501020d050d050903040e150103110a0c02220c031b0905010c110301020d0216020316051c050c 75
    0x71010155001400c6d004d007001c2a501c101c02a682c900303046044503035107940585007140c0425035100041c11074000f070b84c10901c0100039486152030195413b0a541c4405110b0904001d406400ca04022140c0036501c0030410884450034040d000700c03555500ea8001545005010190714034030b04804000440d1106a8100c0052100440c82c2c945403403a900c0000380015200f0114030301c40090103610001d1200d100a0959450900b00410b6014641c0a030070007610a0300385000c28840480c0b503140e4500910f00ca285240c46003280b0000ca8000501203411040b035048418004110140c06940c01440d003085e0030b5419110508a091600c10508211001813058092281005403c043c251b9040c1c208100b201c8265101c03180d540786008040e40e00c12001e110391408a02200c04c02c1c0c005c03800c05800c013002154007900240c50200d410030100101d0348000c40d1504046562954030066090030000d01c1c0c010050005454000e41c00d180c000340c1075084a4001c090220085640c100c00c01906100c0f07516501c801801c0 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 405345827 1250 405344577 405344581
    0x3130605090906030607270905071218020a030b090c10021501170a150207050a0f1514011a0903072d060e06030c21010f081b2403 57
    0x4020410303440100002e1150082c100030405524022561a006d50300984401240d400c200310000c465405c1595211183c0402c0d1800040c250114000c4d98880c650598449c0c4001286c241c04600300c0308600d21038840c200c01026600011385400158000760380c1c102191109990301d56000b58548510341e6205a00481c00c1d82ca003c590703940010346410002c0d8561145a070300e0fa01c4105e0052880f500c650910b07010b81c00030752400d0108844891a900c00c045030000545020800c0e142e280c1f400400c441c0840c4d003914202054000d0090380c104c00c00300116001410702116404269404205106020f000c425040b46082a00480071440c1180c0aa0101a041e2856565100c02401e1100d1000740c4d01903040308034060034000c1a100506080682c0c0e0301ea2070b0345c840c1c0352608040c0062900700520440440d0420405c8407104240c64410703840c41000210f01042640c1080ca4151190110754054140356015410031559414055101800d0120030b4a9590b58128038851201e96009104035015001c480042 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 405347077 1250 405345827 405345839
    0x30607080a0e0a0c0f14060706110708071a09010219030c18140405180303070f03060308121603020a1d04060b03090a17070b060f040b121b03010902010801030b090313 73
    0x1085022201c16017600c8803010307902c803481c50721240c07590040f40d8030860070009a800a8061360203018001c140c65400c0e410508150f80c0d4140c80c3e404110283d843c0c0e640c1a0010031000c0107100c4081e4001c425070000c0d81030081c60b203000310b18031540d610720383c007030544030000d000500b8480d400000403d441e5110841c5001da444503800446041c0d8440e803401103081900140344c0b00d842c82044051900c1010085145a80c0c000c02110b05222a007664420940c840300c000010400da400545014000803030024514240071403d2104070848886050074140140080803003282c001000701100e4030119000841d0007400c800060041165800400d82c0102c040144141c1c5d4030009903001c1564810b14110700321400501144103280203030b050083c0711a40b8000010924108040d400300305802c064808a403842c518030001c3c1300181c80c4001c5d89103e41c440500131100c00c03400703070f45600403420070740080210340c0880d00024858401404007038401c3c02c00a000c1446420100102c07400c448250140201e0191185 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 405348327 1250 405347077 405347093
    0xa1410020c18160801050603010e06031c020607020c011805041a030a12020f0102030f06010f0c08030c0a120204120308040804090911100e01080105040b0118091514030607080a0e0a 79
    0x620f110f80008141420744507514000c4c8644c0d416903200500c0706045031b1038552000c7c1090300082504d03400d40540040b489010041d201408065031035900506403d151a0800034901008030000c581000381c48080c1420202480588030300381c0b50181d4001c2881c4a0508807890949021880300e500b508c0740000990500c011656403860f0884560b0a642c05444c03101d801c40e090307000039940c90451b542520042800384d8000c0750141042210750902400a00f40b5854091041d0000c4034008210308001400c00c6002d68070011600864080c1e400c11030402c2c0c1050700d00d0f030112200170b80c01010b02603200d01240511031241c0c140c030700910007120705004065051914860801043c64514019406a6204a000c50141e50f01e0740b4034100c10b07506c0e000640c0ca00010440a010030302c00040c1442008a081c499070112031000e40d015110408001c1154a0102d072407115958072503200309054a40ca80d02c00b0038995011403d01d80060306e51074040c0840c1c694404110040403006001c50341d602c01c02c910141000070b11 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 405349577 1250 405348327 405348331
    0x305030406080c0711010f0e04060905010906061803020402070c03050609070303030c020105060d0308061909060620031e0d090b040201090603201e0a0c110a1410020c18 74
    0x5a960301040d42c8610f032800071140502c4000500c10907514807480700d07a511940d003440c44e241d0289442000c0030b030440082011207084c0e8100d1101c464643d00180021030050291000030411860030101a000c0c00c00500d0200c607090000a00c00d540002e04942400300500480000d90303080001c0e2411418100c3c01c1a42c1c032503642c031080b004a400c0031204c4040074010f2144d5886000302034488c907070004442c1e40445440000030113050303001c04811400940840071001c0070380a02185000020900e0030060003030449081d40300549252845c200d15154540004025a40f0480c8007030341922034050510350040940c00755807504001c95160a00c8001030007018400c56000d82c0c000e8940310300c01a140c1c0c3d000c9058070380804600c01c45000d03d02c001c00000098030000e00248008000b61000203049100c0c046d400e6000068090004004082060038080790782c3e40001044000c440305c0301b21924220b040d0110000c0d11031400d20694640e41900f020034002d024152042c60010042241d0944454080b0042c0703c0c1 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 405350827 1250 405349577 405349589
    0x216061101050a0504050c040c051902070e010e090d0e0a0b0a030c080903040602070e06120a0b160216060302090a090f0f05060603041a180a0f030806241602090103050304 75
    0x920b00880c402c615580704240c0900e40081c051300304004070500780405424080840002c0000802030083da041c10405c0c2c200c01400ba0386d016044062070414541005441a0012070f0070400200c14001e010400107a004450841800d00b29040309038000025100302c0564401220b022000544165295041d400920b840700a92201d031825250301e120a0b44d60b000d41d0040b400580d00c040020300200031280101a40010028968a9141402100e913420441000001c5a00122200621401941014240719050b84131300c0140740c0b401c11003072441070f200c01074824038060503800a64040702c1e4880c80c0c4844013414078203a0902000b005072542030b00420342407114580c1310707240202146842c0707400d10031640200e4209240c111000c1d03180c0c080c07805030303580544048120360786582d405850300d40503c410640940a1307401008110014140600030210043c00c080c13094407030001c550b00081c01c0c11458402d8441014106445444e0310b80d01c060f1101c000d175000303940a80301c140000100b0100100410560700 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 405352077 1250 405350827 405350831
    0x40209150405180115060e0f040b0406090204081c0c08031e160318020a030816050a051b0910153b060a140d02070803040c0e01080d0503160216061101 66
    0x820b161305c20042890140c000082c1e52a881102d6a01d000a03400d180803400403c0000c41508440c0050b04a9040d40d200b1002d503034000c40d04114180301404090031005100410101c907606004004001c41d81d1554014003594010022036190b10480010607008403681d010121075083c800541e110501806c0358400c0040c0c1400c40c00c000007006901e119007066405002e2281c1c3c14210764030101c0c0d5406c03050207100d080b0759600d261004544108800c401a6000320302804142c2c03900144c00704c1c104200400140114000d009201d51078180429031021034202c00102800700c1c0c102d00c03048403200840812400903460120b10240c1070058155144080c600c5401c1600408140000f8040c4600441c2500c030042803000c1c075000361034465100185440700080c400146080107e0303940d0b0001d07402c00d880503642d0254048040c410b8601300d0b1041ca01400d04180140f05030170f510180201a84030082c102e00013000811088121103008110f4808000403050242e035429485040080400107007502d90300c802d40c = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 405353327 1250 405352077 405352091
    0x402030f040c08030c0c09071e0804150b091303020102223008070201090306091115040b07260c03130b040303050403060203060a180629030402091504051801 69
    0xf040001207800000c418001340103409850390410440b03040040041060141ca000e1210300c114403519045241c2c141c80e12440805d0915040800c0000d51003582528414501407414005035030f202c2806900c014410441e00c0e400e003a40c50700700c0c007a0182410270410b0014640c164240c10003401d4a400c2a5a9a00032028402201808041c50081400074251181203400d41050115188100400380e203801030408100c0541d403aa280b40440704405001d89000c1c401d012150110b1420142e001d90b07240c504030003142090b007428511b1601d40310320140104580c3e005241c1d081601e94489181845199030b000403915401c01d080e41e561264810b8002c5406040005400300c0c41c00700e0300080c0e90503680c041e6203140c00e0505541e81c05000354400703080654085200344000030220015030040c00701c41c14401010a41501d440b0346050501100b419243e050b0000b00d100c1c04c5485801000d403680250100c9602c603003030300c8288100d106101c924260036005410041004408200d80880e840700c0c6001c04000c1100c4 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 405354577 1250 405353327 405353339
    0x50c1809060d1214040611010f05070906030e0109050618240a020f0d091b051c0609020109030b040b011d16030e0111040f0503210a120b0402030f040c 66
    0xc4001180c0d195030120034426680045020220b54440440b840d05110100c03504c6520060307899005548020005460340203403907240e890038003c0c10250815013405100074204000c006e03003802c210f0302820f0200f503642d207e00c0c5690a4250848a241078002c810703202e00c3d0a0001005a0a041700e2090044504c5084450741e6417500b0341802c456403511100c10a2000c0d00c40e0840300000e544a00c080c040b04030410320824402c0880b80c45200310503480b48500d480c070b02107600120765003d24540d000c6441101380c0404040b42005052440a0455103e0b2001591104520040e0703a010100d410242207100403d0400c010441210000d9041e42c03010507800b42004440c1c646802d600008442e080080740e101c1c03009000785e03400303604440301148640d0004102035120445510054000f64030005103001e0480301003003942410b01100b10b60b11140c0d14080c038245d8001240c102e0501c035109607030041004411000c02207542036406050f80701001401555a030810040d4200304200558045c1d900f0240d00300000b0300 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 405355827 1250 405354577 405354589
    0x51e1b0d020703110f180619080a02190308040605030a0501170c0d0215070503130e010f0b0304020d08030a051006080907090e0c0405072c0906041d01050c18 69
    0xc503030541d8000c001c01c034199501d01005150519550f03402080000101e070803581c80b0803001390181c00c589020400c0346030000030810403441411080c004026510000d008191001c111040c1240d0155417500202d54204407003058800203910180030a00081030205160360b12900541c00b1701c407200c0381400350740d80b40c40410b4001124030381d04544540c8210715104240c1000e03915202e4560005040c1140316004078071401103540b00a500300d403150030010f08085001c2e440d0040a014103130003000440258146288492007011501540e65a4800440010308569030b4841c0c0c1640d55501401164403070500054100180c90203446003100310030010b90100b4028443c10b80030788901840b0b0003c10200385001180c000412061000c013205000d43d140c1446603481c1c038000c01d8010450303a980c41c1c00a13003c4103800d14104000459400c40305a40403041d010a03511000c4840c2c001404071070000f40da00c1c440c0c42c0d001d4500e24052801c0705e40e50900e000c029000215070301130080300b06039055000840b5200820852 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 405357077 1250 405355827 405355843
    0xb0609060703120b09010b0a0207080f0a0807050c040606030204090f1104050f060405030312060a170714030a060c0305011a0405030a0f0516030b01150c050705060a051e1b 75
    0x50064014403501c40481d10030000f000418004400c00a040380136080401c1103110260401111b40e5400580c52420741c1d41003010758010408000075052501d48001450340341d0301d01c0c280c00b0b4520400414080e0501c8428010030800b03d000400800015541b5030000c2c001e504a03109601c102494200b09424211490091040c09c41c150440d20345040e040200300286800903541c15500060140408625501d0420007008802950325040c2d21900e0003800300078100907540c01c2498a021303081840c2d014201c00140039003d072407000c81201f90545222001c17030301e03042000201030f0030281400324481e10705070035500040c142d40c01001c1464598925a4000b2114131651285640503442540480046a10902003401682c441c50035600300301780080c3d420a01501580054542144190041043c000600c0881040d6245818140450b50341034840e0b6403511654803d49005110018014410910410403150562502800b045030426050f452090580094110741101c0301c500d11200030f00d40d0b0010701d181c = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 405358327 1250 405357077 405357079
    0x1504021509010e040f140109020706050921070f24060b070c03062007081c0e0d0804080c0708030405040e1609090f080d0b1f170421120b0609 62
    0x500f00001d0105100040c408500c500740c03040d0b40c4010a4001c0241154098000c0a00319400350311290305041407005c907600034085070a15130140011903003120441001e179095108540b060f07a100d00440c10402c28520207600010400380840901c06500d055419040300742c4580c030f0308100210741d06d50030144481d2080f0740002d807070324403a124108000b0740c0c99080b0500b0000b05a020a5240329401420045078219240440e6000c00100d803800660506031424111a003810406001c2e407654086115220804041c6507410002c2400001e02484006030807078081080c20300c02c8406003662400f000e9183c3c1c106018242c8502d0400020650403107002555440351440c000001300c150349002d080340001e24070480308494000300b003106500428441e6014100f800340b80b80010800d0841041040000210503e829404d0108041c9075590030760710500080380c4510b9102101844e450f83c0c03d10884894006450b2507115140034210800c1e15800080c0d40c00850008005002070340b1840e00300300c014003500c0011 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 405359577 1250 405358327 405358337
    0x30519180c091a06032e03142a01140d0609051003050d11010605041a010807140406050702030f061806161b150e01060f1a03060d0311150402150901 65
    0x110b40f9160003070080d81c000d42e0220034494900240307808401601450004150348080d816000c03c10700821454174507055174940040c00d0504410b00f6809009000f6286482c960b0031000020345040e402030f0310101c070020902c9000d549a01c0311001440c00780c94907004184c01c46080c500030403000c8c0c940c10b156405595004014200582c0506400c480c0032400b00310b900000c1d9255200000c103501c17940f04942e1030020007a07800350701d2401540094500480500b5600c00c110800e0b0b0b0441c00c0705020001c1d2019100c6500c0d0079540c651440c00043c0c50300743c448800f8030150084000b4024046065034640f1205044007043e141142e4442c00f074451000c10310079103840868540700703a10b098140302102d043d40803072090b46a41c503507446200d01101154007820542c40e65a642e003406011034104101c251006000200a5140c3c441c81404414007902000d4901d9003c0d404059108040500600b03140401070294001c0b11880b0300d91031410150307060240d401ba0701420f0844100301e001049042240d010328011303110 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 405360827 1250 405359577 405359621
    0x201140601051e040603090303050610020a03050c0102040504020c0c0a05010c030f081b120702010b0a06051206120d0804030f2a03120606020601080d020616030519180c09 75
    0x54400350301004240300c400410f40c0400005800c50b201400c00b03015290360000b021451840d001e0126030340544064411044600c070a1380d4a0360014200a02d681c0c50300e0034030b861720801d007005030180c0102d400c525485400400e00c0e07000c5e448006440501c0b108121049601c00d9035800056408045450b40500083c210003074021401d80101f11040d04520b451000d203214800101600d48c50340c0201e070640036046100010700c00f0b880c1c3d0900420781d02d2a021030322410f420740b41c010054514801e030688a148880840f00041480da6111610b4101c10f1070141501d02240a04400a20610085a04402049480321400441489210081d0300f180108110b42e0440e02042c4030040000c130000012010806441d5107016401c0c0d81340103c4006200030740052202d035052101c8242440703110503c140440d07100e5000c001268031300c40000c3c45809d0301c5080c00a00d42e100e51415543d041c440e20386446100c1d04116907c01d1003801d86603030480b03a031b0140050100007034a600e4114255650b40640768124100802 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 405362077 1250 405360827 405360829
    0xf040b07110f130c02210c01050106050a200a02030111040e070302190c0501150602011a030f03040e0403020f1207030e03070503070501050c070f0b042607060509010201021309050604060602011406 86
    0x2200e19607000190041346d038802000c0c80305860070350b900708500d05000d201050941d40c413a401d01525024203990b08146003440f4880000400180b148200501c010040c69040340c001c1800380309420001d034002d03000384880100707038040301003035400b038072414000d41c15100029011a11902c241c40100c04600c40340300b10f10400302000c07034401c0400d40c0b0a45040d582c403080c080c1102d40040f4070784014961500082440000c100c1007822542d0803420b543d0003600103400d9080d4002000c01100d0a940481c9104005030300d036820220726140d40d0911203078580c0b040b05544006140d2001c0640342c8244241d41d241c81c203401200c2890b0300c81c0041e00c05d03182c040c0d001c088188502e42c000d5014219444810701221b501030780d98800a012541c03035620040c40700714005000d0140d00710203240401280e03108841400c41403082031415a6969007481254100b0a0115100c21141e100790102d41200700038600084c040d54032800301e03400a04040c1e8403540b1a41c035004000528a0042c0a08503456580d0354028106540d400 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 405363327 1250 405362077 405362081
    0x509040902030c120610090b0d030810090504060548210411060315130e061602070801090506040f1403030901050403170c030a110f040b07110f13 64
    0x203401240c1c076016030b140c000d580d80c1310074103228a201c0c03501c402040d103410003501884005007660040300d1030f141040503452107904c0310b2030203510895151a120f41c03644d0714090710300e450000303035081076140174240000e00c400e000f043d40000340038070110846540da54580003040045e41441080c40074480300080c23841e415100c1c034803542c064000c031301880c0e042c41c2040040b180341490b035042a49041e00d80f108801d0105220782007205014003030040e660a403075070138081000d9440c616101c200a1007150075609142d894103158102c1e014a42e041011a819820701801240d4070900072544c080041c13107003020024464105002e4090a6070b00440a44495112921480560420080151081d0104d00c11071346440c00300304000c1d413241134403200000780d82c100351130010300c0406030108071003000d41850207001444a588080320f03000b47d03402d000040c4051a800c0100094084e045441d003122030041f4001602c1c0c00503c000b062090701c41d03041505c0191480e01044810380141c29182e400c00001c14007110030410755 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 405364577 1250 405363327 405363341
    0x130f0501052107090f060206040c0905060d080a1403071d0307060f050711030607080103110d02100815150d060e07140a0c061e1b2a0f0f120f050904 65
    0x10307107030203004c1540740c03404119100c0380d6500607401680540300b0072080c03040e1805d0502c0a0080400140800d01740a0001105880b0760180644099800034030b400c0c0ca42e00403844c7c00e810100204000d520b078640418042d004411640a06503007900310032114410303140100ba02070585005481e001030060326510704842940111608031041103000045142c50350f0200112807181c00c40d641c90000a60462401500300c0300c044020502a070000c82c007820059580d1074982c3da900c0c511346040c1080e59502054280e0f00358a045a19404c1000c0001110300c008200c002010050542241400340c141d0b40c0f10003840e4543e003154004001080c281500c0d01c001c054000804001c64517140c039607102c940741d880d00c0f8100c90052100700750340010b04880846001d028001c80845003480c03400218000e2142102501e0001c41c8a000340a1024554a080c1000124080000d0094102d0504800080307186009406101c401390150f5000071600518481a446010002d0841c0b00c20740d980d40c24a00440c05110190040c = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 405365827 1250 405364577 405364591
    0x213141f050306010e01150203040509070c15051005010201110301050d03140d050a02040f0801020a020a080c0109140114010e040809010f09050402030a15140f0f030c06130f05010521 80
    0x30300c200021541e504200c50f901a080c203480198043d4904000c4401309000c51a0450540d00b09200410540d501d000c40d141e448a441d09110701c1140051500465501c1000b030702c454840d1411060051500140c8000e6007034407020303002008071740f15815088402c4d01091040381d0b880f40c1c1000701c1000003403240070402280c5019950442c10305034000e421005031171b422150540d603280d002c00e0030400421032400c140f008042400017140b5000b140040203440d0300100d04013070048040090303a4240392509522151000da00200004c0d1030700050075005010f043d403402c1e29150b1024070000850b00d4240b44000c0ea000b15806508140340c9101000151101d244e9070f8216820310144000010350307a16540003c51140348000000140d4190b040f80709070040c842c50700001441080e62080d14500d8a44c1056815070410803503012495103003200011740b8140e04d01002a03004075002c2000075050914080040c00e40d02070f040c4140c0000d8a540c011101402100c116280401d203102d03201048a40b03808000d900280 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 405367077 1250 405365827 405365881
    0xb06072616030c02030c0904151a1801261b240705100c050a0e060c0321010b03062206030206040b120c0705120a030605090c07021314 59
    0x454152000d0600c1e9012000c0d0007250300c008101e003c5150520209699000031101c828090030241c59180d06506400e4000c0130003503580d04484507003401c420781198001d100420700a81c88032a0307400003860400a102d41c40e11428242c890010000101200030504c80c00b0300c00034035000004a00580382d403120b28042507045170030000c0040450750b08114801543c010f5140b040e903245842d00e0524a80700d00e603841409061702e00040111300942c04004c9845410540c5040740001081c0070000d04103205010141c8201d22000500c88403682c41200b401030421480100c03601c25a903107166640031484100d4905178054103115043d4040301c00311296458690000000080d407540303a9021840c0c03903002d9003100f071007158082400359024101c4215268001c210244490404880750b031642d9507101d61071104103540e14045240c81015209a124000a10004056951508107c0300005059002d24001ea000d40303088824244810072034080c180c050800c800c0e80d0b9400f5500d640d40c1804d00c0d000f2958950150b0 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 405368327 1250 405367077 405367087
    0xf031005090103030c0209060a23011709071505030906040204020d02071722080d08041e08040302010906080f0a1d031206010e0a0e0103110604090c0201050702010b060726 75
    0x510350001182c0070318400e80b1041c24824043c010005684c50050140d40714810054081c007090403140001c0c1440b00c03030403400100b010003000c010782d14000203071f5107221540c40c0c3c0010080d9014000404ec005c03510001407000483e5041d40044030300e0b1104440e125200e900130305c0414014107007580140600b040d07828005003040701c1030751079400c0c58141001111096101151410b460803030280d030480004d20406d10301e000e103494000c45944583c000141c010034010048001401d014291000603880c6190161454210300e0301d1403d0a420f80250200380d002991140c000304880c1d000360f55103400f400481c03484c100203540b44c0d0f03103400142ca11440958030507003608486104400b01000070b054000c031000c0880c20f843c54190001804c180c10004058030411008400300b1082e020307541c400b81076980040c50f85540c50400400f090480c400e0783c0c401001c5078904410050f10a6041d44050300400e140d600030311042800c0f00030000035004425020f003000c000401d240d502548028101904041058040c900308 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 405369577 1250 405368327 405368329
    0x50a0e1b1e0c250501080109050a02130e0a14010e13030203130e091501030f03110c060409090c0f0503101526070b270d050105090102120108030403080f031005 70
    0xd4001c41c1c55100b80d41d116400800c606a1070743c11421800e40783c0d0880c0c030b542500d04400200354034070600c544424190b8842c0401c403884010f40450700304134182c00f03141081d203540311032407100408101c0794100100d11f030516590320b41c008442c90074106e0314000c0125041e034803596286400810498000c400303502c020080408820010750051008101e5494541824034001c1e00302401d150b14400e115004110b27032001400003c001e00401c014a81d051b141100e403116243c906980381c5070400340203d600030004100001d2000c9160010746c207041c8030394801001c103907440ea0459000c0ca0140035199040d0491056507241748050381c400c941945410080c03400c1c6e55580c4150100340340e0310040c21400e16000c021904840c4070100311100c01406030108151a180f44281d00309040c540d00e112a00822a0403e12602203940312a818820580c002c0000c10013410107440c158000d5200c032000342241d61444000040540e804003d50301241e03001000203280c101102c109440a5000900064600a400d400800c003 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 405370827 1250 405369577 405369637
    0x308061c1b18060503010e12030c0f090a0e191a1e040c0201060e090309010c141e010e1b10050a0c050708060a060b0702181816050a0e1b 60
    0x2c40490300c03000041c01410103041c0350a4400741241009554441c1002201600c840c00481c1e40c01410b92000030f4440640c82c1030300302c46202d0b03c510340b54006060714010810440c0b10000d240151001c01103c03460480b02000e010a98400751282e610008501c105000141003a0030000000c065201d9002c1c0500c2c500170004046032404504040140c0d52000d0901045800c0c070f0307000d078216a1301d1008500308103940000810b001040340000380240e03042d1060001e080030070898504c40381c0d1000e0b000803003181c10714487c41c020000c80e0f000e140c9500c136107060001803641629144e030500f00c02424900d883c00801038160f607035900198010041029209003800462418090840500101c5d03020707203039600303103032070640c00b540c080c0c1e0816500300e10b08104080040c1e40c0c900056010282102d2210001d0390f0343c0180c0e440d00b101c00d040400880c0940906020f000c40c10002c10420707104c048400c07846aa458080605412008445007070702c0c0900d00300c00090340305c0404003614000189034645c40c2001c00182040d54 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 405372077 1250 405370827 405370859
    0x1407020c0118031a070809070f090f0f0c0e0f150708130503100c02060106110a03080901060b16231015050409060b040b060c07090203040f050a030c0308061c1b 70
    0x442c44c24801880080c0d60310030b0810f50455001e0b0001e02105007003089403801031490784a6200081c1d99001c801704a02c0e0240c0050a4480d1070340b400304400b809084003d0001d00307040004511880142450080300c2c50004a6111003038440400c4a04055059644003507541c02011031040120400f02c00241c00e59003000800c04944944d2004605c412000101920b00b0304180c1001d02401440c00e154003148900003403018510307400d40f40440a5440e4040141e0050485803c04000000c0c001001e16051452003500c90105104031020808100300b814030840741c203003403080c1d0a044d4100201815134002d2603004803d01c000c060007000c0d2002d41d01c400240881d5940d5000720341c030b15107880507c0c103039240c18800c03000f02580c02e03034540d442c1c1821111015114506800b4186505131701001150501071010758213040e050f4090115208034505007800340108814101c110300213101c80300012164100001240c2c900e40b8a01c40c0c803038041d80c040c1c0c0c50f8412485203401007881c10508001c0050703018180301d8408 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 405373327 1250 405372077 405372113
    0x90512030108150a060b030705030403030b090112152703030f0c0e03010b010e09160203040f0f0f090908030609040f30050c0309010509030a08030a050106031407020c011803 76
    0x840048440352600c20f0315070700200901d0b191031a1040410010305440d0440e68082d1040c82c14960340d5842d46011380040003d8410260007000c0b0100200c1d82002e44000700003400d0041030071200e52044503604800383c8594903a01c1c42a440744140702030718004101c84414206110b0704000c1071310710551079000111410030b50000c00243c0796144091f41810284a01d001c81d140038030340100b0101034038010131104003000c2d00300c00c219418910b850500a1080c0103907030152000c190014040350381d4880c5440850001e02035410842546900051414030764495510100d6015404d9800c59507580200b0080c1e4000034400d94511400180c1c150000f528403d20b18803040c00300c3c0741d09065085540800041d00203154605052100c104052172440c1d0b800400e540c0c1e01e41003482c10a5580e010480840e08041c1e20720001098180c0200c14041da0031000d42096040c0c801681c0d081003581c1404151410550060342c101c0050b8103c5585203005511035480c0060304c0c000825040b00281e43c0ea540e82d000c1d10010343c7c1403 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 405374577 1250 405373327 405373333
    0x30c040905010902030f0c0315030703060504060c0804051504081b0109060f0b0108010512070515090102011104180b0103060b040806090c0306010602250308030a0207062004030204090512030108 85
    0x5014805240c070405000d0301201078214114909000390a030410005130542c00310b043d0200020b48078020041c0700c071780c3c04c03078024050f20882641ca1401d40050700341610708582c07050600301c0f10407441d071003242c900d403080b5000340090014036103400800f101528060000c2e40c04200400000a184c010b04c0303144200d150340900009601d07001410039000b12203450b4000c0340400d080151a130116a03002d101d060544404035800415194141841850865190700140d00100b190000119003142403002d8403280c01c007a00240910600b6034040e90340c9104900858170850b00400d00042460010b61050050007818140090f1007a1502810000340e089980030041d41d41c401e00c10400c640d41c00303000800742c8200c1900241600d50614801a4a4003403008034117070001c0991915a00e00880301c90f1200003103030484000e1340d590600b5110300d0040c1d0701069081c2d90701400c1002400300c0340800400f040304111140c00c03441c04c0500319800c0002800b004a8107941d684520402c401120b107445000758001c020a00003 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 405375827 1250 405374577 405374579
    0xa080c010209041e150501200705100525020603040b130602040f0603140c1207051306110624010c110a0b071b03030903030309020324060a2310050f030c04 68
    0x131081e0750fa03414100c003c0d02c403a103608100c070740d800a01d95041016808108201000d26040340d5240ca03003c1c3d40b005620050045425415503000401016401e40300d020400c00d1003000c202c4020504249030b4008d420801c00c00014001c140c84404c0150081c111802145c4668070359225881071360801d42260894500c01c00c0b04000140c2c240c0f1810080c62000d50031241c0618080416070198000c01c1c5801707121700000400501094496001c6a4821504900030400f850b120000245088507040d0029090304c1100c0200d0812010316290042e01c550f96900d080c10328000800450b400f04143c60102e901c4420604110b10715510000d0b0703100036183c00b540c00e80d1680d190b03040c1009030401550350200a500402c80920100f64007a400038207403600741c200456a201c00e8400300e0300e0b154807446d40d680781d41003840450b80072000040030b150042c0d200b04c90898006456108501e4040700c04245500c240d41503004000c1e003406d18882c118175500f46410400c0c00d00c1c038003400e1842541d0040707644442000c00010 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 405377077 1250 405375827 405375881
    0x100504080d14040e040309090f0b093402100f0c0201050c070507033c02040c020f0c10091e051003020403020612150d1a0115020a080c01020904 63
    0x7070141c1a40600d00508260710608107098030b80701e0f900803124400b54200005007450f014054410052201900c100304100c040400c000c010880e450525102e076590b0004110350481030b40c4a100a1210600980580340c1e04190740292614140f02800950140e040c0c8201724007000c2c8140e0a5030f45e108103001c1081c120700e00000342184c1c0000c2071014811001d11220011980001381c0c2c80650f43d010076683e001080b02c0f07181d00442d071010054400490346061a12400c4075800b9000c15581c0e102751410320034102c04400591b2141c0010b18124007a600c4055050070924111004c4901c074241400c0c05440c05448d101c3d500725102c0c21254031440080b10482c20000f43c2810340101c94282294034085050a003568001001c42c07088640802500d005407010607031401880c42c4440030440000c0c008a62080c161522582d444150703c84211480782e9a400003c3c1595410011140005a40d000c0d0050007a181d54140c081c1d085440881841d42d400d1080800340d480718820300405103406495901142200e82c = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 405378327 1250 405377077 405377083
    0xd0510050d03021c09060210020309010216050d030f1b0c0204020904060e070807051c0c02160807030212010b0307180b090411040c0207051e0d15020415030b100302031510050408 78
    0x9441e01700702030710000b0032445e6408600c02169000c0d6010141c0c1d83d45a01c0c82e0240640070707810380120a4403141c1c080b9001c215002800300b282b040a500c040c480e140418030741c030040390a80c065240c00030007580190081240f0a0183c100c04074070040c00141094403000118046030550b40080041c1544c50342885091074020242a500120340e213082071804120b5160340e600100020044002c003500e42000d0846d4600038001b0019071741c00940c45c9078035556120074042d9105c81d2484180c0c02402261101d80120fa410f018203402c000d800350007040c000c1c5c80c0582690f40ca10450743c089155903075035403e070211307aa902b44107180941e02030b01801004500c108100021103902d191140155408402c040055403605500800396001140303d02c1074460001000c0b8080314038190006000b51460041044201225400381054541130940c00c800e0031020501a01142d1441c50b4059000714a40c8240000da803007038009580c03104074404965545850030300418412804041d0b05030102d140810b043c01000c42c10 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 405379577 1250 405378327 405378373
    0xb0601090e090a0f050a0b070801060f0e03150c0c010905011d010b151606061e05030f0a0b040f02060a08091018080708120a061406030c0d0510050d0302 67
    0xc003050104030b0400c0b208182e525290420020080305510841d102408410b00c040f81e22039801503400101d0346042c030340083c84c014090050101049a500944c40708a00ca40d00005284002400801d100010400c0c82c480320741e001020560f1221041000407114070782801421141803040e00082100e520048001e079503d64500914070441e07140000c90000d6548840032070400b1070304400030702c1d540d5050801144288580d42409417410303040007000102c50034088250051481c940900408281d101e200701a21a48400c0b0054501e5004400d01c0b0041481c003031010303070083c1c881c5d11800510082a4041143c2e13410081c404c1020034000300802030320140c2070042d5441c0b034a100703004000442180c0d025031800c80c1412805480c0543c0401d0381e40820010f0000c881602c0e0400030034400a2424104031406021140a035401e48240e0060003152800c0c81400d490140c0c2140312910b05102c00d04003042d0003004009c18032458000c00e1100007815803501c501d621103090090340540700c6440d1440302100000700c0 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 405380827 1250 405379577 405379589
    0x305090c0307031103010207050d032f0910020115080a020906060a0815010c0b0c1201080c0105250605180f0601050619030f02031003060b09060f0d0f0b07051801021b060a090b070b060109 82
    0x207400c2c550328600e241d00c04650340c0200c123b41524040035100c4c801c900400c074022441c2600380c040034020503210000200031820710302c201d4090000340d8801080c0b1449000d1101940c010809000201d0000c2d00b106000b829900810700d0840358155a030b4507140e04001054590a0842c100010340c2e07058045510502400b6042d62001820000b0803407000800e10b01c0b81480b1000e0480b10240c075400e10380e01080d100884d040e0060300901503401c1403841c19910382d070807044440e07583c03003084042880d50030b0100f900343c12031340c000b08600c2c2800b1024a40c100701906400101e0201607480300602d80508891010790300820300e1485003850f0320b05518001089070aa414600d00c00d030020790401409035200040d0000041007600c0d080010704851500a802c10308040000f04428a00402c0100d0f199100d80074199000c0c1c41c00890799014240c8005a071111000004600e02d200d140ca8486010700345140180059841841e103401041e640f40003003106904240002c84d241c242c04402c0c0402c942c0d21a410b4800f03004 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 405382077 1250 405380827 405380891
    0x3010f08100603080d1d011a0907080426070b16090f030b060d14011806050a090308010320090108030712050f030105240a0309030305090c0307031103010207050d03 72
    0x803d548514040d409500d081d44c9260f03403209041c480c2141030412414070711003404020302c501c4600000d07e1898004c071a040a004003084000600390610804004d401140c009281140316110819100c2c0384042c03904808013080c204100381c00004202d400c02c46e02c80c0c00030b401150300401c100c0400614149043d40854101e03000c10000f400483c200240c800c0c0c02900c111a21881c0349030515002c4102c03034480d00605140e51030150103017010111808040442d0f84610700c10821039941070480320460b07a9002c0d0180009031204014400101050740e0340821103080302344074400f80c1d0480009203102030242c21150503900f000c00c950f010049280c0100c1d2500344c1c103003403060400010300704181c8180014030440e0b01c5000b1841c105c0c44c450300e6489042e403000e1400305015a071264049800b0b406483d010b5004c0b00028134002c00103103180004240680c110100801030403810b0310359240d076030f072080750818950f40c955401c00407000000d0382001002003540b0143ca0100b848c0b00d0f65407401042e0180303019801c8100c0 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 405383327 1250 405382077 405382079
    0x50a030801051c150203070c0206130905061819020d060b0408060703020a23091503190204050f0d0203010b060703230f190306051e04110a05070b0711010203010f081006 74
    0x7085a000d03000031301c040b8000113842c1c0d6070703e03441111103c05002c80650441c3c1e0018103200008a48a03051064509101007404151141e60a0040301e01c0342141a419040754400842d180096042c40d40b82242c0c01001e0140c00e01210816a104590146d884401d0911001504220f214401d20510f640254541030441c1010400390014003804880c501c0300003144145c8207801801c981540c10341d8070f21900a0701100c0103001044242029503c269044000010407446480c1c215000c0c0c002c4905a070400382280143c051500284071000c250305904070b0303040d526408413041603140e520203050198040d588141c900748068501d10540d1150f401040e00c11001049507107074640c4088111542c0c20400c4154922140074900c0440007851960000c65101001020310f1204000c004c108000d84001160704006441080c0c0d0b0700d03a61882050030b00004600b040c4011070100e8420051294481c03807d0507c0c000305414155103a003203070700907041341000812200040c009882c04100c1000c40c0303504414204402 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 405384577 1250 405383327 405383333
    0xf09050715020a05060127061a0d020906030a14070e01090627060f020d170609091009210516081b031201060215040b0a09030309050a030801051c 64
    0x10340c0c0a030090001000790000d4406540340b00f0456604120b420106441041d612201c12803003070805045410740807103440400001c0a4020f2203844101d80091000c034000e21701210030501240c00900344401d00310b40c20300240c0300700e49424004520480c0c40703000c0001e481c5c0c1c85986240441c40c0180010081002d44081b404450760024142e00580b0043d0400c0c941d1401000c0355808008461079140c1c8d5040c2403204c0020f0280e812100f1701010800680a4454a40301404200d44100e009611141c600d0700d10f0010038201d003480d0840d540c100c070044040d1401401090000e000380c560009c4111060403964a030343d03000326041d140076401d131103d5144c2145888107010780c0005580302460084c00c10b900010703201f40340c5041044107403280000201900d4a0786154402940301d1b0400348900030140c00b4035170303d09101e07042032079180c1d1003150722006a00584d1201c0114600405080d0303001c5080c9541c411405000c10010040b40d011540300703645240741e030340c1450280003841840c0b000d00c0d60315003c5540e0041c00 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 405385827 1250 405384577 405384583
    0x218040b1b07080708041e06081b07020d080412030e0307050906030c040c030b030f0303100503010902060a050c010605062703031c050613060b0a0201150617100302060a020d02010f0905 81
    0x8080d0f00300107a0b50301c0700080c1c200440c140c031076580301c0400486110708000c00c541c1c0e000070180445c0d54030740b03c003491591010040e03406418022031500800804001200c018600901002c450340c0c00b4994803030030503403914180b5141c40c882003001c1c0c0200b402c42550308007900c0c040040002414007038540c440d00d2304040010955501c1c00c103030603500c104e0702c40040c043e42c10301ca54001d9a1014006003100c440000c006003440d01c942c000d407607030381003204c00400201340c5041c14025020156070180ca01c51518040c150308580b0f0f90024006031819548481001680750380b4000039003508040d6014028031600d03524046040e5102030b421481c046d40043c41200110f044c018a4000c11142858020680343d40b01c41c00601c3c075444000003401072602d00040441c407503803441d003d003c40200e941c0080020316603000c83c0c4495041c280c411a000140780ba483c4c1700356021b902c03000a404c820f0300c0020041d43c80d2290700041094001340c2e100700041c7d0001510311880c550900a1841c0c0b81002c003010418160140c0340c10b51 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 405387077 1250 405385827 405385837
    0x604031203050a0e0d050a031a0603040b101a120a0507050d02181807020607020c0a300524010503070510020f0613030f02010c120b01020a0218040b1b 66
    0x41c580d4820010b50620525044005428440010b40702900c1c544071000d021a0000b0012200007482e148a50500c0080d201004008400046c03d8904650b11035441201e070050050038007200c41c0107504005004a0613007040c00300c0274201008151500c40d01e56003a0801100100f80c003112505110a10014079007000856040c4032000300090380c0c6850005c5001c050381603070f0420383e0700311003554101b40240c0058400320b40a092140e0a071501030321100b40c120707581c001c0c0c240d03150f03400280000204038441c1060032214003001e0303448210240c4407110b051100c815500030b2050310380d50030650120055441e15111200590300c114820f1003d54100741c003090381c0f2400f90003818005c90003110800c468500800582480078004000c0301c0c542d01c1d010113408040452624202c0108551008040b90240180190080300034181d0300d8511328000311041c5c601920f05042240d0640c041e0000303903405600d6400d207003036210742c1e4080422580d0a261801c0d0050f800001c000121081303030082e11007954400d45085034 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 405388327 1250 405387077 405387113
    0xb15100e0a0b03010306050a0e0a21031e0c0f0c051504060209130204080c1f1d042a03060302090712230411030f0a0f060905011d0c060403 61
    0xc0c04114520100740c1c03500c800c0d0000015120003100000401c1015005244130b44d0100900303200140c3c801c82000c0c2d03280b1070030380001d260b80b000d03a0300101d082e0a80300400007121780c00e250100d80421502840c0618044032000344640540700d4515a1075140c2000119000036800d1400740e811311080c0e1603694442c2d4050000000d4041c1d1100420706118054040d16800b41004001002c0005250345820081d401032082c0714080c0a040110943c0340380a00103038a0600c0740c503001c0c071800e09942d002110250f41e48524100340d00340c40700d0010320580740d031320940d12a91144800240c40c0d0070f8020300c40e81810000c84076030041604050f4240016120f0243d00790f04a415820700c0c1d0301201c0b03e07a02d000040c0c004440b07543e030f4180c0e4250f0540c184540303001d0507901580c055441074040d20803400c1495102c106030080e02000e0707800b03405200c001540b01e212550b1024000c1c2000a840c0301c0700e580750340c2034500d00100c0070000c40307440181c24101f100501c41011518070840c0d8551500d8035640d645100c03001500058 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 405389577 1250 405388327 405388337
    0x41506111507170a021b0708010e010b0105030a05040f05010c030902010306050a29040503030a270f15031b030c080907150503040609060903022103010e0f090f190b1510 74
    0x115400c42d0458042c1e49204210300b01016641d16007404040d1f8072500740c42818500d40c00c00d4207082e018041131003510318061041c1e607090300d103070b03908a0000090a00504100ca000207101c0d40440416800c1c030903803006460540d00400c140c00c0e14000101030301e4003504500d02c0f6034010101000b003030000e8022241880108889998030801c40d080000060040303521950f018040090060441607104058451041c500d404011543c2030000e20180c80f07860600544000c03006c010000d00101000b0003002105c00c155140100d242c0300340e040409201c03040c003e00c1001003926034000002250f0007104050344002d40c00700620595140030000034031145015a20030a0000c000301180a01c21150000300e10305421400038080d030400340c640256111b07110f801001200c102444001e010144100441c0d048a641501140b169182c1008107010000c000d8082482840303200d0f101121500244164007640d0401f07420040311007582e007014141c40c5c05c014021034103120b51041810701a44c0d802c2403482c0e00d0015240c6 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 405390827 1250 405389577 405389581
    0x3100f120627030306030c0801050411060c1204080d030b010507080a0f0c06050415050c0c2503021c120507030f120e0f0102070c1a0a08040204150611150717 69
    0x2c04541c1040110064118201c1c80890414960907030030950840b4130600703903c10b541ea82d03813405034203d810aa40040030243ca108200080f031030150b02501d2459400360944e03840001c0000340303264030b80c4958049559034000318048010309806109101540030282443c1c0d2900700c0641d2441c40d903101d290285c1e018803141e60f0b03200b11024071a850603280140d1180003000941480d09081d504500c504220044035410300002910189003181540c040d52100c10040184c5450360240e0401c807142c1520055549078001800005031307480340942c21304100c1d54000c2c068240141c3c00e04074000300b0100f034182c0030f20404001d4000040c0c1d006034030040c925407178a0450f80c00c5a80d4080306000c0c0c40205400b940754071411441001103d010350042400c2440f03065280d4001e5980d02d00c13103408031220350b14240c401c0c00a01265098a02908800d80d105200800c0020070525802c1040403408040d00300c500000d04800a24400d131130700300b0031410003580341c0510010740d160281000f010154a01000901002c1c8440 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 405392077 1250 405390827 405390851
    0x6090b0307091203020129010c110d12120c030b060405040b120634020303060d2603011d0c03060402070203030c07030308100e0f060f1309030503100f1206 68
    0xb500c0d40034103204040054030494900f0000d0180803e150101c17040000039000c00c4428240310200c880f00356040e1181031840260342c03101c069a4041402c00f94200d03c02140c030078001008140e070045122015107a800b00e071170307881004200316021240100203041c0f5000e0406c01c603a5881060300e0071900100d4010402c40c9841022175500001608918240e00c00c46080c4080c100c183e0040990068542c0545809441c0c42903c049011011040c04009a00300b00f010404504081e0f400c824054018800410317034102280c20929201c0908140012540c1c010005220318034a0326601c1005030031900811440e070504c0000c0303403244c4c40080c00c5603120b554005007500440d1003d0094820b42521031007075900d00d954909020b481c0c40c2080700d040c40d6004100d0f9010426212286d29540113021791244d00186594120602c4501c13076804500315400b00c1012400a0652218043e00d010a80700780d440300c0c0c0303d0400b10403414045c002c90b081107070100ca4144c024080044022032243c80c0c20f401801c08248071130148 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 405393327 1250 405392077 405392087
    0x50a060f02120123010327050a050f0607030b04150501030506180114090609040f0807210903060e0d02150c13091e2315060c0f060903030106090b0307 66
    0x120358903024190000066580c03c6031440f107811130118141220b0781c00100c0044007101c3c01560351141c04400d000b00182e101c094414040101442041140e103e0340703298444c503143c51206440005154481303400c110000340e06000300419648265400e110030038010f500403c3c1020b40f40511410140d9800c0040c0c0f19944240f0b829104500590f449003179961201d0801c40030754156108030f0f004a000c0d40224909080011040e88a550485201c0e14051495603888901e070b401a03000307036103007613030b40281d95103c1c0d584c55813078001c00040d501c40c00c2400c1c0c65454280c0c00d94100308442c48543d008810564100c86d008103030460004007c3c102503070315598040444620340078820752400d10b450110320202c0c905149034002e840d50000544400c5450754001c01c504240e607200d215040302541d412052050034401d20b2100c070f4100c0c0c00442400c1d002512000801c4468101548860b410350020300341140c0c3c40380a1005a0300147d41802841c076540c1004009040c0c80c0c503600c11844040c000000150900c3d00c15 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 405394577 1250 405393327 405393337
    0x14040303020a20040c02031213051209010323040c08011518060e0c120a09080a050a0201200a180b0703110109050105180c030f0d110703020904050d02120304050a060f02 74
    0x4c00401c151958010001e41d40c0d000040003003011943c200100d295174014520500106901100500361003078084820a100e81012a419041c10f4603880402014a00002400c00d0118014480710851405040081700c0341010360100400341d00d0803140c20b200c210401e080c001034600d114220f030854126092410014842907020b012900030380410300580e4683c0e140142303918442c0c285aa9919140c01e0200c0084400c40400185081820480c5201c003500800103051000403900001400c1d15804a00c1051000400d044038280c0c0c01c0007a1000e122504410b038a2001015103900310955410b100350f408280c49050005020f00800400726030942c1401d40160240d2a400710080c030240c10030f2181c071000200c942201a0040c010048800c0940c200003510040300d110540080107071a80101c400c0c1c50721703e21480410b0407809003c501002584030041c0700c6001c1ca02c0f910050031400c0720204000c2c01c2c01d00003820708081400400a01c000304500040035a065a040180002c9250030fa0807804000c0c862 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 405395683 1106 405394577 405394579
    0x40f0614040603050403120903030c03181208060a09020a02030414010e0901090b04020729010509131211060a0603020f0402040308070b0714030907050114040303020a20 74
    0x402c3d0445174215020703043c842c0319600309070000400d5680c80107080d00400d0701d40304400c025a0b07061007801c2e110227559003807031001201940c415189110480f00c1e00d08100c1c1005c08030381184c0d80c142c5800d00030100c0f400115070301da4001e40e019450390051b01c00d220f102804031304949504c0d4020a01c080302c030400100010940d80c00d0500346001051005034a40d0000e030f09010f1240016090445c1c204079600b410241081c0100d40d040d1880b100e40305822281c020f803c000e003400210660001c0c4042980d6002a801001d0b1120100c200c9110000e40c050100900c108820301144082c140d1041c4152802910038251f29032000f0188401d038441c5210003000762400308425000f00740b60b8a070709a04040c040c94860600c1906804054403034005540070401360300b0050b407c0080c0d41c1c0003c0f4100c1c1c0502c01c00941420245075840c06515051058006002c40d03100544401a00c01b20035580b010b00d100c = true := by decide +kernel

theorem cover : BRFrame.Cov 405215827 405395683 := by
  have h0 := BRFrame.cov_init 405215827
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 405215827 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 405215827 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 405215827 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 405215827 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 405215827 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 405215827 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 405215827 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 405215827 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 405215827 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 405215827 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 405215827 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 405215827 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 405215827 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 405215827 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 405215827 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 405215827 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 405215827 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 405215827 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 405215827 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 405215827 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 405215827 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 405215827 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 405215827 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 405215827 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 405215827 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 405215827 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 405215827 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 405215827 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 405215827 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 405215827 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 405215827 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 405215827 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 405215827 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 405215827 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 405215827 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 405215827 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 405215827 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 405215827 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 405215827 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 405215827 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 405215827 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 405215827 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 405215827 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 405215827 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 405215827 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 405215827 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 405215827 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 405215827 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 405215827 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 405215827 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 405215827 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 405215827 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 405215827 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 405215827 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 405215827 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 405215827 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 405215827 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 405215827 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 405215827 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 405215827 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 405215827 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 405215827 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 405215827 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 405215827 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 405215827 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 405215827 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 405215827 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 405215827 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 405215827 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 405215827 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 405215827 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 405215827 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 405215827 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 405215827 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 405215827 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 405215827 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 405215827 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 405215827 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 405215827 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 405215827 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 405215827 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 405215827 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 405215827 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 405215827 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 405215827 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 405215827 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 405215827 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 405215827 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 405215827 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 405215827 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 405215827 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 405215827 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 405215827 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 405215827 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 405215827 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 405215827 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 405215827 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 405215827 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 405215827 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 405215827 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 405215827 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 405215827 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 405215827 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 405215827 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 405215827 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 405215827 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 405215827 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 405215827 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 405215827 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 405215827 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 405215827 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 405215827 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 405215827 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 405215827 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 405215827 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 405215827 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 405215827 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 405215827 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 405215827 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 405215827 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 405215827 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 405215827 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 405215827 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 405215827 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 405215827 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 405215827 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 405215827 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 405215827 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 405215827 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 405215827 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 405215827 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 405215827 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 405215827 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 405215827 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 405215827 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 405215827 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 405215827 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 405215827 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 405215827 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 405215827 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 405215827 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 405215827 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 405215827 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 405215827 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 405215827 ≤ n) (h2 : n < 405395683) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
