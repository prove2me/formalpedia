-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_2129
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T05:44:10.583987+00:00
-- url     : https://prove2.me/submissions/3c6c6118-da3d-42f0-9fc6-909ff90ddb2e

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 382733812 ≤ n < 382913669 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 382735062 1250 382733812 382733839
    0x40903121802091302030d050715110304050d020f0601060e01020708010c080415022a0a140102040f060e03071703071e120807020d11030d060b19110c090a1404050c 72
    0x208011315007030180d0140c002c50300401035180b00ea00200046880b554000c0c000300c2400040804449500c0583d0011400010911091080402800c248240307140b000b0b001070faaa00c007070316440d08018481d400a0110401e135020042c0c0c02804442d01400022000b08070500081c10700501e4010291419104d0498881580880030000e00840d40300f40c0b580320800110f90a614000200c29881039104c9507a80604180c09000810929040b042801d0010015071a98103002e06502d00b41c10b16408081171000100480100f80c50100e13207001103d12401c51040110a07011010342544580800100206a106c0c0403a101a0034403031204403080c02902d140b900b0507081700f81594000020741c0c101d0050b030700101c071a00c4800e21079000c00c030790f92000b4001d4905090b6041e40d090162203051b04940c1c21107101007000c0c00d0320031066203504044006403070b04031150803c2c030103503d0f15810000351090203481c00300006803840840303800c110078a24411481c07221501d090f00b0000d40702c8a0341500035110304001c1c01c07902c = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 382736312 1250 382735062 382735081
    0x10e0105060f0a0303090b1303051b1017010306090302030f2209090327081005060301140105090c0f0708040816050402030c0a0309170301061709060c0904090312180209 74
    0xf0015203070b040d114403c0311410700b0011240c58012807004507040292105c0400000d070709104003d0059404940805884161810407940441c03100c86a0104105484d4040c04180c50800c501c0c1100c1c0c1084d00010300345817a0508a040d4032460040c0460083c0001e442c00c0602220343c01c0e00240a00400c0700b1010320749914813802581d000352800303000100403060660322072480c01103d038412400c0b0700c0329000c4940d5407940d1705d080082445010051564030000c0002070709081c098500074180e0410044125814400042c51410010709000c1c040a0041004070040c40100220ba4455411208040c0c603159908201540d500c030307a0300c440300c2580d90454001a0b508142c025280503c245d16070050034099812003c400601c0000001e0f110300c0100304c58482c3d200c20010056010f882a5a9070401c0c0001e01041c1c56111000500540da2541c80f05040003c000030041c01e0b0341240324111030205005d901c5040490380100440d01c1c0721803541c42c05c80210041e040c640030b1070700c50a00c02e44e1006090b40d5001c181 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 382737562 1250 382736312 382736329
    0x306060e0105010c08220b0d15060c030809122a060106050d0c09051320030f0a090203031b010c03150b03060f15030408030613020c0a081b010e0105060f 67
    0x2460b002c104d110f00d070000050f078150301404240c244130380c4401c2c141a05d5001c020510615a024841c502d200007a0002640094003a42101e00e04400c6440050340c036020303004082ea07092240c04be007001a96800304210480034000402d04400c2c0d25038440d2921860781c1821584040094051020220f030140180445404030f03441d0304968854a03481e0410f149001683d000d081000c1481c1c04000e18003001143e03e544a0503002d90b00255442c0001d003106180740c40c103040700e42c0c1100c0d88801d60001e104002c001d062031043c06610001c0c070300000c20014600d202192440c00b80c40004010701c0d0381d10010140000d8154000404440295014407800030020504441d025081c00b45107441002040050702900300203980d0030030907001a0024900c5e5003100020800754200303580c01c441000001041c000740c0c0c0390045040c3c0821101020440c68042100340f07130340c1d54036101074009100d010b001c1400000b06440d00b01d491750a0310800001d02a503442c00003500e0080504480b1244a22000c522400103805c1c00444e = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 382738812 1250 382737562 382737569
    0x160c0209060111030423010314040c12141c09060504080604140c03030a0309050601050609060702040b0102190c0312080f0703090c0f0e07120b0d02060f0408070b03010306060e01 78
    0x441a52540d1004403140b1030710f07580400b480d00c0100000a9491521761304602c1000031240740303003c03404e503142c0018240d851034280001c002400105100104d00380341504000c45003075085080c101c0c101850181c85022030380311881803a004403007841c040c40072064505078082e02e455031620035054a842054405001d80d008520742d540c41030000500046000202180204080080700c9164013010002491940110071980005c0e848001c89001c2120412403207016000071500e0604282c185004100180900e41d0041e00c541c0d156104005683d0080c05241070300110084510120410f03800d014000c9415880221007184c461441d94001503c40c00c0c0c0203005500040000500703494829040b4054a0b2200060b613030a8800c103400514050343d0940200200389411300e00c411132a14200182820444010340711001c0e00b800c1c95050a59106150700d65007990448505031036000b0703d00c50703401c54016a00440b00904c1903100204a680340710700598102c92003120103002c21038640303980d00381205c420b12 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 382740062 1250 382738812 382738819
    0x6010201111804091407080705030105070e04020307030605091521060f150d03030b040e0c100507060608070b0c0607020109110d081c0509070605070c0e0c070614160c02 74
    0xc51410b60002c4007032810140381c0c000700080b030160113503180e0b03003416186240140910f5000741000c20281d001440810020301d0100d008000520b840d0101411245400c0f002d180705070350001c0000c000074080e074440c0740900005040f05800d89402502c01150040310100075128510824a00100404041e0540b8188010742d01420140c0c80b43e8101c0c244600024100f420402913503c0711000c243c441c6034018003603d01981e03020a411810605020482d07103600f0350100702d0313048a030a06046441e181d880754084455441c000d036031400c40d414000300400480c0c0141b4914000c8072000182e5188007000340612901a1040c0d54154036070070710270303802c0300c0380040c0040c8400940c115060241c506180000020f60184402c5481c21054bc0c1c9200071031010038110b811180d41d03c40c144003550100700030b03100260109090503440d0a01c50b40f00d45410300007600c6001c1500103140700191001e08a8815900b07070356403094062100e1050203810700c11078607046400c4c1c013520550054103d10b040c032690031100c407d030300034 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 382741312 1250 382740062 382740067
    0x318080f280b061206100905090607020a12020c04060e010311061e031504020d09030206060312040905070201061206020301051f050d05060307120503040801050f010602060112060908120405060601020111 89
    0x740c1d9210b1444200038200d81d4058002440900e2211040c003240f440b401900c030b941505103040043c460308a0700007130708a84065100307408100c0c04c02c0e000503064202c40c1d007113000c500400c1da0320700b0b04030710b0f10354a50f0b61640c000742000307000203a0100d42d024040c140ca12038800611099070540500083e80210070600c4080d50140c2032003c0c885c455007004540010211600c14103120044022901340d0b401480a82030083e138620300c2000349603051102d69006101180601107060344011622800e001d94003880000310341d1074000c103500b54000d40c002c078002d01c00080b5400b01c4080d18240340c03000350402d129031406540004842c110100c81c0500c064554052921040c0c00d05070071013000d000030302c0001c24842e054814502d002c10b10040c0f02560b00b49031071090380250350382c1d4200581c80d803d54074003601002e80000300300010700244c0e03008101c40e810340d001400c0c540f10803000d030305116010b050102070240c500e079000200000240c0880c000c19105a000e40125022074071031800490899038400c011130b001c880107 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 382742562 1250 382741312 382741393
    0x1180c0902070c05120c130203150108090a0c18050709050a03030f12050c072f1c0b0f0105010f08043302030a02090306070206090a030c0318080f 64
    0x680d4081c0a04a02400d011400c494491000c207905c00004d08038400160b01c13800216036035140040144242003000d890039800d506100003074501d04c0d04124000341c18880c0b0a0b00103130452000f08540303000d150b00044c0b0301003d01e5491002d034071046030110012406609110014484a0007840303d001203900240640150b146191821a4411101d041c0c1c4820400c0710441c4c100702c0041405528082c6d108100b86682e9115280b50055241c0044490080c5400c500100c0c02e5101026031740107031020340180e428456002d800640c401c1c03548407480f0002d00400080d41440100c01030380000300c0c140c82c42a25008a22803e9003016500c07079401f110001c08078180c6084002403611625507440000e003082c80000940f00701c1d1070865059030030803541e071310134241c1c00300381055146130800071150449118005019942481020240c540c5d04200f80981030058000e080d0b010907216012048104202202c400b0a0503107a214283d1200e025001c01d421a104100b06100c914020720540c03001407074106801c4440450 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 382743812 1250 382742562 382742579
    0x20a0b0a021303210e0904060c12020301081b120d0e0a0e090a0209060d030c03030c0e120c100314011e0b070b04060510060e130b030f0a0501180c 64
    0x1009011a000c10303001d0159880c0311400006040145210300e032640542190501160f0810045641036410840c3c4900c40525540703e560356190004e40007000402c100211440545042c24219059100c80e0b1002000158568002c2440702864691542c02e40c090351446040214103a800300003000303030303070041c412280c1c03c00d01508618020385400350650314031036680c00002c002800c04542d141c4003500065101001c502d0441c0c500740d440a000ca4a10800112941b0002c01c9600032020040c00e0540c4c550583c0500d50140903128003a0000030503048641032405161a100c03403070103450358020b03500c00314056040ca01a0091031259924864481216131804407052568520489080000c9580c10b5003c901c0511040041c60028020550450f00d03080625041c004c4031f80081040e8051400040c0501c4102d91160070070f06003c01c210f4002c2211440719001100403e0800e08d030507418442d404c14041c1c1c20310045400f00c81d040c000c0008004080021110282c141c404040c002d000741505a014007040c02c = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 382745062 1250 382743812 382743833
    0x20603130215191d030706030f0b040c02060f0705090907050a030b030606240c030a020f07080d0e090a0e0f010902010315120b0a0f1104090b1005031501050c0a0606061d01020a 77
    0x41044c007020f200251490007090131325401d80c019a002949442942980c0725481c000d00c0c42c03071481640d0401c02c0c0d24280200035200d45025244850504c008004559000d00c03890541d9109540142640100d06010328043e2060f400000f00201090800882d01498074020401d6842001c010300030322000192840303401940b9002811003a0003c0c01402030141100e0104050301503060703250010711044e460030446900c1c25850b9845010341e84e0100500e9400c1641c010044042c0b40410345031010b003a113600c1416006001d542d44408480e100301c041a102040d015080003240d07074001e803410003004800c188910700c1d00b1040d024000c400c00d00004043c002412400070743d030b8400c0292400042104001500f03d00f40c0307840c88500c868900f40442d003031110500c0da201e900e14042e0f04a1f0008000c0404031b001800c2400000d00c1d0304103040045130344078420307405034045404200524003642c000e81024901382c00100702a00030200050300308450712038144484c18816040f004140c000f01071100c02540c8424845 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 382746312 1250 382745062 382745087
    0xa030218012a08190c0c0b0403051507052803060803030402030c060c03040f0e01150519050d09050601090203010311030601081f1404030306060f14070b100302060313021519 76
    0x4950070007113080010000c04890320103020035640c04002600c581007240c818460303900403640340b40d42000104006203001820314000c003902c44100c0482e50b00c540045c0d4203402451002c6101c18030b0003c0d007040004041805120f40512500c00b08540354845c0d00c0140d8a020072600250542c0c411040300941c0e14010300503003140880142280c0c50316031205403c01154440c5d502141d030040905005004840c0e0798000320140118903d000d9040821010030400c0700500340d81c032001405400a010048584a90400d10715940c025085500c0c5503543e089040c002c2d4800d201c03d45c1c28089002e08040c3c40c1c40c000c901c442c100e420038002041c08a85285540380030b0041c150030080b0540e943c4072810608100110b280c0c1c4518002e440015000c5e16010b005803407800e81c20103032410000c80032608402100c0680644d100035400590080306903881c0c030354120315140541c0020350700c4070700442000343e88404100707007800341072080d901c2d000d209181c41c8540c4100d000300d001d4171b1401040c1080c1518010704c01c001070a0407 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 382747562 1250 382746312 382746323
    0x10e040c080f0303041716020f03010222090f02130603111b030a020f07060f0c06020d2f0f1b011409030d0e06040f030f020f030a030218012a 62
    0x425641c01c06107250a40da01091039041d0408030800c014810324450403451039440130000c0c0d280c01c01d0901c85040c0703d11005002489102000d114581c6502c095050703840341c10000c040500f000c4035a07810b21004041a01c83d00046c1d1742440c0d000c5034007081c1c600a480010190400c00c0c440c083c10007000742c0203800c1c45d04106543d54003c0c05005c0b0040c41d1442442d0603280c03004099585e481a6030402402c0288200800c10703181c0c000402000015800882456400d45505d40b001d00f020b128178207200079125200c0484011400c0420303407245609507a001100e814194110642280002100c070400c50144411200400a003800750b6220580240785c170442030f1103040000a2003080003116004040000c0e20b1030700180d440807030041c0c1c24184a101c1c1d10001c0505100070032a074501942c904110303c0320084001c0070450341501c3e90041c14000c00003800d481000400b07490301da0014402c010001e4014850743c0b0005281d885221750f040d4090660440070b200d040842c11100284060354007414100c00d1011500f = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 382748812 1250 382747562 382747583
    0x90c0e07050904020301091d1515010203120f010f14030703020105070f02030a0308060f010903051c11030f07060b06090a0512030f04080706020f030a0804020f120d0801081207050303010e04 83
    0x2c6070744500c0214080e211016000520311013038046034900002d200c4400d06968044035501508425000103154084911458050503001e4000102e0440c007925101d070368200c440100b03101d04403090340c0d0354a059800c52054080700661721030558000d5005101e50b04e4054210315003e2016510402c024102540039030040d080601c1c0c158086072410a039010142d0001302c0a10600c0b42d94544041060320301c8030240380500103241513484d0f5030345903c1c2080c0109501e9803a40c10f03012440b40541c0300000e13452640010b4030b4035541ca0640110659200820482d22689407985a00b51454414161105040040c0c21620a5800c0c5010b020b4402e0841c0a420046c1c401440342c200840c1c02c81d00203101500e40d0340d001d04600d80c80e00344080e00d0410700000c1e460f40da401c24007125a003503910001c0343c0d41c40780e011200704040380c14200110b801e0800d01201020f1500410b002082c0c01030704054030321b0488a100d412036410004640c0c03690b115001d07500b0000c3c0603400810040142c54028401c00f41c209001d04680003 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 382750062 1250 382748812 382748827
    0x13030818100c0906050c0c04020706090f03020a030906111e03190e03010b0102190b0c0403060906140f07050f0903010b0307120614040804030209090c040e0a0b0901090c0e0705 77
    0x528000e00507400d081c1458440105015556002d4108001490780f0301303215080900360350960b912152030030913584c043d550210385103081c0001f0740c000c003020319080040110002312500300207440b00d2046005802250f070103200000d545114918005848000360b01412842c580d910810b01201c8817501500c030144424403c0040e40354004220000d0300a0b241c50755001c8101520901d4251018010120f040d90480c001605046104030141c0391180d500042c03c6c0000d5445d0040c010382401281c001034042c40c509942d400c00c00140c1d60021440b103000940c400000e654415990840950868000340000c2040c041c1c80e8002d6000400b401c010f480c000d002254800080011030b1800d9090380c0100030303603000d5070343d0b840520040d8841c41003e210055040580c1385031035111f04d849407085200c002d0007108031000140c0302690a0040120380c01000380184074606006815999450742090701390740c903117800404228801d0b0148a0813007023650062200d49554501060410140c500a01100c1481010420300 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 382751312 1250 382750062 382750111
    0x30f0c022b14071e11120a020f191d01031509080a05030a021303120905041503030e03030d020d02120a02120103060b04090f06060e0f130308 62
    0x42404040303034020704038440c5108289502040390100d610084600004299410b03511004501c0420444803160703030360f101c2c2c0d441d2150746004e0042102c41300c0751000b09039108102d04030390501041070f001c4803040d0011140408154030b0300745c0b11000a40c01003013180007502609010101140c100c020303440e6032084556030800c114405500d040c0d100305140c80e000040c0304100b03419230845054512560b08103d0081940c0e281c04040c0b2034011010305000003c40010302d421070a40494898400d041001e042c21556480c22000502c0d60751402404110143c1380803a0900b018031a50450314500310090720603624584040d5011010400c01ca9014001002070064445150004240100d0341c80700c0140d0342d03000c01c0c030400f1340a0005000001c0441c01003103c0e100918464151505482c0c120500080c002420360003d0000c00d0b980000402410014a00105100b042c4e402802114151501c0160070755420f00c15000c104421201c502104400c81200c0e80400e00c80e40d02c0507440359560f400c400d042c05070355410 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 382752562 1250 382751312 382751321
    0xd080705030706060e09070b1c2a030212010b0307050c0303070e0901050f061828080c010302070c120206122e0810020304050a020907090e090303060108070c03030f 72
    0x1955103500020b00d1604110036032146000a00c1400c40400c154103040c500c96444d95084d12800d070040c24049220300ba1103080c8600b04200c000f403035004010129419a1100000703442079076400362200c12140c034401a5001c1d000726484400d200780002e9540e800c0003071651481d04054032410400c0414000300c107030711504100460280100792980942603a8101c200000140143c12480c01070303603543c102104940b1800d068175409120021048241c2100c2004a5000c60201480207540f21214601103516101142d4407026030315068250b4100c05c0030640103509038412907030010403024021170200100803950070b00b21170303440c40180003515145180c010034407281c83c00c0d590710a2804001100d10074451a42c1d80d904604080c2d000c0c800ea40c640b0b094025611440d144287c80c2140d5000030004003040820b03c5a820115401044203000341400301004001da2850300600500c144c48501046a080d40001924850001650340e981d035503a410900312004c031a6140c00700c00f4540c030341111605000b0076008 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 382753812 1250 382752562 382752577
    0xf0a050f040b12010816050609010806040b030d200c0121020f030c091c031e120614150711060a0516050606010e040b0904020d02120105011e06020d020a02040b0d08 72
    0x41c83c800340d41091421410300044070030060f400e40d1444c000700400d0701c40c2000c0d64600002401c0402e1030f80e891002240113404da00d10166032500410a0410059400c807102000419481d1950900154204203142d95180c00c445c0c2c5030b02040b48180b4400da25402c642c01c5100000c80507074003600301700242001001d150401c1d10044012840499040d4440c101180350a1a41808003040740c150b840c15207000c3d09144400c200c1c0c0d04880703d04083e504000c1c1c015916810f008540c04803c021495860314040e030b03c0003114032014407505490040100c041480d10503904e6a603046050000c500003008101f22140d0b200b0035540003402024840b407242c0c1d9508840c404034460092001d8042450705000041140c035110044a00c0740b0301e050380382050740e2107a0226607030107541a40d40302c59040c0741c1c1c0001103002b070f005a100d0510307600f004000b140c0c0b107032445121190b25083d490311010107034403a002644c55807400d14606005910007100103001d80340c186c01c00074145030050714821034034039151904003087c2c1c041c51 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 382755062 1250 382753812 382753837
    0xb04081e0409050a140f060109030f05030405010305161e0c2306071b0b0604090219030b130506071809060605040e010e10030b150a0617010603020f0a050f040b 70
    0xa010411a080b03801081d500c21403031901041443c46580c8800c01056011700810f61142c1c1032030014040342d02841c04640610303000340c01d035100c8000d0342c9001e99403036005001e035500190401000c10101c1c0440300c441100e420740d9032210100c1c0c1000403080c400107a800e81c2d03035000300544405800040780d40143c2001c054184541c02d903411807501c3c00303124644076016083d4002c200c0c6802d82ca480400780c11045000d00c8d50301401072102c54840e0070004000d00030100010b9408128801049101e400402c03900d0110384c840c5c0802044c50391415034085403130200e0800648203401080001c2c036021301c1000e03a88a240c84401e1072078842a255660700c000c40c2c4554103d02c3c042500010180498243c05070b01d14010801110b006c110b5140c0140c441301c10004610000b0301c809207500114140031114401180660005030500d029640e655070f0040007407000c842ca90900310500400800c042d8400c2c0201c40b04822503039500780c0380c078041c03240031582c51344441959040088180004511111350000a0a481d500300 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 382756312 1250 382755062 382755067
    0xc060d090302070b0a090302041112130606080303040b0f130602041701112508040b030a0504020907020d1e05040b041502070806090c0f061c05100e04020901030b04081e 74
    0x600d8041c1c40d1406607085541031a0342170010400c0180d10410340e4003580d0381075078042200d072115583e013007407801520f034490003410020080202c1d506000042942d614040c07001804083c1d41c41c02c40c0b6890784000c2d5005020030305400c0002d44000c144010882c0c00c4074004010103000c0c0c0320794840034120f030803d80185010803004c8522900c500001d0040c0b00140c0b5081007214a0400d102d035101c140581e800281054a000d038001c502d042c00568010f56009101c6502035950fa85042c40c00d0100400b4101c1e8102d1041030134002251000d0320005112024400c240c4643c1500c00002400301d249004001d10481040740412000c1904141100a0030080000d2000ba80d100e003a0404040d041210b550460303d0142c0c440d02c100500400300007108141007109941420801f00d0140201d9190710540d420070006c0c20502104103024141644541c0c03140056038041c26865480f07802e00c814141003940c000c3e5200121400500100e1014220960400c0c840c1c481d00b4900b6442c2e08140007441040849140d480002 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 382757562 1250 382756312 382756331
    0xa06050906101a0d0e0304120501060501030f02070b0606030a0b1201051008030f0906031005040e060411240c1606020a03020610061b020a0906120606050301021603030b030c060d 78
    0x10590b020080d10442044890303011a0041e1020640120318422410710340310032603555100e03010300441d0301400801c174584211194509055028000b64425580001d10f0000c07000981000c42c82611175603503211600c0e80c0305482c1c400800440307400c05450520503076170324003048503203503900130340303039aa008000740082000d142044082c003a840141c3d0019001b070300204106266131620000303e070f48151049502540703075100c9215200400740b00385c0196400900c0c05034421904080041c0351482240f1440712402004005400d01c201041d100f00c628044101c2840200701c10310b09180034000880c0340c101201c242240c00c080f0740806810a50003580560400c01c14002419810321242c0c0d40712030828032145240f40742a00003002c0c0c240d4000c480c0d5010360700700001707011507543d80c800300c004003400c65003880002d4458240766040350380300404a07446464820001918107060081e18030001400d400780b0300301034807910140c0c0940818120550300d8010034140906a0380c8810140003514108080040d00982 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 382758812 1250 382757562 382757581
    0x1902030c0d1b0b090907081905010e0a0e1605150c1221010e0f040510050702010f0b040e0303070825030c0e0315070f110304150215011a03090a06050906 67
    0x3094000030f03208802001462002e0300c8101c0c80f01d810048918201000c2d0751942c40f1020b501c1414101c6e001518146400000c1c40780e08021441e028605d0354008202d5006801002c654410f07603003036a414008017084003007141f0b190001a8002c1d813100c440400345041c0766203031400c1c00c000c117016003c0e0081c1d90108581801001d1400103040c42410040140c07840c0d41040c004501d14a40180718060220303002c000202001001c0c0210720610240b001e0902141c184450043e0107481d040d404000d01e0f40ca8200c044059151601880780b0075848400070710701c0c2d601c40f0303d02100d201000a1190f42228032149031100c520481071154155141d00b56070000345d21001040080080c81d13450210f40c0310750301c0740920103128040c0c4200da58028646062402022400c0032007541d0b40c00c1d8050b2807000c0b50202180c002003000e040301c114425003610f40c0c03e84414241c0d09051021a05e420f0251080032840104004907407003070140150b030403d05c44411161540d20940e00c4200795074080714440786035000341040c00200b55 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 382760062 1250 382758812 382758863
    0x60a02092106072c060a0302090a06080114010309111005040e10050111010504120e0d0b01150818071a090d0c08011808030c0706090218010602120301081902030c0d 72
    0x6405410710445504008141d1480130144000d10700ca1140000c0c400101030107076040341e94041c00a06080100e40d581c540142c0519400d10540c2d01e60314143c0140e5040d584244901c1c411640d00580807410000300f4018055400e10503500d80050142c00c00001c98120b0028049030300c10510100360485050818000412a00005083c865540e04103001d00002400042d644d070340700ba01d84d01c1c00c00f005080da03000103100e0031881c1c2c5000d030a41031801d0011481c52031440190300a40e840e52210038154403011010300300c01c2250802000603412841090002c8140500400c810404c0f94a0490400c60200c001a01d405c0440fa4112029801a0010400c02500b03015404c00c010301d0f8000c22012684949a0f566940b00c01002294000750014521007042810b03400254680e802809003180304200080e8103405c64004c3c09814058072400c0250448082220102d1b4165003881d00500512a449030220b081c032450100202d03807502403020501d07616221340031407032403140c09843c00321b201d803c0c15200c100754079 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 382761312 1250 382760062 382760087
    0x1b050a0504060b090d0206160302030d0c05190e061306080a0c05090604051c0501050717090a020a030b100506160c05040204141e09040b040b100602060a0209210607 72
    0x154103001d401c00894070f250060301d418510566403000d81c200140300052440c842d4102005028401c0560038040c980e0000c098801c03d60100c904200010000d40c0031703100341c02001c0c20b07440658a46000c001d105c0b032103140401c2003d41c3c007402d03003410004005030054030060ba5810070300008038600d04001c0301807002e000302c0410400909015190240000124079144164050203001e0740d2242100e0119662100e102e00b1250f40000c02042181805e0704014645110004003508012510021410311100030a8015550b60300400414203a0304d15694996201c1e070007008a040030b05503480000300350300d501000f480c144003401c0c855103101480749043d03101e05199030401409244103110a0120501200400b03641c00c05c2112001c546a0608014001c0c2113603402006800c06511002e0100304030501c5411400f0701d210301d603841459590700c9000090801140b00b1034005a022402040c0c5050301a8020050780201402c061054280c07002e070b04c00955410030a00449a10a40400c2101e079403045401340e02 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 382762562 1250 382761312 382761319
    0x70b1b13030308091009080a050c030417010501050117060a05120c032d1204050f060f0706060e09011406040e07080601031a06010504120602030622050103060506150d050606071b050a05 81
    0x1200c80d6201c08141b40902d190123428800c5c0080d4a54044508105540040c1300a20852440c180b03071100c0d403406064284196030101720007080c503901400c000148244941c07005445207840614280030080d04418511015445010302c4101d0034003900c06010350384601c01170002d03c894010a60356010701c41f10200c3d001719a00c1e08100b0b03082b203a11280d40b0444003154012561886405910301c0029098800c0150b628031072000010b44004001c03913038000c00100e0b10032407403199440da10061000d09890303943d01041d40c101408400119540381030707440103210b40c0318802150891504c40c40c00b2490306500f81c00c1600c0d141440a0040c4844030138417071066106500303182c07082c01c0900e0502d082003164440c16004116940100024a01d625020684d64620000700c0d28011029846c400400c02040280825180306040c400090303914141000302c01c0000521240c0185001c0321008081c0041c840504031990150081000c840070800c400c0965100c074039024085101c46180c442007017102d0009500c030501 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 382763812 1250 382762562 382762571
    0x204090c0f0e1215040203070b03101a25080d020c030319060501090611010b0d110109052713021005191803080c0106051e0306010902070b1b130303080910 68
    0x148000c004c43d004840d0158281ca40c0c4071501c50b4400a41401079541048a43c0d034404001c00951100014038001110004242c4008409079080541c2c200d01c01c03000c80482c0f080d040103020612801e19200102c040b8082d0000c5420041c45411030800daa000c8101e201c1161302c084244000c03040d420180701900c000403030040110740d01d80000a000f5044621406042c002e1021004001344429000b0410307080c002003846011a00604c1c1641504022008103400500b0320107000c541d0382080403904002d00e051001c94400510503120340c1307800316030080544590240865030500141c452014900c0c20b40c42030748481e900d41408200807000a0011742d00c40e410459020040c41c56821580507a905803070300000f6880d0b80e0024019005d000d0704280d848140c100050b0020071203482c001640c610104e0008800ba6801a641c46004d0f10903401340702e10103044c400d45900401c2d0080b064406030ba02e50000d41520508012840080782400b441d99402980410907071070800035000828004052542c074078210802 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 382765062 1250 382763812 382763839
    0x405120304050307031407031a042102060a0903030615260103080a03050a1407021c1103120402031009080904050105102f0f0c0103060501090602030910030204090c0f0e 74
    0x950303e04c154480a40340d079040707024842003a070307080c400c000c0034607080045140c407131041e00382124107050704407010f41e10b070031508032240c00c4018104152005440254018200e03501c030058143c0c01022588412414550f031840300003410b0b850405054a10442500c44028020b40d10344001202209145407800003d00d010044c8005019807081e1002e500a51800190f1039036500202c4000380601c0260b11068040001003003c01c0b640000c07900c0c6030700c5209101c0144c10801781c20030307103003004551141080c5410a002400c500d0900035a995030040c001001c903900000381400c000c00310762a0700320640f1004800612094103050a014150041c00143c489000141d91060300500c5001c41809044526101c485a8240300310079603030040005000c0002d403040d064000741202c1d034550425140602090410b5000541903024050060454055802440c6004d41f008108003c0711420f81001051641c01d100210f40d17044140b18000082c0b0032600c91030381648903686c001e84104a50600f451142d8031044110 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 382766312 1250 382765062 382765069
    0x80f0f06130b2211131815020f04060c02045a06030c0803131403010609020d02030405210f18100815010207030b130c090f02040512030405 61
    0x80442035040400141c0c50349400600c81e0300c0340114801c00c5403014003280541c1c00c1c400c1d801894014210100c51582001c00d884201d4402d1359850a50b00d110314000321611b13004542140e030414011030070740400600d004048014a05d841c1c00c00c0c1c00000002c0c1d0542c451000310305083c81000d102500102424811401d14840790030f40c810302c1085100c44030040b035180c20351407503840802c280742200d64500e41001c40e00f45145034024116484183d0b426520f5200010701110b011084034407041b000c2c0110f034090760801101c852030194455400d80c1640d03a9002c001a444002c0c805000c2c148041c94001d41d0301d08003400c00314a0040710082d030039540d070b5841c0c1c64800800301c11011103012110070184143c9800d00d8031501881c080403a40d449401c1103007629010140da90008030300d03200b507c0000d00b130310300c2501d004012aa666403a000040c5294921008500c203c02282d1002d14200e110301d408101c00c83d184c42d4990141d940a19892002e140c01180c1440300e450a4404046152240c100070342c1040c0c50706000 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 382767562 1250 382766312 382766341
    0x201050115050714060c13050405060105030c0c120301030f031e0203091302040308040f030b0a0504050a060b0d1b0503010c052d0d180201080705030601090b03100f080f0f06 76
    0x44010302c007000640c0d204201081d80040e00d0740b14801d0549210b403400c442602c507240e01940314488051f0030703240c0100d25440c041c880c603030160343d040e074ad064115582c4135001019a0310031003505280f07100b282100400d2440400086020314820500340141414902e806005800301b028000c1300d5014370b40000d51040d6002064401e211411071340c0c04085403485100b10300a01c11604043d000140000c2d01190554032000d590085911400421300701c0d5850a0860084400076030700100b940d0045102407000c1221900702c0452520000c0003600f20607025a541d40600700c0c568000040310344c41610803c09803400b8428130150703007030a083c03041c54410522200d082d00c0021110f0303140b240151040c0e000038805180255100d61662060030800c001e031800444240c0080704e84120700150704000012030340352061069902440707068468640701801d1031520585604002c02c141c842d1105c1440009140030b041c01d00700c00816203280540341d0b80340d0320120349041801c07200001c54039034040001d00844140d480785 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 382768812 1250 382767562 382767599
    0x3050a11041404020618040219090f030812180f16060212121005130204090b060c0303060d0212030a090807080303010806190f06080d180602100911090408030a0c02010501 75
    0x1d4540c1d95031043c903151189005124001c0c3e1f002031000c00d00c03481480101020740813889040d265803450780c1d5100940802c010060000400880c018007901415484081d002a085134000b0425605080d41d117400524099102012103060351042011040ca42200311102025028601c00780000c0c1c0070410035190581700d4100c8041c0b50001050000d18135000843e44e04010308001040310b40c1c012500ca00a10107508a8001d844071903182c0307180c0742200e10300365040714609100c4601545c01e580d81e440401c03900c070001c5001aa0056000f560002d2025014001000343d482544ca4110445082a10080c546a00b42d041400158410401403009d0700c00041c85980c061400d214403124025200714150240c102c1c0070300241a54203100c40442c0300400403521424004040c0d0f01e0b9003024040c88503486260182e0303c501805070300580603d556140303c580010340e4260040404000d4844d40d07501142c044401181e0071b80e1888000710601104500c3c80c015084039403140d100900265041800c461002c00c003915 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 382770062 1250 382768812 382768819
    0x606050715110310140f1018030b1602060f250905090703020a110c1f05091201050405121206090402031e06090106050d0c0509090f0703050a1104140402 67
    0x1401603000030749035080540c44103210041e01d0344a0800020107a0110480c0c050075032502403e800e40104e03404c012201121042c070040010001100040c403e550004045450600a1550712000b00115000c018240d00922106200803610918184000e0070310340f01801c4162110180c2c000c2c006007440a8081d6510082200300d10441100171101c166034050b826400380c0e0b08070005000f0003d450390190301400d8070764800d03102c045407403040024041c0c9500301e820880d0f030b011030b110642820700d100c42c45e414100ca001e0350030200d140500041c0041d0b0b600040130b4002115139102c1040204000c4107102030840c5210f800103003818020303414620040b40700014503480c020f404c280700203019550104099511794070204c0f440143d01c1c0c02c0401d016112042241c94910640c240f5800207244d0428841400c0410f8000a1301c0c0c0030a41080201f15a810300900303050514031a2591040c0e400100348041002103100f0401807180e49181d02d84500045a0940054880c0f4580205030b15900d0780e4404c45a03100780e044 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 382771312 1250 382770062 382770083
    0x2060304060b01120f02070309060503040c0b16051b041104030b040f111816090303140703020a050d05071104050105010e010e0616030e1e130b1c030c0204060906060507 74
    0x50004132070790000300c000310300b41c1400c01e03107502241607041c1d0007006c0890003a911401785680301d0209031014842a90002c1c0700110140c0b003040b94030010005414070074041400d62031b5031400e41d01c0d13a51400070581d1300c0b44030400ca22000e20780310785000d00c50700000d0300c0c2d0405030900306131568440d119544401080540704e500f0f80c40c40c100802c0708001206445800092840a1525120310350311f4007038030203e030505032560031080314040c4030307024440c8002125410740d10910149058103e141c060742180008a003035100e12082440084d03824031516851602c10f603102e503211041d0381400a0002c5c00c8c0403a0310b0003107182a00500950364020000d070500b001c00e00700200b403405d154020950a02c031745034142e14101c1403c902c040405a0100200781800e40858000041c2c404203d164165054805004c0d0380c41903001c9144661a03942d60482d0f0000d81d001011034075403840b1b24082d8007941d0f02c0344204400080c400f0740c048045240c40d205800152008040800886042060240c81446206001350040440 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 382772562 1250 382771312 382771331
    0x80a061116050307030f0e0f0f0a0e070206070201050106030c0807180e010602031804060e060d0623090d090515070c0503010603060c021e0703081803060420030a0206030406 76
    0x3440201d600000185510a4a5410904207a610303900181d10850009082c0c0302c0b034207145442001c081c40354400040810240c141d10008000c4054841e0442a400102201001503011002a116486040190007800c4c0b80d140800c0e0090846005800400c2414035025540301c01603880501d8991100303060519242040030303505500200001a4030880702c40d00c03264004100c040d130102c0981100c000184d08445042400070821099903004d00030b810050000701c00240c407034941400c000d1300c50350141e0750008204407094400d00307039450bc4948800440b50700c18140400d50200b00013005010301c0340e19089600da4242000107071600311201152005c0e00d03002c1440c0301480002a110402070000500800c48107613289841001350044108240c058040c00c0413281d440d03180140801942c064590280c1a0141180d40d410b00c1504078000401650051004810301d94808000c039500840c00f0b80518400301040d03c0d000956480d1034084c442c000d800c24651b50006841b62015280c100741d210f034001c00d0314040c = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 382773812 1250 382772562 382772591
    0x3010b0a110c1003020408010f05010b030a020a050c031207080a1406010311120f011e0609060c03030209041503062702120109020a060e030c0a1d072609070e01080a06 73
    0x15040c2c1c00780d500030901c1042c012070a40582c01402212010700090049203910a100740480c1c50074880d040440c0c400300000341b0b2020051b8010000003e9a00340941484000794605245070440a0b4644905068006000707400f9048646a40d0058040c1800c1c042c9815a0380b542c0449440a0691030505440b41d08409400a001007503541d00c02c000e9204021526240700d00b0500e0304400c0c450180e0301c20a482e1103000d030800303c1c200b400c01c2c1c4280c3d440d10b0322804e01d4010200c40142404c44150201a82130044e04d07031a039502e0054088941d0117220400c00181581000c4080310300302081c25a030032038000e4550101c1410002c4004409404450b09641c6c0f81d62000581d001d420900d2b0025405002d80b0741c089411a00180c2d050311f400c4013541241e13070b52030141f0184a001d42c0223000e0084801c03503800031460071003140d807a5691f11524602d0400c0a410f445060644070781e580d03041a51481000200700509103c041200720001c080912000b00b07154944a03602e6240c000d07609010f0060b0707440d108400c5140c071 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 382775062 1250 382773812 382773823
    0x1c0509370501021c0e06010b0d020f120601030b030106080c0603040c0305070b031f0308030a1a04060b12090d05030117150a020c010f050c04090903021e0a021503010b0a11 75
    0xa4906102042032201860709600075444412032507040700320801c0135100001c0e144180c0010f001c03100000d05699003400f03400c03401600802c02004907542c003088500d1b98003038580040c2c0424003020f80c50000c581480780024043c0e488814169000741c1c50035000700700150000078400e00509042d60015500e0703c3c0c1c4d0800c4482c4a100d500098110b12a2440c009150784c0403000440c4102c004444098003080d11040301411070b811032102410f4000280003081c0c841000342d1200001c0c0046004080e90800c1e110b01040690715281d111140c1c81d100400ea444651080c0f290050b030200d240d2002d4a240c5800345c2c000f9186000c180582100401c0d0904803a000e50010010818803506040c040039070380c40c00a2105003e9401000a40800c4d400c00c0660000d288407400341c0323401807500581c01e074202820504550003e00d4440000c1d4114818021100941401c0540d0400e030f10b04843c0141011910714018080505810041d40340d1007007041004000010000c0d060f20284951460001d58440f0402095032516 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 382776312 1250 382775062 382775143
    0x6010309032601030b0a06060806040b13060608011a0c1009021c0506270c01120f090b040c05010908190221150105060405010914010302041701021c0509 67
    0x104030b2048070640036180b04909034100c134402c03800c0340300b00e950320720784807007034032080d01c10100030543c01ca010406e649001c1d00a40c1900701c0140c8200010718520000405a440c0d0354020004103072200014824404d88813810903500748944c061030b140100746209981e5403d510860000c1a81e9070b6448a4215655103100300500b9904281d00c202c00313070f410700b0455100c0105a40b2070b414101540001303812441d040400340b281c80f00030340103040400207000c0199500e06600005017000c07a92019030300b00d000180e1040899031400b54035101068505458101e03510350442e009103040c440061400c001343d8200041d100400e4180740080640a495440814030b8800343d201540c81281503006081c440b1000010b000b1030300303000e003034031060940d80e10804e00c14207201c1c5d0b0148a00103010401d044c001c41c0a55401410204010b2400610705640c0c4e0300306c01140400720740d502c08641d4000a5952495a11541c5003c0030101140200050300344028215a00e4a20410980420f0f481c40780f50300d010070b40141c04a010 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 382777562 1250 382776312 382776347
    0xe511804050c091809010c0309020904150f0e01020403110913082101060309060501060f0906111015031403040b1204060b04051303021203060109061d03010f02090310050c030601030903 81
    0x20a095007400f0318140302c007119030345c80720f6280500e4220100c1c4a40240a20240c015064180549442c1c9510800c10b0b54842118000c1c0d0b00d6445005c0004024460300c0b1200020703400049c1c803241149464005800c5641c0304910548903d409d01210888110b4001d00055210142c60350305d8091801c0080d9180712100c0c29202b0b0480d500c000900e85805400400030b01e4822902000644e80761803003038900300c2c030f96020b010002d442000c09004240c002c118203820070709800300302e615003000e2401c02d100b5580307032000c02c443c91045a281003041040302c068110000d02c60002442c105420115903a03640c0c02520440c401840a00c808102401000d60000600720805481032200d4074104032081c4010303110a10440c0144103404810b450480010180c0b0b00807501656803d400e01d1800030100d071500701840e21020440c0100d006041d003903800f40f03d149440940540050389410301a410142082c118030040c0b00002d0810f0304100c070101216040300d92145d001d00f80044c2c0701060703040450701c00741601d008428 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 382778812 1250 382777562 382777579
    0x306080307152315040e06010303111002030105093d15170a1d0303071d010507050a02010807021006080106150c030e511804050c09 58
    0x348000368103400100142450240400d410030f40503100d0005007542d850803d2440040800c0c1da41100c0456012801e01c000c10201e880315038880700d9403d0090aa004901044009070710011046060004680801c503051045080d5072406001c141304d07500003020841c8400c2960200030922040c01c0088000040f111b603000ca4140032813000e100554020302074808103003850910016914454020201c500000302480d1890307480701d0100b9400303003407140140a00c1034008000c040030828204090b46c030404032655000c4100c0b00d0348800100c080c1c407103060a070400c041007144102040000450480c15a03080c41c03c040c156540d160103d08180e10643c200a11074100400003e444a05403c05410340d4400b00d4101182c0d01460001d894684005030000c020402c944500d80d8a4036040002148508001540c5a0183e2600d078084840e1012656014507501907402401c3c4442c025204e411070718400a40040d25090b2100303040b0580440203030307009105644078000111100f9052060b40c40c0100040c04050 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 382780062 1250 382778812 382778827
    0x302061e16030e1501090e0307020a050d02030a29010f142b03050405040c0804020a030609050c040c05180f01050409021321120315091812030605031606020705060a03060803 76
    0x20f1080400e00c02c100c00c51f82051500600700c01c01000703d440359035000303100011135403030034091050160305800d00380da06001e0386c5a80004112a031f02094072380017603141c3c108540b80140e0040d039034422060b0420040320f0788010084c407200c00c4c103401030340c07680b0350031186071002d45654100400c074103034118107040e842c1021001038420180c02601030b10964a0841d401c1c020540162011241c008040b600a0b600020007a000c1012809950180d20710303500440030b6901400c8601d0219054a165841110000348006140c003029490000b0106440f04200d8021403a24100c0000030010b0040340140e83c000d80c1d0019500c1c0704101d0701d80e07010b0000d00c1084d04107003001c2d800030800302c020a805c003c16a0700511110900000511070712560b140070002860300d25000b41000120070082444030700d20400d904075608000045020040c4483d150302250b50040380307080c00e02c800d040c104126000751018a00300d800c803c3c41248d0300802da010540d2010788256440c2d064044084000d0300955019403003500000408a = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 382781312 1250 382780062 382780093
    0xa030210170108010e0c100201020f030f06090f04021018030507030515090d170a090c090f0b010509060702040c020a080403080316050c0a0210030f14040302061e16030e 74
    0xc12026041291041079a0381c50109074242c030313488284241c0640002c030b070342425854035000504540c07103144001810310314191300c245100da10548069200310403c90420503d8907065038150391190361425110001e0034140d010400120190300b5910034040c0701e4005503401d00c0b031040104015600a0122640c20780e032810190f8881d0480319050035204000c80000c0c48080c2c0c0010000e820f00c040703694042169484003c8050780d036901818200040d4ac4400c501c1000c120812440c00c06404880000a030000043c00c20b0700482d546a81114103100c018480b9403d141e5030002501c100640507280400c000d80c4c40d0b02c040341130044500000300900000b03d8040b0502c141d01b0040d52150203d95501ca0501480300c0c0c01f5240c0c1d014450504c4c4c1607500c810214030040c00d00c1c06218501c0b0a09040104020303500794258420b4501e051a1000c80c040132004000500d03034100300164111201c22103040c04940c414261404041004103451a0b8016550140103200d2003944400501180b14040c1c070f041c1c0103001000c = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 382782562 1250 382781312 382781327
    0x80702040501050910030f11030610080601060f0c1b0e0c0c07120803150f040c0503160305010f0605030c16030c0201020c090c09090405030702040e100e060609060607020a030210 78
    0x160300607407525001007180d050945006025070f04261810740c105185603989203020114070703800c035426005403207090700d40d84041140c1801000c850000c1003403c1d041601032131401c0c005911540402010056186005402c07014403400c940d00305104a6940f00c00031200b0003000e03000d501c6400c1401e020010445141c0302c40010303000700e08000056940c2e460b92044240d0b0b00d000c0c0d04c03002a214500400c00300d402184e4240e400710400401400c0380c15840c401200103402c0b9024400c80b0b101040c000410810440d0950b84402d15001e11400d01708a20750502940748418071103402808240000000801c10301841c48054072000c40305244241102c030780754a40100324a21801089016202c0c86e10054440e180406d041ea00c18442c10103980c0c242040a0300300114090050000e40b40da0008210b40400340e1140e00406481ca421240140304d04100c690642c0e045034242c108407581e40d00a90180722660f0b441207401030700039100302d5001380c60301c1140c000134203903103116807000350b2200c02c0d2450b000703909420240307 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 382783812 1250 382782562 382782577
    0x40b04090507020304060e010e240a08060306072003040902191e270e01060206010602060705090d0f08120709051201090b0c0a020a080c0a020a1212052508 68
    0x81800140c032444003d903030381d00890145401180404815192551164030056020000103180303c42e0280781400782200119084001c0707100200010340750b00c00d10340200d11030380c0090003940100b01a1410641c010140003080c101078118420f4210722210a41d420003c0e14050442e44900715507914142d02c01e01d58600640c0c510b000030490000c0403d02100c0003081181e3300401e00d4640103215091000003400d400700f0080078206d2002e980c8404036203a0000464203010f0031072a001003141c0d50400e40081e107841d070b0040c50031741005010803a001d01034848500c0e00403200c4d404120800700b0041450140480d02139030f084c980ba0140f400c1d04201d00a1b9000c0003039400c5030f6081d1004410000310324055426a045100301400002e04c00e40869101065900140320f009540d1054031129403990340c07827010641c8400c5103c0307815408440010250300d8960310080c014004a0141d80c1d15044c00d903940555104486a02001c2c80004a0314451030942e024061100d6100000341c0d07000d50700b0902c0d003e080b9030030466 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 382785062 1250 382783812 382783829
    0x501080a020a060305060a1401090305060906070206340504030204090b010e0709051f03020c0610030309060906020d080a0b0d03080f010902030c1b070306180b330f06040b04 76
    0x341c001562800f0b481780ea8020780001d4071840c183d90a114000f441000d40708401c1c0c1c10401d1309840000402c04c140b0032140203518000c0601100d04100600038940394001c2c000c00d0384c0f403603045084081c1101c003c1140c400c1d07040331800380c140c00c545140195200d01a41c2d01c041c1d0410b0520324031504214068120506a0b1442d1441400c0d503210402c1c200da00741c0180c000c0740c0c0c100035035001c040c9054451a03040c014103103091402501c1c00c1c000044030781c2008400c2ea9040c2d0b0801400701c0c00d000305608071a401c40a0700c110701d000d038251458440000d5440304000343d85414003c088001c035000d0455034100d00f004250182101c4003040c46441c0040641c0402c40300c1c1c0d000c55400300000301e20800140200e0b8040e45025030164100401e400800e0060b00d0f51200c600c2c41d91107020130000000d08035008101520981c0303070481001280d00d0505d0b4612503c000c00035012080400f00c3d51800c409010581100889074010358045113001101046000c4038110000354400c3d408680000e480785440014020782e810031 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 382786312 1250 382785062 382785079
    0x3090b0a0e070611030f1c18060b010c0201090509091510090e0a030c02010503130b040809040b0a03020a1404091406061002070305060703020f0d1b0e0d0525090501080a02 75
    0x540007181c1c0c803500c01c040c0b58902c0c2c00400c4114414007091000d03098100d000c7c154544100e0b40301d07008a04444180d80c07007030041c647e0b1092000501c14540715131080b41da400e00303200c84030140aa00080200d6840c3c040c0c18807503009000030842c1d41404002c0c5000d0030700907070450916800e15002011070a062442078000f1141003500d40540242c6c0810800c560650584510f045200c03281d0040d54075400041501d000c071008140c00300c1c0032a20380301806005074007681c901a510402c0b00c0611040e41d41e41005140140d04c070520800060300c505d00064100c51000e8a140c0151285800082c0601005d5802500141d010b0714292800100481c00d5402a101140c400060485144d0140e80307442280c07102030229002280004ea215010360024401080300b85d654900c1c000f1007013290b4080b6a215031541314480a19009a80b00541005c3e01c04c40e1140201c92610344169160703101c43d0349810784da94006038102107031403181d8800e001ca950343c400707030952080030303c025a140d01c0010356500c1626016403141280 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 382787562 1250 382786312 382786319
    0x3020402162a08160b09010513030b0406061433040e012d0b07020d05010f0b01090801020f04090e0a0c0b090411091c11041406090c0406170703090b0a0e07 68
    0x2c000d58944102002c51080b1850407170f803c42d80790041c03a02981448801c0000071143e0b900503488502561103804019001c1c2040c0c180041100d80c01c2d0403028001551001c0a50070b035840644803014100a14242c001801b00740038941c10b0790240965000c1e0155003c240883d02e108a420b40e00d041c3d5180c18103000c080300e5084d601c030040c080111300102c1d2091929000344a0101c0c0d400003044094006000244002844e5803000d0851342c403441880a03050b076030040c101c01582d010500c08010300b0080c2c002e504014102281c405284075134410320710b00e030b1b41c0c03a2410034010f01c062001211003074001004101c0560b0f2400204590340c8a0020240305a18007104a600b4001d10f0050b01d010007000b606181c140c080505004c50070a10303400050340c00b1801c482e45107404e65102e000d40e00e40c81c032038000303102c0140c02c20710140f0135603c1000c3e0283c0980c0000b800180708e1b15920811044c000300401d000321800b5111607800394001d01000c48058042584c403400c2082554030b5411000c8580d1015044a00a42d036 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 382788812 1250 382787562 382787579
    0x50405180a0506090403320f0a090b0c0c06090a0302100f031112060d03090317070512032e030b160f030e0601090f1d0c0a120c03020402162a 62
    0x400721401000300d01301c09a450700a880c0714089400c43d6547d449005a0017018a01c0484590400e681c0c0c0040c1b107070f0001c0d6085036075500045039401040e500000c5400c10715100e0150740c8600e501000c00e0300503d40454604259501d04050000441d000341c6038210716405010300400403410221224082410411614501d01a19040b6440d4941030704840c4440d48400c4100000100401c41c150104440504048046032140d42c1c02c6001e0030704108100d40d00d10580c54024102220300d03402c80900b42040c81040192004400e410f90f2040606003814001007004410383c4480f0701540000e4000e2003c0d10030408640000d02451580c1242611203080300707505c44108506961720400842034542200d03004001d2420310703030000004a08082c40106003148200f91485e0451031080c1c400481c0e611080c124030043c00d103060f05c24054492000100c240c01001e445441840800f840000c1c000d036400500f440ea407540034200c0702030303050340070b0b005286443e401c0315000d4040b5105001c1c00013080210b000051003d0 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 382790062 1250 382788812 382788829
    0xe19060905030d090b030612030c1b010f0908030f0a02070f0f140619081302031203010603060f060822020d110306070c0f0f2d060b0604080c10050405180a0506 70
    0x803d080062841c40c7e89007018810b100010160048840c03005026583d003d8006018200003581010343c1d40c21210000b600041c80c02e5030a22502c0280050110184a0b242d00070044942e04c10030403c140b603541c3c003a600c00300d01d00542d903440810040c0c1e0000010540010011079001154980c4100b1040c0340600300800c5424807480c0e8961001d1080414015507031402068002d9120107224452404568aa00440e0408080294102c40b01300d0010040c0200c0d80c06201382c1024000c0c8840c408480b50411901074000c44001c0d200c2a40380c0b8105e1959800e540084142034000d55014022484a1100d031615102c8400e4102000f8400e000b0b801c00105c0310781c1700d48614070380240c004000c010603050b071761244418081000c00a441d021070070014166118800d07a140c00c80c1118500101e052100c07103040c1142180c1c07080400728858074042004000f00e80c400120500c00c440c0442c3c0042d003261407200c2c00c1e2410312895000b9038200c11460b00c0840807010724034200348203044410080c040c95448508020404 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 382791312 1250 382790062 382790069
    0x13060608062d01030221010305061f030b0406060f150212030915040203011103040f050f15060103020a020c040e0114010e0417030405070515181801060e19060905030d09 74
    0x2c02d0501d40c2d40404a50b0b4400305510181070061804200c1810694a94004010300c0d03080b2650400403c1044000c10419a10038415a0341411021914542e907044004511021709083d02110100f410f0044d240e00050040010410b08012160344248141c400c00c2034800d0345025000d0350f09481d180140040840740725020510140140040b4030703008852580001e441030760903640c4d034107408805040c3c10005500490140d0802501d100d070520f010780c609140d0201c800c0302900700c800c45d20601400d00924540029003403c002d601d07001d54017402c030b1604c41c2d000003580e4040c2c2002442ca44500040d4000da4074a0300605640c3c590f684c030307500c00c0030040e1400d8400410a12164101c100003e1000d0083e58000e40304205031060740e50307a10006020b2101e01c486540c60084000f90001080c00110071110820b002600d140416001e0855038510424051140c88107000c400b08000404e50703580050000740c64212100c0030707040d03030b101c1c1401090030f081c1e4040c0d00d010b4451848508016801a103465044 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 382792562 1250 382791312 382791349
    0x50c030a0302070b0c070b0406090f0b1801030e010902030a0b01180b0a170a08120a1d060a0c03061215052401030f0b130911010f05030a0504050703021306060806 71
    0x1078501100503440d90300c105c4201c00140a60314000c81c141504034010401460355545420089003010b0b41c03000340e1703411a400366520680801c1005404210140c1e240c034202001d003000100c03820410031050251041d074000135818041d04150300200196034804905903108411145c1c02d8404800c9448207c80014040c0360b482000076000708846100c60100d003070903894480560707003c0c01455940548580206d40300c1500443c5440c204502c9081a10403103008a2841494045088600740c5036921808058600280c854460605a440c240290010350051070305000e5803e290385035040081c0d5240146904c103543d141440042040f500160480c1c003001d40c0c07030368034890000c403080005400601d07032010b62402654594034041f1060f980d224070640c1e4500d02c40d2020600481502d07202004440b00790045052050741d081021450703034404140d0364008030001c40061240c540d4100f00e46408140d501c0254440484418038030454001e4014400304e890f00d4466800e01c0c1c43c2d81d400c201254510710b1180e40c2 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 382793812 1250 382792562 382792573
    0xd2a0c020321130f0501020111041401080a02130905150901081002031018020702150301210204060308030705190f0c110d0501022106060403082b09030309050c030a0302 74
    0x44000d50300c0c14164036000b840c000d4503042c0001c070b401d00310000340d034051034551000d82d4080100f560280103100303200b9603a04050b4034150800c803000a03044d5101c0c000c58100710f20900022050002d580c100d801e0604000421a0348950303411011000c0e0038101c404120740c254880c440203c070b0510030365181c1070b2401e64010740407040020540c1d8009400052041400308035182d030002c0c0d94583c0e4040004000d4652101581c0c684050041c00500a50845040008041000104000d00703030320042210100c000d50012084c1104e40c000200a003806420240081c0000002e200c81d6941007001451700441841c00c0c6403c035910480300782c800342101c1c201800800c426a21403000241d5800e804a00100d00500c05104012951202d0342280c1000111015a0b00609220f400004070051915808101183e505140c90300f150781e40d01440c00380c03600401401d801c0c1c01411a030610880c03981481c0c98004403003001344001ca820014082c01407048242c52034081c1030280c49407814042031441b05c5c9500340c0c00614 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 382795062 1250 382793812 382793833
    0x1803010e070e0a091b03061a09180a0203010f02090310020901050a030f1e0c0201060e04151e05131106030f0103170720190e13080d2a0c0203 62
    0x5020000c014410003203582d40303d4003900045d58401da004007003509009122001404c6141402c21a402c41d488140030789282000000e50b0b0b95850790055120044014040c00006101d0f4840c0c90010b00b12002541035003070010b0340500200c213901500316264120100d81d1000803a448240492091502407400204100011510a03009400882c82640e200100140c0080302059844891040700010075099071107101180c89580c3c24000e0380090544500b0200103400c1a64541681804050300c0c070329555140e4414a4425900c880e09070620791003100b05000e2850500741408003103c0c4881e007205c181d852000c00604078200001903070b200e0040c001d0b14004507401d5031030302c81a01c071201e254a40b41c44010402100080d200d02c601040340f00d91449100a441002d030100b00c2298190350700c00c000807010210411070784101040c00c0c2e07004030b09000800c100010034188841244548400100c066042c999613010304481005020202c07240b07581c003001070754040202110119000e200281d4590300180902 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 382796312 1250 382795062 382795079
    0x6010e2209020f040504120e010e06041203030e0601140102060a02030402060304110a09020d02040f080613060209030106210501060f150e120d0c03141218010b0603010b1803010e07 79
    0x10704085000502d00101c450380d2000007016141c007210300303e454800750030319040303181d800103000f40e0b24040908003130860801c1c62000c54483c0c042c81c840c0c01e8440d003803160800240350081c5e2114801e80c0f440000d0f11810741e1510403404120080d000d1880c014403900700001c1d140c1d0244e109a13802154020919851515103843c0c1c81a03144000300e08076400118810001010317980c070310003450703801c54403132015845030f1600c03002218080843c0c0c803050071504800100002c800035880e000070b0b00eaa1012005842d260320b840400c2c018413454100b400c6405080301c3c1744841d21480d1110010345c5100d04021710201c3d480303401e40e01203a07145110350104000b6400110b2840ca00030703d12030810000c09000b40480040a40070717107240018103000034011074082c2003c001403683c1b180c2510441000c1900c480e140042440c1c0c1c086d801c020047c501d101e11100c48201c04000c0034290444413020b00000c25558a95031580e21105043c1d003c001e101c800240c060303084010506042c041e07440b0340546000507284407444e01848 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 382797562 1250 382796312 382796321
    0xf031215031c090e0603060c07031206050604030f11040e0c01050f070b10180507050723010e100f15030602032206052d06010f090305060c0306010e22 66
    0x407581401107044551844251056120300e0024580e901519645000c000607450715000d042c43c1d0081d0032140c20042c00022000031075010640c14a010946003180551200082030190000e039030104000a0000a01c618101000501805021803e6084d4074400400c4215802c081544901740c000040c4010158020320262010074214800d20b860011140c3e14109100012039400d60081c2d0908400d0000007003200d6505076481405108105608042c403000d030046c003401070010000ca0740e03004030120903082101114115600280280300100e06090400c8d118000950303582c83c41480c09486221007402805403403403800100c049840154203544540c4080e500003010354204070385044018a041e007144010300c4005000f503000003410704004002242c03203014248100c0070700044d80455041c00701c40c0207546400171303401d092200d030103d80b2000039154121568000340190140b10100a8904410b100031031084500741d8465124050000403c40c490708111001002c402852150b0811010658030 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 382798812 1250 382797562 382797601
    0xd020d08130f02011d0307090f0e070e0c03040204090b0405060a050705120a0b0a0b0f1206060408030a0809251707060801120f02090702030d110f0d020331050f0312 72
    0xb1841e040c42c9005c0f02080c50981c03103500c403400305072396113a04502d04070151290001c01e200b51400340074405d280030480140c210b40a0120340b8141c8002000c5411540c840d4440207a040d03100c1060b248918103800e04a440b80c0d02150b50f038440c1401c041c0094000c41c0705808848031301c080190b03004c0300380d00c03903c84100080c84849440c0d500607244a202041c00c1140e0f4014010b003969540c0260381d221070942455031425405400713240240010700007844007440c0481904d1401e40145401c3c1c03c107540d0341400514003040d203a8002130085d07250101800364100b0a880b8000c1e140d2100d408624080e003000c0e8503640313488500c03d001c0003c6500c001403101c44c02a08040c40c1160180d03081083c80d56058002420002c6c06440d01d40c0540e00006d00d40000d080703180600c200300401550501e0602c0800d111303c03407080c0700302c510f5041029400400170320151450070f200082c0700c28401c0b01c451a01a42004d410480c0700010050310700d032250800110a003a40082156510401040c441c2020384955803144005e014011 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 382800062 1250 382798812 382798847
    0x1003051608090a081903140408040b03150415050102070e0907051207030204110301060305090a1509080417010902011404081b1f02030d0e0109020a03020904080c0d020d08130f0201 79
    0x1143c141c00700e59503001525482140d8813150701d11100761000502128460551410128152020030000ca8031070340584044030441c0b06421341d00d03a6440350343c038204032181211a80c4240760100038880940e040c40d005068a000307808480c80603440c2c52012003040d0b4119514240d51b4041801401107042000c580344202c403121085402c045c0d00c070b43c006425100f1201c1081c07000c41000c401000700300c3c0c0c54040d00f908040c002e000f8146c484011b80340c203000c051100ca00c409005481c1d40790282040b5401d412240145600d12400e403561465550042c040d1520400580c00204001810a01104000102c80888150000405002e070740368103507507840540842540d43c4040080d48150201000441d1340c0380e02d054690186a407035016080c40c004440b00348450041a030315200034100140c540c001c11000b500d404840340d214a5980b8a4842c0c524815611110424021b07900007001942c4c0006141e50381d500349403110809a03450504099480000c031a01810030300003003943c038000d540105445007810300c800 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 382801312 1250 382800062 382800073
    0x30816030c0f060902090c03090604080f041e0515212809020907020f12161415011212030506010e030109050601090f0501050a031415070806100305160809 68
    0x42d10381d50701e1081e151005a9400d034941c4001c204514003030101d66486810684501d0860400316143d03991804010300c010668080007800c8400018070009450003040c03402c98900c40c0281e044641e540d00c80303080c0714103801504007400c10308681200000b034604c09000c1004170300040700003403006502010080c00094003e4050350b00164a2031180050a04201b901c0380045905003451042c4076503074000502d500e0464000e404100c035020070214110b41019101740e401e54403903000302c0c40d00e110035114410080c0306d079030560040c003010a00441c4010100305110300c0a81c29030f90701c42c0c01c2d10256107041c9004104001d00285209191302a50050350401c0040c5022407034944e12034007103401c5a22039801a60291701c060010851541c0c54010380000008601090005500d418003107025100d2901004009100e454801e20b40003204001c44908984411a000f038113040040010301400c200b551030030b018458451160016034042d000792405218192602c014541c03034450111036140000d01050b035503000c0c9 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 382802562 1250 382801312 382801337
    0x309030306030b0f1902031e10090204061d0f0607060216050313090e030703230f03070804110f060f0f04050a0b030f0106020604050a0204020714060709091503081603 73
    0x1580c030700328410304c080001c40c141800e0624411074403800ca0369401180d1401001080f055014580d2000480d0114008015041e1105e105403246544941c11003c1500d101007400640183e11242010080500c0c119518030b9800b43d00a000e01c0000a0f40c2d00b640101c1c0130842040092100d0340104180e03900204000d0050302c45950b1035080d607115030300118911314085000d02482c062445100f0609120000540c03411805680150005103030042c9101c005ca1103207021209005200c00f2101d180344000344103503403841c00e80b102a1280c04103a4003654001601380038680b903410100401210520001e0070f45060442000d44442c1c164030800840d03051a0727041c040040c20385c5403501140041c140300c4034219101d2070000d000e035548080503030113001194003100c240004140041120000240c06480160b610711260a00040d840080018200b848c4690010460643c0e8810025016604800350910011040c1d4109030040d450600014003e50720811014124031583e07030803110240d1080c1850200c0300303030 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 382803812 1250 382802562 382802573
    0x2a020406030503190804020306010b03040203100212040b16090b0912010207081809041509110d140706140906070f0b04061e0c020307060f06050604180605010f0f030903030603 77
    0x39290710031034450b440420490001d45407485400030040f4035140c2040d02d031405070006541c40d841071140e109400c20000104055403814012400401000b40043d955540300304900f694070f5404403810741d817424095011a20300b0f03003117094005450f00c441c2e40c0c1c4d2107003c1c140074202c80e650707201c00595648020034495a84500740c2c280013601040d0700035500d8589601511200b100c5880d11703038184034811100c0204000014010020403244e82032104000144001646003902c40c1c1d060328000540d10040c2c001e02082080840050807412a00d500d040d101c90b26540c45083da020340c07041441410703409052120007054148031010b4a00c00c0c1c01102100071545903a211800003c205403002e840040c0c80d42c904c20080307103002c58601160003024408208198129100941724094a10010003003515500c030000c0329401500201d01030036008090507550b55690402d400c0c000c402c1414202214105035001a5a41c004c1c400c1c40707400c1c034054031800a48004408210010003103510100c06050f03483d034012001c0b99 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 382805062 1250 382803812 382803821
    0x20309180604060807061d010c08120a0e19290108100b090c0a03150f060302180f0f060307020708060a060e0f0c090607030203251707032a0204 63
    0x35102010100c241015020b020a982c040d802c00718450f071003014100142d542c403101180103000c1150045039045d900e100100c814548021014007031000c0825400565400c1c900c051740a10760030030003000200c110307601e240d4541c8900c0d03d1a4000c84201c100071004a01050346501c660708800c0340300c06405421000e50502c0250a801219890340504042010300503988591001d0741e5044641c3e8040c1c1c40c0c00c058603032461081c60300e104101034840e46001850003c01c206a005854440744446040f40c84000040094015118620f46000404c80400650802c02d00800b50707424040c1400c1c5044040c0307c1407001c0359101800d030b04114801c2103c00140401c0070310030340d401400c51050109009103030828006483c0c601801c8ac5040340321780307000c0c0a54150b03100e08076220541d05485007905d424031402d0603800d50003028014090300c140345006e010140c40c1081c01d550318501c1014001e441e501085481007050042500c0100442c0c1c0300090300d8880c10000307040c00040134508411055020b03282d0b001c60180e5 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 382806312 1250 382805062 382805089
    0x30106110f01050a0e0d0801081b041d030921030304030c03051204030906120219110a150501082103060105030a0b060a030e0d0e13020d140112021c050a0b0601020309 73
    0xa42e0345c084016684014409a10f1094440ca0b00c1482541040403841c0c880c400c0c002030070300090700034240070340c0e944403900942d00d0ba031646180200c4041d00001059103941c810b40d91030344145448281603032102900e622492012044000940c115600c1d0303503055031043e141040a4051183c01d02c0702c1d9406880c9907018501c207900c2a960609440d1500e0710140201ca06608045000ca005011035000e8101c1040940414444c62404080c0000c0b05425113040102151000e003881040b8407a107240107020740c11040c100e603c814202e03001c0300142c0040c0d00c00b01c140001800c04107031041001c62510340c880e002031600001c09a100203080d113280800030b141d0707600c41041040865103802d40b43c00c6482e028809550901001c0c03d1020800002c04002150010a54bc42c82d000c1c1c0e501203003e0b21049000d610160f000101001e601e480c958440c0044540f106130004220700c42c204003841040a00b070941c0c04604041d03803100c0102071501e641d507201080700300010300045c111720040c0f0420040780d071424602c0300c01 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 382807562 1250 382806312 382806331
    0xd0203030d060311060903060411150a180b1213051203090a020f030f0a2a080a0c08010b090a050403020f01050c0705010605060910201b13060b030106110f0105 70
    0x1124a145400780c80201c100c4504c520a010620403402d09440210321245c0c059405500c0810b03d4a6103030010350039100480007078203000d0000c64802169038100114244080c04a040c0e02005070359414150b195101d0581c2040c02c0e11648004260080d120110748003115100b03006aa900b4140800c90309402d410454800d081c2c1c7e401650400103506100542800d10704040d809044019104042d5650350403010f000104148190030380ca42503200c2c207100f0310092040100d10311440c07036a61a01241c1e500e00e1903200340c8000c50001800110000d05226440f1081c1c40a40500d0099491401100041100600590550140c0303002085444420f2040500c101d03c3c5002c2e494407003590b0706006003110303042e800050051108000958840e9110303c9440303244015407400140701400300150b114507113407280e258405482003038060007911003a82420b040040c019594062482c540390007031800e40f2400d201d624120102040103100b424412010045410583d1049070801e4001d00705190031503100300c1d4071291 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 382808812 1250 382807562 382807571
    0x31b08040201170906070c020415030804031403190e01021c03150905010e061215090d03050c1c0509070b0c030a020106120c0e06010915171006080c0304020d0203030d 73
    0x4640c1c0201003010740a100f03184150b064900300100035610382c0060841000c1c0440c04801b04115651500604c5034611032681c201209907983c90034100b10380150008607403260b003410045140701d0b400400e44904003141380b142c2e4000c0c446030b0400e4580c030320401603050440c02603141c1c4004080c00708074002d00124003694002400d04440f5150b00c41e004130354102c000d40d82c0c140001081504900304030a07030040c600300e6080c08100021034146203001c02e021814404006100b080202c45440801c0d0344a01c0e00072901c0601984d55410001c1d03d940c0b1807a01e0000d007856428903090240401e039809a540a0724150441d840e42c0c0d2185005005e41d0400c0002c0742e495032000401c140305590a0007003200600c1d414a441c14001c650790388404c0711224071b0042000302c418200008907580e06c517415070001032000b822207100d40049401d004280c890214580c40d0307846040710115005c10080f03240c00049030500d80d6441c0040c3c90706500c68803903030320181043e41d011448480050260340c0920041c500507500c40790018 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 382810062 1250 382808812 382808821
    0x40e10050a050a0506250c0e0406060537080a0807051015030602070c0b0c0a11032103060d080c0a0302060c030c09090601030e0601060c0515040c06050307031b08 71
    0xd00c490203a0040b40c0100c20b5039004002035140e03081650004a602c1d00e4441000540091242400d840d04030058080c0910000001d002400c011529000747c0c0161000c0c041c481c1c44509003d5101040d00032030440c0043c41440041744400d4640d070040713004810080b1030140b540d8040e980e2070034002d2001a940f4400014540080103801c1121828049011800b4020090024404440f04401c0e1001910041e0001804010440c000b11160301505207219265150419002415a1000101c82c115214407072250001118640014402d04014074054602c4911022006142e001c0d040501015000400c54400a000400000c090025a070002c00244080300150600030303e0b001000c2e01c103404108040081c0100103140d40b0440e0080402580c03850400d84500004a00030600e20b00260818012032001003505039010300300d40d000303d001d0400c603400111881c85080b01c0160541e002001c000c2045410000240210003465100416050000d03450f5600c5900110032000f0104c0c04000506c40310030070 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 382811312 1250 382810062 382810069
    0x70f08211f1a040326070b060f0d0503090409140d1107090203060f0d02030a06050a0c140c0c04050711010c02010518030702151b01090b0609130b0f0c040e1005 70
    0x2000600384400b102c2216588088000710b43c0c4200e00000d0064288100140900b111061310340c48058034901c402965582281003484240c402503c000384101d400c1216541d451034a28141d5483c1c070341000145152200300010003000705103466044949200c24060804c0281c020b018050000742e01d516600d4015051484a90824086400064001d0302c107105108180d140c1d5040c020000c202a00c1d00c1c200e01d102400083c0c5400a40440107199500b01030030440081000c0c0c0001e203402405d51501c2c460050211507400381c5014401d5400c125a000d000d88080030700e0a60041c0d500708440b403d00c544a84c043e0b0005500759032021103024050b030b44850911102c000c4204a4800350815038000d141000c107558001070981400721814506e0700d801041c00d500101c03990351278101e0f003a074040080151003458500181045d9044811511031411700002409902d43d10102da41b18903813000c07103a0790541e18600c41088000000d040d012014105100101d5070401054101b800b461000200514540c90f01040 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 382812562 1250 382811312 382811371
    0x180b0406051f061e050f0c010c02010b0604060804020f010c05030a091a120412030e030a090f0909050303160513140f01021b040f0b150403031103070f0821 68
    0x4080c0c1040d014100b0030607554400d0956110713050100410303c01d201c040e60304403054004c40c5c1c0044c170310142c0050503500c00030b01540440c042d040150000d00445003010100460750045120f0880402c0d1007000040052070114a11800514141020392401e85140c407014a1900140f030420041018075005000c0446807a60320000c242e0701c43c0c41c561820b0010b0748001700c100806080100038002c4580c1165020b8020b4000c0a500641107085948410030110300402d04e11462080302140c405004020581680a005101c107103178002c0025880c640301d2100500b01c2141c0030104504200c414008044002000c0007a000105611940c2c0e01c11564818200b25040c000e40615a040d0341c0180b000601c00380e41c0040c200d80c05c40d400c4900140c070640400305100544990341d0314560007811400c2540306804d0b08005401038134040ea6031400751041800e40d0545e244075a000240c01581000155400229180000c3c0030401d05d444401200803405419811520703000d88900c200c80c0740d2034040780034010007104d1 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 382813812 1250 382812562 382812601
    0xf090803041703062b05060c18120a08130519080118050d0f020c060c0706020609032701030f0501060201061703042405070c0f061403040213180b040605 67
    0x2c0d02455828200005001c4079180001009101d04034004010a0f8039002140710000f508282518417528000443c05000c1d40f01140800104c1600c0303208001500b050324014015103025002413625644030b4131500c500b038001031044406c51a080c403000c202e603152560092951103074040400030150400b141729080d590711800b03040104003140018004154000f0b00c1c200b40a00904000b42600f00c810012810310041e0109507412000028038034824540000340c6600302c1d0300941c01c0d51a50b44400341482e48034400d0742800d40d140c0b907c170300c0300300300c500d4511110000e100c0c4141000544a201300202c076068039426400900544d544110402211031510441240410628061482d00c3d04148840084405059a60703c0443c80c0304000710049001d54101c5000da90420310300816641d13241c40c1c880c1c400205000c4e0000203024003007203550f071103480d41c10349018960061800d08032030001ca1a61004107031034039140c1400c2c0b0a0300c5802c0c0110300c03214901c0d80520701540012506292513550004030140303e41 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 382815062 1250 382813812 382813853
    0x501050613031104020412080c1501060807030b0109080a050703050705010c0b011404140117070605040e070c02031207050a021f090b0706021b0c0307091b030f0f09080304 75
    0x118016640600070354900c25607510008210400003a400814000d01403a00305690000140446d0000c0c8000207019000c1d00034900c0c11500c2c0d84403004081010620280704e100c2c0401c80c800013040b1103600a400c8540c0d03200062605400349651070342d07150f140480045080d01c5542060300d0500034464107211000183c5000c1c20030560300e4030075a458240a980c1449041f401c0d111400031504103507115004000c0c1034001c0300d28501c1e296114100003030384a41c1c01301181c540384a50300e400500315000301e0958041b50000f0001640d00da46e181010340d00031080880c1240d06004041c0301c65070b004005006814000d01490051410400c0d0303206001500c1400007088621024082ca0000310356404050001a01c00041500e51628134900d08600a0300602d10340300319801c001c5016035030008bc00200c1c00c0c2c610404404550301d5954800c01c1404843e0303001020b010201d0840c5050b42210701035001030a11007001c00e0005080e4480544403004c81c1c00020048803030010000070301052204070300d440d0f400c19600a = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 382816312 1250 382815062 382815067
    0x90109150501031a010c1703160e01031a0d05070902040609060201110405090610030e0307080a0e0f010e0d020105130b070317010608220b010e220803010603020c07090c020d0305010506 81
    0x5000004031080c3c0c80405a0402c1b55400b000300030085003501030841560031a2001f5124100580c5866141070f20340b40b803000180c11741000c40499072080c0685020419144c00c00f5800701d070000e0030700102c2c5800c080e003036850b40310740400040c0e051207600c010b00060025648440e4028100300d402420341d4610101079100308405e110a010540c0c403400f080d90851421030301c407040111020002d40240203440c55003006400003054000501c00703864000c2443c20035a940b003501c1c14a0000030801c845902d00c4455000603030f4614021030300e0415126100c03015005041140c10003960311008486840c2c55000b8100c07030200030600c171007010b070807100412036080050f04d9104198140b4000a0a4201c001c2c4030b0030303501901d1009171291000d1107219000c56030b0420010700c035644e103401c2ca100b09640259244001da400d91003078010842141c1ca00c1e00c000d03503031005030070340303582d1808000328069040020700e44118019140c000405031a1403140001000c0300340c02401d00326894070400340440720164010350290300c04 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 382817562 1250 382816312 382816331
    0xd0e0a0f0810021c0c020307030305062409030c060409150f0303020616050706141005030106030309031104020c0d020d20192105192a020f09010915050103 68
    0x3040a00d010215007200507101d81300701034040e40e10a0b42041d040403035441d103684c030f0f5007aa03400f100030b1000d18040c0e141030010b51224000e004008600d110071600a1340d06800701b0744001e02c00c1d40100035124006003194401c040311400110150b0044d0700540d0400d07a10302b210000d0450f10360310140201160320401000c10b10710380300603448050041c07410f0a0074502e81c2c00c44199074000d405650507160000e000300001840b0480c00c000341002614040e00707441c0b0701c6200103140d01d414000d00c019170744c0c1541c80f00340306ca20710744d80e4100c1e4001c0381c03c0d8a2750084e002e1001d42e5582804109000004102d17500400e144410040040d020703291418006000180d691140c103403e010000301c0c2e200880e98240040e1966015003046500c0301c0707486483e0710102c4020900c541031190b01c04003500c3c1c0300c0992034800580301d0703100005650103801c9640c0ba4080c1141c02c404101d007109191035004040340040c0003000045d8801f40042d01f6820700340c004503241070340d554a8200e51842c0399020350103400282000c01c0700555 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 382818812 1250 382817562 382817579
    0x30702010c030c0804031a07031b050a05161a180d2109080f040812030105030a03050c0115091407090602061810050c0a120612080d0e0d0e0a0f 63
    0x110700e14080c0c00c0c0025001203000308000c0c2d40c1103c0046030400314401e443c2c80d1342e041c2c0c164007c50035105640082d0400c1547c540c075200301c00ca0300398a841540c868502d010304524040e14160420980c100005040900705030118180a01c4115441110512040d691500b10024060240e40e10070852841c0e120000540b40913420816001442e0a81000c0011180d94000c14002600007104010300c0c0010116410641685031000351051716888019210a1420f040c208c0940e80824803500d94189d12514640c004a4000c0d40203248410490001041c8048012044603440599601c800c840e9035480140076038807005801c1d00c94206c0e5030351410980b040d1030310f40c0080d0f40301c1020b42140d07003500b58404000b641c080c1c2000500c008038002d640901031450640804101508000c0b054130200e12202031511980e2020700c54041500c0280b441781c101c01c4819210301d4100d4001500c01141c0340d42e04d01482034600d800300203030746050360703580d5a454981400001740410300081c3d60090030b1051105000748159075 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 382820062 1250 382818812 382818827
    0x8060303030a0906090c060906020708030f120405070308120a111c020d0e19211d13140105040f0b0906040c180801061d13060b0109260f03070201 64
    0x5440c0001040f03c00141c14101c0041104080080c921150808001005034100c01070008640c865004d03510f0301ca41e11000c4680764845d00d0840c40940c0410030800200000c4100495002405101220429601ca070b84d40b80442c0d000a48140008601c07a04008003070041d4001c40b01410b0a8000d150b0a1800304611a629443c5100548882e1500890444003c036415846445402d5001007141c0e14601c00100f4015916880300e4280e134104130341801d050009014190700420980c55a4a1317002d840900508200301030003282d10b5590091840aa0202d0711001d402a201e1984c0b02d400312648070b5141c80100800c071800030382c000030704505000341e0042e2541c03681081a03100c1d40c10f83d0b0100c0ea0040238030b4121000142e040107911100994480400c2c0d203d0150f000005a403912203d05103c844842c004071400388048680e8800703100c8001c3c1d101c00003000c07138020050110060509404483d21030151000c0a8040c5600006c0080008601d060b01c200402007880143c4540300510714103100c5800080030348 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 382821312 1250 382820062 382820071
    0xc090302010e280e0a0c030e0601180f0c0e100807020c010e0406030204021207030509070308070f030e0301020d02072001090e040f02060f0403021e03061602120a020c0901060806030303 81
    0x2030030142c220300c00f90700c40f1690402c03203803010100600034952900c0e41e100e01000309950000c20b0b50719100340002c10500034402c49a00646020060546030318102c0c0807001112442510f1480e9034075004000d40701542030082e03071182ca0160300c903485c0e6026410144400440010b030035404006c59141400b242c6500821041660702081c03a203c40c0d085041004540540a5a13100070740151001410880461107040301c41e0041c14142c0d001e00868440c040300aa0b075204500010301580010082e510001d41c150918900980c40b9060840e00001c0140000c5e08907080301c0814010a0340000c3c0c3d071010071800880a1503c148994400d080f00d500d01c8c8002030080c51303d800303141640846c0f200454140300200b4844000306a008102c541c1da450311242074076164000b032104070301a940a5540494044240c1050300341044060024030190713890b58824540601720118003025401442c1340d09086104c004c0041030408101c2d0002c3c607081e07008505100b940038050b845241085a4241406000da4011048070b401 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 382822562 1250 382821312 382821319
    0xb030c0d080414180901270b0609092419060b0306040e030f07030e0f0d12080a0b0d0f1a040503040b130518060406090213051c170c010c090302010e 65
    0x38204080d020030780351880a030513921100c0d001020894000f0054005040400700b88440300030b400941c902080381402c4444000741040c50910004019060003844907500600d40c1d421148c0035486503400003042c0150810742c560751800107081040d41c0f42d0034442000304407100c59040141c2c0b4075040c40001503020281c069441a500d80c06100100e0750304006848080b1001034035030ba500e88072481d01070b009000c8060240e00611102407401c071a485d0086860ba08282c03c00380d884c4120740c40c2a0112141c11004004820180e500da00e821510340341c008111a80b907110701c0700340b01c40000702c0c2446103c10408040c5c40c6032015940080000041000c03040d00c3c00c807a0030580341340d1a4001010b201c0c40704007603a001640c0000300d0941c0343e502c14200038031444c002c1500351001c11019464120f5503081e4800c4103d0f0182e0240d07543c00410607401d189640c45031840803240d521050400030b032384119000080070320500d4842400b256040b0200028401c1628080310390070b2400344185507500180141c040c0c582d84510 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 382823812 1250 382822562 382822589
    0x30f0f05040f36020c0706080105010f1808150405060105040b0a0b07050c090c07171323030d0504080d05030609010b09190605041a0f09150d0f0b030c0d0804 69
    0x32400a520f00411042105459400114000e040b1120083d0040c070054800e51080130307400200c83c0c1c0210021b90582e038041c0d48450003a44402c1040e203030340d00400003401a07400c1c03000001510100501803400c1e1200310000c1c41101d8101800c0c99440e01a041e0031140c0f1507071824044008a0752094200e1046915101d035031511410182481800e00c000440c0c0c46401620042c1000030780f0741c078a001402c00c24802c0540404481180c2c2c0c000f01907016049c0704504101d034a01c1c0501c0f0034180c0d005907400344000d60710401c20a01254022904000c0ca581014010031800301d000d0100820a000d0440e48086c545019415460540300242110806200d99031b68508005180d0f8020b03110b043c0c8841c00d103200c0c80b020031100c07584e0760b10017092584580314030314050002c1180314442c81d081404803400b070800c2c0707181c40d420704419034104083d111441042c0420b141d410040380c03500d00c0160180045d82c41c10390000007945d410031000d042c10000c3c0003240522841240c516500080c45a20582c0d04ce1006201c0320f05 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 382825062 1250 382823812 382823849
    0x90703031107050405071e0e0f04020f07060204090e12090612040f0209070504082803030b0303040306110d060506120114030c03030d0501081218010e1309030f0f05040f 74
    0x1401c14842e6004590854141070400484c15004047d0f201189980d0150685501449034101c0c1c3c0c610440e064281d100901003c084401d1034030350060003003509070513429445c0100c04d40c4ca040072a8059800300d640203072600a0080300900070721101d1340c0d01500d4031505e4503001c02440001c03030602c900c580440c80500c04101050a020f8142074403241c0d50b6004c1c200f03d24034240864050301c1030300175129030304003485503108913090b008000744940100c50f0000300803100c2908980e0280c0c003401d2484000c6404d0322041c04000045142c600603c1c0400e0221740789182ea510f600b0907810700755003c0350056401001d0810800013141c1840141c0e034111030481200f80c82902c0c04000107410080701c0e0000ca5818440450424812400c0c1c0e44094100c03440c1c0e2007240c1f068182d4418000f221b0281680d070000e480b8800c805911a54080c8521120010004000c9417450070348500d850202c54403a081500090800408420082c0d0000c1161400c1c030b41d50b007081406c1601d03104001c4120381d514003450050b22032505502c1c = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 382826312 1250 382825062 382825097
    0x40204091103030c0a11150405370608070507020120100c080604050108070e1b071e0209010e0c0d02071b08061005150f090118090c120509070303 64
    0x491100701c01000c1e0780d070340c0c0080c54003203668840c03d40098640d22940c031208041d5161842d1490032107040609014101440c1034204280f401c5107120a030300c40500d0540140a000807454001c20701100e410038501c1090401000400300c0c18001d00312410701c0740402c0180c01503038124003000d01c0e08600000200040500d041000c2c18410484448600705003404c4080c0e0050b80c1004080d40700e00c2043d2020050f607a0380340c00b9195100c1c02c0b031040031880400c2e072011a1484100c00c038040c4284906010030bd1411000d55900459403598402100300440c443e000f030381c1185000c0d03020381d00410070308010039494185111081503a11800c0c280680ca50780c0050308100300304106000d4007140a201030300d002d000e561121017688a1408858000107002c5084c804111840d00c2001903000000c59010241402961483c0c41081d0388140740301d605103d8003101400390311402c003890301c026000302d1002103402c0c11010070183c00c503810844441300c020300701801c01c1030b102000100705003165003500e00402e40d95500c003040c = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 382827562 1250 382826312 382826333
    0x9090507030204020315040b0901240c020a17100507120b01180312090605030403050d1109030115180b030c010f09080a0c051509371203110a0b04020409 67
    0x350042c0c0040300300304446903029603d001d02007061f1401d03c43c81c1840b40801910f0301c000d006001d441020619821002c110042d04003140f04800d040c040d20928076078002035500c2c00580d1040c0d00c0791100001e040507204042c01450034507000903509000605083c0c10140058075403043c1082443d40e925003141d6180e00c0b86084003582c4015144006c00a070300d03401c10103080d82d045114100410412840040c1c0c80e071040c0c0480f4402c0303425945403400d00d0b5464002030003510040f00e28444000c01400070381a143d41c03c1c81901c0030000c1290040c103110b072030007a0300c500c0a091135010f85016494000e1003070b05074401003940c81c0c102900740b8044076100e160120544078003e0540040e07913240b05482140c810800c0391038000007522000c0740d52a0140065090032460b600c00c130350005401c00c00d5201c1c4089010001d900c01c05000643e40590f20141083c248070b001c14551a90000744031100541c0e81c0001d2540060401c04c1041c203210160416401070745070403003e100050402070045980d14405d0042c041c04002 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 382828812 1250 382827562 382827569
    0x10809120706061d010f052e020607111f020f1b0106052e121d06060f0427050106170a0209060609030a020d02030f1c08010e0f0109090507 61
    0x110354803072286051001c000e19460050302d035402d803005030380340307589400708000b40c101e5042644449036541000280811507190003c00c840380103031281809046440703140c0c1c100a0440a60041940b49003283e8001e201407104900740403140c010000902040030010321003080350100c000056529403105017680214031039100c281c650500b8414a00c1e405050642012003110001c4410b903005514072003403013140e249016891420f00940403125030354980191181c1800011841c0c00042c88044d41c5100268102880b4100e80e003900314108101c0e885ca8800910345d4281d00c103840070800f000741108004c141c00c840444080d0f03030ba0300400f520b1040101c25000300d805010403010181030800544582552200000000c1744074084139030009215083c12015039058400007802000c5040a540902480c030f43c41003816a05400350b144028508a000c001d02e42032045400c1e07045900c01c6005000810744401038200701d0400030a0000d018017080b203001d1441c192048641300045105447c03515600d0440e1a52 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 382830062 1250 382828812 382828843
    0x715020c010e031e030a0201050a0b0a0303080718090b01030e060405030405150702180703050601020109020907032c030408240c0f13060801080f010e0a0b04020d0605040605151c02010809 82
    0x1494a50309413408800b80c483c4000d260002d0016444a20100c010b43c0c1e40d100c0900d401040d24042000424400c85410350000c140c0c0c200307207000384401b03a41c8618440d2542c02540225483c0c1070448110750303051044e00e036403550003800f1307051a0400c1e40d10a9280d00c034501c038440c030504030910007020304c0780701804549a079540149144a0348558916507043c55070b0858451001c41d1510000071440d50040c0940c0000d260300038014051035a441405030018001108544095041039140c01c541d0820307522405424403105004586441c9040105440c200301d1103861240400c0c0c40c03003131047d0310640240786a0041d0500885646501800760003101c00d00801b9140d86140f40c0e1101c0c000740e1a84c00a03007090594511009807012805801005401d85003041d006014a0340315488110114161440e10350700140700030300d4000e40f601c035519442d040d00c02c280e405440c5070b03540301c043c005070403e41000c40d44000401e54044a0340d6540244010000740c40b0300c03000c0c1c180165000042c1000c0302c1031050242461441 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 382831312 1250 382830062 382830103
    0x15140403020a271b08010506280e0d0c091d060708190c090503210f070206160b06010801051e0d1121010e190303020a050d060303030902030715020c010e03 68
    0xc04101c41d004900c0309100c02185c0c81c04004203440c2800d1044820700448081c100300108802e410203d140310711000c01800f00182d41810007039aa903110b0201740e204e402251740b1030364a4201070b9007030101c955001611541100310000502d01c2c50300400c5059000005007418000c075580c2c201a40c40310780f400c0008401051818041080182c0c20024003019100190100c1d000303407046502c540c0460303420a11007060650284007031011390411000902d106031018140c0d41c109403210321107200840080c0c60481b0105269020403a495900c20305040c01030400b110481c4d17546031410042615a460200b556005a51055040b4180700038024000f0034010041d103000c007120030390025071009075802c0035211b5055090a0950030746c25000101d0342c05c1406007c4120a4002c075568068000754004e03800c4a00f441018070080d0500000f912038140110701944001c80c601030f1a20402d400d203002a00075054801d811505004000d81c0010000f96041007800c200110210a41c0003d2411201e18500680d41e80b41 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 382832562 1250 382831312 382831331
    0x30d05010e25020304050909030d061503110f030412090b0a050904050c0a0e06030709080313091b0509040207060f0207030203120f1504021b060115140403020a27 71
    0xa607001d00d8440c070044861015241c0200c08550060b0892a40550050b031013400244001d02c0d00405c00c40e000320008044034600b500061028096604c90351081168489010395050002e0305400340390144000070b016140f03804000d40c0390034070901002d4000b0f08203181e02d040050203103004141d900f024090907400940c80e412003120007027541c2d000351207190280e820030010074802e030000000e0b40c890203a00c4e02c80340c030000483c00600a441d08000c040a04020700c0540002d20500184014010504a90030038a2501c4c141f40d441400d5510301109a07000b801000c0a021400307074010b0603910080400c94025a603410141002000b41920684040c2c0715440010343c43d00b0107400000404869400d0440034460344d40b003802584107080100d0320b01070007a0070400d190003c0d00e400d80c001d04091181400701c0c3e1b0450809844c880c0382a200342c00903e400240c1e56075440e40244c00403404005440440c964502d001d040d0743c0800e170095854454045209072200f41300c07031241100300f24600159818481002905030 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 382833812 1250 382832562 382832579
    0x2010e0f010203010614030f01150212030115080105092512020409051e0403021b0619020a0516080a080f1e190507030e100306080703030207031505100b03040302030d0501 75
    0x405e1099001040d04190041d81c46403540c07041d240310b1410665680d00c0d0f40e00c0c0a901c1c6041e5442c54200c3c10440c0200b14098404400c15030143d806001917041034050000000000b80030300006810080c4586100020049a900c0d14100321100c1c0074070341e050410320f1410100c2030b1601d2071799080240c007580c0041404a01e145480e8402c0303106815840c00101180c0000401035009942074070042c00680104c910303c001c000ea9020380300065440a84400d2920080030f414038465203031b901d09100140c00c0001c100f414000100704004d188081e01d102c40c5240c500e840e1a0f15030300c50907403a000f00121004205210800e54480c16101032407800101e03500700703070040c04000c941c03076000c0d00c520100480d4030b01c182010b040c4110183c802480d45500d40c481c12074140c0c0e0801c00c400d12a80381e024100354031000c0220751030303030280426001584a6002004258110718100404091140006041e50f140c142040208007410910034102d400560305070b0383d60b031030300d040413410752040e00b50000d0b1036410708000050164 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 382835062 1250 382833812 382833817
    0x9140102121504181b0302060d1b03270606090e07060908150105061303051009030e0306100b0304110d0309080c030a031218050111090a060c08041502010e0f0102 71
    0x14a8555400b000c4400241000102c4907080031841d20491061080000210300850016160018110784506a656070f80000d07141e521207003401041d0740e04c3e82e021401c4400102540700a4250900701442401c1c3c907e805203404a00441c0e40502c0320200c1c02020003071002c0d60f44440c0140c000e4801c00e1184a0a04592a940b21294070804000485403400050b400c01c000c41c6040194141c410410816480c0c00100801500645004c0e140700c3d126000010014208009421420306d4072000810185290704000c0c4c602c1c001c180700180a5000002000b14110000c1111000e0b9050f042c02c060301e1b511542404116016402901c2741c104191001c000c0030305070840d10520469014404444a19458000f496114441002c008002c18003027004c1d41240002078000c40c1c1035440c007110316000b81034151245400d41c2ca000d81c0c0c0240c0490005880c0080d41458068500900103a08004d10200042c0ea45c81c40e29228a22652400c1803035044507401441c07003074103e540a55002c5003142c0c070740362018842c5070003507 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 382836312 1250 382835062 382835071
    0xa23070c0201020f0d02070b0315040f0506242203050d08010f0b09150a020c040609050f0115080c0d060b072012101112040b0106080105040203090a02040914010212 72
    0x5100c0d01e202c0205124000903260420a12640078107c018a0001e00e83e441c0c0d040980324482048103e510049207480c1e41c810900066665813000c503440c00d1100910050350364600340d110301c075403100314441510b840603802c07540300101c6990840d6581c1a04890784e810034807550801010307409001c0d41e0102065100c50681c0c1030380c05113130041030312580d03e00c072000710f07407103010980c2d9040f81c660b010901c030910309400a0945d40311a8016a44000400000582242c2d031540042182685d15014010140d240014503405000607004000c00c00441c1c40d0094440d0701e0007424080130740350000b0155101400703508480c0041110b080d449450740301c1c03403501c00f003d59402150840e10041d44140b030003161826104200368000c0c4000035100300000d6131501000342c100b0400410300d082d0f040100400300d58803c940d040c0f0850054914a09070f50610000601440060f031001d840b650050050040c100740201d460030000d0360480d40000c004149182500da40303070740607203045440d502c0450b0b1401008580049103224 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 382837562 1250 382836312 382836317
    0x303020405030303010e0f060a03020d03120e010e03070627060b06130b0703110607050a051b0a03020a05060a020f0d020306010905041506030e0f06070503100504090f030f11060a23070c0201 83
    0x240d9a0300d41401009e0506110103540003107890303c00004203000d10007410366509081000305002d0700700c0c1c4201d400e440703d0f802548090340c00004c0800c01d2200c2e80c403400040001410107034068100034540c100d80f40040f42c8001c0d2119550700d41101850b9504021580300c2d0943c10a18443e00c0c2c2c1d9000364440b250440181030b40440c0b00c603180341030310400226409200d05060748a59003030650515080b54150030601c1c2a801030230014426021000c800c00c4042c040c18465030041071188201d14101c1d082c10006080004c1a40c0140308104400d05d411054407038055145200607200c0e07407010012684a0303510b03840a50000e203041c1842d081801e800c16650141d035403603207040c00301034100261141c2d81c0d03041c1003850310f8036000240407481042c032440c0115001f645e03103c0e000b09100c1d200d9001908840c00c844044880e450400d20403020583c00907010450820700341088401c030603918030801e4480c0401040c44c1740596403a820051000d81c108400d03540204004180e42803490440c8001c0c0001d500746205901 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 382838812 1250 382837562 382837591
    0x501081005011e020312100612020a0912020f0a091d070308030403030e0a14010504114005090304140616030f052b0b030f0312040303020405030303010e 67
    0x84105842152008030740d4180d4810b110301c40c0b82d0001c8101e1807a4100070408502003040400000250300020ba03005914003209440c04610300075014008204460281225900501c80700e90356541240406d01201c5150442031900c10140c030020710703020200e000c00d503482050010b01248154190340301c006000318454140090040d07048546507501c0541c440102501001c20028000900c02e420250000342100c0072a1503b202c1940ca608051044041c84805690341380c1c100310500241c0b80c8803100c200c0d42555040700b00100d401501200000e00400c511040325104107020345c0c4000344070070860700020341c2010000e6040c00c0c1480c40d03d0340d1182c424071300ba0600300400c0000302e00d00042180c2c1b440110340b041a4503602241d278181c3e00380f800c03109410300788103041c810b0302c00020800183c1840b50b0040c04048010f038880c4100d0008172100710044038000d131300091000204c80310000488042110321051a06203990f03a00d4200c000c0d03c07031a00419050300001c800000c040d100f40040c0d50040b40e0065032440f = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 382840062 1250 382838812 382838821
    0xf010612020603010314150103030e0102070512060a0e0304121506060806180402060f0a120e0f0a110d08191706130207150501140111010507080105211204050108 71
    0x1080c0003140c06540000200010000140c40b070160120a110080a45920646002c518001280c09034002e42c040380e205c02e218001366905020f100d000d00021240c084035050b0010405547d08401032046000d6540c88003c1c0c041548100180c40042c80c080c1c81412500300c1034a4003c140f040002980b0b94805c0c2400f00108103180190341c0c1e01c1c451b1102400d800240008180300a0850074090020383c0c0000c010080b0204844908004101020544c2c03502c98100e20107103003800c2254440c01180c0488d4104405010b0607000c04181101403070b030030000c5c1c06602c40f0b5241c000390002869806c024411480090740c083e001ca020143d031600401765807145003000881602807200342000325071384e5500c017102c854000440c003240e60140c0b01e02d5000d20510b041c02c0108070401411554280c02480c0c2c00844803004503100d41e03000101d100d05080d504001d2006081c80c050240a40d441070003118481c01d00c019a07003407449040080040040f00107030031035805440d280148041c980c043e0080a0000d00c5d040001f4 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 382841312 1250 382840062 382840079
    0x6030c0301142b2003061609030605130b07020d050a0c1103190b070806010c080a030b0904050606131401050405180a0813060f3009080c0d11060112020406090c020f0106 74
    0x40c84c0320800540076241a0381c2e07400c10382034600b03918403006d010302c8401c1d080840440d88074802c9610a0003400803038501c000301c5042483c844500100740c102190302091701d511a2a60110503141e110542d4206040d41c0132507490f000c2044440b0a010076050f03c00c1c40c2d030b0500300140d100f804820050080c07c05840c0c40c1c9503032400701d601100860300c4502103100620106d00046c0410001d09206140c1e00e030006540003404002030ba0344009650640c2e01d5840103050192910b001030940d107441d003402800700b01c52104001444034540051047c0c03803003180d40b1000500c90400c180620704c5140030342816908200d00d01d182441d20340c1c2105880c1d0391071510b01c14010400c40e001e641c46c1d120801158840c1c902c0711161600c0d450100700c01d00900c0c0350351604201a402610604d000c3d03e01828400d048085d2500d002c1c4080030700d030200c901116000c103c2e40180078411903d0215004e41910480b2000022051541c00404c0280c2626408034615900d400070f4500b04542c040f07410001e07030480304000d01c9080d030b071610507 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 382842562 1250 382841312 382841363
    0xa0b190b03010b07060e0f0f0d03060501230403020603041217060607140705030f0a05010f020412030309050c100309020a0f0b0406050309010608161406030c0301142b 73
    0x115100000d040006100031400c0c1c2014000c0719110717480105181403034100d043d085c0303115156041010f90188202030404101400405080401450100101440c12000a0018184c00301c42e01b498045000c00014110441d01258060b507005040d981d0340e800c0c1490601c810810074a01c901c00140c0d82800b80d68404c1c03ea100450003014000e0600e41000301c15140e0b680c07001d01a41268185100f40100002d036500e040c0310191103045018084c241850383d03802c1a07420349040e04051001c041c4104018007040c40b04280c030030051034040c40c00117054101440c14a00e00080c40002591040315010a4002258075401c100b00d418403c0c0ca40752042a543c0d45050311140c0c0d10301030303400d620300b0510003408554804c0000e1070384203500900100707640742c5d03503a690780c203080110300c1c0c140200c000e0001c140300009120141200c020025102140b551038140c0c1c40b06121300040c081c00112020140011480f030b80c41d06144082075003501c1c001e565040598440f41e0781d0250b1108100c030840b008881c000c9609021052 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 382843812 1250 382842562 382842569
    0x60903170f09040216120f090b040305120c100912110c1f020a020409030825020a1113050c090111010209090f10090608010b0a170c040209040209090a0b19 68
    0x3155030800032202c0400c40a90044100710704020000a84400803600d14415500284400c0c0c85010303500741312000c018034400d4590040b41c1d003043d00704802c0001540c000b440803010150a4081d5071140101080703241031003101158408914100031901d001e1100120309010507a07a507071245000c090303c10f80003603110145032604070b42c800400f0000c2240c180741c070380401c00014160302c103031910324010b03500003402c40310154000e8001078100d03005c011a130310100000242501c00924450030410380813030001d54640c0ba2070340040010507140c1924505807070b0100c40c0c41015510000a00007840e08041040742a0040c1c442180024000724040310352280600c201c8201e20070142c44141d555031400c0707500308106005080c20b00d0702151548005410b00641c850500901030510011442b015000c0c100030040c60780d60007000741880300040a0220040001e03085107200c43c150707405078640d415800050f00070b000300d4402d0b40d00300c1d10103010400003001c142e01400c1c0400701195100d04c0302565004500c9000c0c828003 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 382845062 1250 382843812 382843837
    0x30501060230042c0906041221140901050c040503100917040321050c0618031c02040512070506030a0e0a12050d2406050f07050706090317 61
    0x702c07642050365059408a04200ba803810501d400d6880c0030451810745440c100001411520b54090031010328826010b82221886004200a0920303803650103202c45245442d9043c071042e1711043e650209880c820407c00b0b6021001001107120104841007030080840d54007115500c0c0c0800600c0b00740003102a20141c1d4070240041c0b80c007918000d4808000c0904a4081e03840291001e500b404122401c0000c00145208401040581d41c041d80016009442c010607041480418051403e609400080c150351003507400107480d210300301890041d400c1d442003011002c6082072007906000101459002801200e00075185a1558424100f04945410703050040651240d410804603030422441d4100383c0b850400ca1081d1112000d0565445242c000606019004524007190403542840b56104100c0b8154810304004060221440807010014041c0500c0c0180100881c001c503508004e0401d07544290380c000c0c102c81c00306072a840040c2030300401d8803040300c00481082c10110b0780800c00085d00c00c1340d000c48 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 382846312 1250 382845062 382845103
    0x6031104090203060d0f141c0503070c110603070207050f041a0d060b091303080609010501140c1c031509110a0806060c0d0e1002010902030a0209100b070804060305010602 75
    0x1d1180c801950000d09803540c41a42c1e212a4800304240b1419800a2440307840e030307c020004950388117400d04c030074a0003c8a81510946500012a400004499010042c0c1c030704501c5018961a040300810300b05a07516420a002008104856400042c1c40d802d035801214118000240e140401060314594003901c40c60340ac0c603400c01209402e19018101d2a24890072000c1405945800440c0c0140c20403102c106061803510503480034142c0010059030000d4040e41c500640d5030610002138100198400d80041044000901c100364a00604ca440010410880c2c1240312079503e55004001c2d005655100a009061100010340301030309214040c407030200c409042d030030850340300703801d44c1c0c100801000d20b90400e8082284030010f540920007410301040988034007840d40d00d170106000d04170103944400c80640e1305d080c004d84090303035001a0a100709941102e11102c240d90348081c0e1403486c2443d500000c207140002c180d080400407510b025009440442d40c0c1040030780e0341c421049986250381c103140507107070f01113 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 382847562 1250 382846312 382846319
    0x9050307080715121802100c0b1b12011203020f150601050904060801090c0e15060403080d02070b0405031210060806041a031605090c190c020a030b09010e010606031104 74
    0x1550b4110398003e243d0b04000302041d10344506401515420051086181c021450102c2189400c0d4102c02d202112071030604011000781c0e450300c540b103401806400248500c6280500752120342c030121060b00c2c64110040c9da90396515418074280f1211041c00f1000b502521701c0c4005804000542e5100586285c250262030307481e01801076485502841c8c0c10f030303003040e10780801082c40e45090140c02c0307403580700b0600301030b080b490500d1044800320040c20010038290107114426907640e4402c10750f401e41c1d420014003503844a8448140001b88101c01e001404007641d44200800e120300070001d4035080b04000740400060361860551a50722400d806010041200000825603900b450344c030011034186520110600340d0b010b0300001c0e00e88122001c6100c058915401e00748030f0f5082280810b07802c1300080070383c0c5060119941e082a0f00400603c03410040000c0525884159901d00d40d41200458000082c8100f034100340d200e00d4041c0c01c3c603a02c591099803c00c100040d5440c032070700c10303d0001080c4100442c1403d04 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 382848812 1250 382847562 382847579
    0xe0f01181a06010e041e0c090501020304060509120a03110c1014030a0603080301120212210c1207030305060315060a171614010210180809130905010606090503070807 73
    0x1e002d0812410882d090340090940e8482e0310031810b1441c0c80c10341c59420b20854049410035111180c01d0700c010041d001c00104001d0340c0000a40d01600c6807802c0c1f0070b4a03000300502065002100c0c41605115120304a844414590000845410260254151201107900e2002d110411454600101c001503000e60180c0301416410080c5070031000341c400106e03000d640e03a190208540c000380c00c08880300d0500500710382145021510140402020000b8026a6240910112000c1d101c2040381c41d082d440098583c0c0c030341c07509010542c0c0034034000d52001e07164a680d040050040c0011102240070380f25050803615080700a445d00c44c490b5200405484580781001c40601c40304450403110705291041a890400c03100e170341c0d625400039021001207840c030b0fa25100b00083c0f800940d0259100c0080c030f440c040c1292880841d00d04108550800c20070b903a10305980c8041034022400c1031000d260030380b0f00001401008010b400513000c860107580c551107980d0319101050344a124911401c02c880e80060000c005041 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 382850062 1250 382848812 382848863
    0x60903020a270f1a0a030b0a0b15120a060803030610050a03090c080307051e19080702090a0504061b1b06091403030907090608190606090e0f0118 64
    0x114045041c001c02c5000d07a080e0060ba40300120240d042a1501c02542c081041e04803074a42d84007040395440d904500d5515005005107018101c44070054030707040d0f1002661607041c0008a10300443c0c2000c1d076184041c10040b00c405c901503036011007003810184002040b0300d000013503d0080c803004040d60100d441401040d1415441481140c044c1034540303c542c1c005c502c15001540040c20148040c40e6900420322302141808904030141c00a40a001c00d4040051000100c1f01000040c3c10f0064640c0c1700107003003426480c0540000254804004010042d03042c03034035088a80aa8070500341404038021400c004c44254494458000002c0d41000c0c0380d8139624810b00d2200851401110b0000380c1c04155103a0352190707001d9040e550f00591000040c010911002c01c0380c0d0f4004c2405080c1003105034105500b098552a403070f24499600001d07910b0301c000b0703c8420391040f002440f151790704112510001003e5910750303141e0440861a94604044412424800100d2001c040d90000f891580c0c0a4003018800d4010b = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 382851312 1250 382850062 382850099
    0x22050604020a1d120f0c040f052e0e09010c1101051302090a060308070f0b0702070e040201050a02010e10060503160e010e070507050a060906200d1a04022101060903020a 74
    0x1402840c084c021038030184030100881c02c8030009000306001441c21700044e151000c051407502454042000311040101c1140740c002e420910803032004800f8071035407092010380d581180e0290340004c030501c10300100541c803a500c5001507448007282c041074549001d00301d64044401e8080540210034440061511900031544803c0c9043c0c005009516615080240c0c2c0041c0c4088070900c1c15016608148810620350507404a4180b00030011360381000e503580040c1e031015200074107004000c140105a94002e4100b501110103141c115610f9400c8800c104015090314030916019026410311081c204407124905030583c2c080d0500341400c1d0f41b0f0f000289507426002800d884c00c100c814000c19000584c24024034080900910001c01c04840f20708101e4110707201d07001010321482881104603200741c1080e0a40d6402c90342c0b02d60019100f101000001c0102002110890b031103440051045e1050300689559204007902c180103c8a80e80c8482069a0304010f40c04042d5200355003550810070361100c02c1c400c2011 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 382852562 1250 382851312 382851319
    0x6090909080d0c0c0b01080304050609010818060907060f0216060c0311150615030f040210090b03010e040b0f090a0206033408060618041a22050604020a1d 68
    0x20b000d1011040000ca44455a01200098034464002d0a00c545105180e014000d003c014600d01883d10001585600c100581541031000c41800113020511402c124a44a1548429103406c3c0c600801100d4880110780217504c08a0110880c82014510000e5010070303007000c6414400742c0303508082c400d0b1803503441503000b2403c2041031070000c0584074051029400d0f140c00000f40201c207080a0003001958070000142c141e80c00c40900070840e006090005042d001034044d54040402501034008855007009500908007080c0d0020000130748000200c00140309074080c4540210076100c1042c1f51110020a40e65580107500070361050002d41390030f2004541000701b1251624085640c00e400c1c06007085208060480182c12512105a07c4c1c3c010000b035900000c02c03540103203040e0712075502c14551425182210300450341c480ba510700c5142d10142c100c1540300001e081500381600300c80482604000000c5410900703040070041030030307420180240c5030402c90700d456074007140140c0114400100c454810840d813 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 382853812 1250 382852562 382852567
    0x302031905031c0f060b07030e0904110d200a03020916051c0f062c10050909030c0118080711010e040f09020405060901050d030f030e0724090609090908 67
    0x2403a29140d00483e9680d1881c29010a40c65101d4101508450349a44a881116020818031000a078440740102c04510115400d000c180ca81e030611114945501d052141c01c042c01644003001d00040401003200751040000302c40240c6401070903c1341260a601c00290400c0305034000c10254503460910f841141c0c0c0900d40030b41003000f40c11230340e0b69542414050810b802d82d50710481000d00f03058001c1501030b08001030700d1082e16588000002c1050001e40c40310408060101c04205406002443e4400803c0c004220300c1d16402c001299684a51040d92503203415880d201003580d0324001c40001c0c09185030840940c9050803d0350b2038000c0244000041c441c10020204900842541c0f80d11407152030f006981000540c5036482d1050100f10780c0c2c050202885244080010480c0c2e95664040040c00756161801c05c500219844054020300000c2140e1030359400f074080d01041200c050004030701d1142e2a40c11490418044140031740f95401e2a002e1903000030002d00051200380d0168201600492161503101d1 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 382855062 1250 382853812 382853827
    0x3021b0c01080c2101172a010c03090302031e0f07061205090f060108280203030a05130e090a022d121501090c0906090806010302040b060405090414100204030203190503 74
    0x144032400d0300b101012202403240c034480c0318402c0201e128660354500103020501100b00c1c2147c25041040075083c108400c10605008240c41240d08030000d40d40941101e069102d08030441c80d4048101c020300940340f1071100304540090000407000304662550315030046031072007035001d01d02400c0c5c01840344c00b03648038103800e055003040304000301c5000b00b0041c4060300080503112300403075050300c0c218807080c0c130460032030226405070307802004450561207a030904c1c656401c807500c10289130000c1d9510004034104114100801042c020401c1c03c0000d2003100c0410340803c544401c07e05c045814009132101100400b4148081c2c02d0401846d5600c0c030701c800c125160220a60301c4510018801d03081703903500e2603c2c0d17042800704036001a28080a8180f0f420100701150400b07001650310001444040c0c42513440368569405a180c00045402400014004900c0c40c58203003030003600b09094042c00c0301c80303110314101e10802203c1442030301c06903a030040242098144802030710102c0d400780da005a680b4041004202c = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 382856312 1250 382855062 382855117
    0x12021915080406061403100e0f06150a0603180f050106080d0c0b070807080f0a1b0f0914030d140d0507091a040b0f031b03010603021b0c01080c 63
    0x200540e1000e994040c1c4034600b80c5020400d0700c002d0344c071501040c0d410303001c0c1c00010358000c00e0b24411f68082c0305000a05110110751285410450800042940119018410035451043c1c5044999000307881100c40c4580e50341d001c80c200d8200e125800c0d030b0814505034407000200002070340c650751402344c030002c0b842036100c902090405c0d01c1e074019400400d0703100c0d81c242d04002002d40c20540c040518102000d1a1070125409000130400920052154070a800003070a060043e80c80a8003040c581c44040d800c1205003000503020f104242600c00100381c1c4a00005805000e10a84044034034001d0050001c0095444090f41c52079001c012610f50003034107000580305011f59100752445407005507211010580380134031003445001480e900c6108114100003e102005101c811203541c070040b80850740e56035880c40050584a40c00304680820070340f000000143c01c42d4141c01910010403c01e1a0204406803601c05070f40d9004030140083c0071a11610000d40c0f8600380c0700c042d080000103103e448100540b406d004 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 382857562 1250 382856312 382856339
    0x30c0c02091509060906060f0307020109051507031a011b020103140408070b09060708041218030b0105040e070f05150f0a09090e010b0312090109080111041509120219 73
    0xa80801c5180b003034000e0b8035443c010050b03e400c82002d0301c803444181091008900300307101d068603860400c030000020400381c41c800d51003c0c0040c0e4100d0280c0d948800c082136501c807280c000341d518200113800c158403014004030070792014980000503158100c40c5405c000c00481c01d0303040140143e05042da0b4101686407007008240580c481c601c50140300b43c0d910103074503003c141380d900680503240c6584403204014070150840703110ba0b04075030050810410010002001c84024100e003c2c0c0710004409644000108481d1148542c140c480450341440f0300f5410308091940e5942500c2a644070308c030700384400c000340e00300b024054180b00702020500c0d281c0446900028201d40c13000e286a800100218000c01c21210709118149994403140d0080c40308800200029584d0301da072000380c2c02000c1000624070701980c000c070b503410001c080080080c02406410b8400200c039401502c01c684820841c0300b880e1408900c6003a012080d941e03980d207d00d80520403602801050088008003000008800c0008101620200b10 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 382858812 1250 382857562 382857571
    0xd180e1006122021012907020d0501060e0108120d0c02030403020a080d14120612100c02150a061d060a05090103200f0a0504181407240f030c0c0209 65
    0x40c0f65030310049042c4440784008071200291a0241d402c00600010080c042c0c1d80c2920441a01d6590142c901000082c0d82441070010081d4001d0f0140c850504224040d04017000b101c00740260304a6523a42c0707900c499150801e00441544001007007019241e05c1e1800c2d4042c003000076041c4100c038241601d80d80414500c454030b07080030726980d02031040303840e0042c1e00c03002c1a0b040c8510503403c1030920744040040c0e043c96001502180c41814004007100c00c01804205841082e03449580601414100c01406501e812038060344c201041c28060000300c1200e1140103220880d481c03003e01e0300b14031416405008085030060401d9600100c080e000013400e545107902c0300c0c0a98060b006810040d428080300f000e40c00d811200340350150514920320b0815079601c802e0305003203800c166404901030b4440608818a5001c403680104000e140054890480c1400100c03042560041c1101d8000c503400c0026858859180784442e9000481d81072080d00c8452003600804402d038403a00b015000540d041c0e002810f4400200c5 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 382860062 1250 382858812 382858871
    0x30a0902061c060f153606140c03040e090c10090501022a04090c0b040909031101061a091206090f0c0f0a030f140d180e100612 56
    0x442009200e18184505801020b618450714542894004030300d0781c14613065001c0c0700340100880501c2c141c1040361b4200100120b0150403444005146260340001074090044030b00146180803040d24030b140c503004407464004800d004500f020314264018040c460010000e180c0e03030007288044100ba480d080c8084000e00803d4607400c1384035080100080c689200c0c40c9a20f01a40c548885142c40401e12921040344860207640110382d04866080c40e8101e00c066601c8078522640008000908400c0e079401513000a10a0796507070490002e08103080c0c00d0310200d004050700740c602c4607080140809118014003ca02002d01010075402810b400300b070504a04840b0081242c0002250642124091010903003126080341c55008000e020008907500b01014003004050451300c81c16002071002c1e800450120100c0c030b00413264001e039031003070040c07030b0000000b543d0402008401c8003062954261140e28460701b800f14101d00b031140b905800301d50810a030480c1c85112559107200c2d820307134580b0300400d010b007084c0708 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 382861312 1250 382860062 382860097
    0x50c0f010c2a03030c0504121104050606070c050609210f070906031709010e06030a09200603060d020109051203030103171207031a091f0603061802030a090206 70
    0x240050001900c1400c0300005540914644120b8000a8500c408050301840c4c00100d0543d4241c0c20b40759803095070484007030740d10f60030144020040500c4440101090a843c140801d460b035030305200c170382c0c01100401444800212801c1c070650401c04060f140c50203000340420001c0d0341c081200c401d80c3c40f2291743c0010700e41011421204140d01040071400410031003908000c0c162441e10b0742d414808000008800f800400203480b5a240c3c407421002032882e800030b041c2682ca080c1212040e006003d00842150b400b00d90b031805460618102d0b2019862101c0501080d145076150401c01c4801e01c1648000c80c1403200c4a0000701e213513220100c0201ca1611242c004655070350450410144c00f08a00c0300c5203c40301810428000d590080e00780d0650000745506010a40c0002e05029905080300228020303000060b490070000401c4c81c0b0780104003400c0c08240ca0b00b2130b080d11036000300c0035a4101d020305003d20b1001c3c850b0920082c025801150b002000240000b0a26110b0380055010707030141c1c0c0203c6070607009 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 382862562 1250 382861312 382861331
    0x30b030c151306020319030902240a02060702070509012904060306180903301a01030b04060e27240703090f20100203041809080910050c0f01 62
    0x402000b1002e000503000070760a05001100d039800540301c19401804040c3c03110305d19421901c030366101c0d8040400c01c0c4600700241c03400b1901000c00360402d210b502c0051055101088106001040e203000350b55019101c0d1034940e0030101d80b50748407182070200042040c2d12035460b000303034a0144060700c081c2c01c0e1507a0115840d40f40611500101e42003681c88402c640c03400791506c0001e40c00c00c0c905581c030401c41403218070340701c00d040f83e02c03508a0403251070b070b00d12604000301800007064026000038901f000340c03000c0000c41e0f0041c06000880b0503500070321141401030008a2600c214007104510044800400228001c02c0c01550364148489080e040e074040d20b20008400c580780c28050041d034400260300e010000c03588917880d582000710004401400e0000c0c0b100d01c0c1c100301240c0380c006441000c1c002e485130701d8400c01c1140c001c1da40c0e4410300c40d00075000d1848010741a14040380c040c2142c415007000070103062032060800c102d000d40728110b0030b10900c0310400501151040c184191030b00020101c00000b0036241 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 382863812 1250 382862562 382862587
    0x304090b0117040b0718030b060907030e06150607020418060506030d0f2001050405060103021e21010b210d140d0f06050d0c0911030c0703030b030c15 66
    0x25240d09040c14414500c180c0c48018001c440010b41c040e07000400c07000700d03443d02c500c01c2d9110501401440800382100e0800300510001141550280400780c820388010743d0340e010b04504455040f4850714098028401003900380996401031000c03020001d04c424038109640e400603044400800d0240c2d07030169104800000c0c004103104865104a0a9000e0400c04681d00300041507030080c00c8452040c071840300195142c240c81d00e130070620641d40c0c01c1c00030005401c09050a0740e5074070007440124802d90040203522200340244240f080200006048445a1800d0485143e0b048540c60848607440d0747c1c54400746c05598480341c004d1500c000300000d00c02403151109089080218080c145c9050000d00103014900003042000c1700d4806919078000034a5106003501e42004e005d89520440e030100600c880d0800340f02c02c00c44441c088503110070703041140e42c3e406144416680012075640c1c40038003081c070606c40400d009801c1500c00d80c40003000c0c1c0b4401d02e011400680c654500019842c8031203000702d6a03210041 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 382865062 1250 382863812 382863821
    0x609040905031306110f0d02071a0f030903070b16090308031b040e1e01030803180f060a0f050f040803010302061c060b090f03011401050402070201110a031806080f180f010e030409 79
    0x3c0614087e082c2c00c0e07400e500c007a64030a943c0c411030b5400061400940071340c419001c2900c9180c000803e5056032401c1010203240e5940007090103a40c1400507001003044280e13100c10b6001d00c1041629030080251441e110080304d81c2004001e0040001c0507003000003449805001040a01161001c038207003410555a0303803907141410b82c24a0341e44895800144041006c5405507503000b041d401c00d00d6034071180c90340141d080080b14882c1140502c94403051100e82811034120a0402c0c0900c4010044c660b00c03002070f502c1c1c0700703030686002c0e0104204100510150034420020610804102020440d544800001c171007200ca155200c904c04001c0480d81100a1400103a284407036a011402841840e94003060885e00c081c040c0704080c4559400686c0d0011a406007010000030700400095034034001d103a003005409102c0207030b1402c2c0f1a1010324000b162040c000d0340b800b4060010382406180742e030f2740e02d2850071000080c1588028584200f5442c408144006d004a91507464040d01540d2101e141000020130b44 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 382866312 1250 382865062 382865083
    0x12040515161d010302091509120111090906030715020a02040c0206060307052101050a09020f030d0c081308160e1012020405060105091c03020615060904090503130611 73
    0x80881c014001805501c07244036490007000e2418668111690001078009109178102190004d00341c005040d8541c1161000e4004168141e500d00580c9500c6601c0900302e440303540d600411014113104001d80c0d82010403089500c00000780468a04c3d0380c036850190001e00c40c0420b14030042e80940c3d42c9030114203150180390468011400241032904041c0000b07901d0720a2409064016911210ba9110340d60388040003160202c0c0220080259090440c1c2450203000840410f074060360f502401c840c1c0074200020700c0d0507480310b00d0396043d030644555500d40105900962905042014540c0d010840c8a014080303012a01d00d490301d11b544042c54100785581c0d2030802040c480328810320300000c01000920b4607028502990440c3e001640d5035680300141c4190140d02240d980000c80032814039404980f90341018541030081d000c41e201a611001d840c8458884400d019421107801c0c084c0b98401e007401e410580b42a031040b02a01d0a0a000300c18002c01216a64002400035528029884850344c0c240480c0650 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 382867562 1250 382866312 382866331
    0x50c031606150306051f0e061302040914090f0303010501051215040204140f040b0a060302073909090309050d15020c0c33030907030f060903030b0a0509180312040515 73
    0x2042c41c05580206030000101340f22701600c900213a295800e4001d0741110050492400300304000401e074a000300071401c0484522101b40b144141da070b41000c100000b500c0c12240c0595600f8544500c403004003014940240c0040b00700303205103614100642c4e03140090f202529019090404d9042e5210402044d4280580740324011460545030860903180c0a0b02c03042501da081c1405640c031076880c58510914070072200e00c11140b00c100964844004211343c9501840701200242d9440d0340c2c2c545070180209c0d0090302d0000c003c6220a001000642410444080190700400d48038001c8805014040183c0e80000043c5a4035000440303854250b1818150140c2101040306031104805103401e41500781d02007000301c80402c12000300c001550610108860000782d5032084021103100c440386050f0b005080746142c00c03408a41054032007601802c045d10140304aa10040441d891600caa0f84000d0f2219100d160301e400074003040054035400b0015a840c2c074051440b9100420316500700e00300c462004000503000000 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 382868812 1250 382867562 382867621
    0x40614130201020705040b0303040f06020a150204060504090b040f050423070b090105070507030c080106030614071e0e090c09010215070509010e010c0506190507050c03160615030605 80
    0x360f68002022010703182c06840000ea0041c8040000b40703180101d500000c51603070900c00100b10310741d0102d04e56041c5885403c1c910168a603c00c50322007a40928042c280000340b05000070041d00c055a006980030030320240000500000e403030308007400e0f01c0c001c64050703c40413040444a8151000c204842101d0000140a0302c0160700308044260079210f0204998108040480c600c02071140070311585001750741c07250000700c840760780f40000d6010b031840d4441541e019203080d0880c900f0880b0001018803a41c2c07140c0d640403030303100d1320074001d40c07190000040c2c84200040701065007842d44410000e00c0c00780d40083c90040d15900f0760701c002450100100c8851560b288400240316421307400409440d2004c030242040740400540e41c0040301c6040c0e89401c082c00300e20030a8148025101c412582c00b4107100d001106010f80e5444100c1a2114819034a140d016540100032050072004155240380500e1321500000c12400c2c4070050003419010140c2094801c01e550320244000d010440340b00e1820381c0e040590181 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 382870062 1250 382868812 382868851
    0x2070807060e031b0301020f0a110d03091110020c04020d1a060405061606020f030c030403020c060426010906060f0e101203080601020a0212010c080a0912050c0c0405040614 76
    0x9856038861850130711840b411001e0740515079000c1d0143d031013290150701c3c0540c6130289010010304600381f9896007805801031888122030b80303200740680070030fa94200d000300342e03510034036801d0204d880042c1003500114090300d01b03682c0c010b40c1d0300c0c0010243c0c282c1c10100818000c0b0a269401d00703943c441116684075240403c020021a210070f03090f036050207200144c480310034410f030901401a11850403180020400081005900400400950700403800303a402c8074a00d15084040c031085100d01e00541141da0711400300704090110a06084482500850010640c504640d803901c050355041d0f04245052280044140280d008003220258041d00f100303940303023241d498852000300c00c01d031070b0348050100180100040c2e581c0e402082111405980580099095404900074a0003800744072641000036411001044508655000d851041500150340314284040d0400607502c42d404503088035943e00556096407242d40c0c42d445002c1c882d9000325070204646004412016102800500301e4030f5080380480481c = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 382871312 1250 382870062 382870069
    0x1081f0b0a09090606031a0d030206060409111f080906190203060d020d0b0601110604051c142107030e0606130b040e0d020105130f0f0804080d02070807060e 69
    0x404555084040503981c069a06040318844015000151558180000010401d515600280b07800308400d40310030380c019082e410400000000031025006a000790040340b0207103080d0340143e400f50310840500040011010200d000c19000007180c8001ca8a015032166120340c0041040c1c0d803083c0c1a47c09401280b42500c040c0304200d208100900500d0b9000c40000c500391510125000d41e241c008212034416150380c0f609905005040f9074031400038200828000700f000c0300080007405241c1c001c014040c034841e440a0110034510f411924007c0200d00540602a601244010301140c01d004005100346020040a24803c1001030024820549041c154082c2014040792480c3c114404803401c1c0c1c9075030301c2140c3c03050103800d4407041c5584c0315142a070b14035404900000c0313041c04030850b5002481513039503044585a4850340f00e000600b10411000000b00002c814a0b40c00b01e1582c4501803041c07c0603142c2c14041d2a00f002e0030b40c4000960f0050005001d094000c0118400904083c907000313130090b4609011 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 382872562 1250 382871312 382871371
    0x40b09040c0902130519091a0a05040b030312090a120504270e01151401111903120204060e03100618110f070503120a050f0105131413020108 62
    0x3100c1d40c4903408511080304c00c01402c03922000b0400100b008009070002085815415424810700d420580740a106040382d90300d15039095859074008156941040c5032400303102c05000c0b580d1106900d1700003002500070140c685607030140107200e070400611010303203e0f01d401c0211900e500802028800c06200400c81880ca01c0c2c5039070a1000c03081062500714004d5a144000b4041402c485c6156500301030f00f1006d010f03880407444c411200a080c10504e050015070041d10029003210400307140307801c411405410300202007040105d252003803070880c984144880d24502241c02c10313003002d400a0760340e8850101a140800c207002e01014071b06020004070303142480701d240c400c3e51a007600106989039032820544012250a03074a510b14001c0c00659100120300c1c1c41e644070f501242011040c0010700c004601d40901c140304180c80f5141c00000c400047c0d090200f0004141c0813020024042c0c0d86900c590368035110006205801026840320004041510388000342070880018500d100c9800b50750051a02e030504200c0 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 382873812 1250 382872562 382872569
    0x507080105240301140a0c03050f01080325150509011406060a0e0105090a0b0901080a0e0a0305030402061b010c020c1c02090402191806050d020a0e0c0702120c040b09040c 75
    0x540030b51003400200f400340c040248034100000d800010402e981d1426000380480015a981c2040715540340030542e075800c8400e02480034554800d08c94089212105030403a060900902c40c080650a0507940d0101c811344101b80c415025502c4000f4800c44580900851290801c0c01036407606500c2e00e10040b80b06030292001007c200034480c186085140d0003441220910303040901100c004036260724864034a42e012a444a000442d1200055030490302c40c0702d940304d00b01300e04001e420003e2040e00d04480a401c090b1050b079100000f00904100c5c0c207403d40742c944c6989095000401e51340b003850740c085d00705024100000e00984c8540404042ca0706841405c40f9072035030403503010030036440c1e600200e0303003e020121001c0d00c1c140f0f03040000300b50010109018914a07074046001e101582e1a20248221402c003002d0080d044065a0400c2c0b0001002c1495a54424a040d40391420020b43c0e8000a2807000603507150070340e5070041e04414104d8103207406001404035041e03510440724201540c44040600c40f40c407 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 382875062 1250 382873812 382873861
    0x305040305271825030f020c030a020c0319060b01050c030c2805070e070c0b01030b090c010f020d1103090d150b090f040f0606030b010b1308060c090f0d08070f0507080105 75
    0x4c1d02d6180300c0b402580705004110209200f1505e40701c190000759641c3d40314a549001600c11170704540c03401e10300000c80c03e1015014003d50f2420b4800d40e03844901130040300e0311190500034140f04203001303840700300f001e0504080e622004010008006c2c28500100d050b60341003d000d0300080c0000c001003080001e80c2000c4031600c4610041a58800074211108031251000400244000000109100103607503040d000b40e001c1c401f44c42d5035844140054a4035002044020056081903c080d03505600441070f03460103d100909980c5096886000074920b0f002c407034012965015001600c8a000140d03202d002c101c1c82040d41d0210090500c2e6220030000f81c03000b000102484000d0301010200441500110021607001050a03603039610f0300f41c40f00c02a00800f40004184c1031039078000442c4403001510500552060840900d040010002c3c0b1408100c0118000d07000628450b1100004041c07100a0280600954074510ba4030803a29002d0b0500c0c90700c0d844042c0781d82c18541031160050882c8007180c1c1011205 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 382876312 1250 382875062 382875121
    0x9030a09050111030403080f0304150c08060409020f040516140f0702090a020f0f030402030c010e0127031523011805090c030604060b0f01030908040603050403052718 73
    0x5100d41c0d1952051b41c000a03ea401e000c180c19501e046080040e5008a2080450401540f01d22603442d08480340720481c080010210008500d09003482d90100500c10300281c6100f0040c101080401c00f9503405844240d03d48585c101581c0f049039010501c413803000003001e22240303400300c030783d88005140c060071501a00c500c5441c0041960f065043c2d04488420780324485481e202c00707407030700c11103110340ac00c80d4203900900404d0080c2c00c2c00c2d0302c03d01c503050080005031a41541c1800d0300140c500b070b1038403048026910b0903120001001040000901c41c4014140c03d5001c0380e0241c0c19010030b403140b640e48550003100b800000050010000c5a1848202003407160000079441d554212014130380180d10903499014002c54003840107024441c3c0000282ea4002e95561805002c7c0b280110116103100e180903004d030300284424009184260003441d0064040d1402908010103004054009114810418403101e03504100b24490300b006154074140d801c2007500310105240000b580600c00012504040d07112082 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 382877562 1250 382876312 382876337
    0x1a0303030f130f05012003101a0c0f010b0f150f03060d0206030f01320613050915042a110f10050f22140a02060a02030d0509030a090501 60
    0xc00c00c42c4901e0350408003090701880d0604149000701800810050f4408400d024020320080c0760301200c0c09204203c01c480703581c40c40d00350100380100803010f2605d0104002c200780c010002c020080c0c03200a2085000000b81580340718204003440416060090007280b4071201101c0721a082ca040d2995038102c0e0718510340d40d41d110320000d000326003840da009500c144044207000c0e441a4001c3c04505940b00d02079494022940e156400103110311a80740d0f0b0b88900c110361002c1d80f0509003070380544464081c40d10f180b109a611600056000d140440d81001002c1c1c5160352803800d498940100300100f10001005980c03c1004582c5d508910816a031030010f10510340c003030100301c1c001000201d100c0202c0c4000d03140700d602031044a001800c0d0651340c1c00d814000400205011540003404410202560190440f2585565640680313039000002c5801240c0600c00700e802c0580ca9810060403036008030748c003450380c40709080602d00481e80050103d2486a01c10300c06a03000f2900140c1c2c071001d0319002d080400107241c4 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 382878812 1250 382877562 382877581
    0xf0f010c0f02210309090108070f031e0b19050604090308061c05010c0c060e010635030f07050d03060303080a150503011104030c0e22060f1e1a0303030f 67
    0x1203640004210f00e1140c01c0d110048040800a000000000c4810001030390b600c070006c0c0e5aa000f10300400c800041460780400015501d4190f00354035a0b095921001c54034001d80350414500d40032520f2401802000040f1140c8182d40d115003075010208072010005c114640e14000e1a40400800d4540a803d0b5825002b4440107540304542e40e856124000384104030181e20024410007051108895540c200304240104d51410b00903c8140c801a000c6d104034090017082c0c0c10564500141c500201c14943d2600401d590010300003403c040c072091034802d9959003541340144c80c20441e500d8603400c151a0100a10020f0341c4050502e03008850f403040450b09260300ca106030346003100c0c0d610290f8950320b07007000f44092030340000240046034001d000350b00005664041c0d03c00b2a000480c0c02c03551800350062001c035600d40010004074418092000044c01b1806116100101e4000020007800404081d542502100450044080440c0c200074202c680b80035100200e50349000c0900041441c84074840051140705 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 382880062 1250 382878812 382878829
    0xc050a02040f0b01180b03060d1b0b04031415010302090c0c01060e0703050c040e1306020702040207060e0d05090102030304120c0b100f0504050402100c02060d090b060f0f010c0f02 79
    0x1a0000c000304551482c04000000501d81c400320503001c1480048454510140b0400820842d018201c2075403445d500e010800c000600d035804101e41760a2014481c0e4102e1444000c0c90010309003e000c940c1d5a00d056080610b00c079107040130803803015800040040c50a4030007080950440b9410366184117280c031207540e2003400b8003e0707000304455036203082d50000d2441c2003a41802c0c011041d98400300459114004000d00500c52070180e10103039458400070401c0034425180e000885c45c01904014140183d0341d00042c1030364003040c07003610034646039442220b2840c018000800402414100386260840050021f522030000a001602281d0102120368805020351146002e003a800542d03280c26180050703007210750207614014042013a103943c80100310f0341810b120b501d00582c0c0080c0008000e90481104541000e05c2c07800c12a0041001c2c094800781d02600e004401d0780718402c07d03600e2414035004c0c0500c410900c08501d018410180f000719070780166001100000403d8100584c07089001d006c1c004248600c = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 382881312 1250 382880062 382880083
    0x20d0201030c211b030c02061602100c030b010201060b04080a02150702040e0307060605010201050118020307031d0a03030b0607020114030a090210090321021f11040602011b1704030c05 81
    0x12015125015003248940e4844c030700b180e090720340700001d04156240c120100e42d110450900035034080000314007150208040301a820b00c1c10f104075a4040d5418880310180c034055000940440d0b281c031920a144c0d83c0a00800016040120706242814030b461602990380f482e818001c1e00030044038600d0f0801003584001c5862103034014200f4807284030b2060038a0340d29400600c060342c55914008010995620600030241220070039502d540c1700b0f060140c01c1000035070010304200107150399900140c0b100c01883c160425111440e002810303a40b92141000350545514080c0144a0301d0200310510060707802c590390f00c01c08031a00c05055129078035601a08024428654040d6009400036030742c8a05940c4641c0c14001d0320b101d2081000d2070000c4142c3d8261a80c030a80c0d500c40943c00106048104001d8103010000c036401100b4045544a19599581801e41c465041500143d4690000703020441c01c03126681f0400300c407850280c4010310108401c0240c5140a8001030802c4404003040c81401030400c80c0c801030 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 382882562 1250 382881312 382881347
    0xa1704080403200a05060306010302071a0604060e01050d030c020118030609150b0112050a060b0301031b0f031e030c060e0c211c020f060a05060913020d0201030c 71
    0x160509040052040c0c206100803a10305101c50314805000d03e0710010000880d6015042d080139505000c100301c5103420003061039040507808d10107840842c282d51070880350721035180444035080c1031a4081c04107407080340d0040c4034030b5148030340100540d44034401000d00c03081d05858507180c80580d51004071000e0820703044c40c2d200c4a401c504080140841340d80f09001252049e175490109103c0074501d40b0a40c0e03e620744641c00301d4452001486101d4081e045103500003a503003000150a40c43c0c03050901180c10a0b042500d860510454102422401c41030020240c8008080441100c0c510350b00c0850000500449090030070300700c000e24041600440c0700e00ca00c1940940244442c420111800d90b4600008600c0384c81a0740703811180114005140001d040352407050003800d080440f01108014510401c2d1000e0f0840c17060558072800b410342482264029600300c0f03c08a80b034181103080003030f150b07405058a8418001c7c14008801603030b8a80c00f0303424555080c02c010450000c1d15100703540348840c2c543c1c002e92 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 382883812 1250 382882562 382882607
    0x609051003110c0d0f09050d0b0c0c07060503090c0405280b150a0e33040302120303070e030d0c031110060612110c060105090a020f0a032304080901050a 67
    0x40a107010416089110a41d80e0310072103003035041c0e0701b11003420b038611441d9004102d0308040c10204820704078855110f41c40c031040c00c0c6000c030b007403a98501d410300700c0e0301520000f000401840701100007803144025440080781c0a21160a00c11307503400c0c000b13050005441e410904d0700304079200b6050030340003241d98401c001e088000001518070b4034541603000d40002000161200182541850224111a141182c041c0200c11a846000000c50005507a22580424004c01e000000060383c0d208011010760408001035522801c2c07064015000b0486400c440344290010003907134103402d80c4189034070001038242c60300c040500060301d202c4d8102039060498100d810704100000c620942c0085488800d14540d40040102c0d003141d00644125000b507010000141d0004401000a85031103401c3c6900800c810100602e81700d4440c00510302ca600c90003210011940b68640c006c07140d135203120346001000380e2040110640c5042c1d0385441042c0708060f071a60502c2000b140e180d198074441c020452000541e0601c142 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 382885062 1250 382883812 382883827
    0x9110f0a0c1a0609091b0d0503130b0c1006080a0605070c1406092a0f03150405210a1e020307020306010806010f061106041e060c0903020102060709060905100311 71
    0x52a000304843c2c441c0255400d801081341c0e28000103004003075514080c80d03940f015088104005141e110124140c1c5c1622082c4075030103c0c05104625030f030085c01c4003080b240c1e030b07a980004040e0400c1a02c80c0c441400c24070b021010824040080b61102026602490000d035070b0707032480b000b88c904206012015000c00100c0802d600b40140009005001d4506401108e9420104100c3c003a9000041241c080da130003d21413808400c0c0c100500d0407480712a0080c16600c02c0c10f0070942c0e914040d01c00315406d41d11540300300c024811021481200059154650605600e041c130b000801034106a0346440d400d00c0c01c560260f01a001038424010313202442d600805840c0256541c0039101d6640c402801560340c00b4204d08030000d26103010b070a0b07801c03001c00d101000e0242c0e13940d2900e4401d40c034800c103640d0141c15980f480700301e80003c00a2140c0304440c01140c581d50210f0b41140002480c080d030003081c00081c40706a040503c0360b41d4102c1039000c11248105c50742d0f025422141c5c803c50140c15103020154890303001040380b5 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 382886312 1250 382885062 382885103
    0xa081504050601050d1113140c1801080f060f04020c010c031b0f0903031d120312060f0a0902030c071209180203041703070c14030405040609110f0a0c 66
    0x560055004004641850b44c80d0020071100b44811140140001000035040616060900d4030101c005020040000c0b00f100482c4203c1400358200c0d800c0b85025000244090780042804046905d90406e2902c0015880c1c002c0d5900c0200c1000b6003194441c00514030b1038542c035500c2d42c0444044070031100003031094103007100b0f002e80174150040c03002c98442c00c9104011401d5201c3d4590400c0138205a640601d05071440e02e0507601c0c3c8004000e45896035151441103d507544030512003840e003400c81c030300642d600d047c02c491030350151201034140c0384500e85603c40394500360f0f10b4086400079101c14000050fa20b4480712401c20441c410070710f005140d085241034049034030750807210f180c04442010301e0040c5118900390128003248402c1360010041d05800500d1864032020901943c2d1010036420820101245a15104d1840000e06c1030301d641580001024451070400380114001800820b130b003070006e1040c1c02d00d0300129000e01009284042c03404610003404901c1010903000003030300641c20050031404064117 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 382887562 1250 382886312 382886353
    0x30304140315040f020112321005130e15040609020a09020304080d0c021f0b0112090c1e0909030512091c050c0102040306020f030105040605010c05030a0e0a08 70
    0x1550300c28000c0850030002d541421101d2846141c0c450a11440d55486600540d0300600b208040461a951140b120b0f40c84030201194588502010180300c040030482400c404840c40c004051940c8a151603204100f1501c6801d86842c04000d4001c0200300384400102c46407034a510031001802924200f000e010900406900c00c00c03c4900a8800010391522a00303420113922043d1f6008055900c2004002c2059443d648055002c00c5584161541e040348908124238007410000217014950303944007010415038214480d00c1c2c62404400040c0000316894a41105001c10382c41130b800c21428198410300904902d0001c40090031002000300445806800c1c000c0903600030410b200c256846c1c6902260f1044c8001642d2140220060b921074003a84034040304580c0741d003202c02c10415641d02800088001015800a0462808869440c1d516585040c0404c02501c0e2142d2015060299946802000c01c10220440704041450305150f8032105008011031032a04059110581728003885080070300014074a40c3d03 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 382888812 1250 382887562 382887599
    0xb01230f0f1c0c08070c110d050616030b030c0d060b010e1206070e060f070201030908250c05040e030a030b010c0f081c0b06161406270607050706090c05030304 70
    0x500308480c412024013a1a01c40e420344030300020a00b811304001c0020400c0541851000000d0411803070344013955601841d08900351200980380d4900244044c1d20340d8544624108100124010601141c0c0700c8081107038000100805001107444400c1c0c0f4080340d0041c0521100c40c00080c00c10516540440001c030345800d401d81b00f00380003031903e000701c50f91894880207031510005200e109500e002c4407503005600400f0000c000304c3e4005418021481d0144c0c589159441141400c2141e544111031071804070070341d00c0b039500041c0c4920b1900e84081d00c071080c00401c0e40d00340354180c2000607408108000694043c004402c00502c11001d81d1104c80c204907881000e13201c2e8002044161344020b8240700100299441c018046401c0901405180c2541d06100d0341442101d000300d00c8003c500102d019a00e06001c800c5034559841c0701e6810075125010080c82c000461944213101510700340c20000002446407040701d1024021903221440c170700600000a02400c02000c006080f25611a61044000ca0003130f481c60 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 382890062 1250 382888812 382888867
    0x11508130f0c1401091412010f0203010f170607020c090903090306241f0315030506040303050105031e06010302060a170106020c0109060806131503080a02030d0b01230f0f 75
    0x781103080550040407044107030394801500c410484c41c12014459602d107d0365448040c0c0d92103c1d004035a6040510045019010001034084036900b01040046c480e501141c1000a070780c440420031209550200d003440a0240c120307884004c80e1105c5803105c0c99030144d04016640741c010780c4244011315850b550200159440c000700488113801880c00c018440303a203540c0c003000ca0448180b60a1229100764070030300e4011900c1c86000c4109443c5c2d100e01d40351840442e03085000c80d684034018046407a0030031441000208205040b8454a060b41c01e041c2c460b2010303c0002e00034030004c070b04401d941d806401c10110f240c03c5041442610f42e034654009580342e9441c50100e0109401d66004101e051203280e03040c0c8124401b5040019000649103500010150b054040800c496101808000600d40ca0f004014490b0244e0046850b2850004a00100c45d9103c201074140217450009103101072102e81c07203928003907283c81d803652a554981840c60326481842100f02c3d844400041403403014561402030b40442c00e114 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 382891312 1250 382890062 382890089
    0x20109051906050901140706051005090108030703232109280f0206210a0c08070309060608011d06010b0f031302010516030e040506010206011508130f0c 67
    0x114180244540003050008586001180501a06003d8801000c5140c0d042c94505100601402482c4c1e4036044042c08840399038440041c03000d10003490484001401040350751308481c0d494211800e55034419040014103000c2c403404010884c081c1c0041c00050300c072000314402c1c0d07284030070051000045c40301940d140e401c0e0841c0c0042003100d10005179540c1c1100d00c0340075084555800c52440000551200012a802900d55200000603150380c409081c0c88201c2010303400741403221b601280054940100002001c5240640e96019645c0c0540400d42256403410300091020860914030080c03d12034104545d82e6007421645640351005460440c42128107600380d44450340c80e10f001a06d01d104090b00069400c00500205101017089000c450b209032050424504c2d1402d9a1102e9441519540050300450009140b800e21800c0c54000c036030f408002480900300f070f5030401001290200c2d07450400810840076600156005405032074a114440d00300310040e0036030350940f030420300552107030141d040032900302c = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 382892562 1250 382891312 382891319
    0x105090111030702190503070501060605030f0c19080601030b0a231207151e090810051018060b072307032105090a03110301060803092103070b13020109 67
    0x90240d0303000310100d5001d0204552020301e1542c85c10910030301a11140420403002d40010002d1040301c00400c3d40b07440da40e4036480d1200d10710a000303400034103c92004d001044100851842e6920b42c6440c2017042c201841980c0f14000100e0040c03a000d113010380c0241180c1004142001c0508c1d50141040d050310351488030304014414824091004802c100580d03005940c24480d22003061840d40451920740f4140b0101884141b0298507619004440301c04501445028404407100303021a05004090050520040c00c06400d6814045640d1251a606040d5210f0425000307250745c001e50001c19440c041e454595a02d4100b02b2200381c2e110380e40012614071a40c0c045400c100101e030020480c1c0d0080d8203035040103a84020032032500d83c0307040c60008108041080403625665840702c04059801046071200001466044c1400c40f0101d400c01c00c1d595100f8400303141b1542d22204100205480c410466181d40c0706140704a1a40c003801d50001c020354010401c001040020103070020025000742d035040120381d039 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 382893812 1250 382892562 382892591
    0x510090509040204051306150311040c1e0504030f0506010f1a030f0a140709030203061509150402160809090109020c030703320316050a0207091e02070501050901 71
    0x4403031050350340000d526400640549019880070307a00468000c0000c03600000c40d90780324101e902c450242074520111040500c00e100315103aa1510409040d5010003800049000103130026001a0140850400301840741c1c1c002c520a5050703600039580400301082d604680c1c03034081c2d02c80c0340c2400750500400d0380d00d4000604654800b10010511010903005165403070389885290740440082026403903903114108060380e03082c0700d421207226803002c0d80c0f4928070900b075104060620901802e0340128001c4130141e8001a41d0380010540c000c1100386001c080d140c0100045400f90050a5400c081004500311000600c1714281c000c00c00302c8001c403070204842ea21050010224000c1d01d04e00c8499500078041030001a004040b0248a0340803040488500b40740350030400c00c80d00c400307e107080c131b0081c0c04814410100d1684026003494240307820050b041021410009559030898071801e000907840c1d042143c3ca81102140c0603081210b505e20543d61041d05050a601a18055810900c0d41d8a4065900400c86 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 382895062 1250 382893812 382893827
    0xd09150509010b13090c0b03040302151f0513150b07060c05031e090705040e0a0309120b0705210106030e0606030d08011a04080312060a24050f0717040510 68
    0x1c2c40182100c442900c8559031100030180c0100c11984071486c40c0b0b0114400e00e0140c003441c072442c40780c1e004094481204c0031b042c000200203030103009034280241c0b0010501c00204400001c0d0b4400760307800d10708060780c8843e0704054594918900803603050703201d01165488415005200d0140900414080070701140c10844052004490011a2940386d500c11001d100121a00c1c54002420404035138880c0d4a40d4002011102003101000c204d520000301c0c3c00405401c1104800203241d2005019070b44041c940303801143d100e00600407010000d0000702c0100d1014850020f1201165a41a0b40c65270344c0c444801400030520b130950b050280c494940014514500003038800c0c00c8441c655501c0005901c1c290b140603001e0009400941d11040500001c00d41d118204040c14040180300c1c42c20a66052039418420000e001d900a40031394a0502403031103540c1c0b00c039201541407182a2903c259540d07640c941010041c041c892004004d40d001d03000d81c480f89000c083c05481130b100215009261264500c40655550 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 382896312 1250 382895062 382895081
    0xe070206010b0a0909020a0531050306011805091504030e130c120c020102120c09150f19090b0c0105010924030b0a1404200603040f0f080d0915050901 66
    0x1404c400d0040c000f40ca4160082e00c410312803170900034200402d00300b407018801d0b51800d809000d60b802880b1410700c0301c0750070503800080900364003400d81541081c5618503042016205404406e03298000324a9840381000301004200c0e0b403107000703101c03405c0034a001002800820f95151041c00e001000c0d40c0d5662047c805e11600405640341c0070806105800300c8000383c0b00032100d07002955824010310f14441070340c580580c0b0800d070b00c0510581d9503a021081203c103e816a00316106060b09100d100b000c045200216503c035844042205140c034000c020844000355181c011050306040030450342d41c00141500700d58140e40c0068030910007030f100450100311010001c00c041c4450241614100007044030711083c07540001500c500850714582a0240e101c5119068908544c0503060351002c0c0b22a661800740c034014403104641142c558101500ca50948000d401409080f81090268075010000040304448007080c5581c020720048109040041081c1e003002c1c5c000c2245c0c2d0410001404500c018071442c0420b = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 382897562 1250 382896312 382896317
    0x806060408060f25091707030812060301090c14010e150702240301080a0507060311070803191e0b0d020109060f03060302031c0f0c020603010b0c0a0803010e070206010b0a 75
    0x5a441e42041c0200d03e41c080d01c503a1010030b05161000c04110300a5980081c68603079182e000c201c5203450764003003058983c4250018503811080c1c050001904903c1101d0a0060101f401382c06522004002801014000d000401c1c0a42304540010b40c140e11030040c004c800c0d403d072910074110100034244002030815030750214076110104031000061070712080c078203107142900301e401131398441580000c0040d60082c0c00c40540359004003010001c201041200d075015082d580f90503c01c600220703942000e1405181e100808444d40400019145801c03401201c0122031400020711103058001da0b40301458202e10305181651b42007940e01805410600c0c6403403002c90781a035503221010300e415030480d160041e8944060400d5110180040503a90401413582c1c00b98031402854041c20440f040605440005982941403110f04156100940d848000b43c03811501829420b60b80c0d0042042301c00d0511100f0302e00141228000310011a20390000c502c010300c034541e260200c80d080d9072038085041d0107001d460000c800 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 382898812 1250 382897562 382897573
    0x909050a0c11060c1606091b03140d0903030509030c19080c0f03030a081f090f0605100903030503150d0809030d0809060a11090d03020115050f0d0f030e06040906060806060408 77
    0x6400d00c601100720705ca034060040010303203204a54854450600c481106101508100401d00c1440700b00c1028003412400b21004010040c6540005401031009100c00f50501601086043e0251018010f001040c03030b000300039401e00d0010030620170204007a0f0248010b91300c1102250241802c1c4440100d04500c00100190b040100813031044442000040400c40075200201c1e00d40c4c014518001440c1c0500710a20011400884014400301118440c2d1f006620a189580380e81e00d079950002806825170b601454a56505e80d140700c0c0f4152001c1c9020641a0842c0d001070040061000e43d1020304015002102a6400e8058001084030200d805a03040e1405030000c41c08980002c03402d0b8400700021035150b08250030206008005480505c0428080d80580d441d0070f0b1041018030000030b808050502111104400203030344001c0303038095903800704c01442121214504000d060240c070890f035182c03000070031040c5e0b5980c803400120003030000c602c184004650110046100351500c00c043d201540c007254002e18 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 382900062 1250 382898812 382898827
    0x10062a020607020a05090906060f0904211e020309030f0a0b010b1305061b0d0809100e030c120406080105040219270603060e0a06030c05100909050a0c11060c 69
    0x200d541d102c081c089a114203000d0700003075151115000b8601c03440c0c03044060406032828030280841903200c00482442202c01c0410080043d14649502148c080441251807a1960259064912403c41400d0044820b0710800c069102e950000c010302c01180141e0036604c200984042883d903a0f142c0c0740c0014041ca6a1a0061003000122405001080000d00c1c41c160055036840125a180d404801454108007100d04000f403a41c00c1001007411000f01e51030011003606d000040282c482c504030240a44841d00c0707030600e0074149010025104590310700d109503440f4054031804425a5846842201d010481d2240001040c0c85c00388259000b80411440c140000b04815400300d444a01c03001c1d0210f10804196100091240380004180c003134080d540300007452600b04018a41c054400502143c0581d00303050382400091005c480c0b407030072244182e4040a00c03083c0f1201c145c80c0a1800e07008284004d1500c0e08001201107550840c0d480011036840307170340712180440da8694442d0780c00c45421400003410000304 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 382901312 1250 382900062 382900069
    0x1003060e1513031101020f070f080d021201140a06050a0c0c0f0909051002070c0630151202030c01030b010c0602033102030c01080a1517060f070804080307050f0310062a02 75
    0xa403840e80c481c04c49140b80a040410702401c376040061940f55100c45140148041c00c12a0003649141078111031103908546003040083c0f0f20b2141c00e000230708001c00100010100300410071420080c0036016922a00a600c400c221801030140440c00d41382c2384079070440c0c0d640701074007031007203491441e00128080745050510400b6a0040d051405032041c00d61071036a03400d40d081404400c0345000116500100d031020040481102d0005d90ba040005d50b200c00008110041c0d03400500182920404c1c01c0c0400e0a4015100590b15009021406084580000100002004c145029080305082e04c0700c1000346180c05d50607803500715030008000b901548074440800c00e0398003d00100d644040c4030030b03001c240d81540c01d10300c5620620a45c480480d1850318540b29083c10000d0006075402070311142e0140451404920050101b0400780c405440003070008089903046104c0c00c11112050304400c1096034a042a07004035040101038030503030740011080301c00500211406c1081440c402ea060281c102885941d4081 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 382902562 1250 382901312 382901333
    0x50601050907090b030a09050106050103060e0a0b0102030405030a031205070e180a15080f07060503060319021302071a090303090c0405060f030706020a0c0503061003060e1513031101020f07 83
    0x140b400c2c801c2c011800501552004001d51007a202c940011890f000d4078a051402e4070800e4101030305240c01d1013010b00c482d103055000c0d140c0c04082d0300350203d040c0e1038040050f405d520454109541502441d2045000e0540141341000b40c801414030822441c0d44100d0201c804c0e40781050142e83c094160403042c07001d00c003800045038211061070000901c032080c0080c035045d1010b107036000b03070556001400c24000f21141031225030010031807070030050310f140b510382c001039101c0c003c00314030007078401009021034155100c416200d9030000e1441c00440d40c802c2c403030030810ba82c0021404002c508090440000391080404000e8074002d40d8548010100c04a40e0300400016110042c111034110f149100700034215a01080a6002001c064018000d005514146000c0158243c1c000342d01940c0003000344012816069a031f803017140c0c1c1000d40080d500120161541c282400c00c500d20801c0449031083c0310140991100568510b0712a84a00c18203603000301c07440b801e074002c40c244080d42e02c0d828410200400c02c0b0580307 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 382903812 1250 382902562 382902571
    0x90203011d040203420105010203071b031a090d0f02100b010e03030a030c1404061403040f060c09081504050a0813180507110c0f040b1908030d05130506010509 70
    0x741c8155000c84406140e2202d175582c840e01d5410040c840f80f0000d11202c504810306440da04002c03194643c18040043e540384a40ca4008041c41a8010350080406a869614002d181d020601c0e441e800c80e42c56a101300b801e000c2c0c03170400282c011142c00c24296030281034401c041180c80c0d0081c0401191800f00400202600802c0074140000030304200d03243e640900040c0303a0405544c5000800300041e900003070584410140c440c00104040109104454010907150341000d16010030035038175074a13840c0c100007a420301000140001d0400d02c1e24540d440c0c010102c0000e0b030b0484411140e0f18a056180c5170315600064402505540000051801150748000140590301e1b185c4580406260390b55104200300b66011040d410983d610014000c00170ba02c603c20101e07034000c032002084001c4050303001414004092508911a684c0c80c0c41c3c610164840c03020340400c58800c1002d080070079980e81541034403503000b40800074046250100080324101039540342442c42d5001001856280c1c00c107401d00c01c4142d0b0260 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 382905062 1250 382903812 382903819
    0x90601080c0a1b061d0601060c170409020c060604051b090906011e08090d090b0901031a04060617060a06140f13080a200d2301091b090203011d0402 65
    0x26500744962581c02a0010228444d02002496511285002004803001400e0002c2c13600008010440d0503440100e100d00c2a41007608840c041001c590405128840da0f808040d88500100740710080b00404a000fa02c21001030304d091082e540d80c10118580d007030603000121b040f541d06015400d5581030521031250710860604000755180c20380628118040840780ba18400104681c04200c1c000e1010300034a000440c040c2851036a81c1d08010704101507014803500203042550310795417000c0444a500300003250610240040080c140c0760540206400b881c44c08882d4080414070200394542800711400003156802c0e61440d050946500401d001c913480451410f04200042c440d000840082c80d4113a00186291001000314058515000d550304071840c0d8407407100c00f035aa003080b070203803128004e6104250f40320f1642100c50030b001444949042007030b0072411403586044000700400c42c09110208800440a07030340c1a00f10b83d900030440507807009005801c420700e504c854070714840300c0540410b60841d2006 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 382906312 1250 382905062 382905077
    0xf030e1207090f150b03071409010f230d2007120c080c071202010210050720010e060a09020112020a1704061e05060111060615031b0a020a020f090601080c0a 69
    0x21031000010084c903070044914000000240031015401c540d0030200e00c02d0003104a070600d8030610019021030440c520140500c0000304201c490b98586403960301c1150404149a6142c1e24103101d800014042d003c00405c1001c01c07441c50710b40300ba00302c509403003000d540100b07085170076161150211801e0490301811100610140710074494a00240041c2000c8c019030789101c2c0c05019140002403528500c0c2d08100380d0945030005108905a00c451510341c103001640070005404d080b015845d0041580414100c1c3c40c0c0070311b40910091043c0c54000a2625000340d03110340603040400c16142c203d21680d80400080780c1e9001324460760000c22141c5561050040d400041c200c11048040142d5244c88420720035030b140d451003000200e68003e04c0701d0720280700030780052900380782c100302288254440c518a05184000400041d03140002c00c0852818140240040d41d214042c14170083e40e1a51104170403881514400900c41c05400d10801c0d04d841004141e441040d5a21a04820320311540840010810041032 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 382907562 1250 382906312 382906331
    0xd060e030403120201021309021303141219020f0d08131104091b1a070219080d02060106031109030624040207081309180b1e01030f030e1207090f 64
    0x1040f10aa10180701da80015030b513942c1c01d01014150306c0c001c1e041000c0c00782c41480321015850a00d0365180076030340e110380001c00c25180c20403061310382280b0b072042030944000042c0e0720072401810b0310014004002c41c1c08450f2480d450345542c2e43c03100d10f46e06103400000d1980000034140d48441901512090040015104400318407001c6010b0781da0180040c0d8017880c0b01214400404031202c0c0c0384005100c40352201c8049064440c505900303202e04140a4404c910303810940c81c40380303048003160000700071703401c219600e01c0c60151b0701a464450910030580440d152015081c1d0b40050710085070195200240580750641e107000604c1d202d0490581d181d440d2040001d00d6442d941c41c1c500c002c05a50b030203a61a240ca13040a443c10501c0c00d1615040103041e6820500c41101040070032003500c2815a1000080d00140d80301007031110301442918000f8404140000004103020080c200c000d0701e0b5001e559003040f21000501403004040441c407580c44c480e4440c1c5001c1100342c403070b50700c61180c2c15000b0f003010600140d03 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 382908812 1250 382907562 382907573
    0x30d050a2615030c0102160e0a0b12070303080a0501030b011e150929040512100f0b01030b040e030405010518090a14130f0605072003040501020c010c020d060e030403 73
    0x2011580c1d208001402c544401c2580380420810340c841d10244002c00740107101c0d140c03400050300140700d403054216880010600c809001d40000700c00000c042d01052580380c044658a59a0310244000d42c0070400384c034003140344000c03180115416a50885070055050b46851189041d032803102d4007100340366005e001d02103050140070300e48030304401055441010507420308225242004848400000d8042d24808581d01050740c101664211003040760f401044040410f107a0b81082070044050000f18500600e1041c06003050748002100706007070342c0030000a00f401050004844505280e5069580180810001584582c0040010700602404040880e10f2000840c1c1000e10662b81c00521548400c101d240d19940002550f50100c1c038488007401ca950301d6190b0a100c0c40a40380040c09203038a49000961b5a8001c2440c40f42a8150610310390503900544034941e203e411600543e40140158a4260455031143d1015000503030010f1002e8203010440d51544001d003035640c0c501465000034000007003c6203 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 382910062 1250 382908812 382908887
    0x402210a050d09050a0f060c02060f0c010f050c0327010b301605040c0e06070f0606080c1c0614070906030b010323040c050d0609020f030d050a 63
    0x144294002d001d00b40d00d00c040034090540640100e0b000b440742d404100411000c03d02c80c0411600c40b400c1204030206240041403851140700003003040c1d100e0005800903e07180550141a0107811030100300001c2e210f22060109a11090350036450200f800f4601d401c503c0d010f4500c410311002e40a000045d50703040038002c2140c3d5903404944403100b61900c01040745110178072444030701c140701c0440648503400702d2800300c1420845500400340156501c2d115444400d00521580150070b000401c0c85403075002629004c803207552080d8084800500304640000c01080004100440f028001c00200c11100c40400075448441c03070790425507500d07440c0c10b81a521520f40c100c0d094020a032039515034800606014024043d05c0e44115040e042524001590355008010030280101500707800d1000810348903070070a62289090342c0c100c43d41c40150320074400100725072503101641c40351080e10609002100541011748601c0f6020800d00400d90030011455a248140740a2030442c0e241c00c0039236100390307038030300f030424040d = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 382911312 1250 382910062 382910083
    0xc06050a0e070303090e070e092806120204060e07050901110309040204170d080403050a1d030304060509030601090506060712050c122d0415031b0e09010b030f040221 73
    0xa1340b440c5051014102e0383d201b09901030041d0410380b21a02e100404200f0600c00181747c007442c8414001c5a00081c0000f84011040d001c00201c01e016075510703908801800401c1000881c440c0349400000a030511b444002e040c4203800944406003405000001510700d2070004d103274850540400c001d0040d05a82c1c504c09080078040c0b00c0d170356400004c8034441182c6000188440401031102c51410480040c2e0300c40d0854140c610103103050b03c600c026a0420b03144c04c0b020b40ca40c540d40760101050100f0702075404405052080800c42c00c40300d450f680d0340710781c408a83c0f00b6a80075800080401c0207401080c02043c49240300e0030180b900078a003501003150340b41058212141d0044480c1c1c009000440301d00064070301e070b001e0f200a5110390801840c0c080e01d01154841c902c034842e8000480c003000300c17602d4040d9104458510310003c1010b6074161000004009000c0700c407007240b04e00000c00001c1404000442960b00c00c10000039503a00a45441e020007014403030a10402c04486181d0a012080d07440500c24401c84 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 382912562 1250 382911312 382911317
    0x18090c220c0834120e010c0203030a06270e100504030507150524030a020d0b01060f080705040614160f03020d0c0305120c04120506010608070e010c06050a0e070303 72
    0x220f08203c00c2c00c00c2a02d5011640d80c5404019046000000c00d43c0000341c19030b10080d08203064407540c0d104001000c0d0800745140c040c039510f403654901d54541c010000b1031080e00002c2c42000307119201d4480e240305d6000b00d9801600106000e42a200c09051507202c0162803c6000444030b5a00c40b104032041550022181100080c401003211020484c900e1020030300b40302812414045858109901d0f1900c100520304451a4002c800312200540c90500152000fa40c0103003d80c0b0001185090a40d40b1403020320440300005c84a00044071110300c1003220f503000301002c2e9100c91600d031401c0000ca58500744c0c5405612451010030440c20869000f21301100c299110380201c21800090b410040c0c01c140e0501104400d2099400c05940000d52240c11035185d05a441c241d03401070385900c02900308a01682d0420010740a074201604140040001c00a040b680280d940d145183e44e601b8003162070317034511130240340404c0301c01c03d041c000100160412540109100c2c1c0004100e41015190ba10304400c0d03074000c0c1c01 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 382913669 1107 382912562 382912577
    0x30e040e0a0f110d081b01050702030703050d02132309011d0a020c0d0503010807050d0b0412020109080d1a040615080717041118090c220c 61
    0x10f03064002900108a20300c030743ca045c00c4254828050b0841d0380c030210084051000341400350500c10304596015504081e0070366420340306034000301080d411054007409110041404091f820f0001c1060004420889034481240524902d2842035580180e001c480140311410003169a0802201c406081d04a550340e541c2541000b806854803444060281c005a90400760b03011000c0c40c1a81c1007802681c03080c40d0703120100482113401d15002030081070b02e8800240402c0303001d400c40101580ca030001255240e1a6510509a5882200300d503940703542d070f4909410760020081d00b501c9111070030313903007007000c60f00b040b200c4c6545d0550007850318200071281001810340303489821010700710b00c2c4c0c00c0c1e019601e6041c20300e403980e90310802051407401000110100603a514610b40406c1c01640721501038840d40c2c600c4402c7c0550202200076030441011302c880840d5140361070b441910170b48100b41e40c6020 = true := by decide +kernel

theorem cover : BRFrame.Cov 382733812 382913669 := by
  have h0 := BRFrame.cov_init 382733812
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 382733812 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 382733812 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 382733812 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 382733812 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 382733812 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 382733812 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 382733812 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 382733812 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 382733812 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 382733812 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 382733812 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 382733812 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 382733812 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 382733812 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 382733812 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 382733812 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 382733812 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 382733812 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 382733812 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 382733812 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 382733812 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 382733812 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 382733812 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 382733812 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 382733812 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 382733812 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 382733812 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 382733812 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 382733812 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 382733812 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 382733812 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 382733812 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 382733812 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 382733812 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 382733812 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 382733812 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 382733812 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 382733812 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 382733812 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 382733812 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 382733812 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 382733812 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 382733812 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 382733812 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 382733812 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 382733812 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 382733812 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 382733812 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 382733812 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 382733812 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 382733812 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 382733812 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 382733812 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 382733812 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 382733812 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 382733812 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 382733812 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 382733812 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 382733812 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 382733812 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 382733812 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 382733812 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 382733812 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 382733812 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 382733812 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 382733812 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 382733812 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 382733812 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 382733812 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 382733812 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 382733812 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 382733812 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 382733812 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 382733812 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 382733812 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 382733812 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 382733812 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 382733812 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 382733812 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 382733812 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 382733812 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 382733812 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 382733812 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 382733812 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 382733812 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 382733812 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 382733812 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 382733812 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 382733812 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 382733812 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 382733812 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 382733812 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 382733812 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 382733812 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 382733812 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 382733812 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 382733812 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 382733812 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 382733812 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 382733812 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 382733812 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 382733812 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 382733812 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 382733812 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 382733812 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 382733812 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 382733812 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 382733812 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 382733812 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 382733812 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 382733812 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 382733812 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 382733812 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 382733812 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 382733812 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 382733812 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 382733812 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 382733812 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 382733812 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 382733812 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 382733812 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 382733812 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 382733812 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 382733812 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 382733812 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 382733812 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 382733812 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 382733812 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 382733812 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 382733812 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 382733812 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 382733812 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 382733812 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 382733812 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 382733812 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 382733812 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 382733812 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 382733812 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 382733812 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 382733812 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 382733812 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 382733812 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 382733812 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 382733812 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 382733812 ≤ n) (h2 : n < 382913669) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
