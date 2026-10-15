-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_5237
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T15:12:07.778227+00:00
-- url     : https://prove2.me/submissions/749b6aff-b9a2-44f2-a2b2-63c34e40325c

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 941726618 ≤ n < 941906474 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 941727868 1250 941726618 941726623
    0x1908010b090f0a0515121e060c0f0d06170d020106050108010e060616060c0914060f03011e0b0f0315150306130207121106011e03030509030a0204151e0b1b 68
    0xe030344002c5c58840030103031522101380c6820400c070101f03841400d851502c0e07400c40c10000d4041e00541c0e20801c0c1d680340031348121650305c064000880c0c039141075454440001d0000702c281d091031491408000505500d0040c200042c2c21035070160301c80c6040c03000c001c00422460030049602503004006540079507540d01c2400916210341c08528008285038942205038003031039484218081502c61910103880e480745410104001c0740a42900c41c100b1007000c10040c01354150f2240d42404a04416007144e050940329400d01c00d20f07800c09490340c400b4050200c10080309500100d01d440704410155844610700c0c810983d40307809480028403071405030262595446504003641d040f2170601b508010a00340364206c540c402803078003508510407280307441400004958240c42803440c8800c81011100c040c01c0d1440e560b400d0b9155000780e00582e60501030030b15100096212400f03920070084444131103c12140c1071404500c0c0e181e003003400305e000e0b9002031b81080c00b16801080803180443c0716900300c0001c1c0c07001003a5007031 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 941729118 1250 941727868 941727901
    0x15070f09032022110903330c12010b120103121107120308070825030914160b0a050319110406111b01050712020c1908010b090f0a05 58
    0xf90010300d012051440140d6040c84a0a443ca60040501145a030b5407013140700340c06804d902c40d038950003510303000038001c4c0761424900440c0c0c41507907d00300090f5140c0d200031206030100c600c1250140006180e10b088501403813200c0c09850311354245820103203641603c006e00501400000c0046040011460704503000328001d031842e0440b5000c8030300007034403028100c02c101d6100d03070114082007c40d40410101d6000d64040c03807080071050000c0762145100007910b4408164800c0c3e40d018560707500041c0300443d80b002c49000e04001c0f60802421800e806e50340d80310101c01150300180515a09100328402142e000c0210b039002161301515615402c1c8032680300c0002c26a0403036010881e071002030700240254005070210030351a1440b090760340c4040e032100e0052494000b03c3d00640010f80c01c0040c2c1000820664110030100d44610448000c0300c0c02ca03000c00d401d0903405119449140f104803041100100074001c142d2500000d803054002c6044c40300506890b4030015180d04070240d115400103200803031412800 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 941730368 1250 941729118 941729183
    0xc040e0312060411030403030b01050702130e07090e1902040f02040e0f090d080109090309150c1b050901060f0e040203070c0506060307030b190603021215070f0903 72
    0x2008020100120155203610141403404002030010005a440ca001e01c60000c80180c003007034040c40c40d565954110000c0c0700100c07000c1d044c070006024030009a1649040d8800501000364002000811054040e1826096600001c046420700701d41d00300201c00810992600a480500c9503820356140c40044c0141143c210040c0d0482e00c08240040d02101d240da03a0383c001d00c89035141011544502c840503403a003005080031804280c5c010010021100150701074003140d8040d03d490010907445a44241543d0108001d40f00024544603101040c040141c81c031100748005080c59044031480c1c50701140c1e8040c0c0502c2410180514039405030349141c015200e44c08034220003881150307a031510307020181400d03403401c1d0306031094402c400011741a03080000e0890152600018202c8840ea52070b0b90380e07040c0011285d02440281d40b0ba4030000b0050311001c03594410703543d100c00a4030721404c5100009604a0700142140c0400240c40c00075409190403d6940d000c0c0d0390040c080e0140c1220880d9151882011100c80 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 941731618 1250 941730368 941730371
    0x302030918060120070303052a06071206051f090902040807140d050a02041e0e01050a141501080a020922050604110d0209030a0503030a0203010503070f06020604030e030c04 76
    0x5501080702422098418403098a814414500122111500100c101e00b042d050354000711051001c00e0003580a0b09520740101c81c0c0e0342980541080004032031945104e00410307135100c1014400410b8001c40c0e0700000b00010300d001c10a0500e0f0400207041c3d40203214542d0130b455912103c048a0301d00c10358a4002501c0d11102c00d40d43c49503100d07411aa1001c42d481428413001340021414200d15003009180780d407941080040c4181105902000002c1072001d00b10705404040d8901d60008100d240112103140590200024140c60842289400d4881502c15440400600c03410007504241200e540e0141610a00c4d0040440da01c0035a41c3c3d00901c02d80b2200750b4400c03005401e00031250b050301196032030042044804d20240e03d40740d0500083c2c810701c2c200c40e28000800e020b080b02c58040d40c0d0280c1a811002402c0340d401e12010307107c250855001b41c80e030b11640c90700000148520305080140e800102403282d031402e041464014001d40703540e0060b10040c204440c050b40ba542c0d80d03034200f16180e0311a800030310 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 941732868 1250 941731618 941731639
    0x50a06020714031801080a02040803030a0b0303220e0117030706050705091503060328030c1106070821010b0a03150806090109060e010203090a1e0f0b0f06030c1c03020309 75
    0x40054803501c4e1200160700080410000440f181560f00943d4202d0303424100460441d107a803074135403024200418005405200a210b11000c54101c4901c15030780b18102201c1c02c03660343c200f07003032008488816040418894bc00140100410500108450301c607608114005201e44071860101c6042c440c100010360310000e8030002c09405d0305520000c6020724012400c40c0e484140c0200568411000903140100203414004100d0219010f0000080200e104003541500c15200c07000003421038000040a8401d4440403d440c1c1000e155512201c2a024001c0c0d0110420f6140401d01592441580600d40c01c1589681d40340346840180d0240354050308043e022355056203002ca56503802061891020b5502078180b403020482c0142c107100b200d02442038640a05940003441d100c441c02c0400b0808101c000700d64140d006004910282c101c45512846140300303108506151401c0c16440001902840c0310344c0007624894115901e540e803810f8a0b0692100030f0056004a05050707095016078403009400c503204c0380 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 941734118 1250 941732868 941732887
    0x307060c0f02010b032e0501300b0117160905091605060a0f090b03040812070509090103060f02040302151e0a05030118020c01090b0a0b040207050a0602071403 70
    0x2086140c800c015951100004802003008a00740c0c2c4541180c560180c008a455003c20201e52001c600c441488401140c040021403084e030088031800d9020300c070b0b200140c90342406084001704040c5000c0116604105c409501520740002d00141881030309240110f914607040403000c1030000f00490f61350f0b100468015a51a0f031000080d000032201d050090003005c0c070107051403802502d4581900d2000d00310034200b02d8245410f8520801d0b240360b440c18401700c0680006c0003000c22000310310032846403060503200d0040b14809944024050301d0101031000902c6540f078161a500a12811240c00c4400421426881c00c00c032002032185400180d0062810041d280603804508001e00070708804000e11420310314000490700c1540184a10900040d2042004000742c0400107803040c01c05400310f01c01403500c1000446582180d0007640e0844401343c501081120004151060405012042d03c5c194a420740a68a03142c07601c0038110700400c5c80b0341c0810380b0401c0c85481604481700c0342c8000308490b07684d1401c5 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 941735368 1250 941734118 941734121
    0x209040c0306060f14040b01030e07080a0c0608090c0f060f04170c0405010e040b04020a1d0712060f0605070f0c03082503050703030e160b040501020c180118020c030706 74
    0x1404251441414640002005003407071303645a04039506032469181e04440340003040013503c4a000705604054071036002100b400d80a1040344004c040d0740c8010b22010074645065030002c030180e4851810300c40e9507000c1000c8101c01003442100d410007116003c0300c10b03021000160315802880c08510700c440d0003023004180d1010101c0810000550301085071900070f151010042611001d00402c5240d0f6607100c00b040026110f212816005803009008100d8140c807420643d0303060010341c08038640d034200e00051004107604a01d0b80c0c00c0036590400e00b44450750070100540302e001070302d100d00c2c82080300001e0403a061040311101103c100703902000103d801688c0e4100219103800501c2c0f00f000200000f00081280c10340400451080c95140c0c842c0340c100000358500394018181c00000401d140106201c50364103903a10b100480c05402e002c4c10141c2ca440c07d21000926001503003034194011030b0102100082400c031503252a045403069000c482030410920001c6000e4003c1210380c0d4803500c4003088007001c00485 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 941736618 1250 941735368 941735393
    0xe2701060f08010b090403170c040308070f0201111506060a12150305060703230c09042a05040b0712050d0f020d0b091006030b010212041203021e061909020904 70
    0x40207201980d4500200f05e50040184ca004000c0ba005100781003164071600d1021b43d02101c20551681000d41da500c418055600502046805205c46030800303007150303007004089c0d0070780384401e0003404407070210100c2c00e0002c400a03018501c19407010030301100440c03080f0024501000090b005000b11a40140500001a0b10380421101c90080100003420342d0b10a11407003000002040b0042c00714260400f45041043c0090544a0300360b40c10400313603410741c569005644082c8580320154081c241c6003c2c2c0c002904540105210400c0410002040070540e604140d684982e0071450b070a0021400c0300d0140d501c1d11440e05569142070408a040e440d1001d80d84c05001905036104091200042450402c00c0c100d000325030802d2030390545031007840020320990141c0500c0b94180100d65058103100f02048164105a00880c69000703841c119604265041c0f10441001149000f00d1302c407804000c40701608c80d48002d00b0b0480c078640440e0224855031081d040710103015009001d5580a040a0401e000b91841 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 941737868 1250 941736618 941736629
    0x1091a04140f011707060e2d1e01050706020a03061703071101050304020d200604080313060f02030301030f020d081c0b06161506030203120d0c0503010e2701060f 71
    0x4600c000052621340225030852065800c4014092580c1081419107000880080a0b13800031020030031041c520305040c5510b204507441c480e6440c0b403c2d440d84100001c050308043c0c00c02c3c400360a4001003005982240946411681c045005030311806000400c400400c5036070b215030040103440d1456015140044020808140900c1000b104200d130072006444500c03040e10001d4000e42034102804c08120340019145959412803000b00c2c41041c0340000580d160003540010040703800008240f450352240e40c0d40c0100030842030408c402c41342c580da1030183d02c03400140300207070103120a0b0b0a80000c540e2018102c0c1e882d04c0c0d1003a03500c0d0301e5002142c0038003404101d90907070000440c503044440c0d0562606800307488180c001e02c591000b0224155868071501030305182e04882c00780e120100840140d034144101114102e1101203a034844901603050320548104043c40b070180724081005103c0300c00c18081495000241c00c00c0039045200c0000c07904091120b95018900b80d5283c0000410b00301c4182030b00200300c55 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 941739118 1250 941737868 941737891
    0xc031207080115050706051801020d0204090b030a11240a030203010503010c020f060a0c020309030d08071704020d080f091002011d3412060b09090309010801091a0414 73
    0x70389880d010940f100e0300410a002190342070014000242c200c0c4c20003a8040300415030703428280121000c0fa42660003142d120305542c0d40109040c0009141c41c0f00c0c000582c0c008500518000360151070f014988110802218011210100a0341c203201e4201114948907000c00c0c0002c2d0384160495000f002034100380110751003542060001c003120391001400ca410a103066020304000d4a8040d03191004041c40c0e0000020360000f4844041c490b5024000c02000d4002070301c2c4c2c2195450800310052a9003441d008881888074030805010258441506c0350707194660096a0350355441d07000c00302902601a0590b5594071103884910f620005074190401d111904540c445072003c0000610200c1e110405082602b0b00700450381c00036038030b07080980103000c00180310003a8886029121a95130320704800c0c068094910030b40361085400d00307041c02e00c012903005c281c80340a1070070001d8000c0002e00c60301040c0324150b500d035150146100038503640c40c0410a40d0000400801c49003911b842d40000c2d4690480e50f042010 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 941740368 1250 941739118 941739121
    0x13053c0a27050d11071d090c060703120b0109031b26030306150f130602061302060703080403030204180614041b0f090b0f0c0c0402041d0a020c03120708 67
    0xc60301107a0003041ca41c2c010042c18059680200856020910314441900791282c5007001541c0000030020840c00660b042c030002c40c07071034090007852a022402d83e1241c0504401c10205000c664003603074080a604401d500420300c029030000480e500c00075604082c04403800002521510342158074050126042900c0b4080c8030701a524035411058507613070700040d1b16081000016421b203445510390100d1440d4160050a0141607805492540c115400c0425040039140060203030710b40400805a21002620f20506101880d40c04246503010700d0700000c1c103201d00440403404060194064134060800002044461410144403074060101e9209500701c200c0c40110841090405004090340703004060446401c400c59608129448110028880200081c0080120f06c0000b8000240402c10300c11160607200c0166140309424840442116031007540704004c01c005110300400100302c043d5400d042340d9000c1d620184c1080280c4070781c1a01440d075000002d5403040b500c40d4100c640380906030a50b03602c0c0c002d = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 941741618 1250 941740368 941740421
    0x150c0d0c080114090421081005030307030f030b150a170f0103020f010f0c05161d042f0904080406080901060302180406140c0913053c0a 60
    0x7800c007802080c5001c0000e03c909112030400000c4290024425602d115a0360a481c82600340a10364504480000380240300f03201d2031180002605010b008220041e5251001c1036401410108051031103a05240d1030301c0070004c4c16964030144201070a08038002c55a90900100024040100f001418482d020685e011460301184200600c0c140c1750301801060a004143c0015108040306100200420a94102080c0083c2003800710136644072005080c0c1c4d95003130a00105a0107403001c036509240c291170500401020840912540030741c01d1a06800e07010086003414211040e0050305005600b010205e03040c8810000032400410171200140d076094141d40300c83e1b401074244c0d040c5120180d4061070301004403940409000300140c00503c100360009041041e0b261001411408407103000301d000c0d0105071031000d82044110342d980060401c404102078036010314640c0007016015840a2000242503c841003c000001c1101d0001410302c20346400d8900340a2030f5018010b440c4c2c01c000041c0c4060320304006d = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 941742868 1250 941741618 941741627
    0x160602010606031d19082b05010504020c070303180306090803072319120905010605030d0e03120306151c0f02070f0b0901060504021602040c0f02100e150c0d0c 70
    0x1600610380c006000e40c0c2001c448449010030400d5006e0310950010480704e03010a0f4988280560038a905100c2c2c0c41c1d0340d0054005104644051784a940182c3c010415075040b084003060b54800d980e0316080000889502d075440d0300c20b40340d035500003c010324944801b24080c411600c002e10f01c102c81e2944c0d00c443c20048102801c1160183c0c41407011a05410f114014020600d01e20b05060f03158980f415184042149140c9402d5985041c820b40d80f0765583c10003404103090911103148004058180031020280d000c0119035109902e403442c4051000200219a4540d80d0450200490380c41e448042d89034040d4219140303844200c886d0351401d01c1d2404000d4583c2c07407098001d4648440d00b00783d40982400d229211182c01d0180244048501c0d5a280d0b00490980d0b1540b0181800142c000750784241c80c0b03824814403084519128100044c4a4004002a20b65a0000314001c1084260402003600094429074a107464904038030000e82040c803a04011000240d10098070501010f00c03002d0102030300d101001d44 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 941744118 1250 941742868 941742911
    0x2090907151206051c081c09060902030c010504140411160506072c010c050f0102040b070309090218010507050a0506070f02061b1909120c08210306040e16060201060603 74
    0x83d88003420348402008240b40801070f113503147c03005910f0100403104030044800c640c0b1401d01114803a035a10808419820100a4114100400e0804510f001d0038001c881c40360403403036235069100320384807641c0045d202c003034406030f803c2901d117080000840010740c9861500c450040310f1070341c00124081c200d070101e0090040134500080e070402e8140c0764084120b00442c0c24130320400054030244100011000180802d01c000c01c0100f46154100c0d49601c0e2500d802011901213074000c0700c1c0240140300183d00d00390031f1041d2141d25142400d009945010500e4128208403078190090207a01400c41000130103a008041e10b0b2214405609458481c0e8070200034440341c0c414403400b602c02d42c2d003d00c06e1404410f074101c3d022008207070300e045c0f941515598130419420401012021030324500303031010401c041e0804118071182160b21000003840124442c0c007095480c000103001c6441191034a009050111084c001f194030300d0700c0c4a40720b821454031100040d020b44107600c13440000901c0c1c240a810101101c520a5 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 941745368 1250 941744118 941744149
    0x1b0102190c1505130203070602030901120b0306013305041a0703080606130b0f0a02070e0c03060103020706060302060a171006020c0d06110a030b24070209090715120605 74
    0x14101401d5030b440b0640200401800340135501440c107000030159404108210091815500440d0f4070348070500014000300710051807103803540c203100c83c2e8115540c0103d00d16054403491654000503002c00c0000820a100681e1501ea103c0c000d41d4084100a1740100284262107444951032031070862141c580c50300744a41c10024000500d079402050441c40c0c24401000c03610151620051020344a100d40501d5501c21004c0341e8101c0c0002840b01c0351250103000f5180246000b40b000d940501e0160740000451100601150416900107400d80030000954024009143c025003059158030f9040806000034013400e401c40c50003450030b4001424036080d00702c83c0f010380d0034036405019450380003814000121510b07001100c42c1a00c4204460740141c000000e031a01403e01e54000c0741841c802c4007030025906c00311043e0100d503010400401100c00b0100112241c0039410381301d00102e030b82c0301c0502d141000e1041d0445500c0c204000c04d0003030120b40c041d880c1441072049080c10002207949104005408a8403040e4 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 941746618 1250 941745368 941745383
    0x70b0918040311030a090e0c0c06130203011107030c061a010c080d090b040b0414030f090d030e040203150a05030a0218070c0c0b0714010606050f09061b0102190c 71
    0x110034501056100940142c82401c04400fa2001002041c2c2503402ca60210000100003503402c11400d81c0e0b804e202604541d402a543c0e02d060051020780b512003000404000c0b03000c81d81002e40302191804d60107001c10711642500e82c2d403200640d00c0c0040c15100386040036501c40d401d06000c00700d00080703401400c1108a05031684445030002e40d5403140e4640118181c03041c941c1da90841000414417070710480b40704900c50f61b100c800615091070400c01c084c4040d08005000d52041c892601102c002c00d04958201c041100c1001e080c04183c80c040311810300c049425038200e8004001e1200c2c103602c031940480d0368001122644505600c5e4010301d50b4610100c08080d41c400f100c500440727185d19000c866640c0080b4141f404088001c0705813241410081258401d070640640080c11030f083c4415074050070940f01e103200080c018580703000c00c020018010080c00303007462070300011402155a503c1702101d05130390091036140c111a0212820714000d4204c2e11000d04c03000b04003804952454030800021000a602412 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 941747868 1250 941746618 941746639
    0x1020f011a010e010c060c03050f100302090f04210e0a0801110d09143c0616050c0a1203150608010306020a120f1505120615150a050705070b09 63
    0x4449030080d903d40c00d03040c032030306900e01008100140a4004200326640380440d1504065203184402c40c0c00400c1c10041aa80c1c1c101400180d48544800390840303a2003215400c00d8035141420f60180507502d100c0c03103800c0c0c4480720400b5807035007128044102c40d07030803100f00da5880d0380c83c01040d09807000b5110782143e04c46d04214848510885601c1381d03008901a44400d0f000e0072241e1401443c1c0140c04140000e01d452400f07410b951400c00401030103192a54842c140190300a0b80120746e49c40e000600504607865000c0384043c20300d44034509543e200072103541140c94035001810114102c22400e0100c0c0d001a08144800070550109051801103400541d5070b0040d90b0300e1070302e5440003500060700c2c240401100b441440c8103a4454060389003c3c09454800055a07a0b8240d101c0040704020790050340650288805504584004500141d0180c04958010704044030070000030307204c0380c202c001348480f007501140f101c40d501d5010028001c0c2e18810412508100e40780c03004401e607801000135441d4401002e21 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 941749118 1250 941747868 941747921
    0xc030a091406041d1308070503030103260d0c02031e030f07030509030703120b0406060503060a080d0507020f030a0b010b0a023007030306090203010b070b13020303041a13031101020f01 81
    0x241259801082644901072200e01986d6201440d0300110f0203030780e10360000c001030061103c943c0318000840c80c5945c50343c103001480100a401801520301039000d15549503003145440307000b132088416810700030812104205c0807001d903201503082510100d85205014000500441c000c2c41100d0142c00d42d800207500f0710406690840d00009095102c10200b6243d441810150711540241400b400c9180c0b10f180e02d03454041d084c070010022a50080406600501c00c1104107038010080701d4006030140da940c40105210008645041c0c860003004001501c09400010801c0f008805001004900e5003602c01c4029510700c4100f1480080c02000c4d1800c407084e4030050035900000052004a120303040c04203219996030784810480c1c1090b400b1500702ca00014400040156210000e0b51001e1003011b1061810003d0f00070a981e405680561205c141400c0d800d0700e1016101800c0e45c0da40e000c0000e610b4000b94403880c0c5600300001003070300b0300d01610902100c00d030050b45c103000d82c1e80600e500c201a41041c00c01d51 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 941750368 1250 941749118 941749169
    0x10e0c0901081c300c230d060e0106021f0b010203160501181103010b151605070911090103050f240604121b060c0f020d080c030a09140604 61
    0x1c90908060110803c08210748204000a102408442048040030a80d00a14036000e80f401440d4400410045295024400c0701181424003064140389805440d601c007010760034000c02310740e00300d00c03040003c100c0009030a942c00507104800d0a080d40e000f019100b0903007840d2041e076150042043c0981c200340300c00e1043c03c41070f0340c500e00c195000d40700206d000700c1d4480307201488980e402d02c241c41040207514800461705003401100c1c00d12034203803600301c01780303244d50081d6415004d80381d410003600301c480c0c950109200080000c3c8002e4070f012001040350405005038029140c1c0982c0a25003c241014001600c0110580e0141e20550a6403e0803424684d10080d0f12031400d01c404400e40d000d0400c2c0000721f2054500f0300c4203041948100002070310a40d1100014410524591102d02000594203215001850140d020a11b01c1d030b0544085905d52103515102407a4044d0300c1e9000b41030f11021a8000a240e405900c807412180318640942200382d00c80d0030b00c41c6a203d58061800c8e400401c0c0d01003803180054 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 941751618 1250 941750368 941750413
    0x1407080a020a0905041e0c0504140f0427150b1309031b03090807090504080f131703210601020a0308100e0c0d0506030307031209020f040e010e0c090108 67
    0x6918040c82a2600c91000030304907890b480541d540b1151007081d0b20010f000310b207e211000156800d00a08040c81c1c440303500c0c45d4940004210f4003c079400402d0722215103d80d04000140c141ca01c240d91000844800301c044d06031640b207026503103c054001011101a0300340310301e01d81a2000340605001400c50410100600850003080302040492500206c42440020090b000c80303209543d03081e4440c2c0b400404a04c0c244054000c29841d07880d002c14840040c0381e01707003141c903444078184415485501307440c2c01907008160b83e0300c840902500d0b4a000e0072199004001000c1b00c0b02d074031420028192154031350614a000c22034a0345d015922a40c42e0101290154601c103074080c4000c0312081d2029100c1c0c0c5c00545c1c01c40103403200401144042045002c051146c040c640d44054184c0040d0b08000c83c030780303000340f0b00360781409040b03c002d41c0d80c005082551110840305038043c0024105102e0085c2e0300901e14000c00b004109400300780140d003089a80742c509800214100d408050040850300814481004507440 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 941752868 1250 941751618 941751637
    0x50411060409020d1a090420100f0f02061902070206040315090201020f160b0903030d06061206051203190516050105040b09150720100f1407080a02 65
    0x40050545985589000003003001e00850000035844809080e1a41e0940300840010382410042c10341184003a260b607100c540c0e01a411500001000c62151034402a004400522a41141c403107400e0b00051900140072001005031561402ca0001c44a0b004980321502a1385698584c3c4c1d460003030700d40d40c292980203051a5800108064906517580d0b0310110602c0b8034180e4800d1050315991a07038199a014030004e40444d90480151103e040d506500d98515078140c018060345d01c0c3c011409400580f01002507640c0014040b50801410f80c80c1c0340090500c0c202d0740801c01c049400d10070042180d091508580011441c4070380158240300d1240c42c502c1403000040e17a410304220f0306100d03104510f203c44084045290241000166509083c00c004007102c0c00281030b103502e82e00c008890b640200038051180d52100e060718045e1009040703400016800c2d90442460388451044100758514800c0c82d034008880007076902d008003c46d0404683c25282400c0855820f804100410000f56866916400a19250b0b6 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 941754118 1250 941752868 941752883
    0x20906040801060f0e07110307030305131a010305010510050f091513090c05010314070c08090a060810080d050d0f020d050c0702030c062703011b0210060e190504 71
    0x29110100305084803076642c0140c10780140d050041040310100700b015500300060b1f2800c450b480340b85000180c3e0300c3c07040200080c20180d4810006207003203078110b000700b80b896010090101418422a0103207168900380016941c0707510700804107400f40071001d00075084400c0900341151000941c420001507000051400d007203241420038542c05652400c81303030906070724a06070000f40f03c8420b0400d2441507030b90340c0180c0c0c1490303d8110000c4810303400c0301c01d8a611840170314082004294900e450091360062441c03040e08003507103400101c3e030584c01240303103846558010800004142e0b1038003142e035200346001c1c4000c0420420481c4020ba50313003d4101c4e0252421074007025103003a40b083c03518021690f00301c424005c0030102003090011071030140070745041f81c0800c9614a0918060001c05c3c180c89101450504004a04d400d00e47e100340c6081d000324a007035500030600140e104408001948070060340d01407459551410401144103241e20180300d0040780b01d6200004512054981c03003004040c050f2050320050b = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 941755368 1250 941754118 941754127
    0xf16031e120f06121401051f0b0c01141503122a0c060f21100510110709061d070f03090809042d0204030f06020703050c3a020c04020906 60
    0x42801d0103142c1105449032131170302c4a40400e09442400c540016085010781d80c1070f101548041d01545141c04160f400c0380407c41c1c7d9032201d141001d401001d014402e00d030108172000801805d0070b90a40c002c0c01d10720b800c1d820303940907407181015003110348074507500e5000d8048900198078078a0010580800b05540003422244003426440010384950450100d80e07a110400061541504200c0e4240c40741c03480d580d81f03900d00a420320340c5003101103020038080c02d400f400501407010702c410300c10880200c01c4900b184c20b0326107540d1103001100141c180c074003402007400c00c0111003d5001c1c0e50012098400e800b035a0307450801c88442c0c00c080f00a44401c040c1a07501d40d90074080c8011907039451155243c8041c02050030740701342d40c401055043d05444544442e862600c180400c00110740148240c0c042c03203a100c1c600603030302c00051030142c58074050021a181c85100d0002e40f0381184550728801c01540c000401c0702d410b583c840c80620781e012500c2c000039800680011f0000160340c01e05030090044804000c0460342803 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 941756618 1250 941755368 941755379
    0x19030209190f0311010804030c03120b09010803090a05030a030912021f0e0a060309050c04020307090e0103060519020313030c050102040b0a0305161106010308030a020f16031e120f06 80
    0x3069140c1102c10801150482041044560040002c5820007030034809050300d020f0300d010781458540f060141c107001010b10b9844c00c140c0b0b25440400d008074014821202561a0501e03142c0c1c2e82c0000c904140240d08203080842c0d6464002003007a05030f41e00d55100e40c411420064068550922100308030b8100c0304d0310001021102562480182d10790043d6214448002d4081c10004640310942c055418907144c030683c40d000c18004180016106010307100940d44e03489408045420f448154003a08804100c0030001c020402c3d59005035000d0909007a00705503c500d40305074072040703100030317562040d0a07a403074411710340068043c861408440c0d00800006007829134640b051051540b040484100013a6504c0030011210300003c10051880760510308403114042813414207503550018000030703001a40c003200189101c030554048601c04d81c0103240d030351303161707807003140b943d07202c00105a021000715441354505030803204100030030500b1107040d980d140038180c02d80380d0344070040221140603240542c075104040349 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 941757868 1250 941756618 941756659
    0x80a090905041b05010e15181002060702101407030903121b02060c030103330614090906060102190519030f20060402060d0e0610150519030209 63
    0x401d900503c911100e041c0703200791091034180550400f906008542c0500c140b5a20303800b401d01e1110140c15911a910441004007906110107c001d8035440041d203c0700c6810300381c0c04218940105040c0e02264000703200300003484155003140c40b100001170300440004000b242b098000c044034601a007020b10320000b030f925560058a4005404c42c008688100c50b030040994108225580588801985400d650450740c2d0340213152100c44001e800e81400b04000c014204002181d00160982800204400c1d6550b41c283d99014008100c05441480a0780010f01d001070081601c51044030160301030034007041c145000c00c200c8101240c06640a1113600e070103010148251215a055030300076201d0304240d13031522400511100c07a044051042032981e1980c0250540c000859a81241d8122001a1120301c40f80c0c4400040a610f80007111500c280c50a00c520442c82040c1c0000307450001e10604051840d0160035503081c4552b0401c2c255000781d2080346600030303100303501800c90500b00a015070000e00d5801322194 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 941759118 1250 941757868 941757871
    0x60307030f1401140f090610050c0a03020c0406050d020a030b15030601181805072603030703050601021603080301050d110d030e1e010206130303060b040605070c09020405060304080a090905 83
    0x11100a00006012110300c1494010082c0021a800d00d5241414404280300080280106006510032309078048002c2c010000d6400c40000f9404a852100141c100207681d9a8156403640c0900e1400c0004952070405d07403945007450b6000390031408c8103840e5a03248180e244008203021180c8014078051103c1b51340030310209000b04605d003200c6000c60315104c100c00840b00e010f910a40e540c40c07154144400980080b480700100d6000c211046540041a1100c03161640d20a1035141c2c0c600002041284141d00355101c42c0c0140c10a0b404c480480310381c9150941e1501907400007802050080c00100094908502140d40c014402e507141c098140304000841c00d00c2d4403140c01200070441d2428280d02a080407209600c102d58512200c4e0050041840040d48038034019011041d0741442c40314030301c02e2500a030041c00c01400700c007408075034895462800500d136400c100c6086070366503d01c00f00020100314a000303450503140002d00c060310355143c564030304049a201c1c1c0c070f0420501c40b07204000103410101d4407625 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 941760368 1250 941759118 941759141
    0x607080903090d080d0b0a12030e0f0607050f16060207050f0d05150f160807181511060903130b070f060f09060b09091018080d0e0d110309060307030f 66
    0x540d1030b0300d45c01d00c605007581d1a180c15940618009401040705501e2603460700585c5405051140360360500b14041040341011031006038001000242081c1009000501081c0da03081500603030344103c001182e65400c07106140b0442005a00c4500e080c8010b14082070282a44030009001e1401d40100b695a18186010701043d041d20340a100204000c03031582004103135000086841e9910700900a4001030316400700035241c10200700c0400802e8190010500c9500081c000000c5034064003855408014584100400b00d00e006e80640302c041507000360004280c0703402e900e52110301c035005824214a9400c54205150950310740048034080c20124943e8800c043e44e024440c0310105011480b800c3c0740054034403246a06000e8801e140400a00300f4000c1003001081d5403510011804c9903036100c8242d10b204e2503000180a00c50002100451085240d0140c0110400d001c1512948000080203503011500c260403d00150004c01403001e46d0314200f40255400b40540c200014400c48200000301103ea296402 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 941761618 1250 941760368 941760383
    0x21e030c100207030c06020a1106040b2202090105060c21180636040218100c05100906021b010b010e031614040e15100608090607080903090d 62
    0x25540c04050002002051030001d00b07603d000000d9600610381c00345010007900840e03021880c52038041c821355000d6168004a0111b894034106420315419a480940b040d0f030001060003070f0048000c1000705210130542c1c0040007106030340e10301030030b1001c0b0768803251402c0146d0146d003c545002d100695250001d112681c021540c50302030500081407942451400c192188800707220080f03154101003240c00101d510001c00c98503034014588003031404280b1003034140e0301c10b0011918090401b6400d000180d10f0303504035031001118003a06011750704103859800182c099001044000c9664100e50066a003103445a02c00601d000c100a4642c40e04181e42c48124141ea5110069a1031560307200303130001030030142103025010103022503540c1d042e50b602910900b41d180400031132107038044c0e0b250b510883c8071644400559003010002c403680d48050303030700303e0301041c600ca1002c0010440078031418030548100c48000082c400d6803580b42c0161403951004181e45800d110030420100a620b404100f860030030300c540c00 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 941762868 1250 941761618 941761627
    0x60301110c010e12040837030513050d030503070509061204050c040609050c0d0e03040e0c1b03090117060d0507060f1b020a03021e040510090c0f02100c021e03 70
    0x2c50b13090501020805101c0c40b414842407006080108003201841264a0500240215034000341c419144100010814511a10f0103c05041d001802801500500710381301e01e12680351010050b00707203001d040140c0007880c01e000086049000d18000d0022001c020010350410312055040f04008000301c0307040340ea9401a5400350300e581054014400030303101d00d100c1172180d490110342e01401400358004480b4200d44500383c1a0b480d0000744115800f4200707904140005161680d003032402c951183c440500c0c80c03074501100b8043c003400071040d0382072040140c0da0021440c02829040300d0020000d040c09505c4082c810010000400c00c220707602c0200300c587c44040c1c90000429000d440d030707211100c070501030b00740007200240181e44060b030803820b0744d42c112a091400107884255410f19403114406d0390f00a85480d00344203694007149404000c440c9155002e02104411900c201d5441780d5034150300002d81c0c000101003126016503041902040c1d01441184e451241c7c00942c0c40441c00c94201c401c146400004 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 941764118 1250 941762868 941762891
    0x108031608070614071d121c09090c08061809070302011116170d11060c07081603020c1e0a0509070e0310140610051806070f0507140f1503060301110c01 67
    0x2d10380b0079500e01201d0000e07000d14501d405907100c03e017142c446230020507148920140d50b80101c2c107400103006240c000300070321071003240041c1c01d50a0554815201d0b007999180d03111406140e4a070640308000c4000034110701440d40e801910301d01164074440ea0107001c1d885c0e161000064202d0305074024050118200040e00c140c81005040003106403840c0c0070802c51580d03141c07201301d0000d02182c00403503691403580d40e2221170400040500501074808845103208001606241d80000c43d0980c280c42107807198500040003145415081e030b108296a0040c204000401c0b6903c0d0400d015984a105810a081807802c0c03c8002420600c820350603001c0f1940d521140d51a840d01d0585545d8802c01c19100307400e000368246c0000d0b0aa004214082101c00da40508260360b946801c800e44058943c461047d61020b8050301d4515142c08080c0100d080072003a10f0740c0d000c494a4050102150684081e00115101079181d850421036030004101d250151740302c40002c4208a110001019103403108800059100003e2 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 941765368 1250 941764118 941764157
    0x50702011515020c090a09020306131b05030a0f060b0a0f170712080a18080d020d020c0f0d0204060b0c1e0c1e030c06030915010803160807061407 64
    0xd80100b003440d038803009a2610039800003410f02c90064111405c8071150784030440440a8104104025054000d5000340040f100b820340301c5c03150440c481c2340e401d403050b01e000c400b000f0260014402d0701c1c2c1c198441d90381035000c500d100750075440705070150b0340201d206241000495507110095010b03644c5210001e00810140b0003001c032400061030840060420136140007000e00450b42444806407030182c0008250b03000c180034100e400d0041c10000ca104501c0b50344c030540c4644807a501c1e0001d1016000b15080700b0802840132908541c0b4010052800000741da206081c003560140740e00d400c030b802903035695000c101d40c1c0e80c0e40040c207040c0c140321009006480003e1242e405071403030304250740d2442d400028810388950328115648032550002c03a1000c00524120002464180c00142d07898002a0000500c0031010000c12280c4061000701403600c8266610240540d0303030f00c20300307020702d80910703180900350001081217008100c0c0d14060040820440340c080c60300a241d0700c09544810102c1c014880614501b00d01 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 941766618 1250 941765368 941765411
    0x11203030f050f07050c030405090109021206100816200313060305040b0105091e0702071e05030a030f0203040801020409062c0c03070c060f0e160b0d02070f050105070201 75
    0x1c0d040180402d0801840c071a1414401a00384028000007050340c03038440500b04161001458020032800c400c1d42e48201c00d20003540290070004800d1800400201c031410010b1800030304003050358030100311781d99060706000000348140300b22041042214804820128076101c11008002d03480c00b450360340240507a40d140e5030206900c140145400c000400020440304604241125401d8807040000d58408400c200b9003a504003440034031030156000d201e08160300050001c1607610b0340401c181681c41c0c000301058080101c2c03080d241d1661260300d035500024070034204200003010a0040300d0070b00c1d0703e442080d403c3e07800a410840000c0c2d81e07084200025458651160789001c00403c0c1102c800c02c201c140c20b15003d02c0100000095200000030602480c4950308410100c1d4100e0410440201052290300151003807050480c1d50b0704c5211400394288130300305145e404848141c45024580215103034580301035080036909407616010074400ca00031a40070f01455114401c283c0c00014101c10414003846450035 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 941767868 1250 941766618 941766641
    0x1602040615020f0625031410090507050c03030c07061107060911040204080c01030c1b08030a11032401050d06060e01020714061e04030203070b0a1707080c0307020703050601120303 79
    0x81014480c00481d6505c0c080d00b1080714600942c1782000c514001d40280181c001c070b60207855002000c000241624440d8a01234900e21340c0c1c04c0c05582c40d0701900303c80754058079807400200d41003080820721703ca20000082200340d02c02c41b008118402e007240e000740181c000c06e500f90b0f619902e4041010030844520610b55500004903021401c040c24842059a81c0350b800d00d41a05243d43d4120022559006940c160300101703400031003d203101c03051700e402e98070b80d041501c3c00d9070800d0a01c4003240e4048080000d480c41141c4041400c6015004680c0ca4400e010319025038038144541080208140742280c007400d000341c4001e45a0200310b40d81007000a151051603030228038111550180c2003040c1e80c0701d008030303441c85985202c04543c90100c608230200318800c82d400254103100351200000c103111004054101d1200984607030100c40c00550710700e00c0c7c0c020f0856140000407401c100090040150300040c1d1b0300b0110f6481103c100c1d0352a0b5a807946010020f0700204c0210141844100c10103030b01d4042c1451400 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 941769118 1250 941767868 941767873
    0x41e140715080f1f0602030a1704020f0907170c03044211162009040f060209090a0509070603020f12061203130e01081c051602040615020f 61
    0x20a0703000020300c60700000d481c0c4100c006500010800d0456000c0c03050098401d005984050950355540c069030700e1340520701070000304101d03140c56202c07d807480d42c50620503500a403030308018000c08420014206d4008002c8000d000c41d80f001c2c40700010000515a01c02d1455590303207542c81c20282811000300a045c00307000211601030700d00c0d0a1602d00c22400000241d40742d03110740a070070b884080d61405000700301c034441000580481c01ca2508a449100f2031162809801c400012000d100d1594801d11044c1c440560030040b010b010400156038050b550402d5030103040c0040c1840b40c100d0006025160941c0c81c04045a11242070044201050207000010a4103007421480c1c000300311120005805010000708070b4913040d0001550036210040c80402606008003600e50355100070007050390f000124020034040c5503800d400807070740240004040f070b90112106021a0900510b036030456055101f51a4038055003030300040480140c4450240300302804140101208100920744000e24005040030301100c00d6 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 941770368 1250 941769118 941769149
    0x24070f0b0402090903181e090a0507030e030f09010c1514010302040609140f07021912020601120503180406050a17010b010806010801060806030a08040b210915041e1407 74
    0x80f1050000381c08600588000b03551f28045482202d42c902c1000490347c12515a8003040001e1000394040d034864840f0352002c1000050b51172205a903801102802440240c8c03c0102e02803548c090390a5011182c030529284881c119200303510350540711424030030310100c00550014030840c43c0a002e04c90290101400400c80501880d90030514a4406005551403c4810b008102e40c14420311107900034081c940c003d81c6561070607141404254800620050060040d03034001700e104200020355682c0307079400c540210304142842c1d4a080d10040c640c503509034032035507402000400d600e03143c1d1050300829111062441090605100c9401e41d100c00c100c060403c08824208000c9a8000a0445c19140c581c60a01170702d41d590408645010700001014058000c0420002070780b0b201e0380c0040180b42ea40d1b8203a0f103d81803040400c407050304400d593315802900a07400215214440c0005568020300681c2c01d4100149458140c18000750191002d45240820440e2411074031010040a40101450314100428 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 941771618 1250 941770368 941770387
    0xd02060108061902030c070f030207030c0503070b03070528020c041824020d140103020111010903140c01020d06060203090a080c0f01030b03010f0c1809020924070f0b0402090903 78
    0xb070920180410754071130780480440c0511060005880181b039012401d5600380c2d40030708000c0d684440a210460b581c440301d03000880d85050216400d8100d0301003031704060945c0c58000d81614240c0080700c040754a10185008204a04032040c030840da014400e030040d00f035a1244070140802d4030310f00b6984800212000361440001510882e401840301c0d00c80490f00c01d0320b10081e2010b40648241d0080c0e0240c1410450421401e400e41c00616048034400d032116100c200040c04564203a0f560042d003d00070914a00c5100c1c22980541c0c0200035006680c0001880c0c8029005254121a8107821820040e400421000d006060004c400e502524078000100030180030040000c0b60140240c03140b40c101621040c0e11246524250070944da40c0c510440c003405028201c0c0001409a107181400c01003442c0e42450028009900e44200e41c0908009084003003066248000181a002c00b80607185072140c0c100304950108101d24940166540300b031016a46074241401001007165000c1c2990485410030010300c3d11 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 941772868 1250 941771618 941771641
    0x711071509080a0c17160b0d050a0e1507170a0c1808060a020d06260c060717070c0e1f050603010501020c0112020c10051906060207060825020d0206010806 68
    0x44450044038141e40700c034161040b0341401004050f440c1d00580c6d00e10046884400d11000d003d0040d0390403010400d80c1da4030040700082d950104548005508618481c0c5200c1ea4517581d01039016801d410b000010302074080101c0c000d000102d5040340051356a443c51781d0490391000d880050002098500740c4814140cc0045895410140008112603030001e40707220040e0031504001d0043c810000c4404131850040e110714148507a419820106020324040311400d460501305980320103802911002030f000c84021440704561040005803032050680c01e001034122040444d1611944903015008104a01648081d00d003031025044684038034002c0c130043c8402e903400540441d01100074a041070304520b5810408001344a2a40d02c03030720500036012403170525002ca40029001390307100d0200001c1c0d000c01e0030100701181c80c00c0c094400160013000040110510030800103411400296115144050a0100e40700440c1c46183d108050b800036022082c80036010f0203418010004d25000e02094601211a02c9 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 941774118 1250 941772868 941772893
    0x9130b03010e120409060e0c0316090f06030b030d111009020f19060e040c0509310c09050a050a2c100e0709050102030a0c06090503071b06090312080711071509080a 72
    0x41d09006201e00349210bc1c443c5410100a001400d212801c03162144c0004005d0f0041d45040e42c043e200c0e000c6021007852049485030001c0140502810002140103007040250075880303810f070383c4100d00c0007000ba020b0340c82d00000301e00b13030b00c03800c01102c441850004007402c480d18460042e07101e40c0c0350010200781c0035004400c4501d11041102c01c000c0f16902c2d00d005030484007140c1a40b06c00840f4108105451251542c059107140081e0f4603005403140e512410840120a203000d200e41011000c01e04015041002e022801e0714207410003585415005c2e10009441d01c00200e90301c417007900d41554100403113004c0002c0c2c16001800781c64603481d01802c0c500080e5691150f89200760130400f13154120820301600307900290240da4071200366642c40c00d4504201428220407250401c001c104688002a914040c1d03480800700c0741d00c82001602c2c0c3c0050711050302c44140040200c410701002c001c150380302c12030030f11050f07010f48040482c4000c1c919024800900c08016a080360b03800c1d80c41720880d240070503440505003 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 941775368 1250 941774118 941774131
    0xf09050907260609010203011a09100f09090c0906080702010b1806010504032001030c1107050f04020708030f07030b190e090c030a0c09050c09130b03010e120409060e0c03 75
    0x40400c8a505804400c640902c4018203030151209011515006400450480e4201205602003140c840f520040f00d20401c05e005070306c417010300715584605004051550f014202401c20095065a6081c81d6080c2c42e07007682214001038403084140310181c1c2001119410942c0c1f4402040b0164281011403201809400c010f002d0502010010344142e110b81c0848000e96031001d200c110110494000c05a1010b8140c441800b080c109400305941500c69880f0107070310030700c5c1e00042c40114602014002c1d07100d00b00d0000c40d04260200000340c003080c0820000e50142003041d4100800e0700c1e141000804072604146800d128004180f5180703400384216902c1400d403101101400c1040c0ca4035000c103440c0402c448816500f40c01a512001c0910110003042801c484800c803040c41296a24403081c6a1807140000e004d0303002003101269040a4459480034000d500003400000b6000382c810241441c00e0400c05854559580c0010f080c04071048078010303440100040d0301065403a04015030007001a01004006 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 941776618 1250 941775368 941775389
    0x412020f061c05091905060c0901200c401b080405151017010f021b0c030f060403180e01121119050d0804050414010f09050907 56
    0x25140300755610402c035050602d1092246107460420030500c40600021590b20049000d41e048070416011000210818a40c1c400c002d40000e50f100700144150b030704590b01990400c040e540b070001103490740030501e403154059540285009800310042148221004001c2d009540007000e95071078890380700396500e100f91014107120942841c01d80030b01008048c2c9250345019044020303100120160822110f900450040f4159144d01e0202c600c4d0062182c41618140500c031f00743c1c1340410010803004100340c02086c82500102e21950740c03915082c1640c10010408048400c4904040d902d0b000400907038040940c1600601600d60f4000d285c242c9905c0001e2002e0b0a022240c1c4440a900107001c9080d006030000ca8010f80d031558403605c003034071400c9022780c040ba42402c000014034418508510034104408006081d0f00e41d1900340b80600141c404c81e00b204841c2142c1c00d110119144e61180078072610a1400040c030101c80d80341c10040c10b0440c006030301c0428040e1900d414030151003000b10301c040546100004 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 941777868 1250 941776618 941776639
    0x507021b011d0a1214010c091202010c05011b0f080c1e070519020f0301150501210203160305010b13030b0705070f0309060e102001110d02070c0605041202 68
    0xc07403561074610080d402d5004001d4500414921201504251104d000d1001154090421704004e4220703107000d00000041442c070581007000039800c441200400c3d01c1032401e168490705079907a440c2940c1c00c4110029072903138400032440640794030501d420040350f40d51400080d07508040c584501540b01d806140325014982d1040e141001ca1080200c84140f41d00004403035290300605541d126003004404100d10918425200303c1c068a014024081d01d130f00c2042d807100800f482c1000560b408403c1900050003e0b160400f4500c218640744043c62050001d40d03030380c50b4075804800d001400c82c1c805812032030f03501c01c050250740440da090002e0241904d074000c0350000581c03507200303098440e805407a800a0076412110a1a01055408400d01d001c032403240e16207040102584080061068400c0c0d00d0f5800a01e00d404800a00c82c2010342c3c10307a40c0507440c400001c0c0c0c000c1c20241c4010550100ea032071840d03ea0001084003c101400d0840c0c1300618280c5416030a180c20840c0c811421004010003a109918030310b03 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 941779118 1250 941777868 941777897
    0xe0a090c0909080717030718030803060409290a2a03020708090d081801030b03030d0213080304120b06030105160e0a0902210c070201020d200a03030204090507021b01 73
    0x40403102d013541c1211200d00c520120203400354440c0e204444100000b07140f01c5512041e0449840c1c8003041e03a5104003420309695070b0702d00703000c01020036100c15203145442c2134884555695030303041e515001c1100110a100f0f4601600d01c001030b2060a50102182001e45c20802032038820115510460f60381c0f89000340e0b0310000e40c14220100e014401c3d40d0341d03010f0f241c800f6074020000c2803001481062521881140c0426001005504980340c1030941d6405801c00c02203140c014500d98020500c401401c42960411500c0b8410280380da0856048a00d54200c0c6510781810b010008503101e0b4010740c00c80081c00380e8680842c3d0010f80d8680c121542e0140881280f4100d000c0d9507007201c800260444a80031502d80d800b420b10f4581c205100e00403a04050291b1010600c19a800003c40324099010707002843d862030040300444082d0a450492204000e14658090302044103000e000d00d0380b4083d03600940c4460400c2c1e45001241c0010300b0090556000a548254261000341d041071440c4090030110140388601 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 941780368 1250 941779118 941779133
    0x33020c010804031e03091110140c0a0b07080906090a0c18181101030c0c021f050715022a1e0c030a0503040801290409060f0509070e0a090c0909 63
    0x24403100813000c100d488400c1e441d07160b8004100d2501034480c40d04a04001d04c1400713100b82c0c0b106001e500080803c02d040031206032020051941e056000101c030905a000d48803148000d80c20382d06000001c2c0c1120a00c0b0088404102a60300843e014000e04506115503880030b8007254039100e80c03a0020f1520304c1e0b04030035034650f80c080a0350700349500d404041803010307291441082d001c414000740441c0c0b6001115503035922070a2944802c581c0682407841d01000003203414040700342601101c08200003045200000740703946450044146180c04d0260b10303415041070005100340c01c44500d002c4110703444c4102d101c9050000b4008000c0c400500603402180c041c00c800703410014031101098041c450031103824200702d4004000c000b1179482c400200040701648001d408051080401d121a0b80c07007502c01d092403071405501c41420381e8400c00f00003070409140000344081e58070441e84118190820b41c0d0400c00003a03040c01145d40149460300c2040589140e170f540c0c002c021514000c0803030381540c41d150300c005c005c0d80 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 941781618 1250 941780368 941780387
    0x3070f050f0f0d150e0c011b210804020306061507020d0525031b0b0a1d12060a0c022d1207081b03040f0902130b0433020c01080403 58
    0x80e202860010550410501c2d81c100c0080921505140403d417154a22010640c4c484c3c11905030741d8a0b81c507622040300d02c400c0c1d4060300030666100c2054101c0d0710030701c40c250b60380b00000c680325242c40709030745010300415061450040c44503010380101c1d50541c00b01e4180c0c504845410781e044074490800d681a040071450159841400c0c1c07001c03490b100d042c1260000c0314840d1001c9900c10b45a01914a074040290000c120320351180400c030302414017035501c61078004d60b4a4040e8403c1d014400c2128000080044c0c402072140b60144c1003600a403050048420060103440941042d60000700f49405100c82450b22103840740101da040c1814030400d00840c0c480034444c090070110400e41042d119099424402c0c80d5900061207021841c80003480c0068840020050b0740494032210408004180b0f043c1c0701101940c01300c110005026489000414021603002c00381c0060200d003141032015085040c1ca400c5880080401c803070341101c00788240c02c4043d07030002e01280030590038a0b07d8400340d101c61800340c41c008074 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 941782868 1250 941781618 941781649
    0x90d110309150d29190e0403050c01021c2a05031501021203072f0d14131403070915030303180519120c0c0603110c0a06090c0503070f050f 61
    0x3000c130030341441030f00d400400d4840c03050100e5000b1316200d0301c00040a03c151381c600c103e003000d149600000300030074042c0300134102700d031940400545004810381c18402840b240001c550b494a548400345030104d4086d102000b81500728112907410500488805401804020320415241908901c0f0050503403082c07007100b150460034011075480707040196026215003203c0d01c00440d101c43d5118400c3c0f500390403001c4045150010409096800c0e140c44e8111005202c06450200440c020880720038088140c0004600820030313010700d8100308000e10205070401a055000200490804e0241e00700005940001c1e021640d141c20005483c26450000c020400c00702100900240035080300b00e01d80c003c9420118040901c100a4040344860f003c80644000721428006045210b2001c02030000c50b0082c1d11100035030070b17150f02050501e0090204c0364a45050074200303c1e000c540f01c040c207000b081211215203000c1c00c0f0450141602d00d042030f2074060ba50745d041c400c0c3c0b4403c010420b409001c517212564501a5902c = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 941784118 1250 941782868 941782901
    0x80c1207060b0f090c070b1b0d0905010b060c070504050402041103010b0d060b03160806011b03111b03060a0b010905100806130506011b0614090d110309150d 69
    0x24a00d041407001064410140d50003414464000f800ea07142c0a044944140b0b00d81030090b0402d801a00c80c0b011106005042e40c1c6002c20b000c1d100701089046401134401030410410100c2c1c0010140340c0785095661010b04030f80030780c5041c002c2014500c00404d46d07000b03072841910002196a20b9000080c0500410007000003104d00c000000b04440b104207005141c003000c19402070102e41d96501c10801c8500c0119105601c01508003020a64103200703108a641100301490590f030a40b411405541e42c5400034001100841c5207550310501c804e4040c010391004043c2e0140000c0065441008a603d8030340007030041403036998604900c666a80100020303009048090f2000314240400b55010f0000301060701c1c81441034005a150040094030350203900c3c442c040696507000c20a82c19a00d0002400e82c019044070f1441d214030307418500d0500c41101d10b115414074402032012504d100780241900711811a81c01107900100b00013005e50f11761038102680c01c010302c2c02d00c5545d1480302d060040188507400da0342e075101 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 941785368 1250 941784118 941784127
    0x1d15090d030908120406050d0504150c0306080613211209060f181110052106090a05240607020310050114241c15060305010819080c12 59
    0x16500440200c241c0d0403803c100e40744600032843c500c205001e213101e845d00213a402c100101d011400c0ba004150840e00c14071a54100700160f64040040e0b617443c2d080d910001e40e40340d1040180c907508004650308043c001c1c905410b94241510760f100486003420041500890003290300c200c05200d8007005200130381510382002185018908017000c1d044d02d01034101424105031088400312007141e00700200507401110084010301400602c4254140304080105000061110b440c202100f1003120488600103200c4084070720b0400d04029901e02d0140841c0c5059140000b08600c600060f0201c0c20042050510000600e0041000035068030450700000e4060180e04c90411051445801c5281a00c080624030f41d10100310505100341040403070100001c60700f0210748220007007000d000800248003c03c0350343c0107000f10481c101003a10140242a070395418150401c216150b4180704042c0984804005800694140b54040c84102d42c10140504003030f00000700202000800c00148100203080d0082d40e0300c5 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 941786618 1250 941785368 941785373
    0x4021008040c270e010c02151506130f0b0a320a0305010e2206090c030b04050a05060a02040509060f030717100b0301020406020d05030603070f08100b011d15090d 71
    0x1d01d0f0060b00d00b0b0141ca8140006000d0792a4180260201200756900a00940300080d0302c40d80c0040014200707029208540018110640300d010045c040d0404030a0aa10154580394030f00c0c0d100d044652040d50480ca0178005085000e40c06140c81203070344505404c81e560f1262448282c4144840700311800300003100068200340454041d000b06040398010944842903581d010740c822401d82c800d42d640d01c4503948840c00100000e8a0741c0c82000304030300919030122203603101e50f20f54110b004240d4054550b45d00031240c0b441041001c01466030f001c0b208040c1941031524102c00f040326444007038a220700c6050721506410f6039450402c00d640003461008990350500d10705e81e04190f102c0c0c818007002d60b0f0030b90408400101604050080340c0445815500611000200d10320888241c1c0024100703c2d07041c00f9400e80013641d04014440704007d040e80901800c2003c294010510807a946c200910b410f00003407500d01100c908100c40746907510807080d1601c00c801d28910b035401945105840110754040c0912807400309 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 941787868 1250 941786618 941786669
    0xb03070c020f03030405061b0a0615031124030a11030709051f02120310150e041d120901020a050d020606030601170601150c12030b130504021008040c 66
    0x34600a0728050340740344850301495240c0c4224002c2a400c480104001c09030908011001a05d00c405c0c0010b039005400b040e80c1e43e006540a071001407029034480181441440840141510405000c44c0c8504814286052801c11a440864500070780140440002c0ca400030a03040f0442c5c41c1d004901c0c2c00c1ea03e15107600040c0814406008541c0250003060042080c0b54a030408200c680891750014001c120441030700d45950791008003100901690441e0005603030321049e4583d44c80c80b40b181c072051108984201800300311400401c0c442c26a10b080c0441c1c0b40b0003040401d400c0c43c50240007504990b140c00200c0143c1c900000510010054070a01c4062038030b0b0342d804108a801004120161401030b641c032901c0a00301940001040c24a030010001081850440080c0e44130080710341c2000a600c4610b51648405541901001070100740c85500a007181d241013003001d00c6101040400700f046081030740109015528101c09036090080b02c0c800b080a109225035020010051103a9620121162200000 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 941789118 1250 941787868 941787887
    0xc06030b0103020708042112050306132013120f0b251214090109060b1e04020d27060501090926040503070803120601051c05100b0307 59
    0x28a081003041480d88240200c0c1c0701943c00080c040d003014201000c0350708000003503e250b840c0599001c150000500c0c002034641340d005141d190180c4030f00e446400d02c0308508019100201140c90814082c2e8005280c0e59962424420794000035194407003088104034070002c2d6049120108a103440420400078150304410000c0c0c81400c47d10745030b8030707042400d01a414030b440340384458100b081c1c1c848000c14810440560032440109003c039514045170200415400c0a03903030710000c2e0351182180d40c04d2190b0740c01040c9a407241581c44040702024402044114100c800d801d82c032a5800080e4140c06c03401c42d801404d100078520420340701f24040304400d80302c2c00c66481022150142450300000d514121840b806190a0300f002150750396590110a070b41200b603c0d40c2c4100c0101d0000d120101c0c050300e00300442005003080034011070340c0d1101d40d013204d019054000c1119040050400c03450840300032400d03014200d460781c5403000c44c517900c2d000800d0050303900f02c0e003009907580c80201c00c02030050390140510 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 941790368 1250 941789118 941789129
    0x12030206271006031a06030d0c0503090d0b040b01080f030f030415020f0a090905010515070303240602120a0504060c0606030b0f160e0f0f0411070c0602100203070207120f020d0c 78
    0x255581c0710105c40484035040115000790381904180114101c0600410f450102c5610460550385000b100d60001003800822000645ea044019001c110030403109a031614090708488008109441d100403400d40e4174881c0b59410004640040f000c83e04205440c00300c0048210244000e6440368004881445542c0003000c2c09000145140340014a451841c0700d05810b8480213408198117442c00c0340e08425136409084110200f56456100210202c3c1518100017081403030041051428070340840240b0b40003c082d0341d80100300e0708102e0581500d0f0000100e27000c46020341003820030400381d030400500500359580094124820032007040000c3c03104000e024421540c100d00091060b40b00b00c0c0c120703901c00343c03401502c7d080034540902400718601400c001044100042c408a40e40c90b2442590b01a034000d42030031101c2d0090f4840c1441100c6c1c041c4060710705060720300b40440c2540f0302040300030f556070210710442e2102c89403427980c041406650540ca900d07141e00905502c00480301850b0501c1044180d1064 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 941791618 1250 941790368 941790383
    0x304050a0e270a021c06050f0601030e010b09060f120d030207020a1512050a0e070b0903010513030507060507120e0d0f0f0c20030d0e010201061203020627100603 71
    0x420281a550451000b06200c03010007448060510f03070a00c0344039034202c040b84100110800c550030003d249802a44c2c49006400c0d50310350b003400c21a0024056038840c20b00c0c4039441e41005581d828640320391406990040f001c48040241d040207401298904c102005580310a000d808070031b00080350150014079120348280c6075400c0c141c4d0b070740b810030426103999158800020104002a108811070303410050f00840241d10010b01004d000b64698a04117943d404200c0b015030125003003d0300c2c0740070300c15164804550145440c221034980d400078028492040000c0c0340313070780d42d201044299204903c40310015492100821a055206121a030368200c03c159440001d002202c11742440d03889070345a5078602240e5200c140c10403100781e940b004a0101c1400b0520881c1d0141480040da5a0402441d0204a00350321480c40c2501144002401d581940d00901c8241c4040c0c0709107800a9070019030320307600604120b480d0380201102c038141c8a44140c41180d040c820301c00c030840b980700f050540d0f0010341100e202e800f4 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 941792868 1250 941791618 941791651
    0x304150909060b0307030f020412030207090e060907150509040c0c0501050130081207120e0730080a02070f05190b0d090812070806010216170304050a0e 67
    0x242400e44031036000d041030f49030007400480d03910b0340213410020550500d208054201030712a1f20301c51340306040c081c05500592000c9410480da40c1d69101d0020006030300d201801c8030346005001503507120380310300c04d10300905c003414181c250841c80344084e44e00405008005014100a141004005c01d629034001c0d102035180c4400000e82c0d0050f21080b114507042e11003808500740e0b030310451310301060340c1c550f05541000c020000100d41d501c9011845214121a0311001d01c1c02d2070090116080b07070903021455007542e01c440d05c18000d00381198802c00c4040e03001d005203401924507407a02300b80107406c44e5008200d02c00c04984000500d0300450110305403282d503030a90f00140daa6001b00508440020350f00103150080c0d1005001082e44203005011140d2030b000041040c245a03614a03140c0c0c2e010310500d61800c603440341840352044e4840400307500036801f4801840000842090407041121900c00c541d0300c1d00310101c3c5040800e82c10700c265002004018000030000d90b882d20843d0303101c0d404503034921030200040d0713 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 941794118 1250 941792868 941792879
    0x120603010902090c2a0105010614030601140304260316020a020612071106150901090b090a0c020a170703020c0910031704030501020c010b01021e03030402150c03041509 74
    0x1081440c030907001821240c154641d201c400c40c1d941c5c002e010f25840d900707098854206090183c42e8040441000600009143d0714010000784a582058035418604604200b40a25a0303400b1301d03030300c1003808220000c40e0780361514580400d4420f00c10703800c0441c01000134a1002c112b14108080c61190280e841c580c2e2500c0c420354801c90302c0c3e111220000394001c00900c400c0003608181c0003441d600204a00f4000820f000d150707104c9140c90000c0703621b10445000c6044451090400106290042483d12000e02c0708481003000202603400091600a1903581c80ca0000e003060710820041055581241c01400b458440310302da061030b6032051070144c001d481181c141070310341d00f030020541c1d00c1030000106003000c1c5030030b60307031500089110000c0800c4001c805100100101d0b00a1004080b0b0308144000001c1101900002905200b6a031940b81d070702044060928088003404811640e0069044a5500229400507040d00440c001c01003450824800072030041040c0c034503c406207582d000c09484800d8000d6540 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 941795368 1250 941794118 941794121
    0x91315050301020a1b140a14100c1d0321091005040501020322181a030106060c020d0204020f13030506060d0c030f171306091403031c1107030512060301 67
    0x1508400043c84024a41c4071524807a8425444036111b0b03000e10f072841640340c030003c4c605414802c1c1a500400c500c00b588450040810080107440300290b01440410040480600482d40030340d060300140c80c14101000300caa4080c080c9500e82d030108070703540012441c11710308000c20360417508205014036004201d2a40d01401041030394200d4038142d004525020001906803006601c101346814680c049074008103043c3d00b048135002400302c070380c0d1002078661070001c1040d490040b0210b035140603924149007402600e9200c103621441c1501520f24400004d85880441c000b03114410342103484420104078032443c0c03030050b03205c1c01c1141c0c00303441200e505e034850504006a004181d03030028040b2104141c01c00004080205044600b40551140c0e0007444d02d1400d071042c0340c1c0c03058001090301110a0000d01845401803000c1c00505541d1002c1100c0e0800040403c1d1340f80f0580b84820f0703204000c90190390900301103801c402c00c2c104c0d0140e00c0a0321403200746405011504060045410b000501000821a0405 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 941796618 1250 941795368 941795377
    0x1203070507030f051c030903081006021e1e1e012711221808070b060312041202040b010516031b02041506020c1e0f0609131505030102 59
    0x201000d05606890343d41c42c0401245001e80031105400340d00020045020405114854004952000f140d600e40d5132800402102000704420311101e0519010300c25680d0014003696840b102e07000090b400d052000c1c41c41e1030984004041c02854091500d00030b4045404900700081c10703001a9508030715140200360780c0c00c0e00ca001010b41445440801c0c0301c00d056a0204051445502521811224030401404500b0cd00f404581c40c0b008040c40000040301003c0302d1007083c0c8211200000740d04c425990382c0d00ca085500c2080f40107010070b003000300480c0f100d560501c0308401064454200c10350310b039075412414a100b160802e052780f05074030300000c44806500035001c6400d0601c4010128841044541e8151030450f251001e80041100a1240d0350040e125441662204289a00900165480c040c0001c0c680302c6440300443c020481a281d80300e00501c084081e4481c4c0304211005000703c000200030448a00503200c196902c100200c40c48040c6902c194058501d42001070171008110b6142c0003410700340e124 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 941797868 1250 941796618 941796623
    0x80105011503060b0a0f180306021b120403050319180602060411011440080f0a08031b09062803020405030a0f02040f0c020322050906090a060b0d0b120307 68
    0x91a6066510b91003041f0a007442400c1042c0c0000683c3c50791a20760417600300c00201c400100408000501d440c00402032340e130380d40c18440b0b515440c09043d84d645a403280680e10780154107184103201c440c0b2490080c0348429418201c0304006041a90b2140d000799079a000781d0301039890380110740050015520888862500314161004540723046080140c001d0740d00116001d09408004032819072a00d21480c0c950064400000807034183c4007070406001900b403200711955991194052400b44000030780360030a03a03510170349801c90340701d65441840c02001e2900c52120f40c10b82c031660014011003003111400c01c1c6411000603040c510840441c0da0400d404030300c03450081030b51507803048071032000150b030100c400340110740b002e44003048040604030600b05a624031980c500240e0404a00c0c3c800207003600c2d103801032100d83c090203c440720b4134100c0401c00088010b00050301400041000460000c3d141d0007050040001f02d15030356403005460418001002009101d500c00e031014a59810340d9100007064984464 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 941799118 1250 941797868 941797877
    0x60509130303060b1804060f03030c0b04050703120503012105102d02120c090607080c15010e180a0b060f1201052d0f0105100306080105011503060b0a 66
    0x31503995450016a8640c0300c00c8003015102c56010952800b440c01800035202441c02441412400d84200b1060b030340380e500821190b154202d41000440d0344045003030030450300b01009688540f03c50400c1810502a9040a854a07407018242c6045c0c2d58420000d504803850070407800d105855108030314054420f0003002500c254000e92a146200718254024440b04103041e200c0e42c0743c3c442c0e5a103100814401c0c02e26518035241d0100b03814801100c0940310700d900501d00d10a4a02c0c00703041d00000307501801403000103070510b040407440d8101d0110070054481d070488204000265507039981c882c5158044201c800302c8000350b48410403050030100082c050042ca5000300b52140603924074081c006609060300085510141c09024422020760038400c050280440c240c4600000c0010403a00e880c108004030f00d403500c080d01d0b03405c0040307404280000c24151401120641449002410110f01800705500082125440c1c94000558100b203000c0c81c54240245890034802e480e0b550140980500400c8100c5c030101c2d = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 941800368 1250 941799118 941799121
    0x20a021002150408030f0c070818040923011a031c0c0f03080105040c0c24021c0e0d0825031508060405280303020c0c03031615060509 59
    0x1403600290003008214144111103019585100303103055880c090314162002e06000080c0882c581100d030b021544032501080c89440c182040d1356540e003510505400c1d03600c8160580c4913000a07a0b498004107030340d9411123800700140030544d0b40030689c1490802e89118940c41c00b444044005041841401c00706001000f41080c1d105405400c040103000340c0b0a44100b1034034004007030025200b614106055401303036448401960400b0240003c03030301610305210900044c10b04490008002000c11140c480070750001412001036982c240300607000c0c1008400350302ca0300b4965406500302c07550041420b00c000c841240ca030612008419500c0480c26506c0c60b49000c260700841d40009038131480d084212080385000903030241690b020611014194000b07080c04d4010780188002d0050400400d174481d203181d003045856614015195070b24401d1628000c040c1500480c01004800381448019901d290103410303280c0c0d800c100d01c4041e0200e5000c02c812200806100300d0031000490b94400d0304140c84014000d40042d = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 941801618 1250 941800368 941800373
    0x71a1b010e0105070329040b1005120f0115051617090906042003040807120e10210f02090402040303020c01120b100c2f180f06040e15070915020d020a 66
    0x7004044240d880c0c000b03844540014103910f0303442740c44944805540d0f41d69210a1040400008610080c0c40c0c21100141c480042c03000500394842d044070078000e410030998031600d160301156500307030710312014104807440c2c0494200d031101038000b010f01102c21200303a05a641d4010400048032910003280ea1925443c0c100400d8642c0c0400041d40c2081c050310b0744509050302c50751160b444c010800c80c2c41000a00c001c80880d0b05081c0028904030384010307814180450401080265840c1a03020305441d515034849010813041c4000d681100d038a484c000d8401d55a8503200c4c14043c0d41d8040d4081141d0014454002c0c00c0d43d0700300c891040070801a0010311705400000030314000c80c0c0440441c07100b92258101c1290b12100910400b000c003000b821008448212480c07904d0400112091481c0e80500c2400302d01c04200c3d160142d001150792145003211f0020303c002c1c040385103e151440710b01e03604000b440f401041c0402c16810000750404c403120901130104200840340d0480e2500030b18041c000140c0d04c640d020000 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 941802868 1250 941801618 941801681
    0xc0a140c0c091906030501020a0912031d130f0501051203070804330914060a080105120115080102070501230411120706050918040203071a1b010e01050703 68
    0x401c240c0d50407100c0c0c002201e105810301214911713401184c5a03980001c41201d42c50f00035540d0700082450441c40f0402c5045a1400703000315400b040c0580820a42c440045860350390307820003d0320460b401c1010400d0420400340040106800e0007840d01c02e8200c18544080d1110000c02c40c1c074851350180185003080d1908445c010a0750f40c1302c1151011070540c140000074241c00c1140400042196a603007010146403014000462502d090350a0088108124004840303400c41c85840c11180282c0340340250500340010180101789003000a003201088080000e02e405c0f0540150501c3c50107840208800b80c0c070701c60f4045240d881000c2c0703000300492410001d0081898420020b00d440303006800204c01000c20214641458810342024ac0450008a682082030914100c400211400741454031440d04107600000c0c0d40c0c0b507162003200c001c0c03071000e8000012220b000c02521804c2d03402002240d480180001082e020f0a108102d0844561824000910040c0301c1e0107100070320313030801b04c000c0414031607901c0390b10 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 941804118 1250 941802868 941802871
    0x16061404051e030d0f02030a1401050f120f0102130e0a050f0a02070201030b03070801150b03010503031b0a0f120f02060c0a03020a170a0501050315060105090103050702150c0a140c0c09 81
    0x4030350f01090080c040241c0881c083c0c8025040c1468005070b880c80d01d110354100322031801100c0e104065040006000c161617081c400849140125180141c000058403a603192040c81103101d00d4550006c40c079400c1c9084d81d00808003e8900f0b0f942d1400781d6940c0c102840b0100d40d011a0f0700a0010001d001103881041c080e03006104c421300624021070441c2690300440c1c6071501e0340c0d116280c0342e992074240007035034010080f00b00050314084c4050b602d554902000a079407400707040f010317820800042c0203074900c134881040200300b01d55010321f038907511f808607081800c1010210b01c4200040360040b2000c203c1284040307025031003100d1420045080c400c2c0c0d02d031f0880003900958540340c2440118480d4403d90051b810055214241d841c601040540c14481130600340314100d88004044800d0405109031030380c00c013098516010080c600001c081e950044201d01c1d05540d050a07c2406200405100d000600580107040b500503545400132005030440c01c0b89000d01c41c81080c821070f07400075038110460b850540c8265 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 941805368 1250 941804118 941804173
    0x9080a1d04050108250b091507051006061d03070621110901030b0a03030509090c070f030c03020c0111030f0703111902030c010c1e06060b1606140405 66
    0x5400d1180d419001c581152000e07008288540c1c040014000d6880800f007030408410301240b00c0521061406c01d0881590059103881e074481c1602441c0380c8405500c000c00d0741e04107600a02143d250481e070140c908000c3c6810302407540098050f011072814480c0f280415155039001070000d01844bc0781035030841e00c0c4800b01584030048503444080e94800011130150700901c2c41c1c414140c03681c4c3e001a4001504680d09401420300031200444204013094002e000d0350715402050383c0c1c4414a41e00c0307200103070840c070500c80000c101c003802a1803d020315512802c91a0150701c650200c411032076001c0300540b017501d40c1c40d8143c2c6c00742d4410481c6013000860328014011091103030814841c03c0c1c43c40e27030502d81800c01d918020340d04040c0400021055150420015141c24000c5c00c242170f0840458465001c80c903800c02c0c4014020001e14492810012140e010074010221b010799581c81d204042c01c1ca50815550400c2a120030341030545021a66000e403034030074042e9902400400950010140aa10000c60039111 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 941806618 1250 941805368 941805407
    0x301151413031b08070303021005040302030f07150e01062105011b08070801151e090801110c15070c021c080313060c020c01021b0406031707031209080a 67
    0xc10355a16600340a01c040c40c4265240030003100641001c640c1c950f103d6108030600e0f4407220040000c680c000c180490710808401c000310301940c035400d05916600c15070719003c84251000801c0380030f00400c294554082c104040d02408030080c000102c41c00d0700d803180641d600e003001c0b403c8a000d03054196080d0035040307481000041a100e2000c1c10004080b480301c046107010401c42402c010070780340d200e00868054404510881507175600040300801c1164081c04940321900c0200c10164400d0240d5080700003030410000174484803805034103c461640080e41c1c2c0c1c011600c102415980b001c411360008074442d107103039941c0e14440d946a80800221100e810b8654283c01c841102341c81c080707480e0100a502ca4508071406c1d030340302116485c03d00120381e10019040d086400800e5503106aa80c0800c3e000030020403200c0c9005216000b800090042485600c002d0500c0118600c88441070483c4c1d0241c55218007e031101034200144600715801c0e1445000002c01c109030400401d182d00d07015030002c1c160240317a0030f00c = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 941807868 1250 941806618 941806627
    0xc0e01120f150f0312050415050d0f060602160503070e04031b0602030405030a0e030f07051212031911030106090905220f0501050711032d0a08071403011514 69
    0x488440041500020001d10801c43c0900074050384c03e200205940b400d04d805442d00f0302c3c0951000e0607154030400304042000020f016000c20010b5040340c4060001200200800ca030340744e50203907071103000443d481c6156041008c00500d518000c581c050480e250004130300b10541e911360742103030f40714840070f660740a090500a841d0f02181c40c51002e14400c0388500021a0744010a890141c07029a888140600c42d601c4603800c5951000f000c5140822100142d8502c1700c000300c081041810002e1461f44204541e81c080704106058110390088080c1e411003140812813151610b81400440c402401442c0c08140b07458020425600c80354041548203007440a609207400c0140e4401090040510f0f050311242d005040e0030007400820300c18190440c120342402c0012480d0544034a07102d001d15103249984000c0402420303094004200d018154100000016965044807036003d48400c1c1c040e00c1e5400007446410400e10041c2000c0100c81c1a42c60201e0308008100106108841c01210385540300001d580c10320 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 941809118 1250 941807868 941807891
    0x3090602010603050c2707020c180c16080c0a080405040f05010605070f051c0512011712160503120406050a1802063105011b08040e090f03030711010c0e01120f 70
    0x6c80460140e2456030150841a03a400308000303203a94000102045512180b050040054440c000c4030140500300140d990a00d00a04001180340034046100b41a4002d646c824010011a01300800c1566022981006400c041080301422140c00b400b403000459030400810b40400da0700e032030110040c1d100750101e803c03504104080740d00d03482c4002c40c2d8901058001c036618131003021402039940900102031150a1070046456410f03660101c03a00849a98040020039048019103d102000c1c6541c0201c11a6903511003070711f0a0102c00c40455084d2030107480c1902045507070030203000e0340c18005540b0000ca8601003c40d000c01c121944040940000408492030821624004186e2a40c911000640002d100c43c649070000d02861555202000c9211407a01148000784204044c0e038103841c1d0405a442c2c2c165030740048030746083c400d1315040403a41300100030070071071030780c41154041c41c51a0180280041092440d0550702200020f00c014082101c000c80c2030740e45030b81940809454a840040410002d071040c = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 941810368 1250 941809118 941809189
    0x150c03040c0f0f05011715040218120618060415110903010c02010c0909021e072301020d060803070302150622050f06090f04080d090204020d060303090602010603050c 73
    0x10382c041866071400503c2001503680180c0c0c15030141c510007080280c1458018008180010402c000c0e510655000c511001d5030204103a1520650310041d12080d07182841c0700d11240c0d01e20b03085030349403448064108069418000821000c1c0a95402517400c0c01e25402c1c0502d000c054005500c01802d21441840b45103d0380c1c0e024042d440344188590000a03481d04418001400528260000c01d00c03180100112441e4010300841c0b03214103100304c0041921006e1618103c821380c1200920603910301c3c0c20290f2121548019402092840b58220082060b90703541c01105481c1c3c01404809000b6030409011b0301c0b80c19241c4d0310b6403a0710800003080d00d9035011071210b4100000741c0141101c810306a8503001c204007000c0c01d01456800c114106c1e0702c03803681c2c80c00111001c10010010720090010b0800701d40404900061380205200d030754000c2042d5116803104a06400501051005400255008d40300054450042c80b0380403d494000025001041c401c00c103002040f451081010f558544603030428036040c004 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 941811618 1250 941810368 941810399
    0x360b03040510240927121409061602030f070f0f0501090e1303031d010207120e130b0612040807060b2205042102031324030b0409050706030e0609150c03040c 69
    0x903144006c00010260f0010504400301c0205018910100300d6802d00d45d4501d42503510010402c480080703840c0c290703c01309007000705921801640d0b01ca030303040c0031030394000815030782054842d19988034510b10350380c1c03004580070080382c401c00b500b54040101180b4041402ea0742d87d05003e000381800f107015011012454000d01001c508000141d50106d0310b6010000700000e6494048011702c0c20b40040c1c01204002181c5012403d40c061030b00340c0d42d1104629035118407080d030340400520a00d0b5847c03480c0c1420050300c958801d41044038007915100220b0b01614101842003161304407401c0001c01481410040001080050b2003039480300e0680301904515444403450b4075180d4040d81c09035441d01c0205943c2c4a00d8410b40d0002e080408048824400460440001d4000c0360305910340450011f407804007040040072b0f1004050300a01480301e0100c0c00030b406070845003010040f48110b502c035940f001c010356140c403c244500d08680d030107800460240041030010359006400384007020142c55403a4480c0000c51344 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 941812868 1250 941811618 941811623
    0xf02060a0309020f030a080a050307021221070c0803130606090231050306040b0c070f03050903070b160b1806010e041101360b03040510240927 63
    0x1180c451520440c14a10350809110310190300410b010121550313019403234098002404200b000c04000154401c3c07082001d81030f20340d0401c3c4c00caa55100201000303080045c0011882c04010900400319032094482c4a0110a00381c00425a07400c40c1c8815204110314100307404155111912a1008104c95205100500c682a445800390130b8400b12903060b07200001c101da01206c07044a41400400a0361400700e03189500640c001009030403581c982c6c0c0c4078202c9000340d10014100c0c15142c4621410141c1240040c5804141202180c5460f40e981086c04803074424041900710fa003142030b088000041c42800d400e600005e5103e05654202062002546802c800b40d11605503c00001c09101c10b000d43c225900c20326680c00c1c40c00c000d03c4090404c40720403000d4400d4081c0300d140000d601840b062004801400041e199100b150b030303620308050600d95519141340c5202c0c0700321403420300000214091540801c0e40507009801e030080031841c0420b4000140b80c90340800700c0c40001510213018480303480a482c5030207803 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 941814118 1250 941812868 941812871
    0x7140d150f09060b07050307020405060a15090603060f080c040203060f12010b01080c0c2a0d080c0601090903091202060f0f1e0c070e090304090c0c050c010c030e0d0f02060a03 77
    0x42c6044040c42c01c1c0d8440d0780c08080502c104110700c0021807004421a0300b00c130f030155408100c584403400482d0040201c1d9100c07841c0c1c0c60040c0c94409180f80c1c0150020222a1503680074020b040d110b29072202590f4862141c05465480600b00c00c1c0d080c1005d070095070703000c00000d10b46c210405246c40414060b0101528014480e5580c01503600744e0342e08403003190f40103868490030380c1c1070080d0f00144c660f45200104c8681c03090b030902400d0160480508485a0070340202030005052098079251403001074204a4020440340204000404c0e4201140300d900c0c940c0f5010354911280340d24111501d1340b401002803044ea00724104100744041940004000c004080c2103025066468901ca501c048240d004690004010b080400c02407146240005880c0d083c1d80c0c90181d04d0085031141c51380e55185100f60791040702d9042c14080c00d054090b411600042c4128020000c0d40c244d40010300c011250302d402c402004001c40c109140d0380b034650070100b0f6184c0e001d40c800c5903942c0300b404080d0000f9516400403241100000d = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 941815368 1250 941814118 941814149
    0xf0604030f11030105012c19051b0c0d140a0804031107030c0e04020f01080405030328390f0305060105120a0f11031303030213031b030b0108030307140d15 68
    0x3082d207c0c981c010046940b801010090801d882c3c0508003086500d604552503450702e011481c0c0042007500a05904180e07175007648e070350352402d441a031074100c10700c08000400c2034010140d0740f1500c810119480610035503106180c9170341c0d999041d500007000300221840351281c000d020001865604996010b450b5142102c4078514051041020101c11904114100415213041c003001400002c03d40b030300500d4403101c0542542000c04402901444d40c410b41d0038042c1400e40080d190200c2c2c1450101d00421904401c06070031500381c40d800000b0143d200d600001d1031200640f038070309109a005c1034000b50140b4041d40b820640813621000761600780e4400c26801d50b5000c882c40d0102c0113102e481c02d00c101d4900c0550840c40c000c20300615070341c4401300c00b409060300000d407000d581110350510b04c003840e03004001151510501011940076001c9020803100c81d101e8100200e8450302c00010303244540e49642e5004040951003001219030341081c828860125120200c0b4540fa00f1890340e15005440703950307010741e681e = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 941816618 1250 941815368 941815409
    0x20f0703030305242b0614010f15050306040b150d1e060614030604020f130305060601110c1002070b0a1e0806010c0f0203150a0e0c0f0604030f1103010501 68
    0xf01c4160803081d0803280c4c02203411407562100c9034031960341d101091500440c1c0540c0500100010311148009140d54640200580400310750342c40175059506200d020702d0000c2e1070b4540b0055810012543d81d0202c2c0341400000c4852070103800c0100380050240c441866000c14001f02943c54100310201c8103240d0302c4003051103000d0983c2c005483c0174881910248541e51412502800b003c00840401c00e1144000000480703907100ea0b01283c3d01b0a400c81070460369400c2c48095081001034a00040740c5500400b00424115880380103003c6840d80d080000c1d220594183d0f0402c034000c8415441d50095000d044c00c00a4203110101c040c241c080016207070b000035001c180c40e0210802c07003901000001e20001d00240301d000e0f640440c0c01c1c244680c0c028450508030780d00d0f00009141903001c9002c090450007034810482980c1054110400c03202c0c0f0001140c8041d000b1004101c1140c0280c0c84071600004207200410101d90b031050b031000701c2802010400c03201ca640a0100f425260309800c01d5021080340c0001094 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 941817868 1250 941816618 941816641
    0xf050c07031707050403140109020a420e030109020a06110c090c043309030b0f0105010813080d0914100606050414120d030b1201200703020f0703030305 67
    0x54440c0c48640e4242c18600102e02410710f010300d0101915480031400c01c40c99020007580071000f6140c00511500c2256038407034084640c084c9240600102988a89000c1140c03079480c010041203002c14060228007140c2d5a808580d005152144698990349480c41c00005d0b03264a11400301901d030658451000d042d03030101081c5024014136605000309082c5003081610b040d14001c1d207080e5442c0c00124030f400032107d85101c9414000a255160245006c103417140d6481c0c210001104413441072485003055524103c8001003034409120317245c0070603100000110301501d40c8080c0d51a40b4031541100d03051641201082e0102c580110080b1040c8080c06803800c1800c408020326020f582c3e42040601c5403034280320300107040c0c3c010343c0700307503100b86252025450782c654581180540c46545801141e2042c2c0004400801030614181058003c60f5652500300d0541018010050301d03813a040d14404140c1442c0000724aa075014007070503800c60241c001901c88004003403003c800298041e50303010850b070408004800 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 941819118 1250 941817868 941817887
    0x11e05090d080f011e031a0105011b02030709020d110c060a1d1917030a0b040608010b03060114030f120a02060604050108060a152d0602010506090a0207060f050c0703 73
    0x501030341804000c2c120040ca20890705581e0118621000041c5d082e0000440c400c0c542c00080090200b06148241c010034480c8440c1260001d0740c40070941071a4007501040781d0354801010790150008981805010402e070000c2041480000001521001240515041d82c120a803a01d80580010303007804088115401a1660500815071039600300040c1011030740e031128042d08224040880b800e407202407040582c003035545901c0f016050340e924031384000040010301400102502c0381d490284003150062051041e0480340303001034014116642080b14402d070300d0b10300e84804d6a1510654400028444003403007240410480c8103803480c1c0b40d91314280040d05041004012a014030326203001088040700004040303811220900000441c0e00d86030240d540101d52a400000751180722a41201281060780c500441868080c04100c001d0303616800100e00740c54042c1d501d607600c01000400b16903410072550050102620901000504410041c125030580d81e0850b1300400d00503012a000041c1600300c100c44 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 941820368 1250 941819118 941819143
    0x60405101203110c10020a050d050c0705090901181a1b070b060d050d0c29041e06060905150d0312020a03180b01081209100f02011e0509 60
    0x2540c14501803101e500c0640401408012540350001e1092106210b0581c10003400303040c0403030000d007401c406507a542c9028001c8405100d00318000c0e83c094410002e40e28030070311100181c240c280ca00310030010204000380c0304074415542d50381a485c0700d601c402d107e459400c1c1300700341694608003642803240c0608030040480c00807124000703e0f1340c2e084020b1011115159804001d071039850f1542808034410540d4050020324910800c180d2441c4242c00070050000280300d8102a0745980019002c5500e22090404004019000002245c00100071068000c40140d82c080e1442e866029610b40e0016a146640061801540d038403d000c004500140e0480391624140c4071100100543d90f401080e0584120326840c0199000c504000c240f482a04035500e003c02c03c160003903660455040c01ca198280a20031075110707110300008030569a0060080d06d85850008154480c0f101170b203d01503801c00c00484030003045541c0c407100240010307911560881c904c0550074001400349041c1c1401c6281c1490341c07942 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 941821618 1250 941820368 941820391
    0x111e0f0d0512131112100e03041a0306012106051807080403120e0304030812010e091009061116120914040c140307020c03060c1c0b010509040212060405 67
    0x81c0c0c0d00e609061a01980c02c0302018039040e81044842c10242c0e0f0340d4402051082d4040d17400c880389400b01c4000500e69054070812042007125003021f00030b5903942c0c822407203011001d0303d8504425034085181005503031300102c10b041080b0050700d461000c000001000034000c0f1043e54641c014025400d12034004c5013080c044a43c1d1824605081da0098010b20000b0001400c0049200400c03000f00815081000440c5c0e130041201c2d01d8648a03c2d100c00d80d03802040742c0311200c00c1070900000d802074100b03c039070b801045c424020740b0b030700740014031000050502840e0031740d0560b440c2c2081d2000c42124200805070351152025210310f00c1402d10b00518806004154542009800704045c002c030201c107005144417560031100040c8080784500141d03110f00601c9100740e0820008010000781d5900810f02e001440c0c3c0c100c09a6005a850448840d094000d031074582d0060b902803001820f10141e02c1d8012490f0000504005042030402c8000405980c00110000b20309486d440070301101e41060f0182e0307508001c00707400 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 941822868 1250 941821618 941821627
    0xf090b0a0203090d0c090f0515030106050117060406030c03030519050c120714030403150f110910091703070c05030d0203160c090f0615020d020d111e0f0d05 69
    0x100296240203107243d0381e1246000182000400c481101e10200600d80c0703101c140705000803000c0b40c030002c00d82115240d0380114000d0b82d840c0b4030304e0107104030015114143c45000c0e032840042d0720007035110310043c41c02d03800940d11080813000c0f0340c0344c2e03044100547c400d50f0341a550b064106881c1491825000040003408028040301081110114058030503079907400d1420303202c40b0719061030740c2080d0605051122a010021300442484844042007440c3d0106000a002c00024800198100d407580140390b4005032050150780190320b484c030305404420b821440c01300441900c90500c00146580b050303407003020f50b00019140c801c100f005c80607040140310807005450118003040c1d0183d12845480e502c80012000807020204101403c807400000c0c003d030441c200801e4a1640d12080149458015120802045803841080700e200140c1d0320f035508159400b81503800302c6114292281c542d01e00900225005a80c0e420f1040140212000380450501000b807580203002c1d0242407c0252144492081220810 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 941824118 1250 941822868 941822887
    0xf1e03032312010b0a021c08180307121e230309150f07021b0310150f03080a0e0f150a0c0515041a010b180d060905161712031b030103030f090b 63
    0x340d0f5a6000d124003c81141c2c00205127111802d6100e004c40003412124109002848258030524540c144080760398404030784080c061050301e200d80c00e80c1c00c1100a1000300b4010614014074006103400c814181c003201c04104114030002500e40040b103540c005070480b2030411421a6041003600c0400542d601514402e901040102e922002c040c004203003241d45440b036200b5495203ca12010042c85d00700340706040c564a0f440d1a0303013140e008403115070024407140c21121041c5040d54010402a000800c1a13900008014100d00c90340c01480010b010700c000d4240c80d5010510620000c29074180182c425241481c0502c0e10b0faa922900307007000440d205031000103002b801e5030042118140501c9200380040301e9900400900300d032209040081c001070824252004015001071290b4942c015000311248254035800b8030030041c80761003000c0324103074030035250152600e0015000759004020814521000b820780c14a140d0540e1080e80f040f0300080e001d5200544155000c0352100240041c0742c1c0c91858941400c = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 941825368 1250 941824118 941824127
    0x111005100902090d0f140f060103201e060f13050a06030b0d06090f020a0306090b0901020306060f07050109022218020d060507021005010f1e03032312010b0a021c 71
    0x11000105403002141c1228180300c01540c00e0b20858030080212400d050420f903103640c0301e040038031080780d02f107584500c06042c1c5003810420319801200580348041c045444030300302000b55401410303103800280800001c0701e40e080e0700c1c1c000c001d28030007145045d00407072401c0d05010802180f0f85c01482054a00144e40d1195a217201c40243e50355040314010446c03aa103818890b0b505094400300a5100000280000402c00c5a410810500380034804a001c6542c0301c0ba00903090784000c845107907200a040201e42c07204a002005490194001d01c00010320008560102d800c0200440505250b51078420010000c2509400b4144040d41805946086840182e02103500f03c0b070002802010a44c075280010241f40c420031506121960940e03062106507500e0200c24103070700c40b030300a040c1458000d0380d0a840608920403d00e0880394035681d03400907480750b2038054202441c0215180e8425100708000210a440500040e0117802017681c06035032410703d49006460300010400107006181080c14006010350013 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 941826618 1250 941825368 941825389
    0x3114c0306050a0902040e1b1c0c12060305030301302d1104021b0109031d0d020604060f121542170406060611070e07030c11100510090209 61
    0x98100301c8558201c5240140954000c2591090800f27010440c41000c9410003c5050700ca0b8031008150380d9107000090030baa17002c5c000035141d90f10401c0108000412500c0c2c1c529242008103e00d07003031000010420741c6172803804070141c80041501c0400242103050960341141100135580e0120815000c2c0d80340700015a0320785000788038650204641207403180e03004010091008820007000140d440b03140284c6000740c0c4040f41e114501c4403d0b400e03c0b0b070f41800c80d103500308603400800c098201340c0b40c92021a4022082501c40c000c1047c00c010103181c02c02d450150054400321a6040c00c0f130b203402e040403207880011242c8803084004a1000304100f038412058040450384e08160401580420b08200350b03505607040c020030b540321f0529010801801041d6200c41e05039946a5148042c540380003d0040e0b44e9030b0240140c00c52550107401082c00349003c0d50100540d5115414100700c0c0036114800307030341058449a6443c04580d218010001c0390a017443c1420701415607101c00b1404c0c408000c020070030f5901c1 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 941827868 1250 941826618 941826631
    0x4110d0c0912022101020703171e0a021b1603210c1218081b0f03060708150d03050a0207090c0e010e190f03114c0306050a0902040e 58
    0x403075920020301d100301a0fa204404c00e4000255654a9280740c000c0107400150445c000301c20741e50000c9520044048028031b0075403803c0c9040e1905456401c4180020750010040a910407686908000800f000b88090100e6014449004040c00d2450610141428200c89500a04c0045500307070080550414051182680c00c1410105907220988064801170000e4020f0461000b1100c0300040080700001c1e54841010421803d08420b80c03190103200a03618a4a0010f074580c125000040c1e00d00c1c416000650320146a601c1d8800000504002c50344c440c1140c5801e50000d8400100041c016404014660042181d18801c000000396020f000741142c0a4100751410000c0300c00c044902036950000007054130144001c01c803103550346d400d5203450004c2d05100441e416001145c2110003460460040c002150702482000301c0d1884e4100c80c5e2003170141c5400d0a04000064910130781c0b040d1410403900000c03509a440000386181498100304030886180d00103d86280100018009500e80c0451550040c8 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 941829118 1250 941827868 941827879
    0x51203070c0e01050631090c0e040908070213112a07050a1e030512040f060801050307030f03110f01051503061902031012030302120606280302040504110d0c091202 72
    0x200350b921403011b01c2060780f10b002402400590081035080b4190700c1034110f10504e03161340445881d5207040c881aa201c0c1000581014414800c07100235081180340d82400c0403c050000614000a540c448041e4104040240300c0e480e9044003000815100c00c0764001c510f5490b8010305855140c04001b42e200e13400d500607440307409241c80401e41089107028258010b10350101c20390b40f004c1c0d02142c071041c4e590050303c80ea403800100f10100080d00b5002e180d81d18180c5001401401030281551500d43c00654000d800301d0030042503896038450041c0a01c900d0705da0480c00c01c000304071410009030a004052445007014881d4000a040c4039000a0078000141900c106c03201c00750f1603580351600c0c07a04502e40307a40f26070f8200d0304d0920703280109981503008001c04c1c0c00803880c80c8a982c4450f420f00c10300c0d014040d800781c50703a08800e065a402c21882200300003c0c0401c2c2c81c02515064441c80400c0546003c41160080e4006c089840e0f0f0001d8043d01414403c6c0c5410b02d00310342d0451410682c42c0c007501c600b550290044 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 941830368 1250 941829118 941829157
    0x613060209010e150309011103070504090207150207050105060915011b0f0212011e0606021908040f09051801271b06180902030c07110307051203070c0e010506 70
    0x241d0007625a0240c202c3c00400480341d8000500c54031000703600c1181c0c1e004c0d040d4a84401d03440e40d482c148003502d00035519591140e0030203081c054404000e50044001743c40490072000c019034144d40074001421001d02c80c000104d40c1d82000c2c410b101d070210000c2c001c01c0360180c04030400d03422a60720681e581000607c103e01b02464904a0500480c50450400c01940003400e250114003800c5c0c05411180c1c101e903c1d0b078a41101c821610104004550581c0100001a0020046103030f04800340b00c40300486038002c08066241aa980b841c15028459503070201c604140c9450400840213400d52130b400c94000c056000b400041280b03600844801e10000c140080798080c03038800014012044030429075501c5401040c410652a10f0f8090030103c0418041e213030010b00e0703600c0890004424000d0320300807188011101d00317112650340c5500e0303c40180b40c1c0440d010310401c100054242d4800205000e0510f2150107550b41e000756040110150209811003008094540c004029588681086802400c0147d00e640e81d003 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 941831618 1250 941830368 941830387
    0x112020d0212090322050d03050c0c04060906031a060906011209020429040e19031812031704170f0d060e060a0f080604020f03070306060b091206130602 67
    0x9010707607001041c4400c0c10404010b4054800801000e20390781702c401540e00c3c0b0014405d814940c1003240034045e000048811a580024042c0015080050b9414165040b08010f0320205085903600d5001c241004c0d201c1c1c0081061154003144414841170440500d9081c0c84c000c40840d1800d80d0181030641000b0342489601c20540300d96004980c0d07564020410b200e00041c4480500d541d9650a080d2020000c10007068201c41c500b0348900260079100d50080e0001e107504910f440c0d82003031190b000740c051100c1c142803070783c844c0e501c0010980030300101c10b074110319103070141002041100c500d00304200b1282014140000310321800b07100064240d4074542c4030b0317540103148844000c5000f1180d40030000d40c106400404d24901e1130340002c0c8a42d00a94201d0842e0ba41d442c1c95602c104007a100d19041c0d074000c440441e025081803552080c641001030103c44c001c580e00d079a03440444150f50700c816100f400c0810074000130b00e820054207842c080d1441c0100946c2c1881408c51402c2030034004003d160301c0e40040c90580c1e = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 941832868 1250 941831618 941831621
    0x120209071404240815120703050f0106090e030403050a330b12070e060d0305120a0609140f190612050a0b0108011b0f170a0c0e0a050112020d 62
    0xc101d41c6001000e4903240e41c0d540f0703200c030307444140407604030154150901c40303543d842500b0b500d229560200740d14443d10951340034010020303178007148155540600d0380e0110111301d04200c03009616095000018807903181c0700c514821152034032004520303900700700030400100c0c90000348208410b401108110f0b40c076244110013002c501004402d0002c441c6441c80441d41510740b54400c41c0c00300d0054a803001c0c1c040302c07240030726100d00c480e0040c00ea040e140b04001c0b034800d080502101460030720a040183c544036240c00902400c89044038a401d00300d45840003405440d40e80c0c05490171040c0c0c103d0b045085030070b1042014201c0e0348014030300e000c0ba640c085040480310880c2d070440030040890301d034001c0076503e85003002526000d05880030340344603c1480001030108414132403050b12000d00c0815181443e0610000c0320100d40f0f0400410422a2a582e02d01201c40c5501002d070044103003001c0025200101c0e007020b003900e20728a0044c1d2256200d8601080140d800004030b5240b48892807005a9075a0003518940 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 941834118 1250 941832868 941832887
    0x3060501270f1b0e030601061b030e1306080f0d1806050702010306030c0b0406141206121005010b0318011e0b01030905100b030f0c10120e161e12020907 67
    0x3c0d0810094002c104104d410240240c1060380550903280700e1781c3c0300d80c0c040e103c910309c4046220280c543d400700740e404688604119a5119401041c0010a40040b4184000d41d95260042045070b08014503291480301e003000646556482e5003000c01e0320301340001c0025415582c600c2003009000c8006651000c6a10a80c41072000d180e00c000c10780c003802e44818450034160031078058040440e400c49010841d6031940d000f503544504c400c01070314085580d04010722045031800040e0f0f080c1480703070041414011078680205070291081580407500ea291000c410340391005400d000101d01d03490440440c000c000c0031001d96030000e502040c00718120580900481c0100b420900c084d081e40104c83c0c00b44040741980d04044040002101100c0380c00041d044541e84405100c2c80c2c0541c071031010a06450028014108006002445000054003c9440b41e1071814840c00c40c40d01d011300c0c051104203214409141980103000d141d005540d1031000e050803070742003440d110303544041e11610740b01c40000c0ea9a0f10416144 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 941835368 1250 941834118 941834141
    0x7140d12080106030e0f0304090c140708030f1302010c02270f060111060712051312020c0301150f0515041802040305100504200303160c03060501270f 66
    0x350082100d001064081d080c0200d00002c3e0512000c041d40b40c10015401180601d020090b61519150078803010082001c000c05000740100745c6010354904c901d82d8042c2071454041c03450180d0740e10344001c0c06254420010003280502c141c510074070340540da01070085600d155054450320104035940c41402412542c01c0d8512280910a80801101400703442c0c0e5103005020a0701c50843e0f19424003209601d0b540e08455a000041100004800600460700266042818032600c0d0000d400d07a61141503800300d03800b0341c407409684040b4240e69642424400d029001e50b800103444503186c10018107080000a5204841c405c69592249801590700c44040360f0050060006040c48003580c010801e0283d08584001e0b0b92900a0340444545021103004443c0301d01d07030150504c240501420303820003100f6980c58070345805100900842e94459403ca240c10010760040c407600e0219813440c40e0840558a0582045081c201ca42545201809540c1c41ca60100c2c9600d03100421440d00310b100040080810442c3c8 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 941836618 1250 941835368 941835383
    0x18051c032903070e0f0c07031419080f190906150e09010c05030f060111010f020d020d0b0406050303070b1b03070306031b08030f070201050906031e071107140d 70
    0xc0c1036000c07455085140c03201020b40640f1040b81d80c0301d040c800c4a5404035015107502d45280002180c24020600900310702e031080c100b25111405004104c0e00ba5041032504c1c40c0e04074490608045d0403600400603d904c82410042202c9510305a080310707090710104103421100948034210b240802c90303e81c12200c034a80421b0005410290b403401e0302030007001c043d00c054005510f03081d07084030010300c90700c00c8910865001001d1201340c6c61f04001110880c402141400b0655130b250080c0b0080696800107140b1013201c158090b03100c1c440c030080d082c22981c20f484028451403405804020544010050f01c681c035800c8010b6140e19a119800c0b070141d00761400c0f40f8402e901c400010003140715013541c03010007034a0090f000000f0140326050500c0944019020b50b881c1d66009100d10414a03d00000030848544185002801c00004a01080785c030f41040d44c00c1c1000024104400c5170043c0755080240d4005003d10b40800a0130143c94800e85505080c00b4021101100300c58104094807010350402e01e1a621841 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 941837868 1250 941836618 941836661
    0x1e04090f0e030f090f1e1002010b090117100f0509160e01060305090a151b0f080105120705090c0918010b12042d03020d0504032f030312070318051c03 66
    0xf205843c121b807042240d4402e40403098580c0000740f05210f84014880041d006003500d03402e1900000d03900c12007050001d080d1061183c501c440c1131a83c041c0540403041d55002145a040c18400c850030280d641038490003405000c0c030b0070400d03200401b50b59070440d000c40c00c00040c20746450340c00310304240d00024041c14172118810340c610035051780e6001b00c1e000506803910102ca100c0103002120300c011010a02800541010300620851906103048002c900954084a003280c2c2c0e6600401c40c01c1c40c0886038401d00d00c90200d401005030515442c00b0480340b586025a501d550305140c5403c03036030300031461052a0079000c0c5d030008081158418851000d87d050301040399810340600c8841d044841080001c0340140070f200b03081300019000b0710645059941c848035411916444417031559280080005042c1a0603050845c403520752014401402e407518543c20703070200f500c2d040201406132000f0201328002c10b585000000040f0b20049a800102a22000384180d200d40468085015143d044150785000d8003c41 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 941839118 1250 941837868 941837899
    0x1511030307020a0b130b060f060c0706050705010c110304140f060f031b0910081f0f030309050a031a0603071e050102100510030210051e04090f0e030f090f 68
    0x10030508081c0b04120451380c84c4d9130780a890b4402902c62500030040900c0c10040351a43c982410342030301410028240130b040c0541030030141c1c90082c0c2c40e4401c101041c3c0001c0c540b0288a82070045816243e000c0c20440008010407400580d00d20540c0f2502c0c4400030a034132009560760314400902c8444100418590b1100500b850b029560341c0150b80708001c401108000c1c100515026080d02c070f902500a09100d5820325000c004d03240c2010040418a0343c0450340c50140082c0c00300011a400b90001c00407000d1154203524014020801c150411131107026104001c00005801030808942d020908032404016101e64022915054071034004041480d4100c02524484440b02d502104580302642100c1c0101d40021650045810a035000c01038510280018000341c10000e00c5508a00ba1524107280380000f03054261095001c0600d1940030210006000c0102460ba8010303110a0340c00c0c0740c000c0101c101d10f0300c1400d6880c070035030300c1104039010301250100d030039581c1901102800b00064170b626203454800 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 941840368 1250 941839118 941839123
    0xa0b0703020d0501170d03050705030601051317060402120106140d1104092405102903160807050a120e01061701091211150604091b06090504020f0301151103030702 72
    0x905c20040364403620302c40d05a45442400758030b02401c1039031185490340e201e150044900354003260a54050100520000a4818007e0180c455011016000e071000d42030510400021400640700040141e0401906210b5043c040c91000620001220013130010400d502d085040c0c042c070000301580c03240c0f030142d41200344411140341f81c10700c03140b8000280300b034001550340008840c001c1d038070b1060920209005010048100011054040c3c0103444083d4054040e01c601d4420b6001326650501003042401d000d460300e80054080b80c20454030304041e410941a008000c1040e42600c00c0c0200755a29a00440d01d604401e41c8484090011a4848206513090b0a007282c0a80526002101d402081c002031540c894421320380011118400c0c0058040b90819802070f0801c0000035040d41d41c010369031900000000d100c0c440c10803410341d05410100180f4607188002c0c00c149010391146000d1401005004c41c90050f0300c0c00c40e415240d030384810320440302c0120401c42d10b00000f4840800c0c1c44c84008103005465400 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 941841618 1250 941840368 941840399
    0xa0506010501030f060e0c0c010212150913030807180b0a08040b1b07030e0f041a0301060902031e04050a0203010203040c0e010911041203030b03030a1d120a0b0703020d0501 76
    0x80c3c90034801c0f00120601102259143c0c85a02040c030303141408035520098100c0107109043c0d540c40098140700304040a0500c44c1d8081d1949540445080010f41b21b5042000070154021031050b000f08880c98a620060104c40005000008028440751020100d035119119a4040c20310a04c20688940001c1030141854105441c143c07001e01c00301c0300040b000d410341d400040c038105042c403085080072103580d0182c5800043c101c0b01940310072046180f03620b648807485511a516042d00030061550006010f140c21074541d50440d40380300d4010070070005003030381190712800d4100c000b4405142c0c542e19410981c4c1000803d1fa00294107500000500c4144203040481070141d902d10105490386036030310340307014040320213201d000b2080a606000801180003890540b0790b0480c060f0034045440c0c8419400030781036a01c0301c00070b01d02084007410390507141c045a91040b10452803d84100121a260301c000c5661141d40d040010400a0ba90b00040e041d03a100c1c0d0140c5000d0500d900d018486540c4607241c248150b5030 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 941842868 1250 941841618 941841629
    0x50a060c050c0709061a0c0106080a0606050f03390d0606030b07090501021005090f120a02011116020d0206120103050a0213021e030a0b22140f061903050a050601 71
    0x1d8404040303030139142c5129000455001070f10604401e4030801d44000030350840c00c42c01d0002e540e55400060341403070611160642d00c1c42140e000030010b00740f508000244203801d0441d80280d000e02c0030742c04207284010003965070024520030701701025042c4080086040700c0920164102c21806c038030a0401020750000029130f44294a03030702c186e5403a02800c40d0218403902c1030340e0040e4041000c4a100811640c00540c00c920f2020540310403200719141c041c50074040030b4807071404803000103849200700c3c1d081c03041d05444809580c0d101d24102811010300050303104404068402e1031101c040c4000c40da51001124100c07600580301d44e24642c0d4a09245071520f51903030303050b80945960401038406d81e96900c01c6031a1808140000240c030951030481e40005d800c01007010441e60394420400c1000c0d40e0b001001c400100000c0003001c0d003900c007000028141c0319114544c0d0b41c0c0540c610184002e0240070412a42d0040f4103403a10440c400c0b200c115041164031780c2c0e10140a0f0300941c803041041c40030218402d4103950 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 941844118 1250 941842868 941842873
    0x160f080304060e0f150a06030206030f10050a080c060a050412050606100311030412020f0f10110f07030e0609090f070e060412030809010e160f0501031116050a060c050c 74
    0x314002c1a207485401e11610807840d03812170b08114690403d144c25068204040701d1300018240d88aa01240c1d0b02d61065a1000005402100304024604003a5200d8050102511a9a0410301e452103d69803031903802071a512800c00481c64440703440c415410f0764000c00c006e0140701020308007810410f8849405613040c40c000d030501000640250b0190142e00c0f800702c5140c41d504c2c03070b5688580341c01c000e03804010145402c501444c1e071400c0452070208102880030762281c011740b0100c00104000021030351541c107002e218400c1400700d030744105d081e50290b03120031743c060501021090140001515601c226110345621481c02c8040c045500401100d452180c400c5484200a410b2a030b020070006010301d02c1050310550107900c800c00080d00c145951904080300b02c0010903200b285804403407c0041e02c0070035540b1414880fa0421644502c0c2001c080200820309081100d181c03181c950103068855200e90306561800c0c41505401c0000c01c020011800d60490000c110100c2801c40060180e0301150a44100340b = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 941845368 1250 941844118 941844131
    0x904110d06170606030d050301170f120a08061c172703011d060105040b03031201080a0b100f0614070c271107020409050717030d06080c0312160f08030406 68
    0x1800e00042106c5440c51039110681560300c2c0c1250303148a800ea00106503002c0c040c052a00c1d884010412500040780403c001c1c1c03e451b20007080300217100c034000400c00c92154080315045400c000d415a01b142c4000d4114a6680101c400c55600001920860419030200400c4000018110b504103078807105004c0128001d100c1c544d40106140100c0850240440544d0005e10040110b0b107030030f9028481c5868090180ca06050001d4500f42030301c0400d9010303198a03009400c10704100036401400d264001e03640b440380e1a00c54100b4034400f407000310a00469046c03044420344c0004c4600ca02003a29100766000c0c0104a942ea00d84d030005511050000c05582d108124001e01d54081d5194021880d8035904004628100b12603034003004081c01440740103441c14040c1810108040e1042d4200070003200f05c1380c00450b6101d9203240540c040700d8669014207102d0304001c0088085541c0400d241703ea4040c0e800455803a0600c00e2800d0600c0c507240c070001003550381e8051203081000441c07409540306a005004c20084c5 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 941846618 1250 941845368 941845381
    0xc08070309090f02070c090e0c0607060c08310f08030907060e04090201230903030a030209030d1d13020c070f0906060c0201080a02030a020d0f1d0d050904110d061706 73
    0x180c0c051458020540c0d840c080f0240f045507c6c0360301c01d0026564013030440300e0421014001c04c0e203580c03180b00152079058540e442010290340000348103400900710809144800c0014a10b00031030310803841d111034140319050f40311050001041d0700c0170000c0e0b0030619040e501d0900d024003070b66400d0f40e44901000305a20503420149890644992450303242c041e119011001d00d2188032503007130141c0380046e440100d42031001e82d6040d20100090f10a58440e42c40c0103a036030010340101407804400400325000c102402602014101300031600c0004141c054400680c440468240701d4040d000d000d03074580840c41101c60004000c5a110054821152228130401200d902c034401118100c00181002c0d001c51944c1001c180003400681c021a4006038000c5c00600b001201101e4606841500c3c0d020504a41c0310203030a00782c1003120060406203031400000f0000840c0080e8041c2c014003810b001e05200d0380d5030301220728030300c001c0c030b02154003203a07816204000c95a1a42502d900303490a042444146100d5000060031 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 941847868 1250 941846618 941846621
    0x170912100c1e180b04080d2a08031e1f0e04080322020603040f20010206062223180703022e08090c01030203061806010c08070309090f 59
    0x10324002d003010840e80078040441030b40d491624485a1030b5032191001c000484030741e940c0150000e0520302029007005c1d00103c000903c07030913086210400f450603040c2185c1c1b0941c050303800020f10700d5002d03403265183c0c0d44036604001c024407801c02c01c403504d2040e881042100860544400300211540640040c21a1654001800d6050840c2c0052100030f00308003203840825a1179403640703020001106c090010966501290091f007040d6030480341c140940d00c0030741c200079021400040724001c0e001203080603544440001e40d80c90700a08014001c0e00c1a88440f148000c4100820006181003002807081c0301101b446050080d00361207290346868a1100412a0b0b43c60002c0e2807020300001d40c000b481200d05607002c01412000c100c0c40d4182040c100c404070b480030480162a03844814587d00c80041034a8191801c0e81410207500d04907040510401c2000003d990394030510a05403c0403240011039036800380140c607a00018403014044c0d8001150b020105988104078000392101004140f0900302c0421900c2c0 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 941849118 1250 941847868 941847887
    0x30b07120b0904170d090809040b100f03050c0c01060b120f07020d1404260f010b030303150301140108010b13062123010204080c090c07170912100c 65
    0x160b1164042c0003241c0480e0805542c02c16144040118600d48809104480110b820641c0c04403074000c004101e08140e4501403082001150003564069005043c1d0000140310341440302c44070061560b1480401c0f47d50a23071000350351800d402d403002080f01b540c03211081b9905412111503603410f91001e20029010715142d40c0d5a0b03000305040e0300240745081c9559000c0e00c0302c010b141800e00c01000103000000b50400c1c2c446d00038032400c4d4140740c05040341c0039640c0b00f10309000b01d602500c034090303050150380150350303e001089a911010b007401240030000c007440021b000d064514111313200c041100c4008100102c043d84078031021441141c2014013103a41c03000c140e00380e0b042032052050440d03006038802e507401089160171040910030400000600034408410581003030000300340721142c4d030204050060070002c00030400010411122020b00d8034110052001078459120001e0032201e0144c8a105101d00c61019129644402081c00003184d1181c6a0265a40300030140910824204100610301030b004030307070300e0 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 941850368 1250 941849118 941849141
    0xe040512040f030308130b040303050f0109110d0b03010b040c020d0305060316120317130204110f03070c1104050a0902031b100c02031f050907212901030b0712 70
    0x10b00ca6140707035071016280c8190090000d6009201c022140b07001038425400e40b4800c1c0d02c01c3d2000201c1d03040603140c01d0001c5405030800f03050181b07040220300d8007201e1041540d02648000201150280c0301c0400b1030f0240604201d020740041c240308540b01c4d41382d0041100f1091402e00d40d010482940c03040704260341c9580a00107441107103140081800784018103039241e2001e5004e070034520121120802c4081841d801284c180d44c14000041501c01103141070b003e0412404c540520301030510032006000f800314070010703002c0010301104141c82c02c01c000c14651b4141800300e00800402441c903201c034403040542000d082c1284030340140031030050601e00c0c9080301030082801400d95243c0f402c41c0901030b50040380d804070a0b640f41c0b03c1c080a5001e40b80e43c240300070301c40100c89600450315050601c00186489500d8005602e0800b20110094046488080304d1b03110540114031089040b0041d00100d00d060000603020000341d42100011041c0040d0340c000500402c15030f929880513198140005007180c100044c00c = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 941851618 1250 941850368 941850389
    0x1021603111f0504090c1b05060a0c080402091329101707182919030b06011404080123070207030803060f0402090d05101103061f03060f0e04051204 65
    0xf8032517120180d2181503440740d00c0c1042c0941e003400c4079002114440d07102e0100c03051340c000001c0000d159098014030703c0f014410704261982e030030168001080e800c0e0003845602c45400f11801601440382d510001400d282c3c6244a03503003000c0d9000100400b11008880c481601e00343c01d00005402d600c1100a198000220300180041e80d080420b04020014480d814010080e01c50589160042c19a01440e44080e059640c40802401e42e800303005a0881c05403201031030541c40a02040402c08001515620203001d00c1c101444195002c2d0510441c000c41e004501151302e07004040301c41211218800455018034680904c1c00d540710801282d071602e443c00700a100c00380c1480850900d080801c04040301400c0144090708250048000c20004030000000f500c2d107170b00ca81201009441b07103200c1c40c400894154059480c40c6000c40104040141c84079040d10480c4d03840c0320304141284a60702030005460b2414180034000d0340c5050546032210196020b032014021102840b20190b00c0000301c0c0c0442d000c5180703 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 941852868 1250 941851618 941851627
    0x16140312031509060609151305040b091801021b060a150b0d0902060405100909050f0705030f061503180c060412031b0807081213080d0b01021603111f05 67
    0x1c0c440541001307802c103078002e1024009400c050307403a1143c00070b00340e11011030030780c0740c2c2c002c00c440c1c01000b40700c1c0c2d100d030740206c0c075000c52640d858480c1d03d26641e0110b0101c3e03014000b100303c40c19560081c4184000000030701e00c090030b1001070040209400d40520007510040c0b20802c094000440f00440500c5441098001000400ca1840c0300b034206110003400201a6403e05d6903c2c80441e140c8042c40c00709100050745158140b00140044c850144c002c8840b400c400322901d00900080e104d8800544080000380201000505d0b50341c50207490382d220100c404207035860381048401408540350000c00085103018400403082d482c21300e01c0039601110a0b140310000a22400e8405460306660000c00b00c207400b42220307800d40402d48420003000300c80d119840340f9584078501690840c0e0104054070030500b481d00181c10a01155061080e9844900c44681c0001c01e200c407880140e2a10300c100440da4500c01480000005101c40e80d9400e0700d45080c01d8400245000e01051b6444803440c108070690301180d001c0c40b = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 941854118 1250 941852868 941852911
    0xf02011701080706140d05090601030309080c0901140607210f030b0f010309170712120227060c060a090b130807110406080a0b061306050d0f051614031203 68
    0x350540c08010070080c5400b41c00c01b5050f003501c0e011200b902c19a40604010401c02d5403144101008014030009040b19001c64000958445018403c1c9010301e0702c80c94148c0c1c400e59405040b228000e50140b00d0000401c0510007525901c40c40300090000301e00c900b40c1c0c1100310341c004d00403486030000083c00c40002845500064000f0b000706201130304c52094050f802060510148000d18055009985c0354440340c9401100515103030b009681012a280140b00101040751485040e5920020b14903114083d6400c1d2004100d46004101c04c6141c0c502ca00c105110104000740e00c41424039001e25076141c42c66503640501c0006100b0200020046c0808010709404200d0352030744e44042030001840031510360fa03101100c610305041500c064511180c00024026180703001c2803030501d001038100c0e05110aa03e0800020510f004003400508449181c445010130044180442a01c922140c104200d03100d460310000000c1c90f094640c054080e01c0341580300780030f44640d4170980307110313590415400f410b9140e0324 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 941855368 1250 941854118 941854127
    0x181d070c050703030203030a20090d02010e130e062512110a26150f0d020411030106020709140115020f03040b0a08061221070f0f02011701080706 64
    0x90052040004410a48001410034804100198000c1d0b0066881e410300d071001200b200c294011b88a0708200350aa412000701e098016181040d03001c030381044242c0c1c034900050365081c2c2c8424079564024100c00301d10b84000c1081d44000350b50b015000c2107a40c140d44052080e06106d11341c6000012201014043c02000380c411402004143d400c3c000208850342200344110b02900020f0b41d210104484a405090b12002c1c880f201d00c064a46002d0090701e0709000c0d0110b4914030114081c07038055032940c121200c0540701c40300030000700b85d4041c1c82084440b102920300030311508280207800050041920000c0c1001c040e0048040c2c0c14640d24001c00780741d190401035050603100c6580c240641c0030711030400c44220801e1000e080201903080b85541e82d88452100141040801044144502c15200c480c800059000503100303890081d0049080064400c140c1c41d15032409200350081051121214500c20040200c18400c61a80f00b030b2221445500c02d140103a40c400c909005005455000500c10031046108 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 941856618 1250 941855368 941855371
    0xe04230408190c02030c0315070c060b060c0304170105190504110d1203060503060c0711010c1209150305040203101808041202120d080f060402041d010303181d 70
    0x1d141c00a203407000c881c03080d1034110010107102002c01d400040400030350805005c02c2e14480c000320301038024a0318414010b0503602c800703080c203020480380174044e20401078294014071034417a00034401529072600c0303040c003983ca0740540a59640780805138401e41c025101400f4450003007001c070340041c582c91107403070005005010041040d10170101c03a059200c2e4680761840395000381c0d0f00480440003200140c45001d0195021340d400140643d000004100c1685100301c01c1d101e4203584722400c0d40c021590400100d50390f81e000c0101404061241c0d006841540d0000f02d95011180c0310f840380020403280900541c1103410032100079405801c0361501c806040d03010fa00400c1006008aa40703195140715803900a10703500103070459041e02c0c503076810480561420b443c2107429944800c1c01401848041e00004002d1000a8061611400d180300440c14941e600c1c1c056a010b41071300c1000c480008000d0000000000c001c0c40309801050061200301000030540c8611001d441241070101941403034400c4200c0030900 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 941857868 1250 941856618 941856623
    0x2010f0509090a05011a0406081303020c030708030d0c3627051513090c0e040302160f0b070305031806100e13023d030c0e042304 57
    0x10401c00140741e80c1d1042c0c0d081d8024042400002450b41c107003c83c403461070000b0f48503540300c2c0c601404108049a8041e00c03481d0b200d50701e030364041000030640c90140d25190700101d00300d901d40039852022584400c000040d0240c9961a94103115101c98680c09448015403424403840720030031340c5058001c128284191100d050010545005202e17a0b8800d4a814540c2070400941c0c0d440c4107143c15103014126011b002e411000c28046140281401d000085400c500840301442c07464903508000244202e180440004000b0413000c0c0c0c07414501441e00a4542440c01121508140400c03030205c0c0404042c3d40203000d40e0712a422080c9094281d071000e8030705810040611082c0340c10000c070108035041c1405164010300c00504403816003420710f0300c52200344d80700030415030a200354103002002590716410304104e880c0c0e51240c80340d00d00355a0100c0340441c0380009a03603400c1c0780e1926003c40d0081e501d644030b0381c01c8407038540d40c0d17030780074569030301000f0944406089514403403924000c0110a00110400c8542151 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 941859118 1250 941857868 941857877
    0x1c0e210313030b15010c0b09030708340b01140a0504060e09060a090b15010e030715020d05030f0a05060a0905010603050709090903390b0612060702060402010f 70
    0x104551400c0c65540480c02a207000ca100040420070072581d03458607500700028090141ca0000840c0008060405250024200004140210f0030340301c02801187c80d4a90082851641c45468200f4461aa5441d000c0119a10b201a03032030a60600e0920007c0074840d40032090040607483d102140c026031407000310166104100240c005003981d500e203c2c9030014141c045040c111443d000c400d4a0a20301c1c001d12001c200d60411281100040464400d01c2c0d0103510300354401460000000101c0314000550101c0350941324600012441c1c5c1180030450b00001842d900701c46150a01402c202c429000684160480c01e42d5440852508412b64202e6036000d00060702c00e51342c0b9640c07030884000340c50080c3e102901003a07448061010b056440140c200180880007014050b030003490754010115980340d0f031415003105c60f0315541c0e55003241901001600200b00c104074003200403242405001c2d1442034030003500c02c00031451080c1130f008010030220711405058018144c2591035400545490418050820030003 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 941860368 1250 941859118 941859169
    0xc120309010e160e0601020a050a0803040846091502160308040f090902060d1d010603140d030e0601060c150c03050403020f0f100915090308091c0e 65
    0x5200c208000400045a038446603150f84c03420740d102000200240500341190846107601e000304a0020320860b1066000f446641da03580ca0381000a410300401f051940d02100c01c042d02c2c0b40d1103090b0b2003c46034042401c172201800a440c45100a00c1e00c02c0680030001180b045201000440c002d15242949089d0718019a22458050780f01035503200c119800071a41e4a102150a00c4661004a0501f014000140c810010800d1940000e4124001e40610a0420b1348a694a04100b4012050b8114681c1000002d0100b81c0d103900c1c0844841c44071600003003c5108588260303041920901840350301070060b10240c48140d082c1386049a035020451029030b10300a500c08041200345042c4144c8840f80b2603a54000b415007010300d0000e0070411040c050082c99400344481852041000c6265041c60b0381401d00012214214a0280059031103104803240c0c880c94001c0c024181a002140700e4403901e0510305030764000086010544174400724400781c87c00503032441c1c0d8412041c209141b550f4001498140e100441 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 941861618 1250 941860368 941860391
    0x3091505010f05300f0d0c170a09050312180402070206070f030309080a080f0601170a0b040e030307020c09090f0a0f05210a091a071e0c06091404020c12030901 70
    0x4660744c459041c80941c4800c205c0909a001440824202103d5240c0444042000d44440d02284001c81044d01261030010307840780010300640c041c00c02400f000d8281e80e111654607205084603005070350743d176842d8450000c40312020b02c2c01d4404c81d50303200e5004180384d0802c012a03c1e04c00e801880c0620072030a250f640c0105001240800000e0078990b012503507407140b5031a102c8551040d00d88082c000c1410b011040c82c4510062080840c02c81e441807a00200160400301d20300002c02034242d071100038400b0300000050003015036001c101e01c06080419160b000140e26070502d150795403d20031700800b906400c200500c0000403042c41c1c500c1c0c62180603e040b60755501140041001240c195480c0c0c40040f8000988a030805821640c541e0081103c40360444a0000484c810103641c03144100061040a40c0034050355a10080c2c00c4030900c05421082d402000303600d5503000f501208250240c1c0304000c60240e110381c0381345014001c44071003400000140096845041d64802e240d0400340040e42c05549401ca808036 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 941862868 1250 941861618 941861689
    0xb07050a0803010b04210201121e060308120105100801050103150306050a0501030203240103080309030f030a050601120c0c02010c020a0b0f19030510180f05010603091505010f05 78
    0x307811312081d070036995481c1c085440302c012510203440d1040e811901200700582c4e00045404078641d400342012960000101c001d61804216010000703001d46441404010b1199801c05055030700c078254000340361a41c840c82041062124070061400142e071000050103254400c0d040f036108a0758095401019076100d0b504c4100b5110304030748002400d40d8500041095180c104401d514203518420040b15903c0e1140340444840f105010190a030400040400e4080c0c60410490b042c074038040c020192641004204400030b040251042c0b07001078910b0001d1002e003400c601c1075070003c05007501d480c14081010790065070642d04038141070381c3c0011200d10000715802080c1c003c00e9004110071071250303503840d060000000c0d805000640d0081506d0301c0100020152000305d12016241040c1001103210801940d41002e024651009211079003800000503c054260304141d0805120b00504c4003d41034074040c5000b19502440350002c04172007444c0820a9003005110810f5100c0012041d4400000310100181d = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 941864118 1250 941862868 941862871
    0x7030b041512060c0302160209150d0f12050a0914040f0c020a06050c0403110d050a0203010c082410030b0a0302180916060503041112100203220c0b07050a0803 70
    0x12002403001900b404000b054030aa84040500703050031810b01010007403c80d1144510b600c02406180c000700800e40b40039010052003a0740000a20001e480269803520711001050789000726042600400404901c034042c0080e40c2c802d12031951000480d61510003001e41114211034807980003a07841144883c28191400381c0c00c3d00c1c05640d0000c26030704d689c61526504490300140660140207040c082400002d1030701c200316142105c211282082c52095041090030050040c0b03000790305610b8110b035886505d0b0070090807841070406291841640c4c9090b465950352014689016074002460004c80d048030740290300100200c4070107031600903a03e4999000c0b13480003002c0782d2010030401d44201003280041042080b52882c1d00b20808103107603e407800b10090441d00010b80003c00070b08100711200082d4a880c40802120903000d01114000e202483c0441d0003580251445620015041240c0e001c101c0030b40c442c011000e610200c80383c04030303180180780b000ca500600004c5889000d20303881000490302000c080e5 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 941865368 1250 941864118 941864129
    0xd110901090c09050d120c0813060c02180f0708090f0304081015120312090524060f0d0f030201110309070602010c09180c140f0408060f010e07030b0415 67
    0x904002100d00150854a55038000c902c182e020451400001e201c460000c800710240307003025861f03088586442d00e0f45000700c80580405140240b000640d55907c0003405000307078001c1d5100d03560080c6100e5500c01119003100c0822602c28400c000c43e60003071040840c1c0d13902524403015507a521032408416800e540c4075074012022903028019444d03034000c00b4401c0d400d5407001070404040c0c20340740c00d8926806030b1054101034280076500c0c0c6d583d000c7c0c1c0070b6074100380c0407903134003005680b118207030541d0a0200d020048132509013070070b0505c000b03292401e22190054140c000200640502c040b01e42d00c002c0e03860340c5035a0803000c554a5184050403c08000b004e1802103903144040d045540c100b0742c000b030031140c1400032207080091005040120081044503410160300c04100801c1c0412001425102001c9030f003a08041c140000440d21500c0b0034080150080d01c5508007603d00684070b1034007c00002c8428000c20b02003403140700118031214040d500482c80e0107030181000c92601c0e50aa0205800b150301d9225 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 941866618 1250 941865368 941865371
    0x31109210f0606030f010608070605130f0303032406121d011104080f0c10030902040e0709091e051228030507020d02070303050f1812011407020102090303090d11090109 74
    0x601c119440c0c117001e04907411200100800a06142c108129607880b154442c8400f40400042e04819055a030b12800340a4004a07044c0541c50f90b4910f0020014005c0d21120072000a42c0349404110100244401040300c1c070030340e1503006800b842c081c40001859101001200d880d40080080f02c1c22800b8011400e0840c10b501810b6140c0346400d190a08003c6d107400000e40b20307044115180000d0761064a00e20700b10030507140016440000340f001c80c0007450031088054840c444d0360000101c580c80e6800c1480f80901c01c842a445821244d002d402d160001d80c0802000e035003160407403407590030501d00900300b2050302584c2188040004e81203c202e0044007501700340025181c0741048101ca0b010800d1800f401c0680c03005005040c03075a00d0003000f90260448100c0e0f54840081c81c0000541d6840880301c0c3c1c210020414484140e0800b5564001c8c0b80600c90346550345a0312000800450042c404c0c0d400351023001c0c0266280c100c1c000108411014082400c40f40c2103031051601d4403540300d2a450502038030340f4060 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 941867868 1250 941866618 941866621
    0x5070303030902030609010c09060f20070503010b030a110402030c040f1211100207030204050910050c090307060906080c031305060405010b01141e0a0908030a050403030f031109210f06 81
    0x141810114000c11b41e100987c1090800b02c07685900c41502d10417504186400f846a03159005c04907005039400d0105864905101c010591048001c21440c0481308100d00030440d00d21101c0070315442e802d8074070340506407250044003400e0078245074004581c072402c1a0445480c1c20785404846031100000e8000016000002d901c4008000031611040380712107088940c7c903602c4400c00c5000b5075521490100034021a01d94000c101550740420181e100c61203400c1e820711040c9460420000d441c2c1003900b48500c82c0c41650000102d550040d245102071710504d5403412007030399170302c10084803590000d4421000780c4440810745000c0750082c41000d000d0741c426400401c507103590100042c030003a03991071000a012800c00802403254407040421040c250015a11501c80e10199400c0d41c01c00c405501031030243c0000104408076660002c02841520300c2610f0b0300c2005800c0810880c2124800c2c5a50b0501d25001c0100a0382441c2605000508002c40c40c480702c00410101d81a90a02041c480404440e900140 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 941869118 1250 941867868 941867873
    0x10c0b074817180f06040b07022209050f1501050108220b01060c020f1f080a0905070e010306111603110c220e0a210e180105032b0e0d050703030309 65
    0x1341c91401c0c0a81241c0044c200b5042c2003221a1620480800a00c180e0504200940c1240002e008998a0100d40c4080007003403903900f07166484082c421071480341400b0704012201e800050104030f5058138810b13921403a07aa590b80c031170309051084020040102a0380d01d4075410005408141060103001d0641c0d440a43c2d4040b03106100f00a99a41c00d25881400d09280c03e44121480c1c821078000b030051450000d0741c0c0d844000d89400117100f011000703096805403000c045422000310325818122403050008009070f245080480041303008004007201e50348040081c034000709200d541488001544503064491200701040000c081444e804280f28501a1440511840104034402c0f4407842d00d00e00061700055100d0340d14090001c01c0c080d181c0a200701d1b06484545a6071042c4030601500402403e0f242c0781e00340148605001709400d00c42d0b02e100c1e00c290581e40001c176483e800703080a44000c95184070014010b18206442d404071110000d41c0040c1b5414180010a5040000030021406a00c000803c2c2d131690 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 941870368 1250 941869118 941869129
    0xd020f04031e200a1a0318010908070f0516090e121e25030504050a150c03111f0e19050304050906010c0b07481718 51
    0x25070902c1607500c180d49610300030880e04035003001902c0e240c49aa00c11410008000340c02c10710a50040c0c1c12a4040003007114544d900b1200a40c0114503012410b4601803508920f00c0c240e800f0b81c14000c010403024005a400101042400c14030700303100c1c03000d442014040400c0c41d02118020380c0628011501c4c2e41e80e1482000050000340e81106070003040c1440d00c81031a040e900c0324103110100801c41480002c24103141107007105184031035544210b4034103940c00c19080c02001c07500705000d05481030400640c0002c0040d2162608141d061103030300c03450301801c0e19450a0745d01d082156007a00713050081c0b2124040043c900c00328000e1600c602c0000081c922150106c0518244800c8801c0301e103510140310b01d0011850000c140c0d422607404881034020350b900d070b4004031200400304070700810289020085c07040003500800c0001d04454042d82d08a2203a01103502c0702441501480350b14005004a000c801d244056682e2410503039014290000300c0884200c84c071926035000450003a41c0100f02c10200020f807414 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 941871618 1250 941870368 941870393
    0x301090f060c0e030a080d090f15050c040501020a030e120307051b0108061305040f0f060e100b0a0e061203190f0203040e060906040f0e0102090f030a030806150d020f0403 75
    0x261804425280c203180204c0d59844202501521140000c9088400c0e030076140c0049102c542e0100032040700c803055180001c140c1440f005107449050400000402524a120546007103800c141e00034002450315072801d0320008801148280c004850710b00c3e0b8844d801c4104018240035119038001c01da46010f80703c0746051f10321100e100904024144003402510b6480210103902c08054002c0042c10b600c461070080006c4100c034900038011b080c4079141400303121099101c100140104415510000031241c16041100c0e4441d01007940035400042c00d201c809c80c1001e0f8142e0102d1702401011488440300c03c2c03a4a103400196483d0310441a02513681946070703014603480c4103040140000c5081c0f5003450034201e03004800809081c05560201c0001f000c658a0350040b44104210341010000d81d400804214080d5020300041e50040300d51703428401c41400c00065891480e909550380d1000c035260842001580d241e0b510720120f5001040c042c0c4022030030b81d80b00a080114240300a243e44510b1131401410b070120 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 941872868 1250 941871618 941871641
    0xf0e0108070506070c0e181f0609050f2701060312031a3003030c21091e030706140a3207140c0106050909060f19021e12060a060f0e010903020301090f06 67
    0x1400143310380310040450094010f091070409040703209030303815158030710400b075080b00200c2c0d820014000305008004030402e01d42c100c2581c042c0081c18031810a003884401000481741c111925101480d00444000c09203c01c820765810b40760481010007150510f0358005444041e0303c0e06002503040c0000303a00b0045511486884076040a0616201c40c00540300c03251702411752003401c540382900e24507140902c04c4410710344e8042c2c020802812543e00700000340008035a0011120301d032802c2d0040c88400c0d5805042c80381c607000240c2107801c0d0b845200e848101400341c044010306c6250f018540c2c0e180c0c2d07d04084e1100183d01d400000d20207240200f00056110080c00d9007400d60004024003040e800355541659021800500d8071510a250040e000001d01c1181d0000e076020030043d4418500c40d014000038100c15400d000c1c0d10f0700c41d490701401c00440d6512407007941d002c01c0c0841198001107018443c0d21080c80014103282507899920340205e400e441300d91504a0320f400300240c9a0041101500c00c0510109 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 941874118 1250 941872868 941872871
    0x80304061d061308090109050d06060305010501080f250522050c0c060403230705030c01060b12070f050714030a021b010e0f0a0f0e0108070506070c0e181f0609 70
    0x40494a43ca07050001080c013500304040040c00d011164010394140c8014000035003541c0e05502d007400c1c01d2000340042c1c0811a0365508003000061502c0300012050725440d0940d02500c80403d500442d03c0c6103004880300c0c420150701c0d6210010b03182e601c01d1194030191484c840c2288618400c070b40300c6c134111100140300b01e1641d4800e21101421081c00200ba035070055150a021608445142c21807900c61304900d081000c0311000034041082041c003202901c11f840c00b80009100340c0ea201c00c111541400399201c0c0507507001c48140000c200c548101040740f2000600d00300546002d10b641c60741482a2100c00c40d9070340650000400303c0d070142c1c5c1000445e41155800da104104800d0a100003000034a51244580c4901000503a2841a0390b8544100c8001c19101401d04404caa0300c0140c200602d20903c1480d040d03000c7c0c00c5d4000750301c0c00c1500c2110b001e540d001000d503c07400d0400488814090700640a45100c14260780c101c04800030800001410301d80c110085820100700301100342c00e44680da00b01c001c156 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 941875368 1250 941874118 941874121
    0x433030c0806010b070609020a0306111b030301080a1e020d0807051516050901171303080c130e04080702040c0305012610020c0f01050f060406140a060e030a080304061d06 75
    0x1e2501d013040d0781c4030650154001c034240b0001e000081d690b5205030006404285000351b0207030a091807800421000038144950000c4510420300c80e0f440f80824414030665400646007500000c40c4110218003043e031840c0440101107064011444100500c04111980c40d0002760020602a007000000c11011071100f8040542c540401007010034403c1100c0300050100c04680c00065a0080c00f01d600c50f20711000d000d03a010324004d070700c0001d21140010140c0116840c0d0020542c07041603030303040780c4043c040003110701015890703c01e407280c40c03420092090340e604001b4007042c4010380d00c038020350002400b1a0740229a55050100c01128580100651a80301c40c150200002061010450034041e800c22a00142c990310201803907428081900800901540303014100000c03281a00c00140c010a41a82c0c100081c50321410300c00a02c11560a80c1c07940410f241c0410000c0c20711500c10400c3c80e140260550740c0d075200a51741c510741500151000c07601940c4406441866100c0074010700030040d41400240180e = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 941876618 1250 941875368 941875379
    0x1020d060b0c070611070b0708090a08060c030105010c1a0a0c0207060c051c05091002010207150e150405100213051801120305090a030206030a05041208070e0433030c080601 76
    0x807440c2138840e8005111034183c584004200030303c0000014606600f010360b0715085483c000103160710030405244190704c14480400c146000180c0280b00e00b800320461861a42080700654490030b0300c48003142c190039205003034a0f041c04100c080a02500151401154268102c0c101900b13101e0650060402c0100072503905000c43c90015041340802880e030001184000c0111048920703104040c1d1003030f006881823048c104040c3c1e0550040100c5030103240b8940054010aa2802c04e940302c07624070040d40e5004c040044414802c0c00851038005219904581c07a240e40750320340c082a03802240b0105190482d00c0030820041c2000c001003030400ba002c00c030500281d0706140b005030544040040203001c0005c04120810a030b21002d0810002d150024034980d12894885110409000121000c44060102c556842c83d402d00580c140ca01950a90f11140010b00124043c0f0000b401250310801780394034a0942d07100b907412070040b02032410a0301c90620780d4660550603e001070040e941d001c0b05466100b079004201 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 941877868 1250 941876618 941876623
    0x105090a09050a2409051302060712020c03010e07030212070614130f03150f2903011b090303110705060405010509042408100b13051806070201020d060b0c 68
    0x191501c115000803079441e14010300c0e004120400040c03c600c07100b201041943c0e2119100c4404451082038113000545d100d92440041e02d61181000303400c09000c1c07000314005180e800308440d901c9880c0c4100c480c01d40c43e1100190a444507040121555080070b0030a00a6081060b688509100703420700030407615150240080107039180c0d4030100070f000e0001c250502006213840404000f0300490342c401c500c040c2c0303a00700b00c2e00800809000001d035901c0c042400208010f00c4c01002c005405440e482c00310400154601104091429090f9502d556905d0300d00d010f0300b0300c078401060740050641c0d803103e603941140303130140c10001800400750040d03000d2001000107640705011601610020700c1c190b5103a44004003c5805449407403103c2201e114980019644031005d10344801c00c44100104403a400484442c4170021071303c410420680080e44120105455019a00400e4010540d00c2441941c1c101359413006040180c1600d98100503500000c032010345419600510028041c4038420a03d02600811042d5 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 941879118 1250 941877868 941877889
    0x506030601090b031507050a030b0409050a120309060908090f1c12090312030e011b1403040f1a0f07030e0607030e07051e090108060601140c100207060506030c010509 73
    0xd803819141c258002d003544051008262409800d0900d60403820086c1002d0310075005955240300003131501800030100d15180c003a07a000d842c0c22401403c0914410f854800400f082000f06c0350501d40c40b610032000141d02442626012401070880d140c60f0840760782048070303410420488500c2442d1220070f0030381a402091081d0405940088500082d03400b0907400c0e111500721758005894404101a041d0310076425400c40a1000c480c54000c014024410001a8621120045030800140c003140d901c140d07292014011904a03018142207000c1000e00e6580f004640d01c118840b501c2c58207140c00703101031099503089407500301030b090409000718114070314012750340e10b0020988020151500c0c0c640508040501110340540385c06030031048110124078144003a0656501c004c0d00038911030f03000040805010030080d00540050f92003500343c80c0310b541480104c1d0014160502d682c021408c3c4216070307a007180300902030a44a41004550343c03404104050508448084480c180481040a4151969030700d110a = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 941880368 1250 941879118 941879129
    0x10e100b040905250e0307050907020c0f04090c0305150a0204030317061f17090c0d021908030a09080d0e01140c0712031107081f050604090b010308040501120506030601 74
    0x406a03501480c0c00c90136001c8544258000403641031304910342d035000c0c04000300c00780c040c0c00300d079007150380c460a01c40015021154040142c00580480d0218070708024a84080c0500034808a8a0b04040d1613001808442e43e104a8095101740b820141d8034818100391039204001d42c2086042a1840c0c402400704036419103070111a80c44800080c24a1703468001ca04e01c7e003030300110300010780c1000100151640d220513410210140c07003c000150600c20002e2402c100d0400540710450070581907085c04140c00d00d403200104006062440420007402c104064000301d40d1590394420780071320380417100c2c0c2040341030000a81009007690900220742d8014020503c243d111025841d42d815181070b44505008542d04491018080603502c05c052552050890415018407002d99000319640c0b00324660340e1510342c1003902070400e40c2d1181010303600039900050b030161001d000440d10028540c1c50109103e401d070001c41d01f8807c0841c05024a5901000407286170510382c804010038204000065514481403140c3c = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 941881618 1250 941880368 941880371
    0xb1207031104021b1203182a21030310050301150e09030f0c01150f030507030f1416060f050412060f021c060918020d0308090115060503010e100b0409 66
    0x2204040c102c078613880568925010507a611050341c500c0316070440c0e02c00e030350b103150060740c4404021415201290b80c814610310f1502d41c0d2543c0039a41c043c0711800314072071880340d40a0004a01c1c40303070403020040c2040000182401940e80c0380740c03101c43d0351607120031500114003036850000c600c007140000324200d07002ea0700744650424007030742c0e2101070300d285120b49150001c00c1d520105031096450015080044852102c017003400081d1749a14a4842d049200e10004d401c907440040c04001003600c28000919041c006d174001c9240b80440b10f809407038002881c820180d60800124104011a44400003992410084c98601c0c80c00b45000306220003254981c2019101507640d018181e42411594100c9861014080322882005e000e10701d000c0003032202d4032604420702c0c10030342c007000380b100c5240c480701c1c5096000700300d4850000309407808c5a403000c00030415980340d982c07102c61001c64142d010709000108040d07030b903582d900d40c18140c011101100181080381031610081047c450b042e818015501503a801150 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 941882868 1250 941881618 941881627
    0x611100506031006031b050904050714010c0c150210060f030213140c0c01050c0421140f030a020f0705210c0d0c1d090303011509050303030a0b120703110402 69
    0x281c10516070a44040003d45011000001c0156402d85903060705907440e00440d2182c0c1e00d07014010000c00c100c4008182d82c000781028412403403403140b030510504062404401021180d90b94188000c40c4d40c20011070800201c100c000030542c10405904a0b03410024140702491400424211034205400000e1242c4080184041210b80350340c0b1104881d038659161003010f0601030016000c0da80702d010700020039400c0400143c182d11940d8100c0f0101c4240448660140e4581d4441c03114049010034100c89a03440308000602507982040384407580320100d0095951a482c400c4080e2034100440083c03030050301300300d40400542e500c0601511015201e026000103100100700c8050609085208003607001c0d866010440508c42c400c01c460742581d07010610090392010140318440141001c6403043c001d40d000300010b03c002c0044072a888101c0030242070a45c021511500004c0c195002166044407050ba200170b4007a4510701003c21040c01580b11024240090039034552042000540050724003070381d00000c = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 941884118 1250 941882868 941882881
    0x10806011101020f03010906030201110604050706051812010e010c08100b1e0325050702091513180302191703150607030306060e012f1504140706111005 67
    0x40441307101c40f9646078803d5607980c40c0d0446000412181c0800d82c0095000d914034940c4901c0000c11602680d08140100b81ca140741c14030413501a8490b80c44a0740403a044000000c2545500c00c800b0b140030030640011511014030b4000743d0844454221100820900c030083c80380c0203001c051040300b614000b072070050380c9410590000c0484401d520003e8003569000040041d4005000482c8914254920080d40d1464000e0704c1280c82d40100c00010754001004004540065440d541c0c0035610300c8082e00c507201e2003011803c048115006240c0030b06070102503071000410954180411030041200c003810104070142d03a1140d40341800020080003402000001145510317000740405010001c0062410765034441c0c07464010068071441c4200703800320350a032511549a600070b56010b42181d41e541e4444491310716482c4a110f17400d80030f10102616004400f10490f401480300c6150b84602e000b40e415402004044c19000d01c1c12082d640640304000d0720a107540c00d03d840200d84072124060468004c10301c1d44414 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 941885368 1250 941884118 941884121
    0x18021503061801060c051204050105270312070506010608040b13061b0507060b090c270402040305060712020a17100512010c08090a02030316172704060302010806011101 74
    0x81e5424915080d110b00002026035201d00c001030040e200c0c20540b448010708075000d0540380180d00075103000c01c0c0c0a2040e071104010070348845503550908007056041c02101c40101e0308007500105510102c00f0005201002d01008202444c0106501d2401080529058640c010254405032180411400000c205002e000d03a0350082e0074020444150001c544922044c003810691203c1b504440450909401501d14a002d1501070300c14807601580354034000694104941564404003a604140401d8918202c03c1d1900d10160004d988a000240414141240301802c00c09502101c1c625141c01041815800c90380962261540c069a00c0c400381c42d5100c1c11141041d000c015003004d5085203048518240080c8150040d05203501035803107251094407414840e90701e032020150b010790158000c001c0d4021115242100660341402030b100d200540c0c6400506a0b61076001241035001c40c500840f40041d25581c1c42e280286015085900308111499035001030585040100aa030500c03c0c80500081002800e = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 941886618 1250 941885368 941885389
    0x91802060f0d0b1e01030b04050603100c020106081c120902010507081b010507020607090e04020a03030e01090909060f0c05120601030c12090c0f0e0705030a05070302070203061302041802150306 85
    0x2041c0740c0c0b4030401c04103495000c19160013001c3c0080d05064244041c0d050600c5038501456002d4090300d40001e0314103003040540781c02e0b02464215940ca05000030580000c1c02030b0320790800c1000810b03d07491380c8560001c2020b201c14081200080c901300c10040181c0c0c0050440c0c20007644800000d0300e0381000038440074446084840c0d503081b5402c3c9010044900e502081c498410392264448400303085e00c40320902108101120020b412900105060010a001e1005c0b88d9450030b0514000c2161b41d1500b0500d015540c14000498000d5165000010b07603035a40c0c01100740441c018a00182001903030b1000c50311030400640b015040c10f9844c0d0851040a12442200c2e21800c81d00d0800e120203034030361503e40d000c070341c01d48140108003a0086020450325204d0940c40d01880075135641ea030841c0c460109440082a010f8800d4080c180d01b0480303240180c03000c0c80114440c40d070401d80c40c0807501b0640140816284000c0e0320315030311008603542c10016a52030740602c0551401d50461522aa0f0302030111348515070 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 941887868 1250 941886618 941886641
    0x5270f100c050f030a0507020f0a0f030303050405060604051e040203010f14090c0f0328150e1b0d1b050904080d0b040203070c15061e091802060f0d 65
    0x102152003403640d8101c010703051450700c10821905000600e04070789489004a2521000040040141c42c4c09440d01c003980c4100c180005040a0b075882c0d0318104be00d40c10790581d20840200e9119810002404000c0c005503600c03c1050310280114981844003442c3d2544c24158100490b07601d0000c98199102540106848114410104816844c03101c9420140004581241d414444d2001400b16424074000f4070103042005070080195040599880c00391501c1c031016041801300340403504000ca80005400c1503507540c0e075000001d40580c1141303118140300c101c0100415020300c10740c41802c5600c2d0f0451100d01a500082140381050110f412210035026640c007043c0c2c0003036102e0600041c4007001c8000c001c041050f40040250b0b8031440140000d9000c07c88440c0301003250000c142c000306000401e5203094104001001072100d844920300e5075040c01c0d0414185103c20100d1003800100a903101303031100b8456025607000402c0182c3e000484130f01c5204044580c840010a08080340b052941001502d4030 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 941889118 1250 941887868 941887879
    0x10303030e1501140901080d0c0212010b2d310b0303070c0501170114060304051e0718090c05011817030901031d0615030316050c010f05270f 62
    0x140d5800001401400480016100312202400090f1f0b8510010750030700160b00b176480b0f9403c0305840d5000c201101514100c802030b15500c0300200c400e02d50f44c1080c0c4130140442101003110704800f075240302210140001005004000340d0b4202c0300a82c1c000317003412200761000e0780804202048501204060405102165094130021440c4e104112558842000380d03103080ea60100c1006201c00c001c040d400d001c0c400c403220300c2c4007040344800500f4268019980035000e40125580540b003606079102d4060402280001900003d07801d100c152007400c0c06280080b031800c000d2001c0507894941e1403011665202c0c1038103000710160818000c01c40c04040d10300824840410094030300c588141d1a803030390710400b100c60000e45420380010140ea00740c2e0744a41d00908220082c000c50741c03555200032150190300445985440207000c041c5101c0ba445c003260030124070a0b4090004501c4410008d080c0c0820104c0302000e201d400e1003122145071054400c2c4500c000301102d030002c40301c8844081261507813041134840c0c021 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 941890368 1250 941889118 941889121
    0x60501020f0c0907271406040f06051e070b0105010801150210090212061e06060f0a0c23011e02072d080f0702100504050f060310080d1e02060f010303030e15 69
    0x5c10064104801c0720b000303000c3c10401c4d1940340104219485a030241010000c2d4806003070014500c24806804503949d0403d200e9201120116194810b0700280022078650340c0f00301c01440b265034003400440c0100919180e031051107042c044081d40307441a04585052380c80d500c02c2c50758107550750445820240d075103070010380d005410590201302280d9a80c3c50300b0781ca07a0b0b0321200860190304101c4100c0700c0029501c2001303828100303500b00468200400f103c0a40c0c04000d029540206803030200e40101254071030400008404043e4000e8964401032240c14140f03041c810f0182e040400e20080d000c50661a22800381e14940036600503040041d5121500a007181e80c0104040e4038444644d0010a107180c02140d94102121300d0b2041140c0d80d100d240a13a903049001c0050700042c0b81800c201840d007004d40b9040700d20f901c41d101e055641c40d10024040d6200010b4610b468200400c803500302c2504003007840e1016002c0c901e01289031403100c0d08188002001c159a030007402000b101c0a00004900c54200e1150808a = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 941891618 1250 941890368 941890427
    0x207121704120302150c0703080a020c0106180f150503030318030d020403030f0e100e0d050f030708041d0903070f0213060b0301080d050310030f03021002040e0a060501020f0c0907 79
    0x641c00305d0840702414036400c0300030629043d4400250f503030721a0301d0796940c003161f40d610310000d0103034002007a0350a00d5034951902040108032003180000c0c0c2c1c1d144100000d1091611803180040c0d551071160051a42d88440003408591030101c00c90380d000c0704406107881202407001444e407451155100b0f0200403032010901004240d8031540026a10209554280d503c601400800a4440669107280302142d11482210410b0a0140d002c92030203000b2010b8034081607029041a085501482048807480d00c0010140281000c0800e00113035980b503c02035981604d046c1000c00da4038032901c00f0140070110410142000c65540d2150134003989070762402844541d68481407180150001e02500200b4040d210b141101e1900c50700650f485801c1022504068501e9500c40843c88005000d0560450003038030011a0120490700051008044614603158281b50450350201103489981099045400c9011040089200000c110030451300481d510300440c0c94021040c1c1e140080a000d0000413103900400440 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 941892868 1250 941891618 941891623
    0x504020d060e0d1d09011406091801051c0f030309080408031314040e07050904031107060c02030d08010509070809011d0102121015142502030d0207121704120302 71
    0x124403d031601c82140c60107000c400d020490320761082036a0007640d18030040121480c1000012100900680124a08091500402e054000110b40b0000420550740108004e0400031242d030240d46002c88148182400c07503523181410b9816100160805460b05054014880e401e03048400410101084031343c0c1701c1020610f00710f2980603105040310600040c411140f581401e025000f503107408500030f010658140303020070030181c5014000b07a00300442c9001407410007070200b00c0280a4003150f118082c0c04082881007601e040c44008003403040008007001041103860340c0702807d802c149070b401d0408280c0d031442812401014001007541d00d0343e00f110015214010190b0003071803502d5201c591880541c0e00c140c3c405144160034840c2c4800b560403040e0340306885216061090880060010302c42c5081102101400c5182d1a2076001c0c51603280c216040045140401044007195098006410810700c0c0032104160011495006000030074102209125a0400d02c11075010300580c0c0042020054541002075 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 941894118 1250 941892868 941892883
    0xc0c240708010e1506070611120132061c0c0903020a08030304030507140312010b0a230405040e0c030105131203091e1109160f0809030d0504020d060e 66
    0x240401e00031070001c1503e2400903189480b0300200140e000d009583c000c140b00c40c40c3c1c0015001c3c1c0781640c1c3c0c0c21542c0c9411010720010144aa000140b000071541020000c103072b0350106a1801035855100105400c84089441501c980d588003200c5481e1184000e18128528450b942040ca0240d850042101c81d00c80d00a40c035402502c1c02500c424a4a13500c0717000b174580d00d100544010b404200c091020744c0000344205a4104040c40190503241001752142c01e04a0b001030a030031000d80c810000c64061000313540002040e079402c01a4800c400f4080724907001c4080c80c81180259405940c8942481c98000e4003000240350004000c0e00800841c03400c0c4c40001040300d040c10044504607902011141c1c0d1603c20300504140707a40019441e003405036202c0e029640c583c0b62520480f540130010321085031555a451f905407141c604281890200c079024240181030441e000c0d091020301c9500021700c11854400000d8452071840504001365903101c900000320b082441d443d008103003d00700f107d00c10b200d0b4000302e80034 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 941895368 1250 941894118 941894131
    0xc0b04030e1003060f0f0b12070c050a080a1403070f0e0307030b0a05040501150b0306091b0705060402190605030604240305030d060617040b150d0b060a08060606030c0c24 75
    0x410b1400d480300d024500d8508a40f19400c40241c061205888e802d040b1202181c00c4152407c0003441c8001d1a920241060107101c4161120003010411500e49500400d0b5030301c1d4281c2d5102c11700c1c51440c0410340030b40310f1121001c50a00304048140c5600c595142007101002864000c00c0e582c41928082002802420046804450b154202554080c48140001d10281600d1001c0503450a6903541801d1090198000303206e00c04100c0c0d151030004c40c0c606404014884103000720b000d8407040c0f520b401440f481e100f5840075103440003c507010812081c0e5100c0241c94101c4070450307000c03a014042483c0c154004100f078003509699401d1a10002c20020b0001c01045640e000c6e040c2404070781e9661401b5282080c1384407440c01e100600c400060009400b542401d45d001e030715542e21f000240001c5022070f10b40400d04104503040200c080a2101e07516105000d000108440e030006c0c00c0e0b03440d004000c100140000340c080d03518a000801c8104086a041c000381400909410700d03550405040e00b405070a0030380070b03600c2 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 941896618 1250 941895368 941895389
    0xd060914032206110601090f0b0d060b010e120304180e1e1b0609010c0c0308041d0603030a020c2b030302190806030705060901140c0c150a0c0b04030e100306 69
    0x203c20b8020f001e000e1201e440c035005480545c1c030b40115880984040564107020039500e03401170203544e5912540010707082c0203010000e0302a010310005460011a5000b1522500748040b00c503400c000c000040b00c080c1c071120130200c4a42c44041c0d16240140c03100e84480b10250044140300440548060140150100d2413802c44165085180c91458442c01440d90160484403c000c00200344d40075010694501e4442d20541d2150f80d03590301c65098a401640000004e60305841d02500e51046030300141e508610120042c2d032400b20060708c06035541c40f081c40000e001705140d0b072000800340e180713114108011038599150b000900d003501d001402580041c5c01d90003440114980c5000091140e12614450389020f4001c04c900ea0800d000c200d07098014100c41c40c104000c0442441a500708074010300f107131201e004002c00380c07001d013201008488070050700304d400b5508040c0300540c1865404001038102c1c58020740d0090864176a400d0032901d100200300c0054020a4284544191030b916901140c11201080e20 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 941897868 1250 941896618 941896687
    0x501030803160f0e09040f0b0a0507030c0306050612100f09050406181106030c0412080a0806030a0b06090c0c150f01140604090e0309130c08060901050d06091403 71
    0x90f01c80e240302d44108800602ca03000c5003407481c1000718025800c14000d2001e45032401c1c2907685c8603078001c0c0440300c00d1541c030b03102e0045c06005c4c0c0e014003824030b0741003060038140911418040030034242c0c02040c82c26503425103c00080f401c0308090409100c0074055104c82e102e0740d9502d40416001918040d0b4003150114500403d0000285c428180c00304000e9000c07000e0154000340b442009010f400142100300210800c0000041c0030511121b101c1125104e40c206170303110206100d0113040550010a514001c1e04403e202030005001000b64541c0000c0031140310019444807a008101c6005901c00c1d20b43c00d2041060340300419000000c0306100381c01ca070755130504030303030b03d500403101c07104080b4a019421560030301040c8103650380b80c0c20034200c51400e141240d080083c000001a0082c20000c0c019894590b102148080c503a80401e07120341c0880e050711001c042e5458400811846a60711001404040c0d40f1901e80c0c007044825480d08409018400480b500e4216030501c0301c406014005034440c40b10440c10 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 941899118 1250 941897868 941897911
    0xf0e1002061b1e130b0901120504061b090302150a0915050d09030e190b070209041722080d0914042901020714090115121406190b0405150408010501030803 68
    0x81100c062200c12380d80d480c1c2218401144c0400b502010340116210360f1208440c01154400360b44182c079413569507960f182c56510b140144460301c1800b6010400520701003040c04e4103941c1200c800350407514441c91440e00b52109000440b564002d0b8000f1540c9642000c2d210f406040d4000e208c9070980100711807000b40141d030710b005840d02030000d1294400b03581d82482080054540080d2260380103008004030700307200c101a00101c14550003d404d40a0621916080b03003428030f1781484020103070852000500b82d40606160207401d90340c451140a0010000f90580f504545940d0009a103100a0400c80c0d04100b44074408a0340540000b240b050041c46150b40004001488a0000f9841da401403d81e000b2030b400d081e0005040010400c020003405200804044038100d0b92107829103540090018001030b003000e60820030000500d540010b41860151001e01442c2c0300d1b07004803030480e24101c0d80340b04460901c0c042c00003d4040c41c2c1c8a0b10726540782a00000034002c01100862041098500c842c3d101405078 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 941900368 1250 941899118 941899139
    0x30109050106030e011e09020303070203150405070e011206020d1509020915032a19090e010506031e06010c0c0e0103121d0d0201030b100f0e1002061b1e13 68
    0xd4003101017817000d4080e031250b50072a5074021f184080c0080e05403850114107802180c90a0659440e4803060440502007005002080c4020006024414410b031400c0d45051070780021903040e1280a0031325035000450401d03030940b5030720a904030015803c082d03096a039540718402c002d411585c1072500400c1210170402410b00450102ca100320801c840e031001001044120031108104204e0460500c2c20803c0400d10050020300c200c00c101c1038580d03800d402c03030341011683d10740d000060703221034001e0710103205020020a58811402c100350020080c6060360b6038200049900020105000d0f01c81706c031802c4040b0b11304003400309141c1664060503090980b204020001c50f01c0d411122200c80e613800640500c0c03403007441c0402c02c0c120080d00515010500d0140c460000ba1510140d003c40804160b03031b0500c0d00c0005412400581540500301c1c1c013913001c00550720300a501c0d40b40c0140f0350003c0d107a152030a01907684950042d180c042505002c00a4000d0840001500507400400004408003003080300103040c10340c1 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 941901618 1250 941900368 941900381
    0x509090a2006071b050303030a0f0f09120e1f080406060501080c16110405090309010e04020c0c04111b0d09080307021c0614090c130c1e14030109050106030e01 70
    0x90310143ca4081680c03038100032502c600030040004440144002540e0350704001844c0242441000050300f1941000c0d40c0c0c0032940341410a5001500304070900303004c036060000800c0c501700c090400d40051950400011003522414400712154400d484040700025030000038117109a1080108101e2651202d0040d14013240c1242c85242c800c404014103400c0c0c030802452340c060540f0560140c02c1d81c1b861107002800b074a00c2180c0306035550340082982c500c50340c0d00080d007400c810000e03281140b07480b003603e012640310602c40390510f00540c1c403200c0c0505520031039001c9902c946141c0824105d13824896181d551544450644200018038103030000c80c4d440300120449994540c0140b95a6011003852030030350b6079604102098492565039256000120b403540412031041d40030303030050031034070020604020042ca42d4180e5807a02600c1c1a407284041900b0600c01511000607001e040f07031080080c18103d80e950a4012221640780000c400040c14030324582006c0c0c11380d4400e032000e2003503180c5005039a01b240c05 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 941902868 1250 941901618 941901683
    0x60b06031e180d140f1b060a110d110702060a03360605090c040c03051e0606160f1202060720060c0f0409060b07020108090d080417040509090a 63
    0x814080382d00540581c60080014010b0485039040940204c1c1a8201c0c1e00600381d020385c0150300d902c0c1c886c0c0800d0144005a80403440d60020005014540d80e812a240103505010051960b5101c0401e94004c594094820b100d80c0142031994581007000028082c18000c0703c0580b14103031007502f501249642650105091000c43c599503504040d031380302d80f8080c2501070300140342e9001d0200c8014481d229030048101d0741025443c0414039007410050310110381c001c0301c201001c82203030b503003070201a507942e070308407403010306141e2100d544000c05090494480d850103000814140c8402c00c00e4503d50380204005115007415150144010382e00d900e1091088030080c41c2c14004c4d00034800142010840030064905000000f120034109900c40684408982164000381d02c5d0107004501f4104569000f003520b9030108401c1c029040d4100c181d00d015080d944e0150004000c01c4080d4952a0114010400d0310b000b40402030038a0a01c1c1885881303103486007880c00c02501c0a0402102035064021220603180f05880c = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 941904118 1250 941902868 941902873
    0x2a1009120204020a030902060d0516020106031e0c05060c010b0f0103020c0a060c02030f0705070503060a0b0102070905070e0603130b16021b150a0f020124060c060b06031e18 76
    0x60140c1d0800c402580b1125210301416640d01450002d61280d4016110907070446000041d24202148407065600800d4048402c580c1000410f00c00a11034000e03645040c1d94440742400940c4451610001045242e0082a04803001103501c1d0f507440d50542200700303424800e4405240c1c1c01e188038011004da21408aa2084590002c800d00c000100540d101640044071441540e040a140740705c8180f8541c0444800d45030b80d40901c2e0240000c0c90b00f8041190080201c840810440028000203915482640710782100e10743e44200040a0a004a11810344448003d00c9207a0743c1c50403240d020040c04402006803004007208000814100e02040d100c055400c058008004040c4c001959000003246200841e0704480350f024000f007600d61400c0079080e0203d5540340c42264018186c002400c4519005410b55000340035400c0d01030760100454054291020341c43d041490f442d2600b003680280940701055904044000700704908030000102e05076050700c100300014115100c030011090014000040c020264 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 941905368 1250 941904118 941904149
    0xc01271e0201171003170702030c09010608040b1003060f0c0210060812091f02210f04090c05070b04030807180f120c1e090c050c0a11032a1009 63
    0x908910840b15400136201da5240e41c040c1c3c5990b281c141848014001000e0032001180d00c900b186420710601c5040402a24a11440d40c501440208402c01c060000340c4515030b06404a15018400c14801d0069908204284202c83c0c190350188024048200e9040043c020b0000030540e50341140102822660007000a06054600c00069802d540c801d154003644100e412100130107040503565005072220702ca401070100d41c450380360144140a580588070007084c030100070040c0082d88110945040d100c030364600086204601a06803813900c01c241c00500751012081c00c1004040d0700201c541e101c5c7c500303aa500c440010503010341c140d6072a02c501031079000c001008005d01c044c40e0400704c0420000d00071410114225941d050903050b01c0b2030080700242d1a40298010700a8860501901c4117004182c03600d1440c045524904d240c443c01d071410300603c210408801580d0035501040a000000c8241c1000c14444001204520b030185041d40307164040c801108981412a0140c442803049030901c002c2c0f51000d = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 941906474 1106 941905368 941905397
    0xd0b03031204060506131b0306050a05011710121a06060c06060f011e020a0203010b19140a09020c010f051602120c01271e0201 56
    0xa54810008540340540840890b6801904140009150f454040c0010280b0400d10954171001d400d088242d41008035420b9060419074164a04000e06540c83d011f00ca001d031018030030a400314000000344071071180140c030b00310750100c1441017a16445860310b880c061007109208090707030803c0f03c2c400e1a1000c0d0401d010015006075040f2161400c0245a4180039a1881300030b200700d004081c69040e5584a9014040c3d00c181641c076030406010f40c0c0660b8500954842e41d54005078800d40c2801045041c81c00c2c107244410364a0891711020384103e04250005000345090b00c034a41e08051301c008001480c10091000d0482002d01c0e07400814038506d0801c80d4420764101508110941044d520050b10442c0c0010309010041c0d01c5040b060f880e1010b0425107801000581641d084007003000184554103101c1d41d01503603105120b007020300c45815205514500480620340024041501ca8101849 = true := by decide +kernel

theorem cover : BRFrame.Cov 941726618 941906474 := by
  have h0 := BRFrame.cov_init 941726618
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 941726618 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 941726618 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 941726618 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 941726618 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 941726618 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 941726618 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 941726618 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 941726618 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 941726618 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 941726618 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 941726618 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 941726618 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 941726618 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 941726618 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 941726618 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 941726618 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 941726618 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 941726618 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 941726618 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 941726618 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 941726618 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 941726618 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 941726618 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 941726618 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 941726618 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 941726618 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 941726618 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 941726618 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 941726618 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 941726618 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 941726618 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 941726618 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 941726618 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 941726618 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 941726618 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 941726618 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 941726618 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 941726618 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 941726618 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 941726618 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 941726618 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 941726618 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 941726618 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 941726618 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 941726618 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 941726618 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 941726618 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 941726618 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 941726618 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 941726618 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 941726618 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 941726618 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 941726618 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 941726618 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 941726618 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 941726618 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 941726618 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 941726618 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 941726618 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 941726618 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 941726618 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 941726618 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 941726618 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 941726618 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 941726618 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 941726618 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 941726618 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 941726618 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 941726618 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 941726618 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 941726618 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 941726618 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 941726618 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 941726618 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 941726618 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 941726618 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 941726618 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 941726618 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 941726618 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 941726618 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 941726618 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 941726618 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 941726618 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 941726618 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 941726618 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 941726618 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 941726618 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 941726618 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 941726618 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 941726618 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 941726618 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 941726618 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 941726618 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 941726618 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 941726618 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 941726618 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 941726618 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 941726618 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 941726618 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 941726618 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 941726618 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 941726618 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 941726618 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 941726618 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 941726618 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 941726618 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 941726618 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 941726618 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 941726618 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 941726618 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 941726618 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 941726618 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 941726618 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 941726618 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 941726618 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 941726618 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 941726618 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 941726618 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 941726618 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 941726618 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 941726618 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 941726618 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 941726618 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 941726618 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 941726618 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 941726618 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 941726618 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 941726618 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 941726618 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 941726618 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 941726618 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 941726618 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 941726618 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 941726618 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 941726618 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 941726618 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 941726618 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 941726618 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 941726618 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 941726618 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 941726618 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 941726618 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 941726618 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 941726618 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 941726618 ≤ n) (h2 : n < 941906474) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
