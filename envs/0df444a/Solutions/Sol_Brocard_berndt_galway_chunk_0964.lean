-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_0964
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T00:32:11.543359+00:00
-- url     : https://prove2.me/submissions/a996a63a-6e75-4cf9-9abc-431470e93f18

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 173201438 ≤ n < 173381294 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 173202688 1250 173201438 173201453
    0x53126180d030c111c3212030c16030c020a08010c141e1c2301090c021e03120c0306060714010b0a06050912070612020702040603050d0c05070902030103 67
    0x200010074200424003682c1491700c6050302002c00140d0001c0c81e5a0900304e074101001d00940c21001c500503400c20280300070541480c0c406001c116030350180142241d40d0850401d00058000030000f6400020512603080e48041c02c0400c000514000e0b12034015030340460060007074492107900103615680c10240010100307540858222800071a001000b0349580d00b040048252030381d0074180c1040d03000f0124003a00800c3c403104540a628080c100100060b02401e0921030441e40e0300e440d5034200701c03142401088078044580040f031906140e441030703400e008000e0300d0304e10742d800040c1e501409650000c02c09001103260340d0344068210700d810701e0090851800c54000381440c46480002000f00c030405844244004094105203c80d400040c07040030f02c145c8801c4d000b04bca800114000340302d50900002000c00c0c69020817a502503540542d2119603030381100203544069845440100d0300302d50b45038400408242c00740445907043c6000d0382c401c00e00943c02d0a000340313400c1e43ca402442d50248100010000184c54 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 173203938 1250 173202688 173202707
    0x90b092527030b0726130609050105010b040513060312180b0406020109030f0c031d030c0d0614060a06050313030e0d110103053126180d03 61
    0x985000e4041e401100d40d20402022a61140d108540c0303040303404010000750318002803041c40c0d0361341c83e480e003604420036003d010303400f1429841001c1203000c0843c03020003188040140380e60040e0000b0415901994800c0c1c00c540d0300b68030140c1c07400c501140503c41441c0c4082528032544000f50280305860441c0c465006450708038194005010808014070201d002103003141008041600160b9102d82d92490017134003030031032035a0881c00500d046000c1c0700315a01902e03011024640556820518034030139540203044a004090040c3d2501c9040c000e50726640c1c4907001011618840c01001c03491001845054592100103070496105104080091080d203502609482c0d022511000ac5c1d030201c112810f080c0da1810310f005015030000d80c802021401e001705407841484909003a03808021a6541d5040541c1141040c0c0001c101c1084281300c803a981780780248101101fa0003003d5107405896101d48055211170160281c0840b504040b03004025408202640d85201c0c0c005e880d6003414815660b00107014a02 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 173205188 1250 173203938 173204011
    0x10833060a150824060d0504030c0c060306050f06031e1008010c0914030102040b07030c02060d090506100e0105030307060b0a050307270b0f0d0c03050f0703060f02040b1b011104090b09 81
    0x7c0d101c0000302850711a050f4440c0160304a1a030a9209840c0d040c02000b801d510700074507000c0c500500f8100280d081031001c99126111003802c0d43d9426903240c000c5265514060200c0b054030542e03140101e04883d084c49018045400d940f100c0701e038035180c540344c04400079000701a02c3c40385c0d106020421a0b5a06507084900080d8145401c0302c11036450310001c1d4113400f4880d908010b803842d10703500c88100b100004450b4000c907506201c400c045030391042c0c0c078180c81e1424001c00d82c06800c00c1c846540050140d802261006070001c00d0340010a40302c02c0420f00d0302055501582004120072140780c0040d058030040d00310040c100c60300340898801c50b00800c6030aaa41500300340288103a0780c1c0c4000b84000e2100e01c0010710360040990b80301d800500c82482d46d804c101d0100b600d200389002100ca0b103900e224402c503001c459a83c80740b1803d00b00f03902c00b840c05990035408060400e5480d480c0c40d10302100150000d10107040c080c00d0000321015034030705000078070300010050600d00d03480c6210b00b9400043c00c0ea01001141 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 173206438 1250 173205188 173205191
    0x19050a0b10030f0b0105030f1c0e1503090c15040b030105060c030d0905011a0a030c030303020a12020a02011a04020a080402040b0409060e0303010833060a150824060d 73
    0x301c1d0000341c410103499652000d04207107600d2092104202d860342d40a8102c032000c42c116003000210a14040e101c400740c80700c1e844941c60003601c0d650f0b0a03001c0c0512080c050300040c80780403c041040102e102d664001c0350304441a030028850065a45084907a130701d1018040c2907024101420b1102c218004d21042c02164410b04000c100252007000400455400a840c01424010000c240c54020702038001414a1031030b5a07503c404580e07030383c02d0180c60070017100c0e0010415a02189180c500350008d50110403c04100070081c540b0500328041400203003030510301c984c00003178904a015007803681a2084200280f03c0c6004116900082d80c2c0446065049501202c00040d01c5d003901c000034004100c24440140780380d061807408034580c68044041d5049804060540c3c0c40720045c050f61030001e1041d901e0002a20078240c85024508400c000041c3e801000913151107691900c81c1c018045401c250352400300025a25000c01154005489420a01d00803c10304414900d8200c0d0000302d2070f00506105a8556 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 173207688 1250 173206438 173206441
    0x1f06080604020409022a0f1005090a020a14030706030507051e09040609020702040501050102061303050304030306050604091a09091005040f06061d0f06100305040c0306110a0219050a0b 81
    0x80d074595044a0007040c42882c11966000c5540c24448a07601d0244824000400c0306480001e2100108001413124000409042c54105142e800350003400301801c240c8843c402d81d000e4600680714016200060107002440d00c00b40040e032410940740c81590f400110405050005100520341c01c001a100382158101021844c8010000b00351140e019104007154450300303040c0c1c000780708101d950042c01118001e98042c880d90781c840d4010f998441b07054070405962042d005144012038402d90103150814401d180102e2845e9603600040d046822540004503007035070b1030048140410304108a0070149105840d42100c510307052400e2034541200040b00c1e0611512080040c0400600003500e0040e154040c00411103a81c0700e418a0559056500d5a12080001107000c5003100380000710301c92141e8002030010858156a4000b20003034034010300101c4041040b080c02100040311401820704014201c05155283c402007000207103820f0002c0e81c80e0402c480c3c0000300001080317010034070611490300010801182e = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 173208938 1250 173207688 173207701
    0x801050120010f0c12060b030c07080d020304110102160501080a091a130b07020604020603040213022710080c190903060632090105040507050d091a1f0608 68
    0x12860300000c002015460404000c84030007081d480340000c1c201c80d545d4880d030314208031460f404030750302c1c1d0040b180c5035030042c40003a401181e500d005052840c0b0541001d4288004040c4410603a00b09070303030864461004003e40c100550381040f5042400708018850300c0000d24080010303104010151608a24031307214000403092000b05407d81c1880124410036403c141752049090502d00071440e408c81d0040d1301341d40410801807000441e140680d40040200749507444036801c000d800601c0300354040c046a02889013204c02d80340c40100015119801100752120364004007002411700800441200780141582403102160b20001030f06d40403903d41d40708085194180f4820b13a4407005c50780c4020030b05030402d180803d20701002003040b82c0341241900d6041c6040f08403160a8900411126200d402640c084010055450a5005190880d80c0703800c286181802c1c0c1265082a41d84040c403da031804820110481d641c01e1041c40d0643c42001105c1d03110a9000e890325001c02d40c0744500c190410006c040c400b06a0 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 173210188 1250 173208938 173208977
    0xb01140c0a020d050a02090c0a0807030b01091203121d0a140703021002070303021b1003050a1d03041511100507050412050606090105120c041a0a1712040608010501 72
    0x19002c0d00100340072035103501c514003580e59030b41d8a01c0403800344003201c1c045075000001c1001c4e620580e0b20340c0c4401000760303524074044005000b9654114100a007000300002c103000050041021070b8003995820307804810044003282900e101c07940911404099a6080c00300d200e0100d80d500001c1e901c240b00805188c10b56143c2c915098141d0806035202d0b08428036512403680004030f050803a03100350281d849018401550f0214044840a026001420320340002c0407603220754040d95000c11903210002c0c108510081c031903800c03004014090059400080c2c180902e0b01545441c100c6e424003450240400405104210340b94141e2190a0011985074008600101c2c003c4040d10017070150f40484c0b007051481405c0041d92900c059842c107003c0c0d02510008207090424092800501c079403003004002100391402407000034176620b00030340f126500ca1030444203280e4400303445c1c0c0010080d501540c19070040f48030300b00d401c3c0446019001d217818030800c810017406030000383ca1030454cc0c090900040031f541c4031500b0300 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 173211438 1250 173210188 173210203
    0x7031103070b032701060e01030b07020f03030108010b0405160912030302040e0708041a06031f15060309120c0f080901020102090d0b011703030f2a13180b01140c 71
    0xd4880b003001c800c10000d94640302800b020034003d140c1e10701c412072900160300c0c00c940c0140036040c02a102c0000500100d40b442c1035032034014044d0310486078400640d805040c1150000e81001e06144d44030040c1600300c2c03400d402020b4104034a1001e00c0c0040006400291001e0303010720031a2440000122000e0515009a042d07800a200c03089010b1451314003904010900e40c5c089404407040141c80e088500d00c2d0f102404454030801c27000c0c0c002c5c605140460b542ca001c1040d200c152094a41c0c59000f0042c62070140c0789900000c02d810f441c089240480d6240101320305203510311080800c549801c50380080783c1460504500c00b90094041c1d03a45000a0340101e019115060310184c01c44203012080b01041607508801d0b040b030701c2d5005000350209031022803a0712440241c50a101c0c603a10980800ca004082d0f14a068204c4120104da0039140d204000040e00b90700600c1a42c01c00d4071340410100081020f040ba041c11100007070030200040c6540700000f0f044052003040c80903414101052642318a03408200e040b = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 173212688 1250 173211438 173211449
    0x6031803110703080304081312050606060c07080a0b0a06060507080f0a032d1d03040504051f0305060124021903030209030118110a030c031412030c0a020c010f020703110307 76
    0x4c80c0d903882d250810322080c1e44603441024042801100005250f00d440d04d842c801c1c0c03603100c0c0240c1815181c5004101458101011078126406032403c001058902081640040d510806040d040e5107000c807a207004550080d80550148101002080300042c0600304407420100140320050f11440c1200e002c900518181a40b24004d0032804211034113441e8000c6800400789800c074040c0017448034050242a0080182c0702d01c61580d000344014005071405402582e07000d030300401142c0c8440700c0c0681d41202c20f1996802a00c898101c0d4005000c4102803140c10403034489086072089200640d61802507941d400080180b002210600c1070b002054480d404a4029100c014002e02910254000e414a02411702400316000c0b6054141005a030820502e58402c80fa000f43c031500100786103071035181c418014038201100a0003544440071a0703400003000f82d03000703200485006031210404480070346440c1d00f06040e6414440c00070600181154002512020f80b0b5000c3c007d442c5a942050100349400c102c3d0304003 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 173213938 1250 173212688 173212703
    0x40b0a05031c0e040c030e010e0304060905150910050c010e1504060e0f10020414040e030a08090a1b0e060a0b0904150306020a0203030609011202030604060b0303120f01080706031803110703 83
    0x10b460417030f60541044084030340c400020014040c01c2d6008960700c0c0f141d881108040f6070103035020000e5203004603a20b2100d402d15800700c0d00e03080c503e1000074000711340b00d0042c10100d1404245541a401e0920800884071300200c000d00c14008030b00c28041c48000002c0000303202a0312603d040b14211014003c40030b503200740504440c003080110341c100020b50800e0203076400f480608000b82031646014010011800700d8403000e140390050034001140e541d030780142a29114800d40c2111000207500008580303441c021000000c4045041408070703684c09201500c102d1140c10f00d9041030144044050483c4e407119030854001948200c5020900102c401d59403014103114804102c903c10307650040001c40c86100300300d542030590f80c1c88000d0014000f41c4e4080181d0140d104000080c0015a264081203102d94000c044a051001d411000712020344121002000140c0e01d000400951804004c81000b41c00c1c203050600200300209264803190b02e001402900b0041c65010141c603007d018072100c0d0203540c0082c1c0 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 173215188 1250 173213938 173213951
    0x50f070b030106030b01020109022b0f0f17070c0603050601090e0117012d111b01060503010b03010c08060f06130b0c0d03090f110a081b040b0a05031c0e04 68
    0x80d50000340d0000d12850f000b081c14001c58004940c818450b08208980c000c0041c541480c1441c0c1180d008464245021103240b03503000b444010484000081d03418501c1240c01880340700c0365107401b022480d080045441d4402c3e00f4804c80c4000340c4a00140380640703010346000203840e501c220048400c0380c002d60000f01d040c81100000300302c00e8040f4081c00c14065040000340460b0004010000150300c0d902c3c140c0740b403240e502000c40c81102c2590444400001c10030481c60030301c0080b641c283c030341041c10f80542c420303a95101800c0001e1b003000c1c002c02500c6070048008100e1590280d90150440d00c009141c3c520990704403031802807554800054500070100351003007441340c2d0303164000018260b115540c8046079110314412419254400d00070200082e03030180c2c00000540107a5200311000410480903680300103901004030762a641046543c0d05e9440e50f80134108019640d0f42400122030007091121b0143e45000c80501150f2000501c01443c000c503030801e4026003503441da0807900080048004d0340d1141c14203d = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 173216438 1250 173215188 173215199
    0x1803030d1505031209031203060d080a05033324121005060403150f06051c060f1517030403020a030b04030807020d14090f03010f020415020a0816050f07 67
    0x6001c401901c03410f604440c03040350404003451403800f51988241c1d0640c020348145c141404401c004d540c0240303000e400240c1c3d174421070341d0715036064001f00c1c0d000d00003640203c2001048001c040c8441c08070004402d46403113122001070414018504d2401d52070050030400c000b400c0324082c1c24900b180700b41c0110002a11950034139110701c01c85101340c42020b5a140306000c0450030749450021501226030020f0342206a41161103548050680e00d100e21040503070b23038480042c158941400074019802000e078400c0d1404132500c0c001048568072071003401802c1c40c1c0889100000d070050060380540d4a1000804906100440450700d144200d800c0290000a0840000100100403030b0300c41c00303180b003902d0b520032a54030320700c04994800078000c8550002e401d500c4100c4142e84800003c15074580041c0002401d403c10b00c001c80d0035036001c1030b4124112640040c040140d5075204c074050361100e429202401e543c0b41241c030390081900400008080c109840c44040080040400c50000700240c102c0980d101c1d260b80c0d6 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 173217688 1250 173216438 173216471
    0x114070c0e011e0b09010801030609030e15030106021213140613030503211003080c16080c040b03070807050105030c09041b02010c02010b0117090304180603150605061803030d 77
    0x961040f9900304550000c41c201540310103075000500c045e500d140641c4c0ca1a2105030103421420811b40c1030214440c6611210346034640044000e101c203903402130390f035494480000d10f050702c01045000c81e0394041c0314032482042581c04640032282041c1d4022452107040c00081c0640c895810300046081c2210000030400c4030201c040c0003c0c00030101c080c0c84459111000a4200d203044615039000e204d89802400000c1a00000c2d16a0004e0a000c444061011914482c511411900702c4c4909510003104400305141500a02c0400d10099000c0c00b8950f0ce48100241c1c1c07403810303010380c030705101000c030005001e0b80103c130582e9002800100203011000080700810644014449440c00550801462820160050290101031030341a580d401c410040840c0000f202180030782200618081003000003030501c0c9840380280080802500040c81c1481c518180740d010511205200c40a400c00400304290390b03a01e07081e61000c009821540c80c46980c0c00c0006400d6104081002a0b10352400e00d0b100c8284110 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 173218938 1250 173217688 173217719
    0x905180c0c012a0e0604030203060a09050c03030a020604110102010606210225020f060f120406020706050415060801060b04061101060e01140f0d11060c01060b12040b10050114070c0e01 81
    0x51301c0b1204103105a6051040c0c0b03100744e0001a415511050120341035004503070100e03004034020402d4a40e11500c89002904661011000000681c005070a1205114041e851985080c07000d0008000c4185003240140c0100e00c2d079094008003d102841a012040c090b804a40c03541910016140c0c08412020280e00d00c00240340003640240300f29600c1031200d0901700c08852644006c2590381d41807084c1e00c03640001016004100300d550680a000d8100000da0313034002c89024900c1841e40c1401840d039015600e0443d21158003203019030b0306200303040110294503000c90741528210702c2c119011640c1307081504e0241c19542e00201d1070305c64580001a0b6000b011044500c07918040b00c40d0300200025008020310130380c501c203010301050346a400d00e00d46441e0440c01090950001c500200e201592100c040d81c082e0008041d002e00000c20308104400c0080041c4200e51002c080440c00c0e0b009402c14000800480050f43c41e045042d000080380010b00c04a0300281005101906007a280c9686031701468801408 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 173220188 1250 173218938 173219021
    0x1080712021317070305071202040e01020f1e04150c0614071112030606090d0f08160b1614030a2007030f090b03130627030905180c0c01 60
    0x800f20400c001c0b480d011480d44200d90300440101185070900c21000b113108101d075000c90f40a030b40c9004c032849035102030002e0700041d144c2a140548801e01000b2640700401e1049281e560540c0c104800d22508002e034002e43d003569018070307004400e100c062619100400c280a400141314911208200a070b40c0d1008000c4440c0540c2c1081c1c27a41410102a103003e0f501041d42c2c499407055091101080c6801d05840b070581c194028000345c0522001c54032202c0c459030080703050010b4246400a65800c4c003260405440c1c212480b41c011404a1032000c1008261003000001040703240400800305401000982120410426861300541c54182d24641c0d0540c90340000c03c2180895109030741070004501581100b402c40f0005e00c211442c607610000c0c200482c0c003140c9400c4480359501c0050607010742450725103091814a2440c0d03401032002c5030802500d2410307030b80c0c8281c0c406c107040720628612645154603d1f41183d80a8003840d1543c44034240180500224103075034200c084080c1070303076444407039110b5011031400 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 173221438 1250 173220188 173220209
    0x1030b0409140717030d02130b07030c0308010e0103050606090402010302190917010209150c1204030b0f0c0a020a030c05071509030b0a020a091403010f021908011d010302010807120213 81
    0x541d1102c101d044020709010404180d04180800e00104001f078008008005502003403c41540d101e181949054100b01e000340d001a1204140303808145c0c10440e032a000d400e103821003001a6155980303041e5035440080c03000d4042e0300c018000c02e04590103601551040908090520121038040c240201148000c1c450034030024000a5181c190140601c00c45014074805420032041e00500d156804495100d0707103131814a4481d041102008100d0400600042e41c800c5080007602d0900c03030500380c448440901500c0351510104201e030b800ba900068600012541418883c10b2020181807040c101013040d0300410340c80403094110028558070804000541e849a2141482c035100d030105401240240c0d080e403408200c5505061001e0f000051b02d6021083c03008001294400d00c100c0d0240698000c2c030503524003000843e03103541c1001d070002c40040c0904080c00c0d24000a40088031445d00340c10b01840040e05224518001c80c10251190100c1508209480800d5640310244800c40c00142c8030f502c58102900d = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 173222688 1250 173221438 173221453
    0xb01090c0c0c140f0a0614160c0b0306100801081e0c040509031308060601020c040e0f0f070617060a0504090f1205040f0512060403030c210e0d080f07080601030b040914 74
    0x1071500b14170b41c2c802e403801e03665040e03948007020402c00756075404240c2038101c0c48036030003440e00000c0c00c461140026242590559489003042418440d25603d415501814882100d00501140100248a84814040384501d1090b100007032040390801e40382d5180307144c000d0306010400203524000070040105c10440008078031406d07a1000c0b40c603160390060b14002d0040e040810000c56511782504070040d400c80050a0340e210441d150704181c0b400701c881004c1000da8009040800c4420b4000c040b0318240c0024195016883c036001c0001b078160369180c06000d00ca15070b650300344000d04c442000001c4000c5d80c02405404250400785000c2d2450f042841000702d0300b0007403140400c0e141040511040c41c00c14100c002c11054540780e606070050400c6402c0d00040040e1500bc070089511034003494250075005c07000000381c2c054404091400e102c150440070b03013407251714018000c082d00c1051a8540c0102c061030701c0c810319150b00c80100c000d03284d00c400180e805400c00041d0f405014031000c6240c0406109801c0b0b6801 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 173223938 1250 173222688 173222719
    0x1080a0c080708030307080703021603020d0908010b0f0d1103060408040509010902040602100f0e101b030b1f0c0606080c18130f08040302031c020d0c0b01090c0c0c14 73
    0x1c5460074003d04941d0342092001c116614007441e107080e001941401d025050240c81d2a02e24802240f804099005a0040d0b40d016021508040da0a0140c14100000d10141d00d00c20040b60144550f003812600502002c0c03c00000d00044030440515650024180d65035400c00f070400c1101078207d805282d100c0c4882c40c00001d01c805491086400711003054000c0d22040c41c02141000051251440c01c4201545544900341080380c140203202d1020b200a000041401c1559600410f01010020030300525183c40b04e07000003039441c03440750410282000036204030390915420441d40407030f00380c0004010030704002c40428942c138003103032103240c81c0425640b08083e103980d14180b41a8090954010388641c01140c0705101040701c40004d5150b6502404003940b40030760300ea0100b894428480d2085030b89189115245855507414446200724143c246444141100c02c1c0e15003850842c0c041c4540395010b60341c1d002e2001d0040c01441e02100f400e03000306514210a5032030040070040a094296588200e01e0b941042c2e64 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 173225188 1250 173223938 173223943
    0x8031015021e061009020d151701050a050405120307022b02190309090903110610030201112a01300b09100902071407081c0309110103150302060301080a0c08 69
    0x4107660242114841900d04017222009602032110150309039204d245c54100d0707550820b440320007089004884100004c0c4040101d08440d009842e400c00075003402c2c00c0c48007007600002c44842d500c0c0e220a1050b0741392030b802c0b4242d2505040c483c00d00d65034140c0d42446030030302c050440d231903c10904070340030388410310007030f4403250344441c0b203410010007003211404203110040d4194080d4443c2d6200b42402c5404600d070002c60345c500758040700c00d0103d001f00d441041c021540c1c000110001c6065040080211003000d101c01c100e4010300480c10201c0d41b91030b01240341a80e1003207010818100c041d0029440e4552140c5140206526511060711800d0400c29600c54a00f40000790f103115041803070001c00300605014191000e9032107810709540348098014140e079000e07030900140703005060510040103600b20700340c0b00940710f80e400d2010109051801308400c010070180302e8541c08001c02481d0009101e030170780315010040344c5560800383d00712001100208800b10300140c040e04290003100c1000045640e15030056 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 173226438 1250 173225188 173225191
    0x30906020105072001060803030112050708071202040c090518010306050903040609050607030e131407050c030a200f0c03010f0618020d09060504080d14070c08031015021e06 76
    0x4440b260ba0f140d00b00303076130100d0031800701c0b120002013101607486a1082c0307582c0003038101008640024110204000c020400e04004040b200302501c0b84c01c0c079000130a40540c5070303440064015900c0345511540503101d8100b290140200a102109079940701c43e400301c202009010496502d8a0140800e428a10010980342101c120703580c0e1140b26400c0c03038248040da0f000018214140940481364008903540c0c024031710707842d9240e05000034100c9000b201d070078620040503002c601848401c00210041500110840b0000002420120b4000d04600e03041d4034201000d0b035140c0785a02485911080f004c1000c2280c256070a030443c024000040c10340c296408680b00b6100b410450000c1c07a1110040320300e90f4020302802e9410800c009161207050726080b042e1a070440701200c05827000500031107113030454850b4410b60f00a80c184180307249801c03480548224602d040107485500040001100301c039040320010003030705644180504403041282e01a584994610b80340c11034402c0702111580c0c080c0d0026100707 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 173227688 1250 173226438 173226451
    0x12040b240f060f0d0507020313050402070b0f10030503030711070510021507030b03010c08161e03180203100c12090c05100210060e06040b0d02030c040c1e0c030906020105 75
    0xd0718003400410400c00242d2000c9031060a40c6401e001e507420030070040c03061600c074203002e8010750740c0c41c0c00600d00c8143c0701a198000f6440f070303481400380d0703c082141d603144140d1100c1c04105032040c6403908032010b40c0f0903a140d0320081552100104102c4e482d40d102410402c484001c0342168803454441040260b0005100d41c0300005900c40c030851403926800c58486900315030a0305002079811840008a42541d2203d48480c002c07499179001e02180d0541c0e00044804482c084c170340a82d40098110618680c41c100d406000f04254403803d043d50329504040003c102aa03000f41240c40e0f11004840346800780c40541c49480201d16000c17040e401c040c0c03041c000c20300e80c294450b80701d1040608280400900d00856200c0f0003c61085055a500b015079074860003002d480920602c0049242c228100700136186070024050066000d100d1240050320009048000c010302181d01040306a007001c01107418101c1ca901074140307414002010801c00f80c00c0108d03400d04500030f55030b1641d1030361250400da00340c4034141d910 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 173228938 1250 173227688 173227699
    0x60903051306080f0c22030605010e070206040f03050906160f030305010b03160c150504060b100e0a091d0a0f0302060f0f0612120f130f0e0703020f12040b24 69
    0xa1800c00300d28010b00c440031696050244000c66803200412895290300111101d82e49d61006002c202810a501c5034025500d100420451034555200d10b5070004c0c501d402003d204011a07889142c4d6202c0c002d40300444180780038940c04000038181049450250441940800d00c0c1000201d4503100c0b0302c080303a204204021000094040b07100c0211104882d425058a001020ad0103d03891000c082c040c2e1802603000e1500864580300c51410025000c040081d250309002d0780640f2014103856036088142201c0041c94009440e0b00f0071481844000c142e104100d0a40c041d00005a04200104400c0c007040d80c088e50880301d4555070281c02001201060b10b20300450071164001840a00c1c125050b801c19001e801c0c03d580d600450400080501e810040d000700060601240a13000741454840100c000c20640803003864003840e0100d50890000003508150416400050107071010301c0f64000c4a02c0d1001c050300100040c502410242c405d000246c0c2c1817018541c0700b207003005240030108560405200010f10 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 173230188 1250 173228938 173228941
    0x606090609030b0a020d020c06071d03100e0309030106121b0e06040b010c02061603110318062107030c030f0b0a050d140d021c05040f090b010507060903051306080f 72
    0x303a401c22920000c011301070054007084420040c010b1400504191080100148800e04100c2c1025101128110100c44c0c0140707401c484225942d0f00003200c46072104180ea00141600b06131030b40c0d900b50f10540703105d00c0d0558204200043c8043c4841035242a142c002e00624030300c4108100301d00c05a20707080c03180041340c1c60f0107800324a0700c1c5090b03480354120010504180341c1035040da0740450300d40d41004400700d035418106c02c4864140742e0019550704c411100301c03010714500f601c0d8044c4424a00811b0500354051000410700d00780ca40a40c10080540f9580940001c10f54504448001c2c0644101d80e00c01c80000d04042442c6483e4616010f40b0078020001819403014034146028000040c4c0c10510960b40c1c1b80c07100a000302400c6043c840c940050303915038050600191641403204a0381001c058007405c1201c20030041220035103940d18038003502d81d10389020905134894001241c4a0040d008042d1143d03103000e030140e00300350300300707000b08108907007080c640546036540c41007070345c0324201142c08031410b86c580360 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 173231438 1250 173230188 173230193
    0x3140301080c0f0d02090103060b0102010e03120f19090c090f0903020c060307031409030405010e1c0f0305040b030a06090b040908030f0c1605030307020114010308070201110f1f060609060903 84
    0xe000c00d14103070142441c01020005c2d000038200950a0380281c462540d2341c040400302e941d080c000c80100f200090002c0d40f400c02c65000e90b40d0700e0500240000c680030f410601040c1103004004c000030311050041c0c4148060142c50411404015191203400c041c2850310103c0200e1500c540108900340381c1503000341102550b5141802025440103100e50209655403501e01d100900041c0d4076401000113600658176242403100150200d548595098801c4d1040d100c0b00c0040008001010401c035804188a18034420764601620075020b80d03005038403240004003c08ca0a14080d0380302c5001c480344c02006001105080301480212542003401514080040000441185070301c085a03401c940c60141d41c03450030411001c00007401003c0b200072074998000009002c4190b41c24081c2481540c648440b010240d4034540e1081c581d4404c412000707060150644010040340c1050141d032035032000f40c2c0d064400d15140500c824401c1c981900000385407030b1401601041540c41140f0035015610a526000125821038 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 173232688 1250 173231438 173231449
    0x80c0f03031219061701051005031b011e0804030e090903040909020f040501330f030c0215090a0201110c03120d02090307060512160807031d0d090303140301080c 71
    0x3421211000d00d2540441c010520038400d10009080b8640b480800c5c03d1521210f600351403002d0b01c4120111003000040c04644c0c0c0204000e08083d00e035070f0000d01103070040001600d0207135041c8030141d0800318094690f00c41c1034020340700741d104038032175034804404240350000c11003817440136900701ea12907005100a20016040ba44024011400280603080100a54000400342c2d41c00740c01508100c6c01810802c05c0402150301d0074105071055642c0f000ca459040c0c0b00040c450b1110440701e400b0141c85001c100c24041c001d020340c81242e0303403800c10300724107107400c540c516a5a119480101d0000b2210050900d44690106c1c40841030503009025111003614a03d01c008103400684040804550070807018910703541c20486c050080c961030700e5440c0c84030a207200c0d142161100406d01c0e0549040b8010b0344035016809002d130b079404401c90030001008144122400b100c012002c0c8151540e204d02042a034025411540400c1180d100796075116031030026591901e4940428481c16410341e0101c0501111131901 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 173233938 1250 173232688 173232691
    0x302030322050109030f08010621020d1d0102190327052e11161b08010207050303060a0f0e0613020d3801080a0506010318060501080c0f030312 63
    0x32a070482109601511101d08441070710a086010841d5401d08002080d04828118010f01d0700d820f2150322001c41e0b00407546081e070a4501310059a81c00101c10101169a40c40440003481034000a032814a4800c00b40e4001d601820b05040b9030103040011140c402e100740601a001c5504080c030709039180ba0881420900c003204a421101e07401103d01c1c94904448105100f060451080c0a5002020031030070500c2c11a15159030100c9980000c04c051042c0320070f01c121140340d0344e900062440504840000c01c4811a84c03a42005100d5400081c1c8002407040010145025100c1150b000b035030269520001e8040b03112905c80c551440c000000010a50303e4071562102650030301c868094035003024000301e9800c0300d031026031409021400000e808441e10310700000103d040490785056625002d11070018200c4070004018103d8981c8600006015034841d800200445000700107184441b040e41c54240c024202c24010311f0760a11685075281075500e0b01d2070b511044180007602440c81c265807074106a444210 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 173235188 1250 173233938 173233981
    0x5100b270a0902030312060f010c030806010f050c07090f0e0307020306130c050406080f060115120e07030c0608010e07080412050901030e12070605060d170d140117061303020303 78
    0x2e480c2c40785005624180005c100d01e1004010600702c0389000020000c0b1b11700d01030701240c1044801d940300c8000030342100025400981c01d00b0b00401d0400201c0089a2034070503154410f81500614100003000380080d0850131411900d00700900c01100380c220303643e55034022000c0c0a5456070210010890362040300c43e00349182805292400605504d54010600341c8580380c2c010040c640c403081e0103186540052006901419940001c001844a10340004009082c0d8448010010360344803407007000000c0400071440210b41c070081c14034a60799640d41c043c02480b024820502d074800c0707100010b440d01d48681402c91041d039100c800f05561030b10b601c100701c4403a0810490036042c5651080e21020340001041000d9407280c281c1704650351203d81c1d00d400d01c00e41d0303409050786015149881142001800e4012580881c0d40c05e4400540c41d030f800c42030307010040c11030f4260207444150300707000100d50b41e1034072015001c00d404000211050b5855410901c0d407500d40303c45000e40142c0040c008158440d0150404406040 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 173236438 1250 173235188 173235191
    0x2a0b120105060f04151e050306100e03060c090d0b0a09021e0a0306020313050a060f061a030a02070302031c140c0702010c02060f040801050a060e010b0309062a0705100b270a 76
    0x945d401c006d8003406500d1203000c2c6c04500040108404c130b00d04110010120b03200d40c41d1101301604100c001c00d0703603901d000e454511805030206803c0c3e4251651403980f41400d4101280f03440d41e0814480e0030000f851408400e0740a401d80c03903503d175101c550340c0c00c004030300600c00b510100c3c543d481d42c0c5a035002508080c0400302d404c07100852810101c2e004000009103240142000100801218030030002c1b41c0f880c0d408040c25000000340311560210311015641d01c407503201c4016a4485803854201e00710310503c900f4410b00b4061750204c000140326030f03100072000c0203a0002c003001d41e00e400c0c0308100c050141c4840240090480f08003840141020005000b042440280540c200742c1c64540d4582525000c5440d500816a0ba50b42007107000b4801440c64010841490591314508040000c180c44810040007050101500740e41d00c0340180402c0990f640401041c410035440d43c2d024030782507480b0101d518100c06000d0501c03008501901e030211281840503040e0003405441007000c07203211058a00200b001031801d = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 173237688 1250 173236438 173236457
    0x90601051b010c110d0c0809040905060f0601081005030a0f02061e0c120306130c09050607031808010b030d03050402060d15030c06020a0c032a0b120105060f0415 71
    0x8040da0070030107040700480c1c0700210300382d600d003079008014100321112400103602650700740c910f280d0084000c001c659085181596119a45800716015010700385000b03100b80304480810200b1040b60715007901840c0c099175441540d03256405041e1004000d030040980c140c200d009071000041968284481d05403021301058140684048600c114502c1c0301021761ba4501d0002d00190202400d101c660700c0c0086841500d8103608042010603015180811420402a0360340000002a401500c4440047c5002089542e940109240060070000b40c00103401e10800c1400010039080418065500b2240d40034004240720b546100e02100506005002030f40c01420402c602103110605000340c200c41c03071401482c001520710790b140201000986501000c119008000340200103214400c418040741d812604803c00c850b690b400e25407140c41405000c1c16510210200000c4000415001e003d01030050b03a280141a0791b50014040d0764803580c0c40d0702800c0e45040001340300c5480043e003504403170000780c60f040400 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 173238938 1250 173237688 173237707
    0x7140703170727030b0403110106051c05060603060903030a230703020702030d0c0f0b090c19050a050d08040b0c030c0304090519090209011403030c03030406090c05091509060105 78
    0x1400b0b8411600040c1c00d050494640e8894190340a040381d004408030810038910b4a41d0900c00030090001003c0180e07410003c1e07a0307a03209400c1800039101c02003012195460150041c0341a075400ba50442d09400f44d4400144d207490042110b07403240100310040c500d9592100c1c1a00c00801034441b480060f100028005000a0b040200c4d607480350115840042c0d851032103004162828036081101400c000001070440000313041000d041030000d911941440c0c660701c0b640100f80c1807081580e4039030b80010801480b07510003e010128102150070035100d0400040c1c0b28014002c6100381088064805d40d130070042000007032030001c02044000e024505403403c00440446803030855029134400b00030700d40c0320010300075800e4103146c1081d09007000240812411074503070302082e1503030014400c0b143c071008080141e04140d141031045070001c51040741560350700d103490300c0d1140003045100f4060b01c054030364507404142ea0401289043c050001036109514600c0c00c601007044182008258038100b0505005050f40c = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 173240188 1250 173238938 173238977
    0x90b07050f04081c2a110f030604150507031a06030907051005120a06060c060c0504050a090501140405040209040b0c0403022d06091815150d050f07140703 68
    0x101840508200d048220070020000e200c0c5c000d80410b0140080b02840c8456044030f640c44100381e001075500c00403041040020200302020300c03883e805d07001d004208410003040a120f41d0f142c4040300d100300318584480c0000c0342214035103007043c0348500c003000c41411207203001e20286a1048800c400c40d228a038607100442d90b218940143e00c0081800812507400030300300150b820b13070301149030201001803500d01178000b006404068000707044180e5901c2c1403100b0134400c0d403c40d40904400303040000b210b55202c04000c01010240f10300580b15013180c411580500c0c2901416000325002090814a9104ca03220323032101c0c26001c2c0070100204010840000142c5890441c100090380c82c864403c521813902c20035080c0010b03800308541c824030b030421910100d680c40d220050402044660002d07a582e5502e00f040c82c03c010000c10700c41e48020021031840c2605000b0300284105141e1140c02d04c903503221324840460044042d120807000ca200076070140522000040609a01e600038900010480c00d000f440c3d01 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 173241438 1250 173240188 173240203
    0x213090e0604060b01030c0905040213090c05090102060a05010302280305150718180f0b03011a031209060301060f172a070b0601030c05040f09020a080901090b07050f0408 75
    0x28450300000100428041c1138400c00b801080203080500c000305150a00a00c12451801200d1241e80d0108507003041c140072042c41000781088017030411802004407005403054000051003801881902c0010f02010386500401d412039a01518111200c080c1ea4449009042c803c070300d00700ca5801400000001c00d000304900c018981e0380800066542c05c0c24600201070000c0d5440600303424144079000c102020000301d40d0100c0001c071010001d41100740e84000d13400b4110041c0225403560030301c15844410340c0c00b040c1c0d0f640d101000300c00316103001c2c0150000a200e0b0182450300c0f54400e40a000400116000707080ca002003005d05d15100b051401881010300d42c14a05403090000d21207095000b5580c0c5084502c1400c241c1e070304000080c2050007542c0c4402a091000309014105900d403141020554064020703140500f07120503092a41a031100a518000d4026050240000343d07040045545008180318500c0e00980040f0075a055a40d20f0b442652a0f174016500103048540800000803034810500c46030 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 173242688 1250 173241438 173241461
    0xf201c050703021b0a050a0206031f030c08160b0f0a1202070f05010b01032c071701050a05060a140103050408090a0314060610021f02041a0304050714010c020103021309 74
    0x16114100a03509403a13900d000c010410342603002070340384804070b100000c0c2c000440707074101c9109560307a451014141d40d4454400e150781c14031207034140100801100e000c00c041510000c03002c44080801c0c40b42904140c421911071061308020412130310301c03c0d1000c0301c010114090f6500b001901c1e800c801c035101c0101d80c0001419201d001c5a004d9a004100080c001c10343d48500904e003c1c407100f14002400500c400321410f19819078400310402c421000c105000b0a0020444400106201590380811902030a001c541c0b072550580390100040c4075142c4a403401c4180c0d005001058406150080150001c06c0d01a109035103288007845580440e59444c9140e501640c803c0d40b425a1800700132985500d4804085d02103413041109011515500f40c0c00550500c1c0201c01502c83e0f21710b5043c1c10300d10402449190003c103401d020000044e0340e06926400114041ca200308100c51580790b0350241095180c050a1005000800784c080b03440256100e1b030050201c4c008215540d44076140d07140b8039041100e03d03c0e07855 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 173243938 1250 173242688 173242691
    0xc021e18040809271609050d0f05010c020a0c0b0403120f09050301020c0a0c09053306030411090709062c0d0c0f0b030408121f180f201c050703 63
    0x2402c40d003a00d0702d045e00720300741011110520000c0c1001600580f028043c00e8014450056000188075504200803030b8203420400800034600301e414000c0d226511500d080d07034a01c2074540c00240f80b41101e4204c13000c81b6040304405085c1591a00103c0d0320705205016942000326607034001c15607039005e10041500303641d0900148544d01c2a8640f0f03850703021555000c803600900e80001c08c201040c0360050005861240d620032806d8400612170f48500942d4990f1150300800040100800c0040d508001401c03a01c0480341c103015540c5855080b5114103281c020140012a4403551259101140c81da146001220b0007110b0310b80880b0f00042181040fa6050030f4603105003c44040014040e0b2a07502301c090050300c1c070740c0341c6180b070151107d0020b8405c8910100c801c5074202c00141c0381d281e911520b00303181d003218001e5100140e034408044101c000c0310301030180c1c030518001501c6450b84541c070800d0003100e011041d00102e4040864807991030381202415182e0124000480602c81f1824031541e4440da4080c0c40 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 173245188 1250 173243938 173243989
    0x402040c03090b250e03070b1c020c0615120c0108090309060d020417070807062102030a0b03060606070201021903051308070306110a050d09080c01020a0c021e18040809 74
    0x8000001c0c204c061038103800d01c0712000c0401c4054401084804c01e0314070301c000191351074031044123001c188800748100c0c040082c0302042001801c0000b144290151400602c120303501d16034101040030305e180b0300b00c26070b945a00c41c2c01c1c0d2401d59401003100c183d1042503034050342e0402c0001c0c004154580d11603450f00b0022540001e0911640c1125a000304d40b66107800010060307903042c2042150f840303644c0e0040506005290b00707558924144040d813080034a113081e600f0b43d101e0a0411340318ac09840070301c0049128ac02142c000a103a0304010f000c1d00c11442c2c05078001c0543c1165840c0e12031020304000380a8040141c100108564001c10380b010030700900d1120001c100e014911b040c0b5001300c40b145640120307812006c000441c69150721100790b80e05500110b071300007081c090628041000384280358101d02c5550002ca022a5465004210791415500944240414920444180740c0840100040c6a03019040300364180c3c1024122180c643d216200707190141c502088140000d001c20700015000411900801 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 173246438 1250 173245188 173245231
    0x2040e07081003030806130218030105011e03080903030c03040e090c030714041802030f0a170406052b11030403030e0d09060c0c0e0f040c06050708030402040c03090b 73
    0x8524503444409032030103507240d003003603803002d490a14140f10150400c4012008910345a40d02000c200740042016401c65644071098041c0d0100144003030040d00c6540b07024000107000c410a8148121001c0c5208184911819980c5071030f00350300a4034038590548000e111a241141080004001812002400c40e1142c80c00000d01407820100d8549907010341c04c000410030a20203040c48101242d401120007065014640c50048840e50649601a43c10700c2006c10181c2e0021010400b030710840d0007404c080c40941101303d8908c00601c900c5c8a4040041c0d41040360701c044c001c0d000d0030700104941c5151b52020309000c00c010241a40d2030500b50303118401001040c0010180c141c42070090041c9600090500c41c40c5e8518003800d025024803e100130f025010403007100b04085003030180e024041e61600c0c44050b0030300403031400121804941c101c1c1c4000300c0510110b4007902a4081e1103c4c103500064480c90355446500340070103003064071404c0060541b1103180b00e0024250010b494401d064040c03078610805450b2 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 173247688 1250 173246438 173246459
    0x120c0f03050c03100b18071209080a0f02030403051002090a0306020a050a030507021b0f031f02190c0503030619030b041203150b0417030c0303070c0204050f0c07060e010605130204 79
    0x44d102c10103146414214a159221101c90011408010035141501e81e01e020046e211600c01d4901c181540e403410342e21104001c40300c4083e080000c4960fa0b00120100249801d82c1e0302e00c210b0001406642c030082480340f0000b5690000e0100010182030b084040c0c1d903030340d2040181c0c3c21883d40c038004240c001c602d440c1d0141d0b04d407080070391109041c4001d2186581600105044048101d007590081d81c204030070f550151000c05c4200e03d0803a610b10900c2504103203078001402500809003100c1600062260001c0491089180341411900324000e9855900c62004005003071000c10120080c0c0088040000041025102600d00c41d9005070341e06080351602010007411651082c1080c80f10b2072a0041c01c2c000d003800380d0241d0b0140d41c98903038a58000d00c5801441071a50180c0107540c0180c0c44004108141c02d544003081c060514801d44040c051030b1102c030804074844908440300b0400d10703002e005090124900b5000102211218030000900c3e6894001140e6260203080041d038015800150405c00002417 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 173248938 1250 173247688 173247703
    0x9011d0616050414010f020111120609100e2202100302120105100c0f05010f0504050d03050903121302151605070e01142413081b0604120c0f03050c03 66
    0x640ca04603241c141095250411031000e1480b1310b04015120310501050340c005d51213806046607070100d030794984d00f40b920224603090040342e5440c0100004000f05014a207020980d005441c081903c2c0495541c5240c0b4841c1075203c1c90b4104020010030724a03813805038a070754180043e0b8415a50f40545d58000912040f1000720041c3d01042c0504001e40f08400c50586c00419612443c0d030100750b08a0b40081810040d0150000d2643c0408142c980070a22007001000650703111030703024075141400b4a5445101c407503101d0003840d5040b104a40b204000802e050020490032082501c014007520246030052541130207a003000040b00b10134080d50500f1414000300b080180024007201840d1001503050951403207180c01442000ca000b601e440c485041d44001c41c440d54404035041592040e212158243c492011070014840c56125004001c1040702d00306194114500000001d412140b80034a0300318965408840f10006481414000c0030204071843e601c010480114055001401c0d188030000805040c4901e = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 173250188 1250 173248938 173248981
    0x4050610090b0901140313120c02010207030b0403020f010509031b0a0c090518030a030c03060806103005010e16290424030c090f03080309011d06 64
    0x261032030200c8640d80c4061074a080d02c040506203074444041d1801aa40d4203c80071060056140100c20400d6040340c100154034454024a120b42c1c660a50300d105031111110180041d0060300801e00c1030010544036280c2540146c07281c81210003140051441500f12032003a40e00208030340000414117886403501050100d034000a01c040c045a00e155518110101c605100e242102910350700040d4840501590300d604800030302096942d52582460010000c3c1a49020240840d240050108001000181c0e562084010403980ca00c06400e1180c1e11205013081c418010300e03028102c503044d10300340020011071140f030b100b0000802c00a00d0a1842810324002501c2141c0c07480203002c04100000c0b240e4840d59000c00c054000060504044d40c401215100729040200301e402030742003208101d04508490504000259010412503284440c112071010f068030500300394035501070062012440785c00056400c000c0c0c003000021a1018140000c580503107401003490140c020b0400c0100350380034945175012150 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 173251438 1250 173250188 173250199
    0xe030706090b0d0504080f0415031103010b09130e070b07021e010504210c0b1305060f09010e0a05031c03061a0a0305040302010b060f040f091401060c0f1a06040506 72
    0x242044500b0360940030346008002200e84410101d07051254900480e5081c50110680603912504c8462a01c500c42d80425600c001034500900c04080b141110103076410307130301c52a80c01032920003681d04008600514020b40a20341d5500d100c40e292504080200e0700080c24030300c2940303841c1c000c1801001100c0340f00c4040b614510405215010081e80e101003181e0a58a0041d4048501300e44803d58440055107900300404400d4410382c04130b24414818081c203100f402201c1c0c0c0d92880780e1900709010541c01422480702c00c11400344a000c19a40c01021501200300010b04035040144d0740e940024a01502502851000010b03190304a00c0250705029450181c440020848610011030030101203512503424044101036468010a04051007074100e40c844c0d0310020102c42d116081d5964401075980503102e200404030124a001448000d02c0c0141c0d074008100c01a0a40c0076883c2c08820b070b0784030075039040403034078141c8034614440003a91109a01e034001c044002e0780d81c0e0314030381710b010b1008a030b1020742907034400c4 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 173252688 1250 173251438 173251457
    0x70f030e0604022b06020d0501030203010e0d0f111005010e100608330306070908010f1406042003040803012c0c0a02011814070506070c03110609060304030e030706 72
    0x588421070700a00085070302c001c00003d20000403001a0304e07202c4c1030009120760b0000a0307461403208035400840c10789008900030458a1743c07492020750f0301d1990b00c0c0071030701089038007030b502114030301810106d40110110001d0710351104040702504100c540c01d0300030030090181c0006002003c1103030000c900151040e420704070300a0030910790b140105804143c010406d05030429801f0309560b140014030400c140003070200e4203d420a5040608060181d028402141d86025420001c070441740c0034038000ca110b406c4210003070761681018400503107501c0d03800c0c401c81a102e080c282c4400112000444c030503070040070401e459504100c3d6202da40d001000c40641e1050b0f114400300b25081c00100400d41000200090039500c0e80010004c0c1d025105502040300c4982c502c4140340103105416a41c004002e0b00f0320180c50000c0d480344200078080c0a003020107005c2c45c400e49001c3c400620b066041d40b9510304010000f5003011285400501d80e980126002c40004440c0442c01c01135080400580b005042d060030961420f = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 173253938 1250 173252688 173252693
    0x305100b0d050c07120c05121606020d02070507030602040302041a1e0102010e030c030d050709061e050f0f0904050c0906120402060d060608070801050303070b161205070f030e0604 79
    0xa40580c01c0882080d650781d602042c51000d01004031880950320030b291849441030100041c002403002802510107010310000c600c0459040e02c110341503411010220407079036485031a180000c3d00020303d0017116560030003040b000314004000160045114450160783d4a0651040c8415550710f206050b5101e080070015001540c1d44109400c4800c1d8801c20400310000742800403805001a2403103048240000541c3c03001c0f8103000f000812510300301c0a41072080c1d0303d51510440b1030b003440d48200c1d4009040000c6001c000031f00c0d6000c02c4407441e51894141c0c2040c40d10241483d80390711072142e421891178002140444c604080c00342d01c2d40490101c000340d0801920801003041ca05c248040d58040d00352000001d0119650305054034408070b01c9250403c0030549451019003550740550703d01d004114150b0001441d40380010445a2444d44901b00740c1050b00d4001d01544030303900315400402440800300c4c1507400a0349034815503201d040c10340e61b80b03600490245000390807102e1104258080b508968100000b = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 173255188 1250 173253938 173253959
    0xf0d030c08060d0b19020a02011d0a030203190504050613030201030e06040206030c0a0c080d0209120601030f03030c120e010c0909060b1206030f060702060402090906040c060e0310051303030510 85
    0x58035000700d8204070f140c0c1c50001003402074101e14510017500c1e20106064619690544c000e4203404a098084456503041e503034010794a010796100200141e2003042120790400c00c000714030700d9951440c103246003481e0719080014886d40143e00301d105d550328150400c0003503682c5401103242801e2507401070001400c0a4000c00c10300e120003003c2d809400400241c40c03152601c26031001c201c55410000f004e440741d000f00c039220041c0d800954aa0311801c5140e218014612001c6540e60480e503110044081c15841c41e43d0540281840c08095400c1c418145100d14402c8a6030183c56007080d501000042c401e010144d0151406055801000e07026280c16414030091721440101c8003a0b042d03100032020300d43d640c800000e15103141030281e455540502e0050003106600002c2c000e019a10032200c2030034030760396005807070b40d50034048401412485007404208017483c021416910a5a809419a01d000a20009a5096403402d441f001481100b200710201456414031500750040300b6038121441480c80c1944145 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 173256438 1250 173255188 173255209
    0xb2a0a03031a1302090f10020d030b04090209070309060c0315051203040f03110a090b01081b0405040c081902040302060a0305190606020c0102060901050603121303050f0d030c0806 79
    0x5080c5582e402c03120108610b110074a0922440080c404401d841052060308007035084000060b0250411030104078052824004d500740c05151035008098400c81d11004401400d0710aa40a805c41c0d6622485009601d90368403040c8501d10702d8401113000c182c01d01d006000c03290700d08040350801d40381c65000355a01910034448000c5540c2128002d04040c80c9400c0c1600314032596110540742032002400008120a411401e04c80f04011581d01c0c0b24142e9032f038184420340d01506d4045001488600003c0d49413012040849038854600e070394542060340320408102166800e1506101003032816042100052540380e444850b440546015414685140d0105900d80a1030f51310400b070580b9180010341070f80030428000b035910350342c8a041c0300c07103075a544000e9120703102c0c00e020b00d006008480004200c010705000d55805000041e0080109107003240d120592a00988104030789203041920000c0420f40820429903c18150001b400040e201d0b0f207030280484070360544481c14030064408000c1156100005407 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 173257688 1250 173256438 173256443
    0x80f13020d0c0b04061e030c171b0c070306051305031207050c03190f0315090914030c010b0306130302070504090f0506010605030105041103040c0909020d05070b2a0a 73
    0x2403850416490850340b26a1180c00808041d00c0204000440551200303800c00d004030011031549244104006c00c500b9903c422140c0c10205818100160b1202c40304c0111540c4448038aa08a6192035000d22404941d44020f483c08a0b43d03120080600601400744030b8950020104035103007049040d19550b2946900602c40c4950300401c2c0c020009480034024402c84110004075000c0d6582e40300780002c40d0382e5400d0840250400950a081c6030030025000e03100f00000ca85d00d0848440304145408910303000703812888412961103004101c10341c61100c04001514194003030b40008290b009002060516091005004000c0d1a00801d44800401d80200311407081e2041a180811401040c4c1010102d4a11200000b0083e1264000001e101c0f40e00c81c02a5050310821101802490318501c030041e190f02041d0342c040c1680f58805010441400380e0703030280c0c8410f0310181658a50300455242c89081064991000e005460009240240d12801126403814501200718000b445003100700740707a54494000800 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 173258938 1250 173257688 173257699
    0x3061a0307090308160c05013902090a020408010e061509070e09100807060309170304020f0310050f07050703021b0604170f15070503070c30080f1302 66
    0x10480442c8a00201c00c0a1038201408554541341c100d1003d140189035142901e2420b50f894021466610405003c51132208500c00302c000315822201d03100440c401849291a00a400a10000180c42e202c003030fa031041c032141e540103840e14605611a42556010010500c0d03e4000908125108102c0341c1c0b039005d1b1500c10f840404181e95001c406803451606003000c030f07900c0916041080122030000000d5400e941c0420b051791405561a03000f5015540300c800000c0c0b400026101384c0d014003000301c02440d030050004058a02d0001010080782c100740010003414080c0381c643c010400d8480b01100c03199001240703490070318030f40300c81e50310001d4403104002690058000d0107600501c03d992003c080d83d014007840c0144800303199080704c2c1d0340d5031440da411540c91180544040e003108403241089051041a4948919107140d5503114101c4140c140c024007180c4050f0691800c414130750a104540d000f5031040d0b41c540c20700026111001d00406801410a0316100041042040440c424204a141c1c0f9906035035 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 173260188 1250 173258938 173258941
    0x1d03030c031b160809010f080903070803060a03140a03032d02071a07030b0114042603040b03070507150b0a091503050610050a09060503030412080c071e0603061a03 72
    0xb82d0701e0843c8204040082804481c1e42180107000c4014000d00252500340c907050321a082000081c2e0f8091021120240309070418040d16002c546080029588a40c0c0100300c030001c40e44950b00c0443d002c0561106001c1a070281400782c0825425100d110203106903040c001c403042208074030a00715020102092100590003181e40000c010016140000e00582100600c08614080c44014010085640707034600051168216012810006040300d0507914041682c03e19006100d0f4030600b200ca65280c00b40365807004020025110f038920010354000d880d181da4040d40c62030241021151401c510b076a1000e81854400001c1d826654000d442c000c5421190000c9440f00402540351303035252a42d4130150443c090079042000d81c0b00e03486070060580e00101c62500c4d02d01d440e400800700b01c46942c001e00d0340540c0100018040034500d1040e00c06070364410100f062605141c801040c0c10440f95a000070625a82141c6203205004809000360140980380740030030050f071602e00956413841c0a0b58003413080000000 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 173261438 1250 173260188 173260231
    0x9050109020d060c0e010315120c0b030103030e0906010203160b0703090212060f090a110d29150102300c0604050d030506300c03101d03030c03 63
    0x42214101039001492402e50101da0b040c10f2020300030403480200010b01d0401a1205580641300e074040b50802141841785503405d2286002c0358111001c01038505412100d80083d14000840c010340c040c6101b540c3d0700c0580070410081c80303040003025240d10306641047c002c62248400c101511982d094000c040c0c81d5040e1a030920560041200440c040e4200c9400000d482e0301c13130701c002446400303032484d07241904990b9100f0a403507885010054009010341407a01d00d1090610340800d81e5200d00c0c0c09110782c41506400d05814040321881140121103042c5c1c00c5041200811703a80c041000802d07828005414400b9a12254a43c4003554040031111032402d40b541c00c06580d0038100740c0c1d290605400456100b0300301800d110b40d80700750102d400f200007410b000020380c0600b0720380320052070800c04111101065030202c5240d0299407002c02071701c03614418aa44003010381d07410003041c509008512800102e5041101c0b0003500040000d040d20040e60040050282600a00c01100d038400050301c03d9952034032012 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 173262688 1250 173261438 173261441
    0x5040f21060b0105130611070f08060411030123040b010f0602070b030c090a03030903060b040b060a030c0c02030714010210110316110a0b01090509060402130216080a020105090d05160204090501 85
    0x810000705045c055081c00308815400213150000c1c41030010444003000c0c0c1d5000894619031490040c90540e07000720000c41c00051301c010702ca01e01e07000010004106280c00501100c3c0d1401e01c000aa840f0b050f00405003c00d11440d40c5045000d0941d402c0c024034002e0078a10065070b216032504c9440e18081f000000111a00944801d40d10061320040680305c419560b4100104001c8880c0800d440440c40c05990901900c0c286c805c40da4000d001500d401e082401ca50415402001c80c01c00c00414041d4110720000169418001c40d4007400c103010b0340215070202c3c08002807030a58903050131041c807440d004c034840c0004030080c20fa039030080138014404032400d40c0310011200703021041c844d01500c1c482c030800c0004101c05001054103079114110200100d0751112030003035482e03c3c107580c065003101d1001c0000c54008015002000f401480303845021200c141655134061a50240e5400700060759110240501003400340200100d6080b14078065081421002c8080d40b074a400c2c1300c0c02442156641011020005d0a = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 173263938 1250 173262688 173262697
    0x303090904050706020f070e01050906041b390803042607120314040201050f04180b09090708100507031d280b010e040c03020d0305040f21060b0105 65
    0x140c01121035052510302269510340a00520001d0b02808807007440303a01c00011200202ca011200307034031241e46002d050140100010346002e03005529410581007043c500300071400c0b0302459603190300380000641c045560758100750943d581082e1100800b141e14030a515581800b464108080a549490343e2038a030544030780da102403104030400c030f11042c04400300090240a649000c0e40c440c0c0025004400302700d04884200741c89000e10700c0d110020801552141001d044130300c7c250311007a8070381034880c001d0401c0c166619400c41009615203501a944d402c00810040d00041003c004210726130610110380d85a40f9100070038222107a40c1d1001513405031194004401003e0030000c1c050680343d10760190398603074400700c0d90300f85992100c03194608085102ca12000e2400c1e04200000110303400c05100121007600600f0503141c50084003404409030741c4010580e00c00e02e110342c80e202d5a9625140d80307454000865402040004030311611000d80100c8418500101507126000150512203480141e887e03004 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 173265188 1250 173263938 173263957
    0x40605150301050f210a031b080d150902070501020315040902100c02010207090515030d09060c1e080a180b16030309051f020409110c03090121050c250201020606010e0303 75
    0x400b012401c0380070300100d05211b03124000d640320308142034282515110940010300003001554204040701140e20141c5c056001d4180039a080c0910b00da890507800107a822294082d036460754000103100300c2c03e400c40103130300408105440606c444105a000605120f200b040301d403040c01b0a01d42e40508680c824840301000c0d01c10a8010051800c1070140c42d1803000d4807007c0c207030180c402c1c4405c03019001d000f954003800f140d0440c1d031039000d40e4102d175887c80e121100408258008010000301000010642c8001e40500321807980e03180001c41c01246442c0400c3c2c11584042a82c020401c2202c4094140508401c240d43c0c250901103220720007480e07c90325110441c15500301d003031010210000c0c0e0f42d40e2900204101c85402d038060100703409900616200d4440c084801e00142d000b0480404294000c4440c1000503c1c8040540c400340d5080c901c640aa94086603603811103c000903d060851184807240f0701c501c4d41590891250034446d43c0081c0d6503000117803c2505019820065800554081044078030511 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 173266438 1250 173265188 173265229
    0x518090403050306040f09260c06070809100c05040e1305060103050c130605280b0a050406031407170907080a05070f0e131529040605150301050f 64
    0x2030503040080060300b0030303900070744500e0401341440c0340c6440340e0041c41301d05a000aa640c0120025001481c1c03020010324600040c00010f1007424602c1d002885001c0c481c940c80d8a039900c4920b0103483c201c0c00d1226411428040503c1c00610740811507000d001d40381070f02c100c0d44044809444001d00e1011641080100801c0c6204c0c1e1800482081808910002c2c0c02000f51004628400c0c4122003005423006806120780041c165000c015114406c0c034480d90035107003508604040103845400d5640c131684909108800b10b0b00010b01040690b5141c440c0c0c2c075400e102c1107144c08040c14485070003008200d03085119081c803d10140402d800500c02d004e550002c0c0600401c03100480e1b55890b00d1a180c2c1d50603c00c5405119400000003000030300031549521640d44c2040c5040d51018a03a41d8050008103e0581c00c50b66650313408200030005210011039041200d480d1013446812448200300030340d6a16004103000c0c2011000d240b0134102075500703507415280d0403950000c00e541c841c0c000c5091440080703400224003 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 173267688 1250 173266438 173266441
    0x300c06071205091504020603070c0b150102071d060f0a09020d1401080102211e0405100c02010b030d1103090a0b0a08010503120405120f0709020a09050d080a051809 72
    0x254102400850501401c941404107603a0100d06a0300c40b10010640c03111940d8a400040041c6001002194485d800d4184685000e41685444000101c21920320010444584104840350b0b01040710400134048400da5400c2e10f26000d402c0911107074044e20440c042e40b58908244451780d120700304100502a030300d10854494081c06210006400d01101070303400d440b081720001c41c042d54180211482080d400003071004080001c80c10400c442d8004105d0f1124040c1048010020810711690b5030007580140c000f816540e00842e020b00450f010350004800307680c5080c00150064038049240c4d094031110b4104111110900d4020600350301c00c1040b00b940c0302c1140c12000c0b41515110001d000d03030904903510810680e8980d0107242d55a460031140c10308101c0b05000802591804081011308141c01c0d50507070358010840c6400364a422030710b4025021168000c00c11003410341e0b20411040062208403100754860429461740c11452164024001c00c2000004607001a6402d0000b200d0386050080c100407200e = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 173268938 1250 173267688 173267701
    0xd110102120c03041a0909011a0409050f0a05070804031209030504080d200604020d06020a120e011b0509060a0e0a2d061e0f030906150e010503300c06 66
    0xf603600074028030f002480c0c4440d5052034081c10310700b600c1103c01e0190505105900f000d030000e42d01013809200d460244801c0001240248090181c1c13809174400a4200c500ca041c06804402640c900504980c104015901000040380d0310041c1484001c100440000e10142642012603103441550440300d528804c1e1518400307019072245421800c0c802c030240c5405802d40c0350a0704c80d190441030320301941c080e403c0c03135004005c90034550003005681228100f1a480002c049200400d941003000180c08595451041141032400070b0f00340c1004000b280f070820315011003031001440340c0c01850307405c404201f01007882140d5038568500e80d00240c0021410b0381c0b44a03942c0b0641042c8003001d850050a68848484000b40301c5006a515980c0d400000c1002c016600484600715410308492028504040d01c1304007003004181b9510428401801c01c000c10810581400b0010b00e02e908182c1c0403600aa00c407100901c4100071240c44074810b040d41c1e56401c032805482c2545102907005100803501c06004440c1405030 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 173270188 1250 173268938 173268943
    0x5010504050a0c0e07020a0201030c03060504090c08100b030a1101032415080402061204170c1e061012020f04020a0f0201060f0f0513110f040303020c030109020d110102120c 76
    0x1e02e50300c02c501e42035025803203249601a400080d41c8200150b4800681c050066001e50440138650407286400524684d27074a000406407417003840c003950051000314080c0104e010501c1880c00508506005224400c00c040129079900c00310b06010300b980010b41c41c0400700368820340091424511784003608003a0754101c085c048040521b1b1107043d012070100444101b46501402446104a80050500b410440c6606d130482015600a10032250400303501042d04022542001600d1111038804c01401c43c00103121b0401c03425100c031000342001d90302c140204140410791040c64015902001c0d04070b8250b401c5480410300101e65880d0f400e90160002c42c140035640c0e403140744402c01403070310790083c01001e9540055100740c21050048199000c0203000900a41c14a1078141d40360080d0a000010046040304000e065500000f4804940940004081081c90b034108240d45801000324020070040e411640050207001a500703000705112648182c1d1046603000707002804103240701c1d41d103055450038034160154 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 173271438 1250 173270188 173270203
    0x100302061210050301060b040509101809061404240209040f05060405060f060d0e0f030f03010305060c1602041a030601060e010f140a050304020d080a05030411030a110603070504030501050405 84
    0x4020340070ba054009804d1405024440480d403e401803d03141a051106000300745200420070611004201c100040c002c2c1a030010040f020750161000840c4201c1d0325209059a41d0505801c04c0090100207200200d100e442c0c100c00c00c05842084885141c8030071429101078020780d00300c80e0f841841c6c810008031502042e00094890038003240c041106940b00b804105c4040400818039401600500645101000360351040c0348001d45041100c1041c001201c01f280f42d5840000c220390110404801001002010000d454104c0d44480b040d5042040011640d03c80200d5a0006849562140644494006550030074489944003605071489586c40d590050002251402d40a0000b00c01017040c2102c280301c3e500038103202d401007241030325040d9124011522034001a106a03070021008030710500080542c030007048422000d807100d540703901d440c0c00c1030b62825210314111400b940119004800141075101c0000b030040c01102d0280c3c50f074840c031000701c41d01e000b40e801c0144290710f0407050000b800700004002 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 173272688 1250 173271438 173271451
    0x81204020906030f0d1d1f030b1c080a1214041e0c030b0709080a060c020106091407081902040b090f03030405031b1f0e0f040b01050a081003020612 65
    0x90030103440701d4040c5662076030120101d06198008600c0172441611842108030302d05040050101007040d0040041c1140001c0c945a030384003ca04030a06025540500030a0740a0348101e403078908081400d0402d4548100301c04000701801000070f4200328840c0104030301c02c0b41c0c640c40c14003000005a4641002480c007810f4409030384100c0a00741d80c400c951702034541001c001d41e100d030082c0e02451856030340c2c1c801e41001030841350070320400c0500441c0301340080200c040718034050400400c02e00707949040a0708440c05c0307070090801c480c2402d100c0c1e2203e014445655400441034500706000d5a03581c08901c190b0000d08040608003400000e00240c0009030a000e40401182104c404180d482c00c0800c0603564030a5205058064004941d4040003088881524081d0040a000c403889119050b400030311190799022280003003000355184000c1410b00d9603c10071002c205607410001c003061000003a0090041114030b008101d0302c000041d070380c2840da920b0038005681c003134402074032030b10045100d4002503000c8555 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 173273938 1250 173272688 173272699
    0x1008060a1e230102061b0f030c120405060106080112030801060806041b09030c0506030907050108130209040623010f17010f06031211060112170903120901030c05041a130308120402 79
    0x800c08440c001c0c1b190052503a03841c140c941ca001c0b241941040d03140c000500588443c002404104090b044041c0901e10071840b0320050031441d0706005c4050301200d0180c01c41404c203106030048100180d0040d00342030648900d07007407205003541c0340bc000601034098070300c03c1d0040c0c800c0c210048059580102200b41502d03c0781e481c8030701e52a169014803000c2d00044640403040d50180c88100a107500501c207003a000055840c0d0383c80f4a000e40c0d00401c801708029902201c11310340e00c580801044505088400440303406143c00184c035450031414446981960180b901e0000981040e03d00190b004d500c00002c0540302c003c04d000441c0c1d20700f0944144400c40505101084c05c0305410002c4044c04690700341a5080c00d20703880d454428684682c0d04c1c480c140280c0442c0071008020034204c40c4d80811801031105900802c60344d0b1030b21454001425500003622034400d01005104c20300c80014401d4000c05100b04510100d0b03211f03119414140c05220050344050305000000035586c0840c104084800c0c810b500a682 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 173275188 1250 173273938 173273941
    0x10503040206070201030504171210061b0228030c0e0903070f03050d0207060e060114030a0b130609080d02040f0501052511130504021008060a1e23010206 68
    0x155414801194000d60042c02080f5180c015030203940704c50f801c10b0080141c030261844000000245501c000200000d00214004011013180b550b1183d40c06010f8526020b0350300750502c0e01c1d0420b4000742d1500244506641c501c0c00c8252180a05441a0b04080b544030b948816070b0390420082c04685801000083c00400c400282e034103c0000464003800e5010301c0300300b1884421348003180c8035003140610040b441e4081020001043e464025540c001d034041000d003207030303500d0b24400c48801d003d0f07440003e00a802003051600400c203000c1c00c50b64420094003020100c0611441c04030020000300b94000c005450100b0f404070845005d07030140c07090342e60442c00d103442c99444000646007401418089103201d60b80444203030788404c4100104250f40d124054444140b880380000401d00000c1e81c2c02c56181e0f980c0c40041001b5450454100d0610310050b003444c600a040001c0401d41080d0240a403240418441c02c0c94219048100c0c0700b08010f06c650b00620480c1241f0403050340c8120741d1440f0060043c89081c0 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 173276438 1250 173275188 173275241
    0x305070b03090304090e1207030e04050106081603020d1104121401110a0f020106090203010815011a041203020a0f0b04030305071409040c021c0903120203040602060a02030406150603 80
    0x40441e40035008050046003428582460324001d46041007149605001d0300509041500b030a1020307186244c400d03150034204041060900c0110755050384000c04000d00d2038180800940d404603202c080d40b0700d81c64050382e21400011400040c00c164411040190000540003035040c9092810303201e028400c112060109e8110038200c1d003a213171908451918844100481c6c00418003520159610040d6400081411680c616a4a04131b0b04245d04c1514540c016030b80411000340c203488a903000d08000e0010382e6040e203075481910f0450049026109800b0441511001854000c0003203107038459101449060a05d105d103402015103030150340071008241040c1c0441c6130a03000f005003404148500458909002c031040c204030141802481c0308055004007541a038000081c24040b10007038906844502c13040b031030340c07800050301500200000c0441d041404103208640c1e01040c0d05410428001e409030300c0341c4480c01c00c50300400114900110350705c00101d00095090709908049907400541d640a4080202071 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 173277688 1250 173276438 173276459
    0x30c0d0e0603071b120503060a061b0305130e04030918090b07051b011409070506070f08091c110102060702010b0108180106050603071706060f03040b28020301030507 73
    0x2031210941c0000c06100040300540304004a08202c030f00440f100c07201503075648503850030100f00012840080e1000003008914244200448018a4940762600c20f03a101c04c40e4850031415904e00c028108480020190340030b200e8124140c01500744403460703041c64146840d016007080c0c2648603003010102040f00b40110780c02148105008540c214000304100d988041003195154003c0c044581004140d00112000040034810000809012500740f040c40c10910328281c07a102156002c0341c41060700308203003000101448070420185911a60141d2102d05407000125505c1041c0040000841002081014040403000203a11100300380c007174441607110300d00100e00307135411240001d000c540240301207652655520b007215a0b4041050001500da915400050404d0340199440b00c00950950700b0381050240d003c426680216084403074503d0220602c030080304601006101419100d00200003802c00220311600b0318511042180b400c0c010210f1040040c020740080c0000c1c2c5191151102c08648034194 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 173278938 1250 173277688 173277707
    0x20a02101704030f02030c0a0516081606050a0201060306050f04021318020607020f0d0305040608070827010f02030112050f0c010c022e030501081c0509060c0703020d05030c0d 77
    0x1031016101e0b41c0d50b032070546520314102425400c502c001c01c250400d061f000e00c14403a840d0b1060300640000b400e8040740901c00b410b01c0c0c1092030181c0240700600f494840c0d440e1071034115a102c1c1002519007136290400d9004040d668000f52000c0d080030300b0010342400d000642d601c228421103203000440b40b000d0341203003140c00c480c1e059080c4071244820f440161500c1c0020304255031005084890041c0f0500114040401c8140101d000c00e40c0803c0600005070062100c690046040c60040c000345072419600210501c51404020360302d603042d40c00c5070041005c0d00000c1d5540712603d0190360b2540d4032078038120f014126031015209400745200b01d81102c0c0c3c1c0071a01410300c25050b0b40340102140160200721412080000c00c0d0544044031404406a8490034800400b00e2080d440000d81c1703614221a1604003110000440000c64004804c104030907042001e45403941819a441511020001c10781403034940c0c940c001070361001c4004c2040080100000041402a182c1001e640e055840c041080da1110350 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 173280188 1250 173278938 173278967
    0x60e100e210c0304030501050106140705060f040510060e010f0b04030203031b0a0f0605040c0504090c03060c050904050a0e0f030403080313080415020c04060f0803072a06020a0210 79
    0x414001d019a0072a5800c054518040031a2150300c0c0a1226400900d998029407049409945620042201ea80c009424001c0c01010500b07071403900c40f060342c071144c13144801005c845082400501180a0060030007140e0344101c841042089001e80b00c88030340412840903c6003004c402d01da401e0200342a0600400e403811607502800860600022a40c80da0001d11640a10b01c1c1900c580301280000c40c040b440314020040c000c100c002028100790416509821440e04a00c0c0a0350614040c00002003000003144116608900c0008907164090f0080341c0034482c440c41240e00c103003800e0510800c011103510502550074644203c91292803022021a200d0080d80b00103450550305000017006080c8407411143c04520a0701c10368074080c0c40321052503180043c00c050b4401039116055076090350900c1d106a101a118929001c010507152560040c0e891050b40c0c002080004211548066160494020000d49451010b01848580c803400002c1d5104c0050806070300ca40c1c04a004d034880c4c14041c854414100c0c8 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 173281438 1250 173280188 173280193
    0x303040b0d020328050403030b06040b03060d061503081b1518240f060102010e120702180711010501050904020a0b07030e1302131e05120f0a060e100e 66
    0x962016403440250002030000000b80d4401c1342000c1c00141d000034149101400010004560406e410001e0031541c0d1081c50314000c180801081c401c2c00383c040d0940768020b4084503140105100d5107000340150004c1d501c12105001d20107400310030403a408001d800d8a80000300c034031003c0241801825a5250740b8980000e038081b07c140441d0100a4810f2600900040c0d40c0c2110f50b940c90600100d4131090755551101010a01c51003800707500d070300840c0840e8000302c00740b000b40406039100384207584401c01010b0704480210001400b40840d10740350001c3e2441c0d2074a0816207194945070030090a9550ba03100c90740080d52a200c0040351910b815007615006c3c1c1c0e0040c1445041500303060303200b08654400e98080d030030720803a600c06030381c40d580e001890041403407290800368640c82d160900030719030000c0c3c2d000b548007082c030040c205120059024040c4100c5804079001a090f003042d883c00c50a165800c41d0680d468080d80980b0000d100041e04804a1041140200ea101d08800c5681208440c00113030405001c0c1c = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 173282688 1250 173281438 173281447
    0x10302060703110601060c030e04050f18070506030103050d1101052203030b04050123060304080d1104121101080c030f0f0c160507290405010f030b060a0e0307050303040b 75
    0x142062809441250b100f07082209841c200d10f40d020b4030307010090f44200c00007549441c4207810180d0151115109500960701481f645c200403800d00500c46000b849003941d00d98008581340d80c5034041003910020100605411769a5850b410150749841105001602003910701e10b411107908030520820707205032210503000d1400840320075604907001c0100003da0030107440e003403030300b0301030742d0780c2c8a10350003002c020031280b840581c1284625007054144964a2050200f40100300c08101c2420407907085400c0c0301c1c0001140f116107042a50140034540001c1700c2840b1034541c1d0820800264498044020240c80310992130350395400041891000300c411021003480710020a040100030301446e0782141c1c410744560700380f50080003048042c4d55100400c0c4c4256000550810030500b0310325642d22000c40d01c403030550301005000c0c0c2e10307242841188100307410064500f40004030b6034840c2d484440c803c203004091554a0081c14401400c2100e0304100034801c3c050143c00166500e400400c442c210345601d1601c50a0 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 173283938 1250 173282688 173282693
    0x90619200703030e04062c010614090d06020705060403082202011b1403072906010f0809011404110f09130201030b06070203070f090e07050d0204090303060b0a0507150506090103 78
    0x80c00078506250041e40342e480101f0800f50550600c4009550f44801140d04507075207140380301039401a80002e0030710513903448203c440c0d8a44c80031203200754401d03903464480d10903500d802d4009200d10f800242642c0580018041010313440100c140c004c8204042c0414409440b003034a2038900b02d0254004e010499166906c0c004100041411010780e020b60b91501051a9882420b0b0550703101c440202c4400f000c21a440407884516001d420046060b0b02c05140c1500d049000a080c1c0118442403400b40110ac20005110300d0094108000d522611104c58240341418070382000142c140e203240d284220b13103a841064050410914562151030310140f00c0403040b4040d00103600600c0074080440d0051420070221300983c43c204007070802420003c0314072111929221500044520442d0024595045180100300e5585d4480248490b150102d9000884064a10341038008042580c000c0c1c1403c0030110303101c8011500000544890703070007040d440241130f42c20056001100c5003207074240e03405020300005001 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 173285188 1250 173283938 173283947
    0xa050a030f0b09040b091c0c020112180f050c030703030e0102010b220b0307050d030c020a0f06050f031f031101090e0603060103060b13020c0106050a0b120c090609061920070303 78
    0x10400e0032203044c0e03683e021340d81034071001200084040390040f541c40230740c080441d6400454812240c2d042481080f6414030341813075203182418442c0140403095241000170a2050911444041038070040440f03005076624603025201401601c0c009003d5443d181d080030349c0c1c0c02c14007a4400e5808903440200001907551928000901d407105000b42c0500c1150760103d00750320b840c1c0094100b540240c031401d403003400c140b0400081c040580c00441544055800400996401a0030780c2c50140704164096103c7d40c45100300310749507042c0031811200a928900010500c807410760100701500c02170f0780e40142d01c0d80301c2e01d480502400544813a0340690180d00108085059a4000030001e0801800001880070180005050b60400185141541d5580408010074580810008010b0001c0248642480d40034078404080400090240244040004a030141940e41100f2140003200040c04952a1003001c407000300104031840c0e20310041800450b1614100d00c081d00e8240b0480390450003800c00c1030a60382e0498 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 173286438 1250 173285188 173285191
    0x21060c0207030f0809040b060c2a0310090b010503070612020d06030b04060b031504050312040201051c15061b0f080d06030f02040b010f0c080306150a050a030f0b09040b 74
    0x81103004400c40032001030814101c186420f80240a00ca4550009004010803071b22200761480c4640d0b010441008101c00c08a80803005824844009009101e011003400d030222482100d1541070003242068002c1c45015405460388601505c03283c0c191381e0300c9100741651003c0b036010300c2000c40c80420f040070103080690000c00707111400e41c00200b0403a69a5807545180e41c0c081d14101c5000b0303210b442081280c01c003080f80103040390580245044500701614ac0c1516446404901980b41400710000303019a406282120020b0010341300c90100d4114003594400280748080812404c641d19040010341103100e400502980c0e00244d05902003503120742d40b0707030541089800381200c00c40c00030b11007200c40c00c40390f03c42c03d0001d6002d000c0048100c40c4901c1004103d8082d48819414004100c82c0039070f00d2980400c51071030459000e00c0040c0e490b21494000b500000803045c02d60740140d0b0000350b0518450740400600441c501689091056402e082c1180d401c0d181c02c061400c0d080800c200c00280405c05804000e03 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 173287688 1250 173286438 173286461
    0x909090705030f0f060c03040b010b0d06080f15090703020306010b0d09080a0504061808060117010902060c07030b0901090b070302030408130806060f0405010e061519020d03062106 79
    0x1200c1240d599004241404100d81c01840716400a8500b124442420302680d81e102c40200c01b51440c6180c0f41d90b480e046150180030341c81c051740001c209a004010389078041c0010b0300c42c480403510211882c030300c1c0982d542d144269200c1c42e541c02c0c6000c40c4101e14000360b6407094a42c0140548416801d003d25a952504800e07031540c043c5846111450210700d510005120514242d47e502d82d55504080001d00580c4442d03107070221000080314200b00964000c603005041d5240f41b011035440c441c4100446014003a6488040d5000c1c00015034503401c1d8800060302d00450b4455003c81c8600d40c1e0341d882c1e2500b01d03000d080001d41444c7c49030340010801c82c03195000f580d006214280381d60070040aa164440c4030788080e00169100c0e803100003805a07502d000400e141a0410444040c0210341c100030929001c40800340a00e802519414804482c07102c1780400e88900c40d0f8a004000e8105007100b000030343d1005542d100002080c60080040b403005400c1944609104080120541074041a40c40300010410581c58 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 173288938 1250 173287688 173287693
    0x3040311040c140c03250309031128080d08070c060c090315050a0e0a03020318041103040614070f021b011202040f030c09150303050705070302130203040b10060203090909 75
    0x41c562110f11001030704049444400458641c03071115943d0080c4008108a15482d601c401220300002c1d6000c40c030041501d5001e400d0741003c08000d00403c2c512142110354201c01c840c107058800404001600d02c80480300c40c4403c54002c856041815500c0d400d080e41d0203800200d0042000010034001d81000150038030910344000c1ea29075070340310750180440300141a9510794840e0103000414119009507600c00c01003001510003400e640d0360207940e9200301000407100000b658840030942d900c07940100440228070b0f1160f5520310b400c1c50320b50000e1020484e104601e003003500106004510075004038600c030200d44c0044c0b94500d4600610424100d501c2c804504000200303141c002c8080d142d0015100034040c4d000c50401540c1189081540c040f06a00414080740c904203508401207a14001e240459800d4200b440d44c81c003460626504254040d040130350818000140200d12551660045100b01d000d94000e0b02c044d110700044d251517a5051007114010f074024090311180d490001d10068001030080c08 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 173290188 1250 173288938 173288957
    0xf0b060114160f02040e010e0606060c0d1404030204181218060c1112010603030806091b1b03030112060b04050f010618030b0705040e07140d020702040e0106030b010f0803040311040c 80
    0x1030070f031002003140703112903511423032200005c10f0204503164000300c040f50f0060529181d61120b50b07440c4400e000001c10020700421509240d440300040341e01454010341709001d0307003062800341800c05084041c12141c15403482e80d1302820b184281c85c00d40341c0140c00808408181d18210b400c9402d00c401030b2060340c04142c0300c000140310b5518251809000407a010021640c14618240500090030007000d05000b48020b030100808200710822028058030446801d50b01c1e90b10308140c6100d40c500d441280c0b19184800400424040134105031170b59494451441841070030214001e00c42622001e0307800540383c11400005102c1c0d0380c01044020104600c0080107090f451b500c2d140d0488512059408034003180001900303120a200740d40340386502c030070b60742044000718103030000a603602d10440100700c1d4042c0d80492603400b1543d82ea00810804441a0002e001c4251a8240008000028420704d480c1255800c1c00162101e4084240c3d81201e8104440b91941440d000502c4003910400c103401d0b040020101 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 173291438 1250 173290188 173290193
    0x30c05010b09010e090c0402092803050a03020304090f0c0c0308340e0109141306031209081603020306130c0305060c1c0513060905030d06030f0b060114160f 69
    0x38420307802450412044e0301141001c0d12001d0600000c20021405940100702c074002c291155410300040300e100c4032001d00075642c116040030b031442c0c5036003006015004843d8064107256000004e4070039aa80100c01f003211900c0c0403c480109c0d10782040d6800400d490800c854040380c0500b02150f4041d0700310b00010802683c10480d00d081d51000b50b0301e09082c400300b49003175030703044d60141c00c44e00071890a013040c09410341000c1c0d05811304095001d0701d62003040002800300e005415900904001d42d80243c03401c4010000b010050b04507260b0f0300407a1154418402c076003408841062043e01103d4000d0050041500d50314032500e1440107201040c0c0700d00c0c400101c004000341f410000603105032040c01400e230f03c0c2c61b00c410118603a041714000c01d1011030708110a000300040d5031010880030551000000070700402d6450118114050408080886440c3c1880041030012001d04080100d1140e18074803619501c85005580c00600820044d890342c50034402c1150060103100081a058010052040c1c26403455 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 173292688 1250 173291438 173291449
    0xb12070306020d111e09060d0603060b090603060712090204020408070806010e010e041e26040501020111030c0403020d05030403170d0b0414150109030c09050717010b07030c05010b 79
    0x692088030229800074040c01d00748900e100f00d1048540302284145001010b51002658900c00d0055840380c81c00040c5090303065035108100d400c034007a840708c14010607a07031b420120010076117403800901560604000a81c0da10700491513134807400d0b498031035218220854028400419441e60b00300d8000d5820040882c01c4a403c014140040004d0300003000c0c03960601c4190f018440040c0e01898280e200e56040c0000503800b030200310351807140140f041c41000319030306250340002c0310010541c492202141c1c1d210307403202d0200d00074001c0d94000c0c0c000703120040784440c06a5151008451141c00d0250a11041c801881c08540101d441c6004a0031030b403d09890381c480f0005c0120b0680307800ca403e40300240b0040700c0740550241c1c003000e0710216070401458100d5441c41040b01c40062503010195465190415903a028a200c00051038000d0a446882e6844003140001000b0035501d00c8003003810010b40c525030048096031343d03042e038841070310180c1002d03041d40c0c040d260800504011a901c0d500caa00885954561 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 173293938 1250 173292688 173292703
    0x1107030b0114010f030605060306060904150b0a14030105030c10140c0d12021e09153118020a050c0307030914030114060f01090302031204150c03120b12 67
    0x34111100042e07400c00009000c2818445402d8289400c1400411403562840240c03680080c040d580a07070350b6035203180010024004a50322108505120a001c50503031007410185c2459141e85d100d011115000050206103400248103455045c0c2c0030440c0150710f420040f03803660002416003480240e10b4a04141140182c1160412070700d10340c4405811022554403000590700300e010341c5411032070003c034542d540d0501c0412021480d21078100240450203625102c1880d41c1c410f81c841c049549a00c030402d5a6000e22001582c1024040d100d0300303085040c907004c000150f084403050403180982030140c000444c081c1d04001c141c0405e0101c24498010340403418001819814401c4d6500303500d0ba0b0801e1083c456201207540b1050090b850091107102014288049541003001103912140c20303401000105c030401102d400094140c0201411502c640031031001400c290b440070f00359400c1d01e1031449400c64104030541e00c00380002d4024182501b01e000340b64840381144102418190ba48280203644901d401d50 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 173295188 1250 173293938 173293949
    0x12030a030e07060816030506030309120a020915061b07050d0318081204030305130b040e041e17030402010309020604060c0311010614010f02150c04082b1107030b01 72
    0x848250604141100b03018400140c101c60610a00c0c0e4105654004103800b6074041601c141603450f000310390142c1c0c0070402e03652a0040203003400d01800a0784869911052030003422809060782601081c40324001c5004404039030405020541020001c0c0c10f82c20719101e80b184039580c103005071030300030030140c0f10302000b0111140242c455192860342070060502180702d44d40b01d003001d90410400c00d10b0170340b0300c00b00b11006c0302e40518005480d02e04800000c1e401040c140d0140303c010000250004010307984407003c910880c040c02e418040549054201c9030095000ba80040c18280c030900344290401980014640007070040c5800240610b8a42c00701d41191300c1034100102242070752001000b010360246428100000403802800500d01e021181407444a8502c1c1442c14030510304020f815107882084a9099040014550144c5060441995002e940305026040e2140251103101103505152400141c1100e1282030b05551010314690444003100b250b82580d0190041c0c0340c0001c049041404079030b002c4c09 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 173296438 1250 173295188 173295191
    0x501120308060420090627100203030603070605160210020102030a15180e0f0a0809090603030a0e1c0f050c01020c03120409181203060501080105010c0f06020912030a03 74
    0x245508001d026140000c2034584550308183e0f00701c40c640c02050301c00c41100c8607606000d440b0700c00600020860f003c0c0b8448030116540580607114000840141c41503100c074103544801039001c0a500480e20303480100ca01c00e030141c1c4450410031219202c1c038000c00c40403410152101a0700d42c2030b0300040c0340a184030b000f00b005230b40204c144286100b07a80b280e44120300140130603c40640c42c242080a8a402c00c0300780221869842114072038203030301400345221000c1a4003d9400b0904170345080b5000343c0080d172241c0d0250803090000750403414004100c0d068000e694460079483c540d010b04012000040e518415503901c07841540000007001c00c1d83e400d8085100b08082c0c8a180300c1000028509800300600506c07a500101140301d62080b104120350030340781c0310385000c11419110300c00e00c40407804040000b0310f981401d000c9042c681c3c0d4164803002c2618001d995900407a43e0b00e000440e081d0314138030f4020700002e1141103d140058003990003403005180c05024080282032001801c1d055810040740300010030b = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 173297688 1250 173296438 173296469
    0x50406081008011b03060b1e090a050a030503070c090501050f10030609021b01051b160303060b0a050a031d0c060309160b0c01050603150f130b0711010609021608030709090501 77
    0xd507014011940030700920714800d4245600f03500c0c50702303544003003c0c1603000841000640341416203c0c00c0801000d0200030740440b2109580c2e252150307883d402a07009480209a0b08408206400117005480c100e83d00201000c105209010400007211510030030308080c19950400014255218005410000c4900c0c000c0200705080a4409080d01c1c0010b0060010081c03240058043e242c40f0015203580800b03040c41d40305d41c44040c0c0340c00e070004e12064000f1440d0560105559450303582c40300042c0071349400c541e0309118000d49910036210301000e2103003c4006400440340c0311068108003015551102c41981250500301141c41d0b032004400709904111900d150005011410740300c01d019041e0460000c0d801451003183e506001510f400c00505201c0344001410003081c0d9024001e468008030306e8110012409500301940302906020030140038810350750030400002024070303540c82542c046140e100300402146041c2e40d46c003642680000d00b00000d01000c1e140100324549207105d810302030019a020049003 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 173298938 1250 173297688 173297741
    0x10912020a0c120c3818030106080d1101020405090c07020a06080106050304120e090a050105120a050a030503060307090207030e0a0b0721110a0507060f090605040608100801 76
    0x440700c01d4020850010443c40014001501048240700b101c00004110480450000203610001803402c2805206180c00f000540c40e6079500000b400c07a0140000030510000c100000d02d4280d40b40c601c19192030360094900c045055000e095003004800d94040010b18054444d4001482e24805540c2e04d00100c0c004180702003141800000030015080741c3c101030360150f1611200a0103480300620080c5000151084c4059003070051800c1050400002c00e0300101e8900b071240400205424414144250300d00608180d10038000b04500240e1030300180680245661618141c500c3d620203003549401d807080312400500041c1c10710160599601c25034030307036400810040c2007282011090700840f0403520f04111000018640403511603510048000c0c080001002c0b6100341d80c00c1001410020450084404160410501051907420f441c242d480300d0f0040c01c02d958003125840e0050281d1310126004001c01d000d050b0254260980c41102c001c21001090303101c0301d6050a45024400d030310500403490954825 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 173300188 1250 173298938 173298953
    0x6040e3301172b03020a09030206070b0406060b0403030507060b030708030c07230102150403180810050a05040f0308060f0a03030806030c120304050103020310080109031d040c0801060e03010912020a 87
    0x1a05501080003003005040f0029145003450404290041c554006070928989000c0c0500f13500451300100501d880e25940d0800000c0740ca41100c0031100946010004248a4610310542e0b09598040e6030b07a5080104603914000180f0445d490795070305200c0c181c0c000849130020001070004001010181280d0b520f4440c1c11032201609603041c2504c512406245403a82c2d0340010070010310101000543c910351a20b080540d01840183c00c190562002600d000c524090002040c0b0501c031400f0300200320341d076200380c02081102c100341d80c0145a031606a8400c00030a10442e5000e8000c5002848500a040d4106c001050f500c590340c0300700c011484240410419280601503081040002d45d00c00f9203a1411003407140d1244138a0082605065011010480d15402e0320f00748405054514002c03c00d520b400d00700606800031441c001c44140744805801c1c1d4050030107024102182c50991601025a400c100003910010b82c460b10064240d0750f150781c4140804d840c6068070398038181e00d030090850701025041070752 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 173301438 1250 173300188 173300203
    0x18010e0321060906100e03030a0203040501080f061809070905040c0302040b1002070b0c01020c0d210b10030b030c040c030606020c030102120a0203180109051506040e330117 76
    0x104031035440801c02282e615014015a80306a044400405002c020981603886034403480256405200103e20600107640000051007038039826280e0007001d544071081c1d200034030340c01ca550f2608600b54012000210001c0a0b059802041c01007d40c1d03480e47d1105e50703000454100711019101c00c003511608009600b014411082c4890095420781c0c3d4410460f440070350790304458418041940d100103842041c1107000e50507a049800b00a0035200b0105145800800e01e503105000c540040c101a2600800c87d0558400c071481610050240503080428400990040612154454042c061207921174090740d1a44540101d241154070001041d84c14080000d00d00300200036090300070307881005064040b0440c8441190300188100c00507a5030394070910850036130300030410590020b41c00c1030442003c01c40003140c03040d40030030003510300d8a490341c4010400050311210b001c040825007004c00260404601c0300304a84141f17640703001034282c0601d01c1c1c102ca040b45100344d000d1105040c9908205500c08030078007400 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 173302688 1250 173301438 173301487
    0xc1e030917031302310c09170a02060906070602030a14070201091e02011404170c011412070504080a0c0905070201020403020307061b080406031b050c10020318010e03 73
    0x440c00c500e0f1442c10040b04880c103203000791041d817404905c066252000d54480004201c000400000b60003580403403009050940d102001140005002003140804076904840002d000c0009001403000c50302800391a80c8924401c0b0740013202007145001203882400298028480f1820000b60241c2c21044480c0008010302410304690400700b40d4000305040305400d41c00d14030aa6514807070915184010b032880e00d0300e004406640d200100340040c15220540c1c0000c150103030202a80c1c22a280c0c01c00454038851032011000c00e65505025803c2104c0543c42901cbd0b0104240c28502d02c1d058a60b1501850901103010855050700a14020b0094003814040c0c150440e01d180000c1d424513056500194864000c1d010f0142040112481c8000014610311031000e1240c1000c041c0d903845813650801406031040408103201d0301c0000c0e5038101c10910460440318420003a0700901030904092500780c02960026124821004800c1103910149a0a200c2e801891607100020341d0345404419202ca549040d03440d92 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 173303938 1250 173302688 173302733
    0xd0318060504060c0615050306180f2d010f1d011406060a210213030201021c08070e04110a0e0a140607020904060207050109080912031c0c1e0309 64
    0x4100e07407034118144513009584442d022810100d02d00d1600c0c103801a540c40070340d15200c0c400500c01030b21140ea581082c00d0322410300f55102d14519042d20b9a4135411381c15050089841d0102e4402d1500000081c51304520f5240008650f0448c040c140f0020747c0c62001c07070744906038031031003030409101404d204201e00c60303680f0710780f540e00c9180c00c0001400e80d0141202900601640c114100c0500d08020002d480d698140740c3d0440d22114542e900035007e980703601049004d440388240c000f80c69011813045901c800c40b503a98090850b075808070700b01c2e1040b40c40303410903400907201c21040164195200150242880960319503a2000a00e0204010482c456000c014001c860040e005d80917103031941220100d81c0c050b10850202e844901d0300e840203200f021001742207940307800704041c01c11080c0402441480340071a0000351282c2d21004050f103c4c40f681030189101c0d80f40c0c0403e02c65103c090b40001c17a12140604144101141c154100c190150280740050300003a500c80404003001001448444495190a123 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 173305188 1250 173303938 173303947
    0x609060a0617070e10170307060f0b0a2105010e1006050a0602121303060f050103030315120f03140a030504031e08042402121503060f0705030a02090d03180605 70
    0x410a48440c05401070b02c114184d000c0c0054003001c6200c1e103e50091100c5105ca20308400c1000d551500c94220b48c00c2214030500f0220149803501a85c0900100c03400e00a06800c052450540f003000090844500c031502ca15031004a0f0000c01c40a1083d42c01d0710001c500139107400340d07400c51923400711283e0b44c00030351052600741418880d85a0000b8020b8948242040245d650034042c0d015100f2611603a00051a003420024444616089500054101d80c0300f03403014410903021641c2d540c00c0d06400d009401004400303104100101d192050300c5000309000e4100b8401c2c0303010280d908007039179110180310004a0b4030b81061000b0182d1008684a01307018038114031080e00e04a6200034500300024101420150100c140010155039000b240c4c040c051910000319a102c041d40d070240c1401c4422649110088507100300718055050109140e071194007890310303901c421356414a09844a80000e80103100c420303402e00580c0344030784402c0c4003081e401d40039490380d400640303001c090440308580076002801003280510 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 173306438 1250 173305188 173305229
    0x5010f020d0f05041703090306060105030c0a080408090402070f050f0307111908010510030318030f0308070c170403051614040e010e0d0503061002030405010e060a110609060a06 78
    0x103001620210305252064882d020424120303454090b075004444078210a01443c9040c010006c01442d0502c0c6c03d40959060f0b81e5000d0041d602070104852846090b1700410401a10a101c0c6418a50103407165a545040ac0841c2000c541242c10102c4101e4103e008070b058003083c050200300d200c6041100c07500451610009940d0049102100005540640400700d800c2010b01074600d0000060603030480200b0040c5009a4121202032a920003031303020401c504480413100c0310540c51842681c0d0011121062185280d0341101c0c1074070002c18007810800641d028500007402021542213480b1040440c686542c2542000342c1811114040511394151014080046000400074102c2c481006c550010300350040b1801d9034050040404100322074050314900300889074001c8080c3d8014401640c2401e0500d8403c40d05070307500e21450103814045590880d8541080c42c16400800340c403aa249001500100b11807882e07450034030b040e541c52009070081410070031072109034411240108074510302c8101445014 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 173307688 1250 173306438 173306443
    0x60a08010b030715020a0203010509010c090803090607080901090b07120f0201020306090c031305030316020c10050403020d140307150c091a0a03140c0a03050a02031509040302010608010c08090705010f02 89
    0x244500c084d040b45020f850303020345000340041d88405130090020b10807880d245544a00034901071242002244044001042003e000400e80d184120040d04807450540c00740c031a058250040101c850400c02e03c001e010070525511005803039924130912340c12668402c800c001800c0382d1072044a8900b107a02c10b008105141d9a84502981c204a01070281a6640c5074803002041c400d5401c040507041e03101c00018030000021040300742c01c15547c02e03401d40e42600300c44010001d510307040300f04180004009202c20300151600803010408217204840c400c80d56001c9040e081d0854100b24400e403100c0c402c2a08031b440d00b2010380180c00c0c001c1395074949040000c0c01e05010090b1401743e05800c0d040300d8000304940352411f000b64080e00311604400203141507450a6802d0314819130009840e580043c1c00c00c0e002c514500d00900913a8040c404074001151210320300014001c40b184010016821236483e5500000c10300310a205040c2121420b41e55009035180070346801e49814500d078030044c10080c61800b11003641c3c3c0d01 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 173308938 1250 173307688 173307703
    0x3040b04020111151f061e0309062903010b06040905040c09110c1b0d02040b01020c06040906091d121308030f030106030513020a090b04091a060a08010b03 68
    0x4411200469115800100c0c0c14034203c1c8240c0025200e1221141c140344000c40d81c0f544920380812403506410602c180885540304188580360200c3d41c45452503024072846009040032a01d54640051010210703280c0c0b00599aa40114980c50703031564401c060f071285030310f062202d0703200305030000e00c031201120001c81c6940c401c03445804c4000380c1c0c9201003810000c606070300100030080310105102041c280440342c14580c1c40300c030b141d409030304c00c0ca0242d00815003c11101035910b007005154440060440e024440039000d0064814114081c8143c1103503107942d00c4c00603101400c50b04100051850509801070211520400d86006c84842c004c18a08000400036031069105840002c880d1106a240c2e152119081150441c20340c41c000401c840044018020265040320615a000e020a44840c08410000c0d90f01030006034124580d11020302c6640855086420070b400064000144800b0946854100155118044488800940601c4498540440c40c03102900010000704108a01100042e554405 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 173310188 1250 173308938 173308943
    0x2040e06090a0c0921060f020306030d080103051228090501030c020114040305070c0e010303020102121302030607050c031b010603020a08060705070b0402040603050a030c020a0b0702061c1b050903060705030c0304 93
    0x4221140c0e05c0b55041031a220100503440201400030002640c1c5e504082d40003101c41c00c1c02441804800801d1612900304641240d0f009000780400304508101d10401c2d50107540b02d0701c01c803041c0841c0c0c510410440d1092545030300c540d40d075880b4440d04020004003900c6103100010110380c104928405010012000d2941095141c24000d07510000fa2400071403061155100002664807407000006151301900240950703900501d10540d0f6903544818a0401ca41d8440c001e174050307104000042001e8000e030010300041440030f0845c0c0c10a40c510301c40d1103d01090400841603a5120b4074100210304089100340c014003002009480740d460301c49030050503405102c00c040c0000311950b0100702551159805240990703007000964003000858200600030000f0b0360412070154030494070004030070300800309603080e83c0d034010059440c0003001281740200c041d149800303412603981d94160022040030600e1901900040d502c5094488110710b04050070104010f180e202030000c1001000001692070b011030798085c0d0b = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 173311438 1250 173310188 173310209
    0x6051206040903090305061e18030d0f0b0a06020703020a0b0a050a03090204150311120606030c0603040501180308041a041e110a0b04050f030c030604030c030e0402040e06090a0c09 79
    0x10381012910f11354143e1000e07045e8003980051041c40750291595807403000c40000e130000552034a2200d81d80c00070703200301054000e03002844810250100c2d6080b982030141c0d98140481c078821a40001002c0c83c019a002c240940c0c01901d04100f1801c2124070b0350024141d1000840c1840c1c481d01000d002c603c6241c5006080555419188085641d940e0120f8554029848050803441e2213181028880d1421545144243e12504c12003108841c0010014031940015000c0c01e200b40048090001c1b030f800103001154155219014240c040111143d282d01c241c1c047d41d45c40f401810035061081641e079050100980c00b40000041002141c0c0900014041c45510140d04800c00c00b80d041441d80b49403c02802d90340851050307000280c418918018206545080303444c1c41c081d0b5005002c05581c1d6040341c0f5140c0c0c054214a0018010902a50381d1048280c02418104040b0070300d20b0024089038015007028146020301b1051081c0da003400912940d0006c00c580080180e020a00750141c42414a841040b0606 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 173312688 1250 173311438 173311451
    0x211003120c030903080406030617010e03270303030a05041b0f03120509030f03090109091e15090e15010b03040b0a0203070c17030103030318122d0807090605120604 72
    0x2d486040e9400c01190040310a070b86594841030001c0150246120340682c1d1090303e8681d4943c43c10600c00c02c0101134640005519013120115401140d940134156540350031f21103e1401210b840c00e00045100d9600700f40005440c0c03400380391260f41440040c00c4114840c81c0b040c0e0600c441c0c1d40c00c8512000752600115440070000c4464811225803056091f641d425000d62141d4841d030400000150065100036220404071a407601d840d0000c40711849500120340b400034005909840c4954803a103610040100b07103026103910b6111407070a07a6521050544540d10100d802c114100890b0107003405084441c0840e0b20f1801e0540b10340302880005070411040d1640040851480350099401c5c0c40015440991824001d0b840314050384203800034401034000c0ba060a91017102c075480644140d083d958400c0c440c1888030408001244c2580f00a80e086c0307130503070108040414046244083d11400501c540d2584914907000ca8011310403000e6a20001c1801030a00107030140960b141d4034642d01000039200000c01 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 173313938 1250 173312688 173312693
    0xa0f0609091119111b0105030c0a020c0303040b04080705120c330c0c060307090b09031203190b01050a23120c040f08120304110103090602211003120c 66
    0x2070b440340320494418108400d240e48a81038120341d2018100d00c44505a1764110b0984034440da02d200115480b500140c03003000020440b54103040a01951100740c0b0440e03074140f44503400b080c135540c090b410102c040fa80200e8100644a010040c4030f0103410107848621707541d055080f060b80d0304e40c0d80103800303131248486404042209413071011b500c404402801241c8580c4104271010300495001c3e606091550049000411041c00c0000840703020740300c03e036640700e80f044ca0016960035513040701c0c1c040e5905000750440d410846452402440c06003640590b61085148902c801c54100d5502c40e1006051120a021808e40c0c01e405c9040c154080d40c100381c00c0800660b140143c841e80703120301c40c2c424290b4090801070094180318480a04150342a08004101464444440d40d90b101c074620161108148100000b6000500e0f0b030392898041c14040c10041101c500c15510306090360000122006240380311208100400c20b050ac81942210b110b040c0e00305114210307240d00c0c58043d880c00ca24000d0044480e980d104 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 173315188 1250 173313938 173313971
    0x5030402040f0e010c050a030506030604050d08041502070812060d0c0506070320010b0909030f070303020c01020c07060806102a0f0c03060c0801051905090c040e13020a0f060909 78
    0x2c03c04209000300300503850404003404580110450708002031a04002401900b00021814000c54116000f0490104549030032100c440001701701b1200c50191511a0600c8a00d50000d02401072007416095141c602e05015074818401c02400341c1e204040a1100c0c1010074003101d00d15081d1038064030034aa90308031324201a1000c40e5041d4031100d00c8000c24190030b0100e00103510820046408442d0b0f02c0b400d80769400001c1d6680900116504603070340401038140000d000707a00420900c3d201c40000346c10b02080490a03420f00085520035804542000d041000ba1f180404205d0003001d12820003070742d0407540e0800a460344008480943c41840703d85042014450848041d41005030310800d2420310340c2e1030f0700d03000b40545129104c07000071030400400030595140c043c005d41c100e100080c111010b02440d08040104001025040950101040102081c502030080c283d6200c0c110b10a4241c0c4410f11601c1402030401d869404402c41180340c24050280300c0e0702031164400c03215100400318042100729240c84 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 173316438 1250 173315188 173315201
    0xa0b0a0506030f06031c080601202b1d0d031704050a030f032306061e13050f0312030a02090405040308061806180415062403060605030402040f 63
    0x1584a04044200004075035034050f014030485066003503908065104000030301e400c10b0444500c0208800000040071948500f2100b503201d50700080c40048000c804529900b440030040b82076021a08000c00c034085c010312001c00300c13450304080c501540a10140c17040340b1000c1444440c2d1901c5040b8100c4220181440780c0c42a80c5081118094040141402d00d0183d5456801800403404280f07a000e070300414500911881425910740540782303280080c40342c400045050020078040d0702c04c406006401049414800392004502000c07459a60b940d41c010117101d4460980d44040d1041014211000c03035518003290244003241d1010199031a5120303030031418040d001d402542c54200d0701d172004100615900c866401d0258070140e0308010448815004140a80b42c2111401c1c4c025038490b01050703208601302e008a5025002e42c0f034110355080c070f43c0a00d600740c40c960746c000c81905414484e070480d414031488140d030032a031250600b00300b00c501d031280c050300c6030100078406031080e0b0740c82e00c1000b908040c6070005c1 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 173317688 1250 173316438 173316449
    0x2301020313110901060c0609020102150c090f030319050310090f0f0f0614101e09030210030915020903190501050106090f0807030204020906040801050408032d0a0b0a 73
    0x9645901d008144155058507a00040e2040c21800700307461a03604010300c0041c16502c981c5e90b85008021661562400790801400481c118800c0a400743d541c118491900c90040c007801e420941c1c2c43c13b80ca020040d80c0d001e4948603d201c2c0d00308200d080b06c0c600c0005070300307000c41905041c0345880740e6038180458044031565200d8070002c2d00b03054161000d01002c0d80034034030442d0024820065040081c41c410210b034040c7c007036456014a008462203407460141500c032801c0c650703868840003000c0e0f0508001401480c1c900c004001c640c001e4000e00031403130100c00f11800401107190070042d0011648a1708005011441c92100d13090780000e4003c201c1d00d0070f00a01c0021005103443c00244070301d41c6802d500a1500348104000542480380109102814141610840e0302c0e0300d0042c250700d4219002c200c003d5010b03e0a45602c00c1041000103078003c42070143c0780c4214001c0c100741e51240703082c040c0c880c0000d46181c044400d41609011900c1424451010705410065820000071b80088500c0032840141168120 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 173318938 1250 173317688 173317691
    0xe12070b071b11040e01060f09050f0105060f090d03090b0c0607020c010201111c0b1c02011205010e150a08030408013306030b0310090614061009032301 67
    0x4205106010000500607402990384106101061800354a000c40c68000180802045000301c05a03180a07080441104c10000000510030307520400900e52044680c0001101501c0b0707400c05c080c05004408050041c002503441528203c0318001c800480d209529190388144040c680c01070a06108203c000e0180c400311642594405100b030401d65102c0f4125081c1c4014032406114945551060044418455212200605106814038141c410060003602e0420382a81c88042c0e003140e0b61451160f4200002005508403035441c6ca000050600200300e07280021242000010407031480f4280106d94800d15480c25a8407417104000051082c4907940d01940c2144408a408101c00d00191b00aa00302061003110b07202031002003d4601a01082c0c46840009401d285000c1004034000e0b040754103445070080640b49440500712484080758040c1e401602c2080e9164076040d00403103401c0583c1d03005241181c008000d040998001050214107010003000320701074440110710b102403820010441c1c0d207075400 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 173320188 1250 173318938 173318947
    0x1090213020d140403021c0f12110c011401031a060a06080601180f210308060607030905270901060e0a0207080702040c0819020a0206060607050a0606030c08010b0301140a0e12 77
    0x400035956103001440c07c1e50b82d90000411903510340907a2000d81c495003d500d40350f207030a012407107020040c049030140110101c400c000000e0780020a22803d1886a0140024042c1d5419400c0c17014100011060103e42408044240708150b640e11269000319021494620300d00d0755200d0040711145522116511062589200420041c1c9008092400c0d12460504443d030301d1240c140c000850348203020042c0106800c90089035442c01c1140080050b20b009090070f40300203a03601c0118010210720074004450703691070355186005031034020889410180100081c0540d030300303200184030700c0407010301140e46c216130001e582c604001030907069802494005108001d640000700c409450084102d8a84003600c08035030401401c0000303031007610041105a4000c00581e543c40e4240540c07540250780a44440c41422451070001e21940145405544154900c1c000c551904242d1030a4800351443c0c94817a904050120b9607100741c3c9000c4030381c0102c44120102c0e1181c1000351080c104a00700e80d2882c4030030300004 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 173321438 1250 173320188 173320193
    0xc12020a020d060e010b01030216020918030a121109010e22060b09030f03030f010b03040204061806090c110c0904110d0b061305130b04050304090c020f010b0301090213020d1404 78
    0x2d103c921641302040c000e20001410000450492042c00010643d0700400d0095030054141101490750000ca071140d10184000d10404241c0341d80c0000449030300041d01610f141c821016540642590034035101c40e06414190b10a0028040303490000d00c482c0513008108514901074103100803500882c00d401c40800c50903494140d6011540e010780c000d40e0180c4540c3c0146030881c440003046901c20880c03c18070b2403041e4200405210320381c0c0050000c0c2c0e406501c03040085030868112003044880d260300c040025403d842d001480043e1202540c05c0f50500c0b0703021404ca070440101140205080004951201040c3c0e19407074000324030b20b01240d4194206c0100c00e0000100840d03042c0c03890242d0000c4a031401c0005d405600710059820840341c2d002c210b1209080c51002607914001d80c1e070003c0c40765059909240d291026a02112955110100182d100c03502d6170750300320030a11596601410a50090140152917000f19081c1712550300301c40c00c1c03d603000500c0012100140e0020050554200614032a0300702170 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 173322688 1250 173321438 173321441
    0x200d11160b06040b0a08150702030f0c0c0f10021f0609150314120909041505070917030c03190309060204060c110906090705070f0c0e010806010b03070c12020a020d06 73
    0x2242d500d809103103040f40c100310f03624004070114100d4184030010442c5250000c400808164054040343c10f610090000000e107180f52009000e1101940303005100a017000340030040c43c81c40c2d05c011180910b6801010529143c1e011031400c40404550829000c84200c1740140c20040550780e2000c040c0a01c0e14130b200410719250500d0000b100d0043c0340244446079203802d01600c1d03d000c14114041403404001c8075101d402c7c0314581c603501c0b034059107807d1000c800869200060701c1c006c0340c0203c005074a00400f0b1002c0802e980505582a000d00011400c2c401c00340d00469907440b99201c880d41c1403400600714413084e4407076042411002ea00c200d048d900c0350340d6245c1c06044a0840e00d000c5605c821740344484091420000d075150310440000784007005d44e80325000103503100c0c0d221403001d6030b000941201c0d100204d400300304d2150013800100d50318440303503140c2b41400b030801c41c3c1078004240e012010410300c084168000040440741e50410038900780d01c54042c0302a40f4002a156000703402600840c6180e080c04802e = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 173323938 1250 173322688 173322691
    0x510030c09060207050109031203090f06060512070807120804090c030203060a0509040f03030f0b03121201080a0b0601120f0c170c070c030f290a200d11160b 69
    0x80d4039480c2030703103031510002c0e6280c10880c040c590001d0b100078401c0000c81e0381d0f2030080700480c2c40e50a0016446402d80c6a050300c1403ea8a41a035500d0b07140c844c104a20b0502134160396107e1001005428564140b2801c9030300c4000c1d500c03e180f0301c1c01813400284103000b070800441c1c0080030529000c100140f588400a0040d400840b19a88514844030000601d41401841c0ca445035500c03a192142d1140e9a40c1e0a0b0001d210041020750742030340c0e400d103020140d102082601c4036003403040e81094035189800d1540035400300c141c0201117660441030b480030014500205c80c90f00034400f42400701c000e015a85420b00100407031203030a683d190600799200080c40d001500d040501c15450342094150303903400b220440d0303440b51000c01000308000d1003007000840d030513410b00000e90740310300b108003800611401c144d081c4110001c840d5412649007020712582c01824419008203108a1001c1c002d008003c0d00c0214460154174210b4000c2912800c01d83c000502e50012100341c800d500c4000d10008041e800c01c202c0b038840 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 173325188 1250 173323938 173323961
    0x30a0b030a031107170607030509070b070807060510050102100203070513060f0201060e13140a06060308030f0901060e0c03060a08031c0e0714120c04060b0304020102100c022104051003 81
    0x2120390200325070a68810782e64291783c1c0c120007081c1d95203030450114007c000c001c0060190b40920b1202150b8044450020002140a001302a4450b00c42d4205031003101d0016141003141070225108001991300400c000c81c580c000410b006840c0e42d1540001c0c5c40c248181c0072a542200a03854020909035005010707034040d8031555000b040143d468414060040c001a10f1030780c2c020440d009030344009858a050101220422001d9a281d00c00035030321030042d9400c5410031182e80321301100b000b401c02003144540b544902c1e01c00007401400d10300189110000c0000d45030006500000000134126200d050404c0010410302c001c4036500c44000c50800800705024010b00300355420440070b2001c0110010700c40c026950f114a4588007504008100030b030040802041240724041c5400308005d0b44c0c1d4510540d40204038441c070f45079417490703d48002400d21120f6210294858544072071480c00c11741c001180c082c948411011829581c03100d0101c18140e0145178000d640c031403400b900305503465616400504821780e = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 173326438 1250 173325188 173325193
    0x1050f010602160608061201150e0118230408070f0501022703030a180b0406120516081503010608030705070e180a0b150303071416050a0902030a0b030a0311 69
    0x220040d0425090102600c1a80e000502001c04681070380ba00c0f51044240c1001000002202700c1d96003454001d18003240d1091302c058000350010460b0f200216550303c1d002445400802c182d01060628010115a00f4204803400c2c112030f001030204007074401201d141640122030038864800500d00306010b03601c000034ac1f8515421000d040311001c0c821b00c00c004004507008010394180500718008499040f101209440401403038040082d503d001440140040c0140e6a103068441400c01990f00541304081e04001c82e5042590080460a03484202240c000c1007003400100b00103108000240540416042b03030680307010000e282010024006100030807540d03004a842419a0b8040c2c845060441000d1800f0740303604000c1e0094001000004015440050038070001e1030b444812000c42e280d500501000c98101800b100d000904031410005101415103889841d04103270704040100d0200c115900c1032160b02500030001c02c620107025001525401d81c041c040351303e061240d080080c180c0c0e01421024a060 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 173327688 1250 173326438 173326453
    0x80c03160f110a051b1206010506031e0c0703081501081501031116020f0a03030503070c020a032310181121030d0f0c09170708030a050901020105101d0703060801050f010602 76
    0x2030030007800c16031b607000000004d0940c2d42c0ca403070140005503000501100c50604150503101010740200c14060094056154241d20303900b5500d4040d11543c00a4510b600302e500110440c072140e80d2092009500c01e5402004244400c11000103038090b00303c8151283d64410003140301c0482041044003454498001c46001c0c90a281010510500203800e0001a0005000b0400078940034000e8144400085c4080c211a040c65982c4e10f501c02c21808030302d01c54426655031680b4809217001000020915642410300300310000e2910300100c0e80401214005100b110305243c81c9816558115680c03e401080d8860301c05203090082d500d03034403a0b010071110900c403468410201020f16191085070394940d01900ca00d00024103000321740d05803002d25801c50710180700d603100c0854501428000f8003151100da4440079200d144a800190079100000c0c1070740808070b030380d10702042512110600c40012701d12403502403505803601c000890150003580c101c0310f007640c240403d02030300e1180038184a0480c1c403543d0940c2c040c03 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 173328938 1250 173327688 173327743
    0x1060f0914010219080403120e040506030d02190503040807060302040608010b16111c0c05030118020a0b09120102071109010b130302090a0207021807080c03160f110a05 74
    0xc00c807840c907003801a4000a5005816045a240d03540201e02650f000b030f05040d071ba60b45800301088070a0403000014201108180c042c10a4050300c0d40001c01200a0800b405031003800a5440c4030100000c2062045440742d103040c00010701c1102d0140c10004140c507543da03160b50700030f0040d5001e842404000303101c0034000a0041180e02c15150500a02e404c2c040a041468407a035103440784c1c3c01c0080354080b48000010360111009861113090600c5141c2100d1a546070408150848101040d0440c0c012507030300061005079034a0100ca810780c1d405800140c0c4400d40308002c101d00250600b440420740d80b0014490301804030211118000c020115500006d5a8880b81c00b6001c9015014842100f092400c40500040c5001045640e01c161413650040c01c0035200e07000124000d8154250040000c00040ac0c82452581311b1541e0b9444050700c20046e00d1030620615520860381552050300070020150001e401c500e200c0d880c42c6103c135101c28103c4850b8203240c00c0031511800c3c6020700c625080e03d03202c00c0038030 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 173330188 1250 173328938 173328959
    0x83417030c04030f03050f0a18050103020702011707032301091b021b031009080403060b03030705071a130e09010e0f0a02010c060f09050d0206070306050a120c03060501060f09 77
    0x114885201d034840c1814950707915911010500750040b420320a0034801c020690300c2c0c0901400c00740b80d00c3c1e601e42444488019400c0320240c0b10b50017042c1054010000b10000d42d0708240c0200161201800071a4a0394400c1001c81c01011600c1e18604080314469101d600c9405142c1a9030590307074040400c01030300141e07108080c0c403010000d6100015030418401e80003c125003100d80302c8000b0015003a10f404040c9121690202e43c507041c0100c6031890003003000e005001007442044003290054004500d05915500d50320b58581541c800c1a000c821303070001a422864402c41910204803188202110541c1c5542d60002c1108003214045825031808c0500c00c403216000400a240a510602400481001d40c00454449501c41429a65551980080300c42c0903158494500014000c0d0046d10313420718040c900a0400202404d440201030400c0000c0c4443d5560103500000c43c1d1a101d60401d8221103841d2080704840315900180c06603140130300029109400400310303d003c3d480c41e6211400f03c0d44a03651603c = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 173331438 1250 173330188 173330191
    0xc010c03120218190608130201050f0d0b0d0602070b10030209150d080a09030b070315090504031b05160501080f0f06010c081903050f06010c08341703 66
    0x90014040400035403503160a680240342c09011584080003c149920200d960f03c5500e1304007168004c03c0480030040182e009182c00c1c0c100c4091086541820600c0e00020140d01483c150003d005c1000101580c464015500121151390040c0c60405a03800a051000003900325540c250755003015000040c0e50000980c0d03020f400e503603000344810301e6038840d15010703110f0190314108203030000d000c04402030201c5d0520b0040c0100c80c01d103a5801c03899608503c3c00b21040d00c8003400340001c0c50300300340103d02450380c01c0c7e070840150382c1e58500009459861341812104c581c7d035401d14000d0050102880000c1c40404541d099015469140194019544800456036080112404004d145044001c140c80d1130350a211960488014504200e00e40e0640d110790415a019891f100d8018014056600105806003d100c1d40034124107122031952411800103490483c000c10000c083c0c000010b40b0703111790117101c50303c1c03858041ca038202c189081c1c0e58182540c100c0e81368140142c400d010300701c001c8100306180a007100e = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 173332688 1250 173331438 173331443
    0x903070f03050901020c0312040f15051920010507091401090512330a09051f020c030706020309060c07020d1e0b0a0504020103060f14010809030c070305030a020c010c 73
    0x16a5003803040d281281c8039004401d640b41180141858015581d908111050102066044c82c0f681d5503c1e21100440e070222540c80811074800c0c140d4481c0c04a6084803d42e54000d0741c42080001802410000b1292907401c2820701d44020040b82c040348040805501c004d20801881e160310040c280c07210005000f0940802609001071290320003441241040c00705020155440021140d03a02c000030341408100003031201c400112800c00b04205484000380c3d8045801805000c1c1c100083e1209446540e1074841801e864440035117120200001e00c0b40f10380c110360142c0300ca1415262511501e180c0280a0343c01611141254407425010174568600310b0308442e040c0e0780c001c00804410305507a9a001038114800c503800000c1c1d4030340c02e00c00c021803004003603e4440c11a68000088c0c9161034800902150032a401145500d4080c03a01844040890355441181e00e1090820082c16521a05003500d588140007090101d400344c544000104000080078000e00d04003a0292006401c5610044901c6001941d01 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 173333938 1250 173332688 173332703
    0x60201050c091c020405090a060b06040b040e060a090f0c090b040f0e0403050d060e06211002070c05040906051b0309191b0e09010c02060c03220f030512090307 70
    0x190401481c140c1032983c0711501c034181c001040062500080e04550003264020000d400086061080000501c00c0c00c84a03035040328641c0c2000e0518448801c14000e80c0280040c0385141e070003040305580c2d41e03201c000003403413a03200c20700080d8840b0b02d030360010386070301540c44000c00c442c10000f103420300f100003c3e5400d81d840040d41c141d0082c81c3c050f010101e80005001a400d01c081008040036071511070003280301620b012201d900b1a420010305102c09120781c0101580c642041010072a40050042855110315205000c0561581007504220b130050505d94072242d8031a1910101c0e81c100400c94011500c9082085c1008054610ba810303407444912040325003246541045a0520400035680c2c000d02d512402091001300305168210038880da0b10081d04031214065a4008102d8000c0c0240660030140f034140c405094a03041844092401c6e010107083d208081101140015010301e40d01050200c8a410511981354240706080140c401e0303200d071460038660f51180c2c001a00081c1c0020842d810107038020319 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 173335188 1250 173333938 173333947
    0x403020313090207021309020d0c08030406080109020a232101050909030403030504030611040b13090b06040e041203020f161203050601170402040b06040303021b010309080f0c030d0f15060201050c 86
    0x91160080047c003400307c0e80721450200f49004606482411400b60070400d006683e91802e00c2405055950168480c20b01d1500403c141c1c150164007000042c580f80d101920004440d00008420b941f5001d0030748081c00b40d00c0e1a01203015030401603c0070030704039801a10304070100e40700e00801070307100e01c240d000180105400700010000030317a01e0b034000b2000c4012803d051341032035181d0004c0e68259000c1500101c070103101d00d4050010700000c0c4125030114030201c803a140341c50302c1c000680c00c03404001007010340000310310231041c11024020340403034810103c8006201daa482411b144034510f103005800c08c0d40c066036242143e44056000780300b0140100c0c41611121201d8003690076908004100038412600103880e0001001c0d10f0300c03040f000c0c10140d8403d8000c3c05050200302800303640003100b88c40480c100750424183ea40030551450890b840305140440311a80c80c0c070b44040756491071060300701c101130251400070a404100401d511151004d070030341c20b25a0b0f803160f42c0c400403821303203505550a404030b940402 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 173336438 1250 173335188 173335219
    0xc040e07090b0a020f0c041505063f060103200702011e030902010813030509130e07030f0b100b04050d02120d0e0a080a0f0605041a040302031309020702 67
    0x25940c0c08802803500340c1034607072649110780082d001000301c040507a1203003c3c0e07003e02550070b06c484001c6072401d0314100248030300c0d590819a003070368501c9a0b9001e4a4001400d40850700315030244032011121001e0207400030f40e020761341d0100804054004e0005a034410201d822580300380039204c080e0042000e8030a034800825050092a800160202d040c0030100f00da80c0046000c0b01c420614403506600d0000b0000141d000241294030010900321240d070450121600085e00002510784404013903d02e0b120008800048400402070b0038043c03411032103042000400c00070380011003502284140d0394031986446003c1c0f10301a0744d2080c09140e085e9007050200b031009082400d14442400d0000703000b00d40c40480760041d54140481007200700c00050000c403000182d42041c1c40c0740c8004104413002401021f5041d11070420b1f51900220041c00551188003080500c07105040d9840c003030010b0150748041e0308103031902a540b94440550304900011480000a400d0510300c01e4464560f00500314522040ca0785 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 173337688 1250 173336438 173336459
    0x7020d08060303070c0f0f12020d121101050f07031a01020606270a060801141504051905090d02070614070209070207080709060e0f041e0302010609022d030c04 70
    0x20495500342c030044c4802c1021820110540700180402e00f0308000042c10000404401a4150000007240340022000001610f80303039600d5403059006504014414a952400c8071115003402d03031750729107608100a00c103042800b03c664078060001c0743c5081044041d804015480e000e0b40211190158001034005012414100c107000b03054110b01c1010721030034410058100c040c0d401543d03035868141e5544004d03c050b46d4240b0035040710318514082c800480c0b800008500714904821822805a604d850100e2400103184180b50607003c120311050244d442d00110559441c1001c0744d101c001482000d074000307100c500505500f9003c0708030820052908032660240802407402402e40021407107800000610405d040c821100a0410b2100205c2c40301d1a2682a581c00d0344060600e500c0c5184217410710001a8110040c240880030404000c0b206408500701a0f00401302940000e15003400003c0d01441040c0e00600c1d0b044000c1e0480c400c0b40f444a282c0100c9082c0e0008a44c403800c1c80f14104024071199100 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 173338938 1250 173337688 173337691
    0x140d0311010b04060e01030b0f012403020f0c01050f100f0509090a1b1d010b03062806030209040e030403031710030507031406090604050c060918090a02031507020d08 73
    0x100300101d0800890790100d02251143e0340103c915001c0381005004102086000b142c03c211048081242541002d50085601e2017801c20890800301c02c0c1c0640c00d07868041e4050700d28080d0026503040d15418801d0a5a01800f011522000d19048480c00114405210b00140c020744d007280554480c0f942c10314043c050103140203008001a4810110301e140024850804603078940c80c10001e0318522803818012050801064041000300039041c00140301d02040700742582e03442401103500101551005001e01240c2c04488880d03428001da460011400c1380d01340d0010002c0070001d031010084550040c10886d103a01407408020009000000440301d152030300b2401c142c10420070110804040d949540d954903011659104464203146030041c00c140c40070a00c682c642c800c1240d40038000510f815907034203885180d00c595581c0300d4032021030444031075180d40200304000c502e40c52403c2130b10b0030104c081c40e81e16a003954003244244140640c1441030046c0b600b1407402449550000c0c10300f5042c0e40415520b0711340 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 173340188 1250 173338938 173338967
    0x10e06011203120c02070e0906090606010c1401151d040f06110c030301031127011703580b061213050705030a0221012901020106140d03 60
    0x1031075800321443e07941c41409000034840e001000020f14040043d003044100a100480a811020030001040c1c40410081c0d44a40d0901c1d01144e00c2c4514903200c5c0d90f050b13400d21403400325881c00020a20010512000c002501c0c241e480d0580c084002c10104407150740c084500034a40b5024800850001d055604240588242141c10900706440a40120300c0c64200341e109850080d00c080321104903003031040c1c0031403040480e180d03400a0ba04070480d000b280000c0601c10000c6040302d40b411000f40f8642442580c80b000b000e048003840c000240a0300d90617000b81403415040720345404041d43c020400312082c440d0011100b0010350501140100304a00401e448006140c1000040001c074aa524510400910400b280c40315034154525904140349030040030380080d4020751081e0409005a91130250030030110f0700c4207001618001e14200103c0c050315440c1d084c5141440035600c3c3e1410074402c1c20104260310400c0c0d000b0005256181e003803052465851b5461508183e01c24154800f0a214520a844914 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 173341438 1250 173340188 173340197
    0x6030a030e0d0302010e03070302030d060b0901020303150406050d03020c041506020601060e1305070c05010608010b0631060f02010f05070f081e0c040501110307020315040c08061005040e010e06011203 88
    0x80311b803014504641c05408102c0040c1c10005458400191510644000e0315180b1666800c05d500340c03001030742d00d11014200144002a0200280195545802036405080080d061400d409510325019648040c900880c40c0300314204249144c1058009a40008403400c0b0350082541d6460400192080100c4c4001d10382c1090b113401203140e058285001d01d80c05160703250350b101030302074440c20705d00d00b16000d5030009003c0b0f9040c00b030010626512402581c031208a448408450704092000021f803005072000c804610500d0808002016500f000341d11034403040d560000d20400c07491104010481c0d0b0112016004188601403105440d441007a140343d122000a0100b07000110a0003201c0404c94110303407000910f2800a8180300c5942d11920112030007038001c00450a101441d40083d4540e9a0080f040f54584812000201800007401b00c0c5001404e100d0183e03146410814240c161440c0b40d40540c5010340d0800b2a03100c1061340501c9a45040305600c4080d0a0700e9080003103101c0440007824050b004c10 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 173342688 1250 173341438 173341451
    0xa0c09050d170f04090e161404020904060801090c2709060f060306020903330601020709050c04170a02150c0c04020d06050913050a030f05190207030b06030a030e0d030201 75
    0x1c003421004004981ea0500c48680340d03841c000c410016224031010801981d000800240b031047c880c2c4170120705950010039000f00308200c880104000340100c00d80da0b03600c00e05080c0700081420040d4408002503015150840c0003580303503261000c1c10009418040300102c1d19550036000c030f051b0f50340310a01c00e82c8540000315402a071402e0f0384080c1c0d503c582041d00c1040c1e00090000680c90100b000702d44024012408a02907004501c1c4512800001c9031094003c0c5403000010b0111380c42801484050050900100540c0c185969442d8254005004130900c1e03018920081c0444500015840f421507402031004991407004503000703089402c5a19030680900c114041546560b035a80080d200440803114006013142c0340c0410811801c0b805441c102d41e44111602c0035010800104515101039098200035204c0c94140c030040b00c03036105003112260720031913104508412590100d91513046a0241e0316201480d2078036810142c0300c01304808020046000485811014200403103144a180e000b4000001d24 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 173343938 1250 173342688 173342723
    0xc070f0e0c120c1812060601080a0e0705040c0c0203060f010f06030605102f1c05040b07030e03100207050a03080c0901020d0e0612010305150a0c08010311040b10170a0c09050d 77
    0x24150005c0c607165401010400c680c0307503448032800b54403800501c0d051000c0c1052540380c0303444e480c440c022103003e941c850000341d014a00407030b85070148903405001c9030517030714100d0380c4085908402c0c0200d55030303920f242c0c4000a046d4801d0281d0405d4a07001804151007076030b80f003004d503442000300c0f8010f101100340d103440c043c101d603010744034407400b200d500058092900006509500d00310707501050b805111040c041804080c510105441090381d1605000b8641c403c042c000901d0a480711446409407800019008c080000100b00740c175182d4400d03183da010a854610b01e041311070040c081c000d80142d108510f80200d151003034403604008100038112a2804019450a50030003109802c1920190300c00549001c244010403542076000541040400200000d454002c04e601012f21024114440315103804c0d40582c2c80303038020140d0000007042403a0519074044040c00074020112020403c2c2c10720070002e001d0100501900b4000062a41d0b103000140c10b10040146404032400c0c10350780040140012010b = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 173345188 1250 173343938 173343949
    0x60f0c0a05013201150503090102220302040c1d10050c12131410111f0c030c080903040b03041b08010911030a0b010603020f0c070f0e0c120c18 63
    0x99815100d20120200000340300e001d40039000c2111503c00d000c2d1801089660750700d03508071600218620345150b5980b101c151113806030041d005400312401c10358906140e404042e4802d201240e200f558180b00c5100d4031141516200e8410314140d1206001d080040301c01c0c607102c0f0302d600400e213a50500300e042c14055101240350040c9503202200b802000111014040c02e5169458000d0007841600c040813001c0301e0201d000c100c80d900100c8180500b52000524925041c4890354107a81859401d09d07043c070311080190050301c4131a90000201c0c1c03501403045017103403151075002d1046a20100451a0501e001c000f8150360b0309c000d106881860351401040c444004642e0810010040b040000c5035481082c2401a041003500c10181c0c440d40c848068031000a031540c2c1d10078111910341c100141c0704d03c503010b803c00d81031144541001150068110129140070b5400e1004107484146400104540c1c0b144000d0907180310300c850030441d440c64203001031101c0c2070b6680240380809180381c13a107904982603004180d = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 173346438 1250 173345188 173345201
    0x50c07050f030a1a09060f070f0810120302071403070f0b0315090c030402040501120f03030b0a050a080114090312010b0a05040306050103080d050c04060912020a0317130602010209060f0c0a0501 85
    0x3544041300040c4070040d5010000b0702d41010303000b40902c0541c208844003a110301c040c0c0d440782081c0449140080e10078202c4022600080101e03220b002000c50790751030000e440b1030b610b000f041043e0104140081060600280aa081d01e00405d40b040d8414100141828141c00c000c01c030820a026442c410200d54548440d11800385610800b4141c40c0e0400d4810403050302c005070002441c000b01c1a40c01e001180401c082410040e8140c10002000c1ca0210003250341d245450f0045a080071917507000140d00201540710b03814400c803007442c4446079190380340d6141c3c4030700c43e0607034882070300b9807c80051000305031020041413500500d00f8814039141c3c3e00d503034110580c0c10981c8240e61504010406024549003409040e41c00f81240060519150a00d0310240180c0c406000b000064030210441c41d04548803030301803d0141d82c002c100d104110301600c0f681240d42c1d220a1255505110a21000880500500035180e89120013000c5504100701d050b92248142c105240d984c065118400541000c11028401c00 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 173347688 1250 173346438 173346473
    0x18020f0d06120b06011706090a0902150901081609031e060606051206010804021e060d0509070602070f0308040e0402010210050109020d0605031906021b1f0c050c07050f030a 76
    0x140e6408003e0900d0918280300900360f50500012190303041c0e94000b01640c140d0f100508882200c843c1d00e4a0310540c1c014484400c00035000900f600788403465980d00405410881801d81e074801c0a5600c40d0b02107501c80702e4940100000c512201e106000241c4d405444001101c072000300703070144441a80301d00017925000c0e8005400310394005815941400a40d045e50b40c440720a01304142c050405a010808020b03c040b44a8114032110112500c05c1e554034084030200d1440d5002403280e42011042951110818400c80015104690b00025490246950320702261b030030210440c101403400450002e80d41000348100d04501544200c4111003611f4072419001e464500c00042e203132407000f0f207000d00312100741c0c02640c840d82c880824160380d01d900c1041420803581c0820007503211b055002c00c003114404203107440d584500400e94055800e4000c40100141c5d43d080341400d002e01540c1500982d2075224015140001c0e400104c0305000c5400d051a60841494004e4100d460101098070346100380174401c0440d = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 173348938 1250 173347688 173347709
    0xa0201030e161512022b060f0f050307230f0f030303040b06030c06090d110f0d030302120c2514010c02010506030106080c091b0d0609021b060118020f0d06 68
    0x140c07804254008104c40c1180442e200851a1020500c00500795803040b80c41d200c00c0400c14840815541b029411100040040200c1c1c80030032511044013505d2442e103801500d0103849421800101d8422030a0340034803140081150500d040d84181c180f00b10701802201aa4119070321441c0707505240c408000035440340d03006010510550800e85c0c06c05080403500c4204a1044000744000046070351010480b0700108e50003040c1041410542c0003041c0e110240700c6501c3c1d4400641400c40c3d00741034064000305109941e8404132401541d0382c0c1c9002c9810301800f421000c00241c502000880e0094007000089210b008203000002d0144003440329096450b800c00110050351100f0901405007400d000b243c0150942c0e8010300303460b8070403a01203070851500506080c0d13032403801d062020f0505020401c07110b2003102d1940601c6442d0316400f85501a50000e00714101c1e51600a01b02c098114001c140385058454074a0300b407114010048000c406500103180d10326006d9810080c00e14405640d2113140c0080030b40890 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 173350188 1250 173348938 173348969
    0x2032503020705030607021f0603020301060b180405011202090603012909130b06150708030403050a0e090c030106030b030705181f0803091e0315150a05030a0201030e16 74
    0x2002814142c042d0f0000340260312201c103000e41d268000c01c84144000c01c10b00d6011034203d00300d00110280800d60b102a405502c0d0400c04986810654002c000080741e003007100110111030b02c01c0c0000c4801c00d02c24807440441c03e846a000602d8444c0a00b604850001c00104400c01c01441029038140180703081d01d41071a121038210060300b004e65445034041110410000007a0003600d558014510050844e4801c560040c5440007035214601505d2885400850315616883c080c80d0107070599100c203c0ba6030120b11a40c180c1d4400e0300d00615007600c2012030801da00d003942d181c143c082e40900794a103646039041c040c45601084039103070080035100001c880c02c1006220b082c8148a60250354000b0308842c001c4456120611025500201700d0b01100c0d01960281411900030f4100e680ea2600300580759858001c44407540415508060180d0144907071a4004900d400c0640c100301da040ca0620035aa01074100c04065170256009500c070500480301c2c00140c0303000e00348403c0d082035000c440da080124207004085 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 173351438 1250 173350188 173350193
    0x60d0506180f1503150a0504050f01091a24010305060406080609010902090709060207060c080c0d0c060606020106080a14031b030703030515090a09050f0d02030403050105070201052203020325 84
    0x701c0299200d801540a495210b045ca4032684030760f07070300a143c84000354440e004601004001c000c811014103040008004c14641880c080e0115400c04074224280f100f0980031035010420b485151501c0d600c600a91080e80160701d0040d00035210050100358400e58980b00054403030b0041c80603501c607541c0c02000050280e40da104001022401401800411803014801d00c1529000a0b415090740d849040076117622809241002e1244a02d40d000740c520b024001406d1840f581198420481a100c0e003400d0000c3d9486250490881e0110b100c0c0786d0f2594440c0958a002c540c2e038405c00e55040c1800d90640b8681002d008800d12103041c07040c0008402d5000013100d100341a414840d03d9007000d4074500d100540d401c1c580c00111a070a000d0005441c60390350b4031001c81000001c200c652130107400750055a4110384500c2c4040d450750000d10040c0d525508140029030400c0c810f00c500c0d0b02ca800103d10501c404909910300c01d1219124203022010751200300592282c804582030301403407490480c0b01c2410f0702e00c09132 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 173352688 1250 173351438 173351461
    0x9060204081005160302070501020f070609051e030417030403080712090f050a0504020a02010e01060602030d11090603012304021819060e010c02030106030b010b0310060e060d0506180f 81
    0x78000907112803414080c4211804c15401c10300700b000b840c0c6005611107106081c090700a102d0038403001c0c2c52503030015051301001455040300601b0303402401601d46040001c0034400c051090307034000e40c1c5903820401041c0107408994045800121f402400c890074141c89039102c0a090703102c1d2005071032031381d590b00e2a01c1c0d0f40d6034804040c0015010070f024010b8a54174120100c2e903140120702407188115000304a201102d40b007540807001000a540090140036510f18010307459602c4505540d00d224100300204c0c1c100c11012044036441400504420700d142e203400b00584010900201481c2e100c601481c13900c2c4a80d603940050400000b80350627508840c0c422004110002c0700b000ea8800918100203c00c0142a800150f002800700080c04d19901d064202d10000e8018041e580005060060714000402c4c60103c40010714800c4034070601740780c0429202e0005950204001400da603100380200032222000c00590000d540104010b4400c50350207079105005000518110b0b5175000e200203c108120030050360 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 173353938 1250 173352688 173352703
    0x20705041109190b0f030c07020901060e040f090b0106080c1e210403020c04051008060c0307030b01210f0b030a1506140901172506080610020a1112010906020408 71
    0x108451895280344c503141504030b0045409a2030000c8004c03000401c0101000e04450007940e0003807010419685a00300506144203001c5c00074010382c60300c001014810440e00c5400b004541103441c000c10f030703881c0020403508042c0081c00c3c0c0600c0607050090380d041b62007000c00120541a4565420f80303c11400c0346000304449000700f400c081d41e0541e0140720102e1b40100303549902c1c2e582540d02164659601155070300155280d400821a0320546041051768007040010318001d01ca25a010f0004034011401140c030380282a2546410304920b90604441606550106d2019491504086026510b0100007402d100c01d0560903190983d400c150f07443d481da02885060094410b0611140760142088046151607505004a580340c050b004503036420254100501d0b6449c07081c1003a0710f01181c107225025034103000c0d5403040300045464140810303c03a00c0c15031b0b610540e082036a0700418005040303454009010803816561a00024800040d64000f2000e000308601c5502030307407000d82d589140c40301040c80c0540 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 173355188 1250 173353938 173353969
    0xc0306030803060f041d1f09110d0c080d030207110303090a06080403020c040612021201020307020d051e0319060b0418180c0803040f09060303020d122a020f0a0b011203020705041109 80
    0xa021669800200e1440c9103410f0109c0030b542038180103180e0724007988901d0300c50f0082c821b80d1003600a0400034907415001455810710552640050241d10000e050340e80c0140c1c02c400782e000005000c00c4c02102c2c482d80c21542e0050086c412503980c2010f00c408034040b40c04907040410140305641c0888150300704403860300c0c10503890318021803461410081c001c0d140d07004500000100500002d046000c0c1040d6403010903503d10f0000c1c2c00380e49080001d06041070303810401c0c018035401d04044000500002c100261000c81d000c00d0049041c18444a41c4e1074001e14106202c10010000400542c0100c0e0424010602a205490046a80e40c3c103009615010841a0703020840303a0341415010702c00a5400718020110280c0ca00700b4076040325040c4054005084072901c1c694600c1d08a000c180c4c903030401c074929141454082d8003500e0382d00700d101c0760b4035440c1d140140014044034218001000b5001c0300306601074455000b441521109503c5900107020b640b4a80c07945d403401100031461180901c0c2900c106502c001 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 173356438 1250 173355188 173355191
    0xc050c01080f1605070c0602030304170304030c060e030d141005031f200a020705011706010905240715050c1903020d0b130507030c0306030803060f041d1f 68
    0x140407810102d007144024041c02400300d030321901a242501580903070b620343c0d0340056000d07451525040c00a40d40e0300125016a00380c50086e04200321250110210781c0102d03050b581d08000e07003200b038449a01500040c0b2561031148420450a52000e42034400c0041c0c0140c4011340c1010b41c1070111000f43d02c04178030f81200e4481d03000010168000c0da100035241c41240b101000100e840c050010100c603a08010a00c12a1181c00005083c05c00a60100384501510403d885180711103185200503140034000b2500d681c04240c1031030090009107131841c4c00000c0d1000312030051740c500401c003032200616042454122075035120401101003100d858003a466214a0080d607030341c205807513032815003480c2511108100506500141c503030075090f402d8010501d0000c01034440120116005040380081108039000d000280c078003145032032558400d001c1d9104998104000710b00310303154241003000207400160f4043e402907503910600c15411000a540c0560900c0c8005000c109607181c000002070300b0310102030021203 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 173357688 1250 173356438 173356441
    0x33021506040b030c040506030c0a06050a02010c08222109080d0203090102030703030f110304140105060603010614091309051014040309090506031609270314180406060c050c0108 78
    0x1603c00203200c0c0100d1074200c501095a0715000082070034219900403140d08030500001c04119941c110f00100280c0b44558000c002400001e0030440b0410b005881980200c4000170100002461020103980c0b20f50252041301031211070320200d41c084012490210000c60a0450b04200044c014020084545c645002070341c0f4003100540004d48a100b0050300405042e41d0b50301c00c4103940d2032079201d01c4121184840c010f9036810281060420301000ca1900700315503003888002030a5082c0381066a04860958484158040118403810001d400c02400942c21540700c203d0065000402c2c00703581d150a0041d00074240c03000d04180c1100a81e030000181c40074516050091000181c0c1c0304da60a0200e482d200e4001640f0f481d098000707070070001682820254080c8080c008290309d030081d4010615a00d01800b038038a50800d10020b0318000b40c020b48050046400c4842c0001400220b10040504a50154014902ca480100000d08459007608103d0000c0d1500c2224800c0100030010480004424245001e09 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 173358938 1250 173357688 173357711
    0x10608010e061e04061107030804060e010606021c1106040c0f09061d07020a200a050109081c050f0708120105041a0609010309080d0510050105040f3302150604 70
    0x100b50f20900003030958094000040a0007a00d600c5415544014450071380e0718107203402c00520000c415201600c060b89800000c0c07064280500c1a0402c4030801d802070151100080340520512445403906824054501000302950704140041d1303106901c02e240e2004228242054003840181d90380010058030b1801200b440001440d00c4150f03584003412181410541da141400c0381825100700d401040300110040801040301c0c460400c00c5c6040045e140e064480d59a0001151010114811205550400140c8008003803502200d0001c4140d517041042c0b8001c0c502030b900f4020780c4060400c0d0b4403100041a04601c401121a205005100071241844003900805203000e02c8200d0f99101441040b0010315006141d010390045c2e20740307d42040120391201100d02e00c410250008407030100c51803e004401103260b60007507081d1001d4612003160041000e0508007040260401c442c011660b03100c2001c070003452503000c0d042406e15499998040d2100f070110700703da541d9440c00a02210300c00d80c1403801c9283e1 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 173360188 1250 173358938 173358961
    0xf09090d0516140708010e0613020f0103060b0703030501031e030e0607020d02150703120c210f02041413141b0d0903170a06050f040216120809120a3e010608010e06 72
    0x811f4042f1005400c0141000058005160550081041c0f0380c0109581040c10b40560006040b40d024400328518104040c091042e450310854008021408082109456007414000b60030080d1002d0140003e105003500010300b02e07880410030505681001030b031441016400070080300d0b1600c10000a00030308003450300240c121751490288034002c0000c00d401300031000d03032a0001c0b8141d0031103400855440d0b8460b01ba9400c41c1040740042802600d000350080302ea901d952050b80c150986c00d0340560a141c441600301e140c0980c1c400c89041c6149014009850a0311182c8540c40c0503a1081c1c0300c600b10509200c14103001048000d0034066038070301e030102c104425168100500c0034034600700e400503581c40408000720708002400b200900112280482000c0c040d0f00443c1c664002c0d03070144100d0711810b541b00f000238464841c000c60000010b4030031903e150200b00703d000d42038103032000d11352004c3c014018031400c04c01c60407030024268460703440304010011241d00784901d03030041582c04054001407405d02010310 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 173361438 1250 173360188 173360221
    0x4030e010e0105160501060b0a12060503150402090a060305030310030515010605040603020a030e240a091106030606090d0308070f020a05070519090c030603020f09090d0516140708010e06 82
    0x100398413091300903141008003e6101d08050225400d109456100042008041500944034414100c4c81e244001c200c80c6400a50401030020190006180359100d80c24405c800e500604170059241d100c0b40084000703402800614804d143d400000c0301154a036003081494150f0046840e10ba0a420320014000701d0751100807a81507481c40c0c280560b440d190110b01324014070031500e000d602409034541c40ea420988080140c20440c00c90001c0406646422014408461400f0300c020b00040100c0c2c52400a03040c030201650f80b06400600460038a2101008202d0441c4050390407000076448ac410440001d800101001540e491440200309080c600c1e660135a48070310300d020303003849007030440e6000c601d02003000b8074180a48807050061002d002a40c0300603000d001c50340800c0380b040c41a09000440d6040404545101d401c1039801040c0e8105100c00694159000c00c50304000e1420010105002c560070f11b8814088103510401480c05600d0010302030b0847c0c074500b92070300554108100703000680c5407800340c0c103 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 173362688 1250 173361438 173361457
    0x30213090504032c090103081909080c0d0303060e090604060c030903020316110d0c050a06050a230903030a050d0b09041205090a0906150f0302030705041806030203031204030e010e0105 81
    0x981132075441c504c6181c1d0f6a04010190b00c00d00c0c110001c41001580d001504184e80220340e000a411110700c1d0544101a040c00342080039880140030488034034241d119003484038080e05002030159100d0501c6403d43d05d040b00c440c801640840b09100402c8100c1c46030903540010b514080021210342e560081d01e074440e601c4c01c81904410071512005106035500d400780700e05801030200548000d2464001c4e032500706485540c0c443e010040e0001002401001118220010380d0340b03400281030303100d80413038450300e002d580034002040500000000e41c5040004100d240034549031280c8924000203082c0c01d41d48002e80c4140103e50080134800022070311120101c40030136074107005460741c40b400040351640f082603110300d103c941801c90000e01d00025030134040311311007959103d4101c0011440140c003030784015192500083c9080004228011b040c0300c1040329148003050100d000c1d56240c000a10759044001050440d04490007400201a013191101c004e140007800c0041040d81d100c40060b2a44c01001d00070f = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 173363938 1250 173362688 173362727
    0x7021e13091103030309060711030702060a0f0903151a06130b030403020a060501030b041401140105040906020702060c1f110f0f1306050a0207080f0307120c0f0303021309050403 78
    0x8600400860102c0d60020700005800c41e0f4607440d104042076603440040d2680004903c2c039511114105034080125001c041c0c000d0715861409890303010455403030451480e46400c00c0741c500c4000c00090895a14100c19030911200460310104000e141c2451581c1d441d91544524400c2120351200304c02c5c00b0b030b001c04441014580e180c495440313040981c00c000d142c41d00140b11505d080c0c008001c00c01701510040c044c40c00b031080c0ca0034404005070614200c8242aa1482070b016038000100464986500140000d9218001c054102001680400c2030303a0843c403001505038210703850200c855290502d643d0049644c52000740440c1070030b4400045144180c9140c1419014002100c000107980d20301200c14482501203028000350341e451004040b5008000c204006005c1c02a001460039000200ca1881100b0b003000703145081d4503aa41c030031034405400342d0001408a09500c41300841c20901500078001c1c000e03100581d54000c1010103800c0c0320000e0700055000c2e4946018080480d601c41240381401002440 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 173365188 1250 173363938 173363951
    0x3030309020a0306050c3406051009020c030d0b060f0405090c1c0609050618011503090c060305060103110c100905030d09060902040515010f12060504020304060207021e13 75
    0x801c02ca050303140c002400441c00c2106120b03241c61140c2c003d0007110210310311411006400000f0468202a0311000c40d40b88403c002c4181c01306140d0303400190400341c884040c04181c0c0c2c0e40c203c480c4c05d98124003890b41007a04042200100e10000d8055a481c800003118040e182800a44010155006602030b09002d1800d03000020310312200c0c181119035449a0502d01c21540741441e0100010b808603001e54210982407a01203546030404000c0c0d03041c403040c8000c401c1801d0f8280503000a217441038000c030008143d2a11040b01c04a04802c100d107000e081075a03400b1400b46098000035050300d03003104601500d80e1003040440102580032610408100714440c010901d00c4043c280545980079028026281502d45001c0c1010028107034000441c92384203980c2849075a492042e182150705a2003441400301d0402035500c0c6c1c0c52072240305007003403a80780d110000070110b031143d020504a8108481c226a5143d002800009500c5c00760403128440f40d803440b162015604620124611030900d540c0d4148641e290320 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 173366438 1250 173365188 173365193
    0x70f050a0e091e010504060b120c0411120106020609070608040b0c0c070801020a03140a05061f051201151814040246080c0702010e010e0310020318010b030703030309 73
    0xc8440f1903c5207500825500040e0001d4050080c03900f61001ca42c42407034590342c00101d04080c4203421121800202424007103160000b0301c4060000c1302c80d8035104500070000340340d442c54044400c601030212640200010b107400c0d540c66161a540d0b800c0300e0705000c405810000059105080c032513003e481c1407032060319225841001458401c840e00300700055400810f59404070b40d819842a81c814441d0804c1d10b600e92100b07580329044400941e01507412507000051201c42c1c04542078091061585494000e14121041c0a1180d4945003070304500f20912110725a0809240d01c0300141210210388011082114980340300348060703541c0b10701c02074095a0007058541c4042c0718503800c2640703d50b608810b411140c104c880c0c0d4000180649000143c1c90011890900c0107034410b20701c4d28030440380c0355020303468286a9001035503d07c44030700881d410000c2080603d00c4a41301031240c0d41780d40d81c40c41c101680301c0c00c00d401440d0443c4545007d40342503030f02d41045011103540005040085070b0305401e00040c482c10030f0 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 173367688 1250 173366438 173366443
    0xe03030912100f0b0316080d03051305060112060e010221070c05070e07091e120c030f06090303051803040509090111071506090612060528050603070f050a0e09 70
    0x100b202c801d451402c02060744104840c0c000303110014084003a80c241c00407911600036980011300a1b0303c2503a0240c001d0b180c025000c1c0e4030058004e6480740d81d04003c504281e0f140c4d49401002d03044019540262580141003014034003c104501ea884d20007941021440001c0071584015820089000c2d8041c0c2c003c0350f1050b00862080c41010340100075202000e0311071440303100d0103c3c280c0e05400052020000003c0410180c0e1442000d40501d40d00e040e6001c2c905241000c0210a00c1000c1d21700701c203151400800903a1003114a0845445004e002c11110002e060240441d1002042041103181491040080040100845c1c2c1550300448940d48151503034203001e80101541c895942c007003140015213030284140074003090801a104a03080c440d0b130341c6803140744040c1c458030310441e00700381680d03540c0c1c40004d1150b0300171580c0074201ca81816426031aa1846c281c900305c11341d212030718840d03440d028002c250805002c0b91014185680c41088031302c1c50400400d0315080c441c461002081e040001040844006 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 173368938 1250 173367688 173367703
    0x1051804122007140108091911040c03050f0a020a1b1109102904060e030a060f06030203010605060901020a12030605061902011802030d05070606030c030f120e03030912 74
    0x10540344815140c0e204a005640d01d03084d001d820420b000020303c840c0550310915050340b00783c00340d801a01e608003c4801b20080804002003c86041c030509140707074066240d900c513160720031030300b645c0100315420700c0c08991248982c007500c21110140100a81001103400c41c0c65551500c03407114800c150042141014031401c05044495a402192881804402c01e48169580140c07012558189010424840d40440c0148094000082490706010800c405406240c10700540b06002d001e441419010382c0c0d0342000c99032641c0044068644c0d8003014010b6041c24030412002c0c22043d00c00034070300031004001031760ba100304200c010f002c01492010324001610075000080107150140140740c540d0018a03c006030041401d003035100561a2070403402c41e404105510002094002d40175201a170034200044603d41e008440c1641c64a0f154100080040d8881d4040c5005600034260342c103070460207140c4400b01c1c25091100004010280490002940e03012040300d0013454102c48003040c1590100c42a41000003 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 173370188 1250 173368938 173368967
    0x105070c06050c0f010606080c03060303120106030e010b0a0f0504110c100f0e150c031008060124050a05031f0806040b07020f032a070312020a0203060105180412 71
    0x200300c1400104150410094001c2c0e08500069410b040d030b10070805402ca800510440001901c0c04001c20b01858081008507009400542503030f250105a018040503100280d11000c0025558816003124641c20310a65440c01000c846c81e401031894200703117220881407401580e10495540c002c5104043c1900104c818107080b090541da244000c0c0102d41e001408421354010f003450070154134030004100803c2a413200443c21007603400603101c8140702a040d402c01403101c0b00c440007480740032030105020002d036130003009003080e1946092440d034106040180e490411905200051080b95261a000803d40350320120001c0c109001d10740640c1403590304d152580c0806640d000e044c05000a102510104500c40c00c103907022205c0c0c940081480c96501d01c1517600d00320109510f02e801007841d07a072000c41712710600202022165400d490b80c81c0c0501b24050b102c45030015a02c550205800c42c1800c2c40300a004003030860b1503c80c00080200c85441c800303001480180059140780001e42d00130300522b0700303018444 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 173371438 1250 173370188 173370203
    0x60c030a06050a030f17040b1204140111130609080d1d1005070c050a0605090f0f0a18060e070c0f1b0909030206090307121b02060a120f0b100e010507 66
    0x40e5a0704200394640f0400703405440c140032403000c2c0303100c0300e41b900201c034119080d0544843c0b9107030207401c640640040180003114850070314102200680b400f40558061074981403011655020041c1d820201e0900e0340e80b008040c00900042000f45100c003180041192010b8204000051a8410a8408500f070303030340416130100511208462090740a400f40c80d00078402c2c407074a0301242e04c80c810001080d011744222400180c003005140321505061140500786d00c030242000100389a940001001c666007604061040101180700e0b00c0140128007801008041c1c1112919090130049401001292241d20281c0340d000920702d00d0007003150200c41d48441c1e1452102407200b40c2d0b02c0e6070b20640900302246081d80144141d0300801e15424000c41160791070b0364083c0f540d04207205000e6040e2891060a900f04400c00c03041030200c00540c40d41d0004185040da10b40d01c00f0300c1000c8221341c40f822034581b1341c003954481c0d107801e86000f800d440f22048040c2d001c0c41402c0c240341c1c0380d0209004903054803032008001d1481 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 173372688 1250 173371438 173371459
    0xe07020106090c080718150c02030a060f05040317040201091214010501170c04060b0d15080f0105010501080c1905180a0902070b0708090d03020f091801030b0c070302060c030a0605 79
    0xd84d101c80550b0246100da40c801c081c5a0b000f4034a500303294410300035100200d031a03807204500c0c10300441c0c80c0310a061010b0b00b5140002a681c0341c450442d08180350300004030b0340311010002019482100f0b11034032550b0b2008510385040c2500000c098074410301030061110620b80246040c0303cad40206951101b00044004e010560310b8901da0110140e0011000c5c140b881020507101003031400e0301448003038584804145050100f00a41003000e0b1814510355017011103070140200305050184103480a0760811000400c035549044001040200c00410318a68848144141c64407020540b646d40c000c8846440c081f521006050742540d903458480c074920b0381c040c64072100001c4501094015001d50f0b0301420381200c20740c0e0390010903641c030002120705c0a4030f5009881c0c1640202d00913405000b40510050005041460810211304111070600201100b51104001001000007081d0300c0355121014005882c00e101065401a50301d0308090543c0c0440c44000c00002c405003101e1380801c006140042105001 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 173373938 1250 173372688 173372711
    0x2070e06211606020c010c080f160309150905030a020f01030b0a0806012402030412060b060c0102090a06050a090608060d0602030c030703200d090201090b04060e120f06010e0702010609 81
    0x10b660095504600d0100005800940c190010440021801d41a1154a188000c680d51b0410582c406006000e00180900017030900d02c00602c0940c205501c0b94881c1c00c212401e040348c0302d60b00b27401c61400c0b000300400000e083c8100d4402141c0180e81540c10fa4003401d24021040042e0040d210091006800032801480014462000a402c030f040ba0050321031819000d205c010f04200c050541c141204c00f5900401003003107030703561100c0b01c9410107004000c0010503070f0550001079040d5002030a8a55182e4011405002d186800847e18000b81350714103045185c03118100000e09024900c0c8500401c0c080d05400044080c0c4071500120b4480d036201a0841d07803840d094004540503001903030341a0002c0e150480300480d40c1da0480b500000d018045105070304200b03401030000d02400480000308d04220310040e00141052f8400080c04c090403040c0c840100710074120050003c81b9086103c0101c07660f0060a194800c100046551415200540207000c815500d008050b800b40603140e200303c2d42a0728111080c40c1 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 173375188 1250 173373938 173373943
    0x2d03030a0e09150f010c0503040f06090e0f01030309050f0312031303080c07020a210c03150f020f0406030905030f0409060e07022406030c04050103050607030b0603010602070e0621 79
    0x400071085588080b15120b01401d40024980c5802840e041448401040407540c0192854011244201c00700e03490310740c4601d22080001a540d1002000c01c2080034184412140320b410075034001c2c20700840340d005601d9070b10300600d091114401c540c02030368088111242500e003071110f00031a020400d8400d5581c01d00240a00c0184125401070700003c46082c007041c1c00c10310903000c480e8543e0b00200040703101ea00700a068000b852a034402e0f600043c512145500c0081c02869510006501812000f080c1c11003051101003591000c0c20060504d601c100644000054500b00741d03816036850386000214240303546002859880b400c403400802d000007080014204005411900580d5011503011415454420f41a65100040b1b81c0c001c01c0410b00044010001308510044c640c010401001c4079403004400c1d0100c1c08542c02070304151002d8000740100281d0320b405000303d189140054801e1032441d07140c60703002520b4090a00a004528042c00e0225030306a84114140c03101e01107402600120030443d01c1103d6 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 173376438 1250 173375188 173375207
    0x90408130918020a0602070b0f13050d050f010e030403020d262706030f04030e01120f0f05010b070b01030609170c211306050c2107050114062d03030a 66
    0x2882015000e0001c10141d10102d0b8100403521103070082c80c00e201c4810b55009c0560812507100743c0c016945400028290f03980200101c1c070a008402a01d030740c5000ca2606806d43e01e01c0001070066500810081005854a070340e03161000d5045010202080c4040082d03411480411100c4040c0590100d94a01004e46042c0341103100091000c00c80300d441c5030182032000c04d000407100041c803088507200090201b40a6000c0b56802d40c0140340c15404e1601c80c411403000ca662100c40021303455950b080d0540011440d02c500b9000d462044c1419040840650707604c04400070500006150b17640b80d20504041001005d4980401039070307501d0340b540301d80d2010415907562000c000b0030f100207500f0036098035900c56030404861542552114805680381429000e441c0c030350101c3c640c605288070326021620050345104030b0f90745100c40100399956900c0300782405400e50780540b11244420840805000c002e030340d907c0c40007000304005520320803641d100422901040e01c4000e065505400b00240700e0f00c0842c0c0c404001c2 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 173377688 1250 173376438 173376443
    0xc040e0c091011010e010513060b0409060f0204030611040803030c0a0306091a0f1503070309030c30050a050306010c06090b0108060604060e100b220605030f070e090408130918 77
    0x200b200d014241c41c0e050071f880c0192200785401c0039100032140441c4207508208055580a40301140c10b130620f41d11002110184090079070203682c045002c2c4104a5240641e4401e000111103e80c20107007406003058880c070000e024408a07400c0010300d058940d000c0d411890050240f140100040140001d0b5500881502903803240310b484064402456858408440c51140c80e111035200e0440e500d486c0282d00134030040e04158280484000b0810025000e088040b4603c288180c0c42241e50a00004099400c03019091003c2400000c1c40300c0828641c0c01415a82d12003801d191058040304c06003000c400400941201401340b00c10000080341a03100001c0c100c4c000d12084d02c042182c0c41c0d588179416884a0261404208031080110030130800a121307010740401d0b05140300032950051508a8405451040d500c080c0214502004200e08001d00c0c4590307650205540c1804501c03180082d0004030f00791401040284410004500c045050882540680240c030560030b0820600ba0f2a0340103180041d0030350401c = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 173378938 1250 173377688 173377691
    0x3032e06020102190513090e010209060409150806070509010305100506030420031b10050909090a0506070f081920071e120804170a1d0301050c040e0c09101101 70
    0x4c0040d02c62084c02203034040006000603400b054180500032000d050f05100500b034540d003e211403140d5580e20402400213100c43c61000a03581c500c03986c58842581203912121490b0040d008000c15140c100c02211400e04d003d103000505542c81d00b40c03800001110b9001280c0140010080004024584211260380c0c8281c0c10060302840b0181c04059980000ca401074150000c20f4810b610542800740181c10840385034102a401d00c1400c00c08640e6080c42220801515840440700ba024010240082608141749180071200840720000280c00710300c2c060481500140840388107a0504429070085503250001c402c0c00e14466480c0000c0f01880c1c001050590304000e06000c034900302c41e8030102d4044802da11042078007600e034603040b00740c40001d0000d100b6690041080b440c000448188001041d0402464803200c542190310320060800341d018540b058003070780c540424000402c2c503d400761400c0b604a01d041c00c0ca00d0341c0d02c044508613401403454060300040d01049110a45030890001054404175400 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 173380188 1250 173378938 173378977
    0x30402010315060504260f030d0f0902101b080408070e09070806180111160308090106032303090a060c140102040e1504020c06040b160201090503032e06020102 70
    0x2540003035010948140f0300442d204000400c00504d01c82d00c80c001c12920464407211382c0b40c00500b0ba60070302d0f10490b010002c0b50000580c0300c0650000e031042030122100f42c41c04000401050780407811158a078418841800310241000c03241108503103540c000143e03c2640c99440d603036034848240e80c2d01c000d0f000c1d860200e0607502c0081c0b100e40001030268100c500100061086880d800a440c0c904c02080c1103660307440d5240e02d40b03d691120318800030000101020b42190301040d040c10001d15001c009056414035174101f02c0c041010540384100182c601c1c40003410303410104010000c4616511401c040b154002001e40c02c0040d101c2c0e004040030701c00718010400601003145400c105407c0b131103a402844040c205c15004034041c0012142e01c00300280c8007070300051070000981c90541c1f40400c111400c440b5079088034104400c1c0404c2e4071a4500613030380790009106d00c15050780d445032070340001040000003501e0054480407914007005110001660000170300d000603101e44009020394003051055036040712100 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 173381294 1106 173380188 173380211
    0x150806090309011d010801030b0a06031a070f050c0a0803100e090d0207050114041403160305010b10080411010f050d020a03060905070201050402090c07020a03060c050304020103 78
    0x103008545660411000501c0035000840032200010014041541a45c0000400c6d055130790048000585903a400309a4004051030f6101624807408a03201e0000c2007182c00308140582c20941e103811607107042c0c0000765194850810360725030703a510055818000c07036004000745070400e00040c403035601a40c1d101036901d468079040d10100550307045540314010885d01044004018242800c0c0404a21021500310846001d5840348464101ea80742030303185a0740e410700606412490040f60354850544900b0550b00030044894002c0c02402c7c0c1c003240c250120300410040380300d07540c0a01d60100e10205000110303040e907450003270380d02441402d00c003c1c01c3d034007164000340200000300c1c0e8000604034908a1094140c7d14050822b0080d6450039085c8405a04c40720142c0d5032186141e0102030351410070b4408108565110344c0003800703440c584044070180d958070070001c6024038000d03071703080c4451030038a03 = true := by decide +kernel

theorem cover : BRFrame.Cov 173201438 173381294 := by
  have h0 := BRFrame.cov_init 173201438
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 173201438 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 173201438 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 173201438 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 173201438 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 173201438 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 173201438 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 173201438 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 173201438 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 173201438 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 173201438 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 173201438 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 173201438 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 173201438 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 173201438 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 173201438 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 173201438 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 173201438 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 173201438 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 173201438 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 173201438 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 173201438 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 173201438 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 173201438 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 173201438 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 173201438 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 173201438 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 173201438 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 173201438 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 173201438 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 173201438 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 173201438 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 173201438 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 173201438 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 173201438 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 173201438 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 173201438 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 173201438 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 173201438 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 173201438 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 173201438 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 173201438 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 173201438 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 173201438 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 173201438 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 173201438 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 173201438 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 173201438 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 173201438 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 173201438 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 173201438 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 173201438 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 173201438 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 173201438 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 173201438 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 173201438 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 173201438 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 173201438 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 173201438 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 173201438 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 173201438 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 173201438 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 173201438 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 173201438 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 173201438 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 173201438 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 173201438 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 173201438 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 173201438 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 173201438 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 173201438 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 173201438 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 173201438 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 173201438 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 173201438 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 173201438 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 173201438 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 173201438 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 173201438 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 173201438 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 173201438 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 173201438 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 173201438 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 173201438 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 173201438 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 173201438 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 173201438 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 173201438 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 173201438 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 173201438 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 173201438 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 173201438 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 173201438 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 173201438 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 173201438 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 173201438 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 173201438 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 173201438 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 173201438 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 173201438 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 173201438 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 173201438 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 173201438 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 173201438 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 173201438 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 173201438 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 173201438 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 173201438 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 173201438 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 173201438 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 173201438 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 173201438 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 173201438 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 173201438 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 173201438 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 173201438 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 173201438 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 173201438 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 173201438 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 173201438 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 173201438 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 173201438 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 173201438 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 173201438 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 173201438 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 173201438 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 173201438 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 173201438 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 173201438 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 173201438 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 173201438 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 173201438 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 173201438 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 173201438 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 173201438 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 173201438 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 173201438 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 173201438 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 173201438 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 173201438 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 173201438 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 173201438 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 173201438 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 173201438 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 173201438 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 173201438 ≤ n) (h2 : n < 173381294) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
