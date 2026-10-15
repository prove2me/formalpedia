-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_3894
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T10:59:11.93668+00:00
-- url     : https://prove2.me/submissions/021fecc3-dff8-4cb8-86a9-6348825b1588

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 700179856 ≤ n < 700359712 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 700181106 1250 700179856 700179871
    0x13092403030e0927060610031406061e0d060302190302030a11060c0706111608150702071203030f060f0f0e15030105040f050106080d2703080a0908100203 68
    0x211001031601d2506008195010a103014018840100c0b9102d00c0480d02400d130054526030031130030402c107650901030001c003611103035481e0500080d44407001c503c0110304003a06030b41c0504000215211110301e03240d1a0380c010720b446500c540c1d4034010180840d0040503640001c03032140280440c21140001200c4a4400352a0001e02410180029507180c1c85445928444640c00140510480d204041e040c41084000c00705520340e140130800040700c45082502c0741d54282c03010740f0408000d001c00800000d00298880100c40228900c1d103d94100382e16040c2e50b584034082219000320030104240d40740d0400aa40403001d8821300a9940b102c0d00a20300b40243d004000714452000b104009600c1c241b000b0300d400003c410344840024440c0800700e400c2d03510403501030b11048940d8122004125091007a50020b01c140d001402c000d1070303440402000b036a0a01a0300640000c0720000104460221500000440e40030200303c1d43c458500304064064280c42c071504081d8000c680141404170664000c60744103064 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 700182356 1250 700181106 700181117
    0x91014070c030c1a040b0d150503030c0c09060d0807020603041401111c0509030d0b010e1005070b0106020601240318032006010b09091306060f0e0612070501030506061309240303 78
    0x7c0f51145500184800840c4980c10003056000046503141400108044000c582c09016685181024000e81e1500030b0304d028001d08040000c40041a07090007640c42c02035048810070741d42d44687c10090301d10420455004800e501c0e042e00b000094030084020b00b1214012004542828a648000d0044071004c03940502603401c1084203003910030441d4000c2e03c40400505080160b22a00e0012410945440c541140030900014540040c003a84000041c010203852008018030742c10700075014036454503841e180c181c0215602d0000003c601a800014018002100c0d0500780e50080c01c00038182c00e8983c3e207008522280b82c0c0078407001440816190b040e03d080441070703490b016090090002c0306200600b581509000d05d10f031240054094007940e0000c1c07050075a180e041d5428520004034554015151a00c1407104100f04054540c0c0424080201d030b6090800041707503070300c00003c520a44200490f000b0701c40721030f07400400e1039115a800340402607040c4000b0b00c0c6030300c00361410311407040c82400050086103 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 700183606 1250 700182356 700182367
    0xf0507050a1e0602040f1a0406021f0b0d050d0f090501080c0a11070b0a0905060901080420040e0a0c0e010506041404090f05010207050c06091014070c030c1a040b 71
    0x1e55101c94406191101c07048942d1007400e6440c1c07482280c0107500459411946000100035040c1d41c00d800d6a00d203d1181e80d400c0c0f41505d0304034040d40e966440801d080c80030f01c4015205405003004e922203100000050040d0315251034520303185490700c041824050204114100c0c0540381c501c60120740342500c2d81a120503a0b03d480e4000c14030701035004200090108203607080480801c2c0d005124040040c500504002c0c0ca600c540c00015000b139900d0380000740a05018016240640c3e4441c0000780c1280d049441011529030103440080314200d1140c1940d0064282524441c40310000100280454080c0d03030020701040c5c480d41c0324400c100080c801c85600c404284012b00402c90304418032416080300510024154490380e59581407942850025550740e580420b42c0d409001c001c0c880c05010300801c9070aa440c02d0094000920709a13904484a010040e84c1d6a1190603421280c1c1201d11240d0080c03503002c48907030b481c540395040147c0d0340a00081070f500c400b1910011039203041910b040e01c407250710083c00d01 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 700184856 1250 700183606 700183613
    0x1140313060203151005030108060f150f032505120c092e060f080702160909020321040302180601090909080706050411210a12120203090c010f0507050a 67
    0x70f41000d0036607006507168030080c07040741c0d560922200b08040b81d80c07101a100c2d850425028100fa07030040a1401c030151000400015891041041000080403034075200011301c1400071a14140685001040b11081f050000139070100c00c80004003144e408444258044854140c3c4640350042280784a411100c041d000c200043c1c5c4141ca0f49200c821204440c01c1c005100f0300502c59046070b151301643c042000d03007243d00c100540c003110050b402441070009000641c0a80c03504c605010080c811109002c1d80c4034494021541c042c414004101440300c550501a184443c2503000c0d940144012440344014520b141c0d44407a5403004981f01c0d180585a0b03110203464100c1510240030b4421084034103180c20402c40b00010310b0391241c03600403402810f0700032984080344280035115110500d0409040b803000e21490003110001840390b00c0d02d9001640b450101040f235003c1e100c82c92a4130007400f14900220401007001c03000543e910000c4801d0742c904580f040407840a4400703102d00107026165030407098110010 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 700186106 1250 700184856 700184861
    0x607020904080c0a1203020d060602010b0d0b3303070602061308030403052a0f03041a18130c0e0109140f010509030a30050d0b1504030803060114031306 67
    0x1c1040203c2034440900c041d59991400411921101000c07940c04511601110309602c42d141c064410ba000810085800344002418901310742001001d01c07a200c000141d054042c5d8020341c3c10314490180030300b11084201900d0101c0e82131400300c02d019105003a000a903e51001888a00542064000080c6240191605041c0e540024400d800344403040090000d0028005800c0c85030b03031141ca41100802c1451050700303041c40340059104420764414401800303284208404180304000d481d18117541d98002d41801d1a029004610441c0c1c45604100d65800403180d9070045000c0c10103940d100d06c90440306900544040c045c5011302c3d80c4890b43c0c90b8035100681070041240349515014101a402d1502200000c0d291404070368080720305464101d5264000202d01540c1c0b0350105450b0254003250403186001840d078003540d220345c107420f52500022541a181c40c800f01a001d0100086c0d60b40c2e4685030700b04807080f6801601c0c03107400100807000485c4941141d2003030300e0060480c000301d4420401c154403810b01 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 700187356 1250 700186106 700186117
    0x901111b12041403010501051203090402250b0717100b07030c06110406090801090b0720010f0b010815130906141614090306041401021c0b0f060702090408 68
    0x8500c81d4689640c951448074000c0d000400c40b84038110410b5080405050030b403441030740030602030043c040760100303500c901006a6462180540d00162680384030300358010b00402d5401e0b6552500b2078101e21400303001d9030035a001e103d981d6030340300c40701000a5100c000300702c11400c0340c41803904001c404050000441003001054541e0003072034680d580b50600d0726076404441202102e82c0041c140028200f052503000715120300248101402040207840e1601c9001c100d14008240804000f040031801c04c20900c0300e2155880e031103900000b00a00c48030117942030700031f08070b1102240c080b03982c060006014024950700744083c0709001e0a000320031548101450701402c14280200c1c0c036141c950040104401d14148102c0c072851006041450206004d0300151499050304104542050100510031700d644000070360a0b0031039031012142d080b44000c440301a00a0088440902c0c0c02c0034100b40c0c40d0304507915034000c490b0755082190503045941d000c0003008458420414002c0d00100d40100140108480c90094031 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 700188606 1250 700187356 700187407
    0x201092d0b071808100608011103010b030603030c010c0503010911031003080c0c06070605040201180e0126100504050f0d0207050f030f0a050709050f15130b040e070905090111 77
    0x5403801c0781680c3c0e04040f03020350000d803107503032008651a0103054140030740340081032250000c00c006a078a404122161005000703a8041010000c017060721900d007001187c4181080320001c20aa2807000c90081c00d6900a21910107a9400c00024009174080752045900800f424400e048990b072456480d100c140e00300104015040c05480c503642c01c139485100c014209180300c2c1ca4006441e140c148000b4010015030f60810802406004081c8003505420180b103055601c80e10300f80c000144103500840c903603441d5488111250066150641c0481c07842e800242c0250b1080050350680c0b4061a83e032030381d0324400803003400164007082c4100014141074030507400507540581030f54404414030070b142d071a010a1036003c031140d50084404005003082c0c0d105240d08100081c68070300c00d900b040d94003440c008003406c408510420303440c0f0100907241034642c8112a0004050000c0c0442030742e0302d205944030001446030309100e9003400c001410285040c8104403d00d90b54070b20781428404000c2c1191100c00100c80310a = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 700189856 1250 700188606 700188617
    0x5010512192a170f120304050712050c030c04050c0406110309030d02060a0f09020a051306080106060302040305060c19050706020f13050f0f010912110409030201092d0b07 75
    0x24000d40b5500c02e11466040141440c000b84580f81481020741c00c4060710604096402c5820502d88000020481d002d4103404524860707200e849500f012030401c00e0345d80c041000491a48e85c2401001700100d85461202c808074240d070400380781d90040c0b10585004031051444c0240401003804a02e0013007800001c03006042d02124101060740d00400d03e800d030032884500140c0d0215081207030480e501d001e18424a0f081c1e00040c44103ea2071b41c089070785002140a032512685109481404031f05081c0d01a0004140500c028030040ba0b80d00700c044e00030340c060b000c2a0303032500404001035203008580e4210b48101c200301001c4a010000d240048030250412941140c0c415020448a44501b80c20000b50000c41703c0160030b40d02e29890481000b01401c12041500d009500c01040100140e8200350b04504441a400d4500c040540d1442c0500420070301c10086a446482d0981410501d5415408049202d01c111070603040c40e1070070110a100c0348a0300c046142021425016040050a64014150050400e0070704 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 700191106 1250 700189856 700189883
    0x9050312090303060a0f1d0703091a0702120f0909060d1401151509090c0c170307030b0d17070602210402040507090f050607020a030803190501051219 66
    0x1010003101562014890760000c8240821031401240380001000c141d204c20b0b03911031409041c0404000608120412180064005840350b8040d0b004203d80c0740d88251410001140011007400c645015100c00d80140b0601ba0101f843c0c40d0350000f02c2e0340d002c001c001e80fa814402840e04001d284103008089a400c0420b10314940d000032104011003088500b00b100100e141401c08141043d40161903000780408036040c82016161604804280141c032000304010500c802c04800a0711410b01e0004002d10001051396192205150040a10301540306990300384400c400200410071607248102d00940265185c6080c507181c00c0c8000018062140718080150800d5900c1c1608200c9036a611105228004c91742c00b0042107281600c00c8503803101c050f040c40031003141006841e0071003c5a9000305805175500144880566503030b042484000e40d8130005007a60307403410100e032104010a0410a0003140e0a010010405e858000b02c00910801000c00802007441c25051540c0c107035080d20003d41e12258102c29 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 700192356 1250 700191106 700191127
    0x1c02130b060c0d2604030c02280e011a0f1606091a101a0f12010605070501230a0b040e030d02090111010908160305250b0601030b060d090503 62
    0x60010240110041c0c45030542044004d001858101c46181840da01c01180001103003a00741d00c0340e003040d01840c4c4500d0240940c0701081c4650200b09104031014803412216500b1541045502c05485c403e0900c0041c036641c500403205102d600d61030391f2841d071400f8031031a504c0110703084c06482c1c0148600b001b150103100c50384079001100c1007014107a62079140068040c0f10013030705400f440e801030080c00c5445c01103881c01d5071140c14002d00c9480313100340000001d00d0300031407101a810384815091040400e203995a458002034110360055104079029400d0240e580384940c860260080f2665004d85258000d64500c42240e00401c54041150392042c0d0b500c00300034185c40c0c1000640b001540d4082c0050f07460380c1041c00540355194070603401c5200ea06141d40400000e4022054030180024584045c106064901c0d05803001e00a00340310404010b45030300768101a04602c04c440041c28001d21080306d60f6203458004400350780c046480076030070800030480f034003114807140d0203100b6581c0074000360790511080d2603 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 700193606 1250 700192356 700192369
    0x605160210030516081005011b0203030c070302100306030816030201090c06021014061305060109123c0809040b040212090d0f020a02060318060906090c1c02130b 71
    0x801c0040003d039582d0030070a509038548000080d403021410560300d01d00c2c011546851650b443c0c00350f41d0400002180345a03a000d06200050102980102a00d0701d804516051a58411681c403081e442440e81501c100d00c01d502034800c200a0b66040b1005500d003041c4884500342d04461120203d0456590300d0445010821040c030390005400264040c100580b050034003141580c0d9450400071040d96a40240444c990300c540d24400c10504800010501c2ea90f00401a03c04078000d40c080c5850a00e00f025800421000251340d00205c91403a40b01000d100d25005030780c0444840c082c0541c10100c44401610105080c00054543e0000c000c3c404200045000d01142c1642c0200f14003200c1d81412070148040d042d8240f00740d8140e119240383c05a0400012400259110541000a0b004000000200b6010000d000000340241440381c122120b0f410f0100250b07982e200c4c2103801d220140611003c000c1036250601240c00303040e00340c501040b138414450702085034068a010002410a0341c0c0e2030b290761540c4602 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 700194856 1250 700193606 700193629
    0x7050c0102070501050f01060e0d110d080408070509070503041a0912220501080f0417070f030206160806031f0b040c051b0703030507060f09060f0b0f0303070305030106051602 77
    0x403400401c440c10801964540c01c503041e00020103000264409d0b0000d605c0d8400003c02454004580e5000a144000800d541450200016080d0322001a02055010000800030b08992040e103c00d1001e07078645004903514041520700a254070f5944290240315130101c48202d4024140c035040d40d41480a1141010031a0300c040c209014219208038450154007000032400c3c0104820308082031113281c14203400340c070034000900080070b0514140c046009850000c0a03107040551000822440f01024100a9a1004201c806540c6036041079140e4000034031071401d141c000c1c0c5002d801410640d4841d50384100242c0800200381c0c50580c2e8004114696845000300340d05007266480340d03640c500c0d580042d00d1946e802070850342d1499020800400010703a100b800c450724a500002c0002d82255200d0800c4041e107200c2c180a40424280b09200240605981c000e0600810885100e001d111200301030540305e004005020300422002c0c401080814001c400400d000c00d480b048030104c0307041d41d60000c0c4039220302 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 700196106 1250 700194856 700194863
    0x30906111818100b16060606030212100501140a2304030221060105040c05120f090d08010e0a0e0a0f0b01090e011e020a0203160506040203071203050a030507050c010207 74
    0x104a14000750030b0014070055a0601e2200b0b41e015840c2c452140c400c140300300e11492540d11000251030b030680800750041d08410b94018014820320ba55044005d0280d040303c2180d10800d40a9030218010260101501f01160700607102c0302c0d000e05034613104038110b030480c00241042c4110044541b0400d2070811841e000d03440a500c009840d18214014042004600c000d6100d001d81d54050b00303080101c000580c141160300446021415440d190022900c500070000740d0b1230480004020b220404002030401446a9010001c0350b03903030103401d041221f056000b07124000c000c45001000c55401e06240d04580d4502d5581c5007110040041030ba203e14070641120b0080c0d445080392001480041c855014031408891408001c1c0710812003241e0309620391081e500c190300d5840d03001a9201d5468000d0094802d01d0401d8409000c2000644c1049911054200c030201e109000d00c0c1d102040c80301c20240d101092503050b540709418145111002e500400300a403491040c0103042c000060414424002452a50b10 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 700197356 1250 700196106 700196137
    0x50a0c1706010c0206041d06120a08090a0e0a0609110f04030212010b09090f37050f0316060c03180b060402070807150b060306010c150b0d0b0f070e1003090611 70
    0x18005d07c80341006070152007140710b00300f00410031000980c0020350f4150660020f04007507a075156480080d42071142507010142d1415018200801400582d010508640001030203100300411003070700e410342d885407400d404044e0106020a10260030200481c80c02d59554800000d248494600040c8150804440106644e400702185980c80c040c10f2200b4030301020014210800074844110140c3d03c6150311300082d1055211008003030520a0070030980705003c200c1d4040e2651101d03400445081143d62070740680f602c500384030344819072078402c0c8140c6909241520b40701010320b0079175440101d0883c0c0501000d901c190280072000209000e40014420340e841040450710001554231000b003612001c115941c4148002e00070482c09981040503d021190301403080041400c030010040010084d00c0410745d00481025074100c100700104040c2400341c0a54400c1824070765440c0c20844e800018030103c01c2d0840b2040c00d00c2c6509038003981050041500c01c00000c41c905000002d0b100581c0c0129031103040508 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 700198606 1250 700197356 700197389
    0x319180e240916110109020a06121b0e10090e0f0a051003020f0d03170106020102071401060810050c09121606020f0c09090a050a0b0a050a0c1706010c020604 69
    0x11042400301c14994815035050318545840701a04a507401c40c0c0d461001405054803001400e49020f40c802076600340d000302200910368403040e00904210303410a0718801c0d1442c00460280d181481d0500c2c2c012002c0360303500d03401d03000140018000000e0203400d4001c14412101c80101d040307003000819501c100c0f1a036920700b040749028035a4405a400240191600d242e41c1e54050001d6200d5007050141303038006440b0b06564002c1403404440000402a07000d40360b060b44000810581e03810740003090600e00645c112442500c0c0011030508840e80c5128035171440d07010709211400408a604065071114410840c50705007110319010800c0090070340100c403074640002c100741ca95920440140c101401c1248003c09040c1c2c905607c0e50ba80f42e00880045104480c0080003e011f080b040000b650340e070740c1c0700c070684100e0071807890480084041518415085420200000c1000055225510050f041955144c1c2c2c1d1b0660f00b00320303007800c00010f0005070400503041c980c0d00160315680010002000020b44058820 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 700199856 1250 700198606 700198651
    0x1120218010e041e030c14210d06080f0d0c080903031b12070c030b060d1b0302090106111005181b030105060607020a0b0919030b0601110319180e 64
    0x801c1c1d9441e5151340101041404010a0380201d07108210395200320380d4517201c03030580205440d0000540325180840441800b03c454031480d54058410320112070710038060301c5d0f141c4005c20f440d1080c46600580c00d0740811000c44c0751520445998880d18028845640340050420129003980d1040e4a5100100309010402d88000010084807220342ca40081031400c003407240d80c1d5801e12089a11001e08034501d09800b15401e40d4901d41400410b5906c544818464031040030314200401003480160700c100c08034000011110302644d10302c0e040c285c000000d4140c5100102c2600000c00c405490403586c044128000d000c002401c11483d01005101100350800490142c100340c2502c41c001d01c40c0f80150400d114200050310746900503819604c1d111010f5403a081c8401c0442c2c2f20345528000c2e80c207030281040f4004188068030000c130380180000ea990096409040358803541da0320500750007100100c0321040d0441381e94403503850005240034801d01e0160031991861400054401a1003403203001c8602451035045 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 700201106 1250 700199856 700199873
    0x3060e091c05030c0a18050a240806060a03020a030b12030705160807030f0312050f060102060714091c020a090b100207060c03030b01030905060a0f111201120218010e04 74
    0x5042842c41c0c21031640c034110380d81c80c5090041c00b5100040c82131480d1403030180000901e00d04040c110203020101d0003541c07030580020301e80301d2000c52501603800c4510804a1485101c00138407440c0c002d4045480d207401c0c07550450003984090503207001c041d501e801140150391040b030350400f41c140b017200031340e2034101504106007000100d091030050015003480c20801c42c500807800200700c03900040c018023030415609043d600c048145e15804900341c600410840742e59070394030069010300020703403c0301c0960360390100035a4180d4092400200c8202c041c03152016600d003400700b50034400c001060040314904aa0302103a00c8000d10b030001d0048907201d1091058608048000d0030503020584010300e865071800501804000c07851801404064941242c2c503075a0740241c01c80302c0e0584d0302c0011030300313246055132500008110500d0500400c9040c900b205224001e604103035091070b01c9441e18100380ba403800015a00c40f4407d80e0080307070803c007585042d04040e40c00c1041240203040c940018a107601c0e084c684100b0 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 700202356 1250 700201106 700201153
    0xc0605092d04050c1201061d18040204200310030615030308160905060c0601050405242704051c05030106020318040e0a030c060e010e1c03060e09 64
    0x10040301e00d55081100d220380e041c0c111029405840000389611820b818610910800250216001c0c1a500014000750301000040d407030030000d0000d480e0005140200200c0c195040d208400040241c000300b0003514240c0d10098441400c4910101d80d82e608054125a6070400c80d108802e0000c42d51040007841954042c50000600d0018a855100e085940260400f10b02600500c00d41415000c000c0c02c160080350001c0203820000c2965481d1202c00000c180e451009002d1070b4020380c104000305003818121265060303651032440021140380241c80c18440074403201e0b81c411010380b50759005001303d100c114540c01e0080307000750082c020440302d00c1d000d002d001ea5000c074514100207081004001c2164040700752004080140180d0a0000d60140040c000d05280000c280c268001d0604c240b08154000c0c003404800c904c41d420a0003640700c403100e0703203017210100c010703e079055048040c0074480701d042a00018861a004d04000074540d031650305e0300700c1070101102c412850343e10490000d00107041a0f580f106 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 700203606 1250 700202356 700202389
    0x3020f0402070506070518091f0b0906040314191505360a210e0609150a0309060f02090f0a080c010c081902010219021204061101090c060509 62
    0x14a001800c3c0e03035007981c2d180014128000c004000c65059603180441d0480031000a005010300190b041c503010351f14200d940303070f01144100b1741e1800000414840490548819440c010106030809155440d1030380c65191005c03150344940110a03d02e4a000015a0b01c124420302035100002003100500180301201c00c050103942c0801064421714030000c80d01010a050500a10541192481ca824203d441c02c0700040e00202031122001e15860b000e12460410210034034540d9a001200c4060824881248503240c900d5421001d18912010402400c00c0101b03c000368a00d000200d103151030302e482c01182e02c0c000750312102c640c0015484c461450a001c500c44035030400c44201c2c589c2c038500041650781c0c40c400d1511906000c0040c000341c0c288420f02055807100f600b0402807849801810038004c0c000d600c44054907034062410340c0e88006c940d04c0000c070031041d040c80002d414545401c2c440107491702e010100300e40000e50b40b101396200004288030b41d000d0040404c1d0300c0b0136465105040030004030602c0ea4105030f = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 700204856 1250 700203606 700203611
    0x2030c12040f0b16021e010315051503090304030602070f060b0909061824071701210c05061201090e01110706020325050909010b0c1f06080d03050103020f04 69
    0x20b00c10746030300c4068501150803105040340d0b40e070450040140b000f0401a8081d5101e103840c030040034a1080c0c00c3c554260702809903820041400c4064910700d075510140506500810101850281e480b01c0100641d003000110b4216420a50b90b507880b00203986c403027030084659110810f0110304110150080c0388468004582840c0300c0e00d0403190a6a03544002405180aa104031042a200800900c208841a000c1a586100e4030124a0182021000946040c00024003101c00d0302402c20005040300d040c0ca01d0100c0b88800038601300311078500400019001c7d03488020b00b000004e4195a1040148448410801d0142ca650314000340901220132402440c031175039050081a00c06801800102d84290b50300c6400103071a51500900c0f24101402c000d01c0d01e2494034660403a000c003540000c0a80740fa414111002c411130307030f25048000d600303005007c5c0c028202d60000c19222000300126001c07690054240300c0c0000c401d44d6581680346401031140c0c5d034802181e80c5800510660030407003118031505000742d606 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 700206106 1250 700204856 700204859
    0x19050d050c1923161212030b130c080709210816060507050c1c1416060614011407050c01081005060301170c03060f131403070302030c1204 61
    0x2038460802c002e005034104410681c0c01c0c204100703480f8a4481031240101d0004400304003c40d141d0313450322030b0144410321801c1d210011380c0c821122110b0030102c1e07008241c0300e504402d01c20140c020b8800304040035030280d0140c0403020b1039800c030321924840300550f64400d0303854109140e000e046480e0941201d061a01c0c0e03022160114010540c1e0480343c07940c415202c65032404011108030744a0340801c0700a01440c241005d11589642c4400a0150002071a043d5021000083c2c203041d90f40218090142c041801501d0b00d0b0b82e401c200c1000b078003117003405046003401040180c1c0e411040303c1458202c90114a0241c43c1000346580c0104040c16290400c03641519003035103a110035581c2e68200c070001e81003104a1001070300c450b856003441d2004000140916490f9615044622010019200c40301d034030b8072030248007c0c03c52600080d1280104007021080c466a10313902106a60f80441840c1580c040544101c001c13450b59040004184d018001d038080c6807140c030a003003281e0400004028003090b0b10000d000 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 700207356 1250 700206106 700206127
    0x311070c051206012702130e0708070519030c0e090a0e07080303010b0d1d030d02071406100512030c0a0804090509030307121a0607030e09061509090405070819050d05 73
    0x1072102c90902203100d003178038407807201d0b07201134440c81c1d1416000d0703c2d200c1c50009006071401980b43c002c0240782c540e01074541d01e1001c01c861314090045500f00300720460105e02e600707600940c4055a41c141c5464054081540b50001c2207042201b40c56504441c0c4c1d0b240000c50381c0300001e11044000c1d00024001d185076502d04640d4848a000d590b04491005956030341104401d02851900480601c294050f01d8032140f030b10944078002d4015000c00d5441c004c002c03580b070b1425000401e1191151040d031007600511070920007444412103178410811a5448100011600070008004031200940308030644c641e641d0030030481c00d050b03036805003551010f980b003482440100c1c0d030481c0300c42c83c0d16440c020000991203c0e2801d001e10f141000d40500340c1019000460005060707108004001c0682c0c1510303008500c0c2c80d44020300c107407021041c0502c1b01150007071004a2107460070441c0e1642260040301150092922510031a08000158044907261020201040d0400c88244440c201c08151410010b041160401 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 700208606 1250 700207356 700207379
    0x906030f131704060207050604030203030d0f060f0803041a072003210703030606090501020a06231303020105130b04120215090a2f09070311070c05120601 68
    0x2814425200c114000040358501000585246a41c00101c08000c95100d5100c658042d4000d014140c0140101c0002081e5800c11000b10f070101c0ba0702800951a00300c1d00c0003100c0040403d80d10030803006403202400504009051000000f600c40c5502550b522880c040d0000e0704000040c0200950230310034041c40000c0740301c0004a0b2011b81e0700728045d2860850180c00681403a0350803039800f2001034510309101c0100c03c05405000c00900c41e0f1010080d13941c9130700c0709454007842c0c1e1150030b00580c001e480312030010707043e50428004e004004296160748003440340b120500020031130301c80c07160002c6c400d245000c1c582c0c24011141c00074010040d07013044075407588076440203070300c0100f01811040141a40c1c1c01018420883e4483d1404c03032a84446403420428030300c50300d880960f0f4040d00c2d01913554195000d6a64084030407059075081d2010415041440320500c81541ca00030b103030380f050583c0c44000c228200401c100a011b5076214030400324010381454108510200b128004140c964441c4005108180d0ba0750f = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 700209856 1250 700208606 700208611
    0x20f090118080a030503041a0a0504030f02060f1807030231090c03080c030c0616170f060409020d0f060f05070509130509011805010510081b010806010c140a0c0902090603 75
    0x14a00103549607908e0034441000d0700080202100700040ea81002071680e02603111901661003a5109404030030080c0d02241d41e0b120644040501a070300c40c0100d40d20f025071140019001252001380c81c480c5540381c00003004007103078440d0072604c0c0c60b8001800072075001c111811300c440d45150b2030802c42100030351941729990446010007004c481d0001605805e640b01041540c1840b0138100454034a0f1403e411003080c80580221420b0109000f140c1c010b81105610510034420020840c01c0f0100344e0300c6108100180085031400d076040300c17143e02010040741200c4400d010541c09000082810000440390760102e800c0100040108001806084d4165440301810318000f0880d040102d480e1312284065801042c490039030800d0b40100c1a1800101301c0306400040c4a0001300304041701c0c1507558003030350b600c81c2440b5049211140d54080c84090f650b0080003000e81044041c03400101c0c5061680e0707041c03290044000c00400961103e41c00400704084509603c001c0c3c40310a00035402c207042c41d0003199460001 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 700211106 1250 700209856 700209863
    0x2131403160905130b07021b043308030c010c170610030f0204050406090b03010b030106030201020d0f02100c0302120709120206030405010e06040c060801050306160e04060801020f090118080a 84
    0x10755004c51410182c81401540964002031501e08038141120080d40e96480000851030801d03505001c20701c1440d01e84035080d4040c0d65071101c0804166124111081c07441c17115082c01c1d002800000108158030200043c210050391070340005a040010342d809003402a0b00300fa90360410513500100100d58403008211036070189981008a030344201c00c02d1020183c0500d4002c145c00c685840800030741215170b500880d03082c15003900204003680c2180c0a040c00d98515000c06809640482c0202156900c101d04040e80d0b60300b1841912401816500c00c2c509940d40e81050b040000d0700440d50050350195180c0d410340000090038400130081c40d001050840002a98001e4420340b130101c0000d040c40402e4103c1500708070241c007960140d25080c540f100d4000c00340e010301c030000341d03070070b40040380c0360400007800d0340102c180040e080180c0c0412501203031000f081142540d0820744580c1d001410b120300740040c1003229000b00600380c464420b0000103100c48007000300341042180341311040000031400300300b59028582 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 700212356 1250 700211106 700211111
    0xc0412020a180c1107050307120804080d050306041508060a090314162102030729160f030522030c2a0b03060a1512021314031609 57
    0x12800000d04981d125445100c8900364201c0044040d00346034080c0c805802039468008a011400c103010396954454020b0a4259009220510031030920346180c8000c04c2c440d001042c90551079404c55801c220b9140000320210324084148801d92070a4011420082c103400c000c400d00f03074540340c5036070340d2010083c0101d00050790301da030b003407017410312800d0f55589500400c48840e0703844a403c2c482114410004400703542a42ea250212540e000041c07500d241c0c08003e5500443c242202ca4940e01c82e00401c00240c0c00c6101002d2a0129841720307144001392140008042d00d8480d18000300000c3c0c10119981d0480f402c15141204103c5140084805e80550b004202009212910185420b0345d2501c40701c0000fa140c0c0240854031400300d4080d502c0c845119889400d2590f9256660b03000c0d9201d03000c25154180d200e5400c132000c0c44084281112001035075042d152694242401841e0f400480c7c0c40241c0841c04041440c00034849491504958411030805800030195920108560f0102110078050307020002d4 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 700213606 1250 700212356 700212389
    0x1b10080601121d0303100812070605130f0f020f03070b1b030405210c0d02090a0b0103060b1303020a081603060f0b15191d0103050406110c060f0c030c04 67
    0x5280c0d034016450b4036481c018910040c3c1002e80c20503642e4008a408104003040c41c0c40200b42d001011804506c203040c4100c8c91800c00130341c0d40c0d90341c0140100415a0110500c030480d9400801d401f0301c280e9855500400801e03a03d4459030040c4031804e44a540c1d054000e41c0110000c0200c26100001c9441c1d0850403942d04044480e14500c05055110346d5014035403220200307149001d00c000c1001c021404c01c6001c3c0031030300c022405500f40043e10b15071a401035485649640040d142c0b0784070303402004c1410014900014201c2c2c80d040d000344950402d89894402d003100113800d02c11410156602006454840010000520002100d4480c1400c0d808002e003840d445031400188403c19400800d00c00323100801150950704484040b0f22560044659024035840c619208909103000d41c0705080500c50507007185480d103403004010b4000d0200071f4000c4440f655100e000d04100c540840c0a80182005070029011608012140c1c070084e01028080b485041410003d101c00c090b01d200c1200c085400d12000c090829 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 700214856 1250 700213606 700213637
    0x6151b0804080a03050a111603060f0f02030705070203060105030c371220030c0d080f04140a062604080c010e0c0a170607030207231b10080601 63
    0x5001c0e55200d229a80302c0d8070543d40805070800081d000640c210b0752407501e02d0582d003d070b40d69514003031203814118640090090010420703d401040c400c40d250040490902c4644212004a82c0300301c071184005407003c10701d441140380500480c2e006150490003010070803a0038001594050b590403400340c00e1410840b07007030400034580024411942d80c6550f0113600a42d47c00f91106100b0304d4200c11100d03110b200381d0404100d46e600c8034545120002400070225041d0540a01032242150101911030140038407404c41c41c905a8402407024124815401014820850520000c43c40300c0d0007003004c0c042c0810b50400084941c8400804200300011b5118164456080446143c0f01b80c0003503c031030b5401e00d101c02e0b8070880002403901c50b0140998480320395683c2e40820801420186102001c907030014408280c9442c030076005003902900948900703003d101c03036134110079407076101c40c48281c481e8020180f803d80d17580e18062486600203050700c020301c1d140200600248820700041c00e250511042d4a54512031 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 700216106 1250 700214856 700214873
    0x3070e09070e1b0d0b0907030c0233090a060608072d0b03040f050f0c0105120c04080703050a05060a14270709050f0916091e1e06151b 59
    0x156894107036940c07941c11000e84c00380010300031442c0140b04560200380703028420700c203100c0175801c070703601401b00b41b8192600020001041c001e000c03040308513502001880b4003488201402400150000c00005103146022020307501c2c51340c401c0e51a078100316020000200b0080c540c0410824180540c60b0300c00106403840c4020030f17540c03c00380403150b0100c2000104101d611880d596640582e085462005e02c1c041256603440c100c2210a000031414018611060002000c11b600007480450b018185502d030003a01c5d02e020040c2e40140e8503580401c4403507060110a00060341c02c16642d00c8c080c8155500c0130201104c021000d440380f5a40d040c0d040d4003a00105410412111042d580b00c280c03481550303a0749800024003c181d03030481c3c9407125100820003004000410500b40c412044000800c10301d040e404000402c003a1864810080b859041010754014070711a042c0060700101c511000120140c488400319203141c3c00407441c02144081080c0c03140e410146a040c080c600c00400e4040c99031914000e1007 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 700217356 1250 700216106 700216141
    0x60c0618080403060e1002090d03080405010902060c030d050f1005120c120f0c030303163005010e07030b06220e0c070b090c0d080c2a03070e09070e 65
    0x104500410003100300910341e0082c2c40585e4149003181c903012103407040310080344180d0380701c3c55104080030625400680590413603070303206029500020f0b006101c0d80100d012580640e0900000382c10014003d09080b080b40304181d00490100c00001051400d90031124112209000326481087d1020044504e5030781001641403c4401500403004d02810b00a01035a524a0018440682c02205404083c3d802e00009a1344a04440008288038070442141a501d0190280b210841020b044455042000e004280160f080c0c042d0303680001d056141040801040c030014040343e01701400c2001c5507405603070f01d030152080b44800906004051070190207101e06114681e0100324005407820401540144442c00307881240c0c054035224039140c1d1140f150540355500c4d2038003285e00441c048200008241030f2009000e01c00105011141880d51042460314030400c03803030690320703c481048283c1040d400e00344504401419040705a15190410a40580c1c43c4d030514002d075500d508010001403034180c0d1028100a = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 700218606 1250 700217356 700217363
    0x30705041e0e030408070602010207020f1c0807050d08062205090102040323071715152e14091c080403061401050a0b0909061f0804061104060c0618 65
    0x104a5189040c030584135000351080301c0341406600000100300f8010300071a480035071300400030203416040d44e0403c0300c0059060b181e40198000a10004005207070100207000c96402400104482c1122050080c401c00c1c0003002036000742001e00da000c0100420756400b05800c0b0582d54045001c1d592a11800d00901403030b4805481c0160380141107812440308003d0303484550001c03007941d040c40d899102901151501503d1000346600c505a0a56003aa13a503002e10b40004402512003840b941384d000060451113039030240340000311509085460746400c1801c1a0442c0355500700000c1504e1030b090550707124001c00051501580444070701944058114a091525035130004005e074490b0b0322414504010040c60312024401b080c01000443c940c0350140485040328603410205250071600700070701200c071801401ca507802a00c803003901800f0b00504199030600c043c1d02d076503c403010318089c24440207840300314400c2d0392000c0c4200000d102e407680c044100901a0380241002c03c4e69810188032021103c0501401b4 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 700219856 1250 700218606 700218611
    0x605091305160b1321031d060f0d0e0d0c1e0602190206091504020d060b0406081f0209150a121107030f0914010c050c18040309080606030705041e 64
    0x8560820103502410798421428100b04400e510340707903828420742d8820b541c607044418001200000074895180e4516460390420112501d010780808030740e25820a616106404602003441002507403140712f8451000e51500050001d000c0859000d45181102000607004030a0080c08021443c140c0440e15203c4c0e5001c0411561074000d000c0000c20134400084400041c016040030074002d800014105c1e030f4000700c86090310b4103074a460342004200c000c1442c1c11100c0503101c801845c0e880c0c0e0b0340e120b03200c01000100058040e408844c0d003c0110103021002240c50948140030a81064603543c4003000303000c1e0140384880d81c811580381c003500d03844419a48001080c2c1000100305442000c00701512000e48251641402e0401d103640540b07004049000f01a0040e03200604160990f101d0180307070614601903c29034040c503041ca8003107100003280304084860210040c0603c0101903001014a0003003403581d01801017403c01c400060f4440006104180c802c641305c3c41504400701c6030380d800d84445400040708 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 700221106 1250 700219856 700219859
    0x1050d0923030310060801320d080904060b0f16140a06140106030912031d070e010e130305070f0c09151a04050112020a020102120403180603060509130516 68
    0xc495581c0d2007103c0070702e0081c4c0c04150000310b940c001c007140c605903010b110782a14110602c07243d000e210154062901310610400500076602d8907200068004140030380031080c1c0d680309030000c2c001550b0144d03001168081d0100555410704581000341d8150248070b400c00c85081c0d086062003104107500c89400b03001c40c0240110b0408108a540c032006031142100401d0450f0703a601c031801e404a41e0350305805080c0f80050740d1907403c00c0d84640d220038010721440303402c110903000e000080d500d85910703500f00c030050101010050001c03480b00c0187c43d0307200c5444440140a1560b554004080b406004c1d0300038200d5014061001c10009404000d0000c1c00b02c60800700720400440800e0442800305100e00040303141ca02000c00e103011244405c03903045d03c0341030b1200500c440234013050034001d5204150510071550b00780405200c0c41e00001119001fa80a9a0b072400c9980e0301103034003086c034821984803030141031500004002c82e4030ba642480313a02c65142e1800011100c10380c10312500340310f0b0184015503041a0043e0 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 700222356 1250 700221106 700221173
    0x9060d0606030f0203040b0432030c0c06090a030b0a022701080601021903050918180106060f080f1b03071d040e070e0c0415030903030b030c01050d09 66
    0x805001c03078281c0d65040c0401c104215000c0124802550042e00600c0100d0000c1e0125030500c000440441002030100148a40055016440d10724003030560a2504005541444590200191002c1300d4040300d099103450924400504028480d1000602d481d0320f001c00501c0500c0190b054540d00d19002000d20103140854440f500c64241001402c0e010820301ca003c40e209520001e6050014014200900c051804a44060316142c114041c59a13100d50712007a488107104901c48418040d00894668565146507080c8403400d550f00d5401c1507007041192401e02c0103a591080480d0f8000b054050b8450481c4c54051043c1d0300403d240c00455104400081404511a80040001402c1030f104680c486104070500410054900b00812410140c1c840c100a01080003001c01d60394110031740029003403034641d07980907140340000d20040e054040382d0f40c0c041400034150180100f200703001040340580084203d08001801038016440043c1c195503a0b0f0503000100041001e9818240f500d801c081402030340c4c000c0 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 700223606 1250 700222356 700222361
    0x30f02010204150e0315060f04020d0b0a030b0108151b0304030c05070e010501030f0623030f060702030d06061815050c03030f061503010b0a05031005100f021207020d0b04050309060d 80
    0x200c007240a40b11b010040b02455a0000d503407401040001c14000c10526450100070203900444200342c005075880d061180b09589200c0303884021445056190400d42c500340b9800e080540c100c2440d00c0211154041055100e890340818414155401d480c54480d1901e040c00c403550480b81c08001c0003481511170210b0000b40e80480503048a60990701880552400c05d1108203440b075500c00c06070b400b541c400d0301c4080170004031418007124002a08481c900040f09103032615080003511810056000044c4021486000c0e00910780070b040a41030202c1030160031441034030180350350321410500042182c0d1826a03580705008442c108555030044a450303040051480d111084140c495074401d403c2985003c204040760b03010380f0704940251000a0510f81c407402c054a19900040c145185840303000c00114032540d9452300041080990381c1c550300c0c000203e03030b0042d241c598050356840e503d41c0305200100040c0d484003d01c44040340d21989455482d1141e01d4078a2070340c010f24400075405034010402c05202075181c0d = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 700224856 1250 700223606 700223627
    0x51f27020a0e03010c090f14040b03190302011a030a140f010c02060a0605090c0f070507030206070605060406061e030911040501060c050c0405060d0807051e01020a031b020604030f0201020415 84
    0x483c001c001c101813002c01540c1401440c0b10340e10300d040c40c016003000741601c010100c403100b030400b5001003a80039031480040d041030345c50006114180a1004030f1018903a092081c0c000189407510340c0c4c0711010f20700002a83d41e514241009204100036080319074180414030900685691039030080c0043c0d070303181801070b40300c540c02c1307074031100d140e140010018a41c9844106a0b02884640110038036008a08070700140e00d511241040c2d4191040b80c500100580b1510010180240100c0b800160750804030108016510168445410014503100c880e0806074030050102e110f09850030005030100d40b52504208500d00000e28580c0145000000140d86800c00110503041d80300e0800ea40e200400ca00c10002281c200303607040e94215420010200c001100b040091a005010320205c540100009409a006000c20311212b241c59402158035040c942d01805007100340f090035401c001c40e40304c82c03220081d590a0010005000c22411604086919000b9412100540840700404009120140019000b40d880 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 700226106 1250 700224856 700224859
    0xa0c030e0f070503150f07050309010e03041214070501051b0a0606060f08010801052202121219030204120210180f0614090a06121e0609051f27020a0e 66
    0x840002c0041c0040f030401d4103120f11b2480070a0b41c807036110800110b03050303003000b4111032207907580d2000c0d452800007c00c044d0008018000500758040c5c23041c80c0001800181e600d10318100d13401800c003444a60307082010360f14204442c0031203410190750185500d00d40703602c81d030004c2c00441c130304a8085203096001800c039601c0d80c1709880302e00d03551b40e0381c1042d10300b03c3d00c04952214030100d88140440000809410820b15140020906d4200c01002180c1c5070400b07182d084017201045c80040c010f204200300c0303400d5a10072242400d0440c10140307000c815004000ca50325000303209000c4801c901116500482e4245043d030040c400d500035103900c61000100030603040c020280454207822403090140400700489040b403d025007100c521030b26203401070f42c601c2010404050119281d000e000c90010001c52226080e024025020800383d01d0600c4036000c0310005010365503c15a0f80700016590720b216006182160003e03106003010410389942050340c01c0210030507913046400002d50f42c00c555030080390002284070 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 700227356 1250 700226106 700226113
    0x13020a0f1b241d0c3a120306060503130c120b04020414010501170c1b210307080f090a080d0c08011e091a0d0c03110402120a0c030e0f070503 62
    0x12407420f0a104548a4540e14000780d00032070381001c0324140b010500c0b2000780c849407043c81200290942e010440d11808010360f4141007126580103000c42a0144e0250030301038101082282c6c10030754000c00da0f1000030140d002c3c80d50310b07445a00c00c10000402d00301c0100341c4030362748000d19011890040315400080c1c0f0103074816418040744008182c08100703c039048a005841d40724022010341d406009184009102040519080c00000120703042c08035852240d42c100300103851a004651076081300c40541440c00790040710113004001e80e807a04070003001e8024405036000c6009540d05201c1138035081846800030701400d8081094800ba004541103010b64040302c0e182e008940e1380703603501c862100e10080d03da6800702210200c2003010414903480f86a00c0c8007603a032550902610b000c04140900d55805040301c5000007241c0800512000f61003203003401e0170444055260842c866180e0902c01c1d0080c0448030802c1e502c85003118094040da100034407464085040d691540e014200f4142c0b1040b0300d10405000e0701 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 700228606 1250 700227356 700227371
    0xc15100e01230405071205100e01090b0a05060706060807090e0613030f120b0a0b030f100b0a14070204060902091206091e1e01060513020a0f1b24 64
    0x1a0071141481071001c1602e034078580030000800b008040c11014007100207020f0800c00c0021854018000c480c443d00502004414042c60800180054034050340b003101d011345811480001599aa0b08180c1141c0049507056210041403d181c0c0050180703502199180c807503070b1000210480d46400903030711800c002050380ea00d5504c002c034207018440010740c0100040c2551018aa1075806815140a13080c00820005044100b1802080c90340c1115085178411440100420841c02d00400340c480d8000c0d020383e090405103140c408900214061030119000f402244003040c0c0d003c4840d0400d0b144800e80051046c041d187d42c48035203400a62007040e817640a0601082039228101000445500401002008210b00d014004511000343c80c089001202c0d40514080320b00602e0303a00070910b55201440000140c0c0ca858141002000706c4801c29000d0b855005200103078a90b5007040c03012400c030f1070508060010001c3c2d06001140400d00d039200400c50707140748012140c80314805070480045140e81c0420004070 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 700229856 1250 700228606 700228619
    0x118051c031205070917011b12150b030906060d03054005040b03070f290307081e070512061c0302250b0406050a0c0609060902030c0901060f050c15100e01 68
    0x7a807641d511380d040c4012a40c023240d183c6126207000d01503511207200001e030b0351480080300421540035500c684500800072080c4112030405008950300000304845240c01c0d01803c0e90084c0c40342c00b0b0565180c01401010160800c000c080d0000b0310012510780501d11506c201d01088901d03003503103d001d03a9004602c0e000700000c03071b42800100e04099138100300300780e51814074003801c0305907150081d005666555041417108290342c1c0310002840c0100003913180d501640c40e080c001024041c501c040002030488801043c0450f1581201c2212203c283c000e0342011244d4910300800c01c4c009241078800781c8207004a01010505501240c880845180503040481c00c40300340c810384c104141c0328010b038601c5007c200001c01425000341d0040542035882d003820003209883d038440c00121242201c2c1075405589415404013189801d00180b0180102282d518401d541020f400800e24190100400709110000038650210801042041c04201140d080180c2c00d2901d203010182d0340c090ba100390713804000858008a902e = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 700231106 1250 700229856 700229861
    0x50f010b01120e0304050a030f0b06010c03080a020c0a0c0906061d0a050d0c030b010b0c2103220609050114070201060e07080403030912020c0118051c03120507091701 73
    0x220340301607441c050744112082c0c44a0041204000e80340892104100004064a4149070000154020410100c46032082d081540044000510040c10081030105010003e604210324036000408100c0c0181c86000800c0b059141a1385014060700040100c1400200314000303400c41400c3d0390702e03540c07041624107c41d040380c040c224201107295030204110310244040d00b03241813508059805107911400301d0341e982c0c1f03a03241c0e8000c0c02c0c0c00c0402002e600161110b0540400c00c003a418403180498596002da000c8401c40d07106000c060318054281034081780c050b44003516003848071038464000700304006a025502c0c00500038078400e00803000461207140044d0399103006100310011292110380c4840329940e00326041f0741a8200902c11024159154056070114101e840001c2401001d0f400500300040320301c0001d4000c503001054003030301342d81c0c288040c0469265a0302040b00003501ccc81c0001d5030000d8502e03040c3c410030900e5014000240c80e110070410341c00e138000c0404044840c51082104101c2c4454021404d = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 700232356 1250 700231106 700231121
    0x131107061d0d11060f041704030c06080f1b0307020c03060a0501030b0711031911030a0f02072102040b0f030a05060415051e04080405060f12100e0106050f071a04050f01 74
    0x1071a0032044c0021403000b15018026485845035484200e103450031080e82034190031540050360703220ba1060301884030940207600c26400900d0421040c056140283e901d520341440c41c0c070b0303c120b58040400414403450007003026404000000302660010319013482071070000c0c0030034030082c0e80080c010f10100b03840314040d0024001c0b20b50f0f024003075442c020440d07441c580d28004c044c0041080000008601142100a0010300801201741d80c0d40104001e4062000749040056006000c800106800b0100115140d1901c1580e2940c180d40102e403066448000403040d00709009403c1d01800342c054803408029011510500c140c0c17048110317180010180020320b00308d83c3e045801206001078081c4644207a000c114589038814410303028145040c0e140c001044254200c006600400c5001180380444110814000c1da8800c5542094070107040c54200482c044071410b2160360148000002d10f620101d000c24112100d40e90012040000d040140448541711007084806031001d00650f060f40c5020f4034180107c01 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 700233606 1250 700232356 700232387
    0x1206090c0a0816090b0a030e0114011d0a0216050a051c2c060c0304061407020609060d240815070f1107031a0402011d131107061d0d 58
    0x240b05a4442100652408a81c4030400501c040c00c2c0c0006501e6940d4802070820400554022507114400c54200b42503407000701100c0c80e00072103180180303d642100000039443d05a400e02c03540c500d40300e01c440c9000900c11100b1042c840600340c04c9100074020001004143c06204108603102501c4144003040c6c01c0500a032a41c000039181000610895880160080c148541d103840700741080e44080050700e580c0c042011041240c0005c603080215a0b001a0003c0e0100e40e407040c1c0c0b40c9012426400200b880c819184441d12500c40820340390900c4d10b181d131201c104090030182a459810404036900c0d25081035225080080c40340403c4042181043d06605005d99003d031501c8803140003424041d18600c09400c900619880b0b540d0000010036000800d0f0741005100343c00e840307864109400010001c13182c00581c12075600c0c0c0d621554100340c480715098000c4610841d400111200784401d038201d42d2081c108054807103428040d09100c440410400c0c2c3c21a80360603001c03a40e2003403007208241d0f16040c0300700da0413 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 700234856 1250 700233606 700233617
    0x80109031b0b040b071e0305160809060109241e0b0c2113090b190b04090c1407150b0d11060f07051e010c0305060f1210021206090c0a 59
    0x507001032040f80341617801040d24145000200582c0b6081a02e00b030183c0a15030000c2d4440b400c3c0200c054208002124100c401c0c90710201c6403a02003d520354504042c89030b556502c2d07880b450a02010072a40d400390818808062104004c0d5641900001121010080c0c0c11031340c060307074070015815120100f00c600c407049a101a116003400000390448000154a840920078401c010390841141405031120180c140d1100c0003526042c0103040c8040344166a003e0708178180c085038240308004805c0c003901d0885691100100780314070750100c01c179074044012042e868861800304605042020a0700180d8100010319070400c440180901000041100d002e000360005500c0f1030b032450181061001071040c03490004940d8540f402507070b0745a1501440d070405c1408171807420014440c0d50800c1c00758003000580d41c40d0030301c240d041400004d443d0307401c8110880d00c01c07850b00d1014600c0403024070070f40d5908401c440045446a5210b030000d0446c102c2101c00500c204160385c0062260302c841e100b918800887c0380e0304d1 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 700236106 1250 700234856 700234861
    0x10606030605031903030b0d0c090b010219111903050615031605010507080408070b03010603050c1905030720070807150906050c120d020d0f0c050901180f080109031b0b 74
    0x444400e5484c0d03040030380400d929075500984544804034400d800c40c0c4244000c0900b14501240e4404a80307526407400e04640100c04080b03030b16050084101c0032a500030022000310007165001400c1c484801f258440b01d52500c0ae0000144003020410300e01c10b80d44030a18568040d550790416403160006611b51625034945074061156500c0b0700089d0643c03911070b42c204c500d02a16008802d140400030341c011402c1020020051254035858000e0300d400089800f940c41c01e02b0a905546100c441094001104200000c0700140d030091054803010508813032032013032044d0101b054101644500060061411038840c103100014014242100d03281940c0555903008422030500342c085445600c500b01c003100500c59a81e8101092600d880100b004000701c01d40181d903582ca9041e83d01c1a11402c010304003495150108440350540c00904a5903040424680405034880d0254003039855403080d002990061880724002c14110b0341580039118031030103521402400150f9540d18560309582440003130048107114003 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 700237356 1250 700236106 700236133
    0xb031504080f1e121f0503030403020f21011a150a0f050706060602030d0f0b0d020f01030e0a08280c02040f1407080103110d03050304020f01032a0201060603060503 72
    0x180c002401081e40502000c5010910500c00344c0225085801018540080c0058004404500041d6404130004a8413040c98000020380320b0240b440041e0040b00c46450f103034850354403502c02010812440c0e01088510310400212030081141c0e504a41452422400c002c025117020b1105824601c44020440c1c0b81041c030200444084211000010a2004c240315410000d01903002e52400307000070b80d0045494000710160030301030b2860100b000c03003868070344400d4403021b8594200c107810858041d10290381c04075944004a009040307184040d00180102c0c3c90003010812040024a070030240c1000542c039030050382c1d500560401010400002040d20848143c0040c105500042014401d41c580018424240c0f4041000303904110703a14000103030701e2001402002480241c0e88112902500c010318003410300d58000c0e1151001420192040400f6001156a60700c079800c100411303d0081842d090840c0b01003890100480300107144005942000c00100d0a14420310584040b244014018001c004c410300 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 700238606 1250 700237356 700237387
    0x131a01030b0604091e080712020313050409050c0907050d110301090b06031e0a060e0106050d060906050a090b06070812091504080901180f0602030c0105130305030f15130b03150408 79
    0x41c0b04560b5003e0901810340031881d000790b0840240ba10745c02035556481c184194010b0590bc1f0342080f4812468110014003040780054480940780050700c00d504039445504040e280c034003070304401c1d000c485c0c01d02c0740342c000038842c1070301440c122160f0000502a0049a0040003440d0000301d0b0301d004110400c840b00300344c3c018480d44880d0000b104540000c0c44a440b1300e07000c41e26031026088031000c120006201414a40706104600c0184840311042000d50305150002c2c14007401e0b807061806040e100e4540d10394950740d02d02154130040d4803210701d60b517803200c0280a82c400d8608840c070b450340c1d001d0b0380c040c442c465003891201840386a12044541c546451180151044d250518800e0030b6405c1c218404641d0000320240e2a02608c01c64005544411460703001501355103008001c0c0801c0c03100990807200007604503040e607410038a0900780c0b60260ba600f580783d581000c04c0e6000c480d40100e5950000e012003003180d000c2c0c0b01303a030020342c2565140c000c0883c008540100607100144014004c1000da28024480b5 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 700239856 1250 700238606 700238663
    0xc04050306040f0f050d08060906030609120f0c0601081e0111040306020706240503072301050a0215010e0105040515031b030c0307090c0807020a030e010503131a01030b060409 77
    0x51401c00726613041c80c0c0f190361070030103081d2000010845c5c0c1014410303549000040b0030b03400340c030441c01001e0034a881c04582c4d0f101c9400c1007400c07011580206000303212207000003e845008607000c1c00c84100790ba41e591516031395000c3c114403000040310740c0c4010004070818001c01500d030042c6084c1c5031a0915542ea803030002d5000810541d50700780c0d00d150301c111010b02d15924020100515405154950412082500b488055840344000e0382c0c140c50b000d00358a100086202c2d00301d000b420025101d052241c0180d0529024240c1046030601e548008510141e1050f81c05050b6402520104a02d544803003868684038410364865502d036100c0da1081c0b2465159a644440303080c005029a0415094400801d2800c810f03904601c01c0300783c5600600d80302d43d45c00f0721101c1e4480303030900c01441420515103029103208000c0313461604200001000a4424024100f8003020950040c00864842070007542031881c084280421034104107060003046d00381c900381c006c0c01e04003504044500d8500201190144d50710414 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 700241106 1250 700239856 700239863
    0x108060a08030a1106070c0b040f0203010603080408010e100b0f041a0d08030426030a02030702011404030c031101110d02071e230312010311030f0d0f0201050c04050306040f 76
    0x31010046111007051024007107040541d1214039040701e26031141e60501e18001e00326010171454500707180214501580c8950859045142c0143d2103502c0c0c00460702401403500058840c0800190005020b80705510411030402c141c0300751003280b02007101d180b090780c220110140e0320040d42d90015095141603031000d000500d10711521390810000c00c000c904039040c80c010a0790804800310800c4103001344a03041142121080d403a000011000f80c1d0251203600000d454000d100f039000c000100c115000b58000452102d50b60754503062403420380b80040201d21594011000030710401102d0303920003414020711428039064044503081802100f8154003d401c0054242c6141c1c05a040d0500e405a500400c1d1010314000c8000c0d42d50000d03c802a0249060114000c005c2c5502c2007000e408036860041520b4156035000310196122090b150010340b5010410a0504050080e1150300c42101d0f00b04c0d00c1c3c020101865002484180d03200c00c2c00c0d10b201c1c040e0b407003104d415070040760016001507042890107403240d10 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 700242356 1250 700241106 700241119
    0x3040e0f0702010b040c0c0201030e01090314030a2004030203100e06070e1f0305010e0711101a0a0915091b110a1401050f010806040f020108060a030602030f2a0306010806 75
    0x81980010140c6d84065006030120313130382200d20000d6582c1030080005100310b42c0024044c002c16680c00810751180001141c05460700400030070001ca81c0e940142c00a8195604419003c0707030040040146503129200c1203109204040f114481010350b40901c80c152807a04001d08200d40e01c00000360b42d5661080280707644658406508400e04020702090104411255030010b829814404101c1c01c41030040c0801c801e010004801044800c000108174042120400010458004402c1005d044018000400d5031082e0725204c0440d40301d41d56482464400c1000703c0341182240e0f926007180840d0340807200500ca400c0c20b5010160030340c0c007509455440d030f00750404441190307180c1c0c2c035642c08042016003040c10507512a414000010032a03001d41307024001c000702502180c01c2c5592081182c08050368001d042c425040001203172039a481800c0b0008541020065540386044030100520120842d540071610001e200c02c14610034078007500c8944c4020326003009180da10381e0f07801950380380c400400890340042c = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 700243606 1250 700242356 700242371
    0xb0f091501090806010b03160c080d0f0f050f04050706231308060103050304050405060f011b0206161103061b040b03060f0406030b04050601050114040302120c04090c0f05010203040e0f070201 84
    0x10300070031540f03000b0000d0404030313500d03403c0a1400080c07180644041c6000c00486d0494000441c000b40704890540000040000303204254841d80005037034200c9030344a035146400b04100e61031100c40300d51445a0320a0080d10815601c0c1c5406440c100c4103507144d054001c07482c000c001c180348030700002030400c4000611002d4200c2d03560040b0502e8903409803c102c2d066040801d04000e80c0c14140180c0381c10040807504960180080300009042c884c5401c0750555020b100c100d0130301503443d0001141e02400c0c14401c1c95807402d42c181000384503100d40c100792034001c5c42a81d000900e90b00e501d145107049449080440d17807806107094070f190b080b134101412240d40700010031480d41d4295118401c5000541c86104102e206140505045040082c142c0c09281800307040114590542e120904036000d41c0e0f4121030700c0800c0380c220300c0c4c001c0c0740410020003039420919245a410610078040004800c0b5100c1a659859098640c40126164015442140703241d0494030089030f02000e02407501607000209100004241 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 700244856 1250 700243606 700243619
    0x80f120903071a041a030708070f0c05010f0e061e040803040606150c061802060405060a090315060807060201090b071d09180c030c130c09030f050601090b0f09150109 73
    0x200c082e0503c4940c483c0000703080200d250b04054100c0e500540c0d1000904510300844094043c89004001c1740810490703501540d2020b010328103900ea4550040700812a018851911704010704040781681c020703100b540005001c0403007248042040614022070b90b2182d80b11540e07180c400f40c0000d00215180380e122070000c10220000340e030001401045a40c0c0400d400d0b03003403c280c0106c803483d481007603e190b840394107000541c0765042102c04450060360790b00e80e91140004202c03103070b01a40e04010100500190032518000c0540c01c65402e480601d800c1d11082940e50704145e080b20869a0001e242c032101200003081035003d000510311401c03841c0e52076100500a01e0006075901812605001c00034060748071500c281c9003c02914140d00d205600400700c0400303400005100404288a0040b659156031070750440d1407145c0220001980c1c0012202c00b0410b29261903034584409005110765140b03070901c815064038042c03a0880d80507a0140400d8081d4070b86440d0304900c084041030160510000840000d002c = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 700246106 1250 700244856 700244879
    0x5040c0b12060108010e0f040b07050f04080f070806070804060c050403120915090f0308181203030f06042306040b10171b0406080a06030b040b0f01080f12090307 71
    0x32140380749030000341490850000340600206800091240149408000045a002100e81d8125400c6040480d0a5440f50b10880e9a0f10668464207490b51010070001003801d8006948141e242d40ea000b505c52075500c0d043e001e82d451b44116450700000d00424080b501086169000c003c2000091a05c5c0d4a000d4986d2a405140902e2608200010700003041c104419230480e02000e0b81c409491400340c1d2150b241c0004010300060380e00001c0c1c80303a0700014074640e00f10b0400b40711015100e000b030f080070525281004400d450b0741080714083c0340c06000c0700000308545054810b045502c10314548901412a014081c1049084c1c01030a09400070340d6450320154035503c240706200340e40007c0d51108407038446050070311900790014203d618124203544110901d0000381c0300303a0301919254500700000e0341d03420b100c4070040d10340e03030f0700182490062506000c10b000c0c424041c6440356000d140d0702c0c0322690782d0380c03c825569030060070081003c0c1c00c0320b054a86d04805a0004000c0903100070121880151600240703a031 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 700247356 1250 700246106 700246117
    0x50a020318011b0f060e070b0912011d0a0507120201051207030605041b030f0b0d021504030b01060504240801060c0206091c021005090f090702100c0504140301020c0c0405040c0b 78
    0x484d030001c006207404101c501e000c0c2c1046e6407220400f0346003003858941800d52034040c1240e0b45124041c0590f0040301d9403c254040701c2c0e130f071424444890070340369a801426103c1050031030a40d41800303904804904028900032240403158180c6d1074500d44a80d00329410140000548801d00300343d00c8810019144d555402122880310f0000020b8440d08801100602180c02c0880308001a03410401041160360703079904031107080c44d015109060250701a42d0b603444540f0454000070030340c091110000c12400e0f8008050710a403640c216602007180ca0305030151600b0200485103000180900c030042c06554400d6407a9000c4600c0038145905002c90f281c00a5803032501400c42a040320840740c1308400790b1a0000085940300d8141c02e1032032074200c80c1c2001c00c0d40705034980d40d59409041c040c070200d0040c078400c00c038680c0f0070502c6a00c1001020401c0b00010034681c03062103680d04110003200200c8503480c061084a40b00340c80c8100412110203020107200152000820544860324090000141074070308100034003 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 700248606 1250 700247356 700247363
    0x2032a130921300c021f180b04020a08010212061804020306150d02061804050c070b0121120f020d030e060a1d03030a0605130204060807120e011a090106050a020318011b 74
    0x4e140d05400c19040764022055402801ca60600e481c04602c0f40050794a0b140007a0089407003860b40c9c1d61400403647c1c0900e0359010b21881e61001a20b250781008080c0c21a00403402101c200c00d5001e051000c0000b03c1d641a50040c0d410741101e404600c5503241400c0719444620090101424100190005007041c3c101c0000c204d90240d1245220010703140511074942d002490b01a46400d003c015198040c90000500518205120b404507032544d031090403100b0583d80d90f0000d05408160a1844000e0502040f4008d54015104001000300414060f010340045911150010b00da80c0d9900d800e103038040d1446060214a0040f80b00301d41d0001c0301c1c01e00c0218030038824031402085040c07501c024041c05180b10110000d0851060005100681d4010704840d040003052034850a52031503600e20301f00801c01149001041c1d032814424603200000c20702d200c450201c046030090000d0303076030f0744043d51035104034107034040144c2080040d24a0255000f044148210040c5003240100001041031324011807881e6065 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 700249856 1250 700248606 700248613
    0x603190606082e05190b13020d0b030c09151c062c0106050a03061e061202040b040606020a022e09090e0a02032a130921300c02 56
    0xc843d54000d800c80c0501150303264410811450122020314506024004d600c01caa0303280c0030f0074255070781c4802e06d030078000c0201c0c00210760b9110580d481000401040c10a14003900503c1c1400d903003850131100d910f1082c2da003d41c0841004004c0410070020350b44506c01035a20074800d0f240040425118818206940740703c00e204902c51a00c07034040b500c080807142025681ea81099400d001c0c0340c8030b084281d82182d44c0b143c4080340225504100b401845004a0028036051410000055481148800c603032682e00944007000802c0d100000e0100751482402040e001d80d002c12001401401c008940c698058140a001c0d0700b5107845000ba61079010480a402c00043c91111003440343c10028440e20000c064105d0042c50242c416a000c03d84920181c0e030803440c0c0074061420070203040300c0d14213080003141008040c0f0340c411880c40c0e0403200410100d0f200f0340e00c000307055140050b89007007031040c4d804070502601c8800c055040030a100110030580d14011001d40710400e505401500107000f580380c00c50564015 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 700251106 1250 700249856 700249903
    0x142a040909080901080c0702060f0a020f0a0602030a06050405101202130f06060801170607030b0424030308060607080304110f0d0f03031b0917030c030301140315060319060608 77
    0x41134282e011b010424a140d04009080c01655414200c801c4014002d075100d40727070b0540c0f28082e82000443d500244860290b08241410041c0907401141704035032014042050544400521046860480301d51080c825000c4090080b03601a45481c1c105c10702c020b0030038002034401d890032000e90701d00503188500c1e03640315641800400e810100080c00340c1a04424030041e90000c06415640341c40c0a8203110a1507078a45044c000d40d1a1604603403001d4010b441f00c0310007911403000354110b0085910059002420320800302c1e00301e15110080f600700707a40103e40b082c01c1d91240e0300d6050b0100f050071011903000d1041e64080030542c5030380000c0c00c0d4490068042c903c8640355428003405a6103005601c5210f121554031661005400c0070540381501c0119040304589400c40f580d80d45944034013102c40345644004800012400720a144940308a48281e0540751085400003520f080640d0075100198140c00241c04c108415044190309882680a071034041481e40c0d403044030904013500c00c114000d528048400 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 700252356 1250 700251106 700251109
    0x21e07060f0e1506060415050c060132011b080d0507110a14122b050c0406270b0c070e040b0f040c1505070204142a0409090809 56
    0x68111007400c8800c10b0040481c030140b600d0300c681510000c1e21007441420080361541e10742c0d406840103042c525000c0030015092110250040d0842c805548461080900105040646d41c8040c030000300d030812080f1244032103e901c03142c203189121069040140c244c4151224010740e00300120f0090250070841c0d5140640c171950b200f80da0009040800b8010341580f16444808001401c0030404c3c0c100988030b480c2072f01c0207040d60400042d140c0d030102024002c18650803480d200c40c13100e18800b0600d60405081b0962541940c01d40703400729400c0035501005d02c02085821300034882d82d040020244141802105205280c4100000d640c0084100303100110b50031801c07000c1085414042c0070902005440c0f851305645640c440170006003103504013203c190115042001c00d10a101c00f03000010201080e11400c0000100b82c0c3d001140e09a00c50b03400e02002541e8060f000035943d0046400182c0703202c01102c4034810b0448114001c000b6008010100400079000d96544103138840b070f5215400d41a82d41c1507820 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 700253606 1250 700252356 700252361
    0x3804030b070f110c1e0603070e120607210b0d051b0906090c07032a031d090402041109060d06031103031606050709080a1a0a090203150901021e0706 65
    0x50b0144240a035002660040364000550381c3c0c445902118055a20388280e101c10169001510138590000000710500100031313082021140030540985a58540a4001d44080d60300c84003074030041c0216001c0d4a05043e8811440c0c2b180030f4601410b030b0045000d4503040c0104030080f80800050310386400c8126211001c0b030030304078560b05110003140c800d0307080d0030301c0e500080c4060380c0640300c1c1c3c0c046000010721404141c0070380d100440c0c2c640b00c4500e2094600d05140500c001c40141d60040740001c484079011402038003401107034154068050413107801d0b0f9071503609000c010701c0d020342d4624040106010b10001542c0b2000180207080b000300012800360300d10701c1e1440c402c000700e642091180e0002d100c0b5041706401c21100300c0d80190004000318494458910955884801d5001341c80703640100003200302803158007583e01513807107030158200c2100e540e1b00c100380088074a0071000a5050f00324001000204071761548054200072000001071034151601e02074a8a5441c101311482a030f0000326210f0709010316403 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 700254856 1250 700253606 700253627
    0x30f120906050901140a1103040f080d17060919020c07030c0602010b011209080f0c0102190306050607170c06071808030403020a12030306051203041403073804030b07 73
    0x342042400c01c8034510018084da46040807580b201a00491221b818521504030a4000101282505c0c0d07141c2d2a90110381700d0318020701130982948103003540c0c01800c51241c09941d041c020101e0703e450300c0d903c950301004415800074012522140c0150f11b42d80010f4501c0c4002e041d42000c450080043c1c900c2d510301180384040310761180b81503903d45081c1d62032690300311040e1280c01111003030003e49944180742810303084c0110850000906004910b400c050b5205500230840450b1100441d00803c20148044066452602450b43c0040703003030080000149000715850140e034001d07807006007014600ca86451600a084800303500182d00c0e001c0100b003074850740e00075002030000d0101031490541150041100c1200620030b0320408038080c540f0720181031095000d10050903000b8001d44032080354003142130fa41d412901610001c01d02c2e00303a9002e0300340b60000c0c0c0403044451034060b4074a6540b44150007001042c0d18100c00b0202203030401200e12031804c1e013000744090340c4510400b0356136082c45040100801400c = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 700256106 1250 700254856 700254869
    0x806040501030506060112020d060f03031d03100b0a1502060f0108010b012c03060a0204181803081e0403050a11010504051b19121101180e040309030f1209 68
    0xc1100510103d440451600c2d408142801d20600007115202100001e00c50040d101c00d01514124001c10b00d034070701c861140d0840e80a0303664000d41e040341c5042c007003e03005000d115070b5041c3d0000110050600807070b0080e81c0c0c1d0050003040c00c4141d0365500c180d4248490005240d100503006a03040100324070140c020302d40940f034079070000c00a5411080c0042c00c41c4000d502e08100d14260840da160180c1c0e00790015400310b80e0041c1c06c2c0c03011400e2860480020790090f001d0f0040b0191446040b21200d0030724420050389600c00f2803194441c0741e581d1003e85984001600010b946521510600c5040700d441503954004d912a0341e42994a041d03140008102d0008405243c10f00d03410202440007080c00001c400d001400441c210341c81c8410503400003030500058861682c00d41c0664200003840b01d6150110028480c003c1c040100c82e40e20400c0111707010428000042c251181e5a2020700c01c030b0400100e16a03000c4d1107802c14203031954890301c1f000000391040d42d00b2200d28141c41b1400c401f9680c0200b40e140207000 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 700257356 1250 700256106 700256111
    0x10207210906050904230601030b041e09080f0708120f070c03030c112b020c210a0f121409060a05090301020403080a081b1206091302030106090606080604 68
    0x96039600801c0d002403441001c0800a01050540e2556945d07405850031103480032403440c01a510b402d10b441c16202c103c8080d070100e0700d044000801821301b070013443c5040740b001041e1501030342c880e500d10004050003207081c1c880b00c10070710109881d041e01074003c0070b1090189071b000380c80e8500d40703010018903280146660a6a9801c1060159094018003038440c0c6551505000c41c124075412741c02c40b020600c844d40301e5900d10510810801c4404000c081c4d0394481c0503541e901480c0f00141c6c1040e40d0340c2c1111030a46421240e0a40004566103880000c07143c9101380360190b88496420f41c40720046000440d10668210503a040c60710109d80d009404041da5000300b130101c504051184001912500900c3c09060a100001030410f80c40c1d035080d811103002c0c0d907000031819240c0892600042001400725141e0281d4124010240b8100c02d0308016a0220148654188440c0d85c400083c000e1220020300f85418111045841da80141d800303014101c044c01c1d04c5c01000401c40e14050703000700b150720003415482c0581d2 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 700258606 1250 700257356 700257413
    0x9051920090c160611040501090f051c05030f13090b0414160908030f03070f02030310090c051c0e010c08090c040507051215040507021603110a0302060705010207 71
    0x126076810040c0d0200c1548026a1036207a82842003580a400d601d00600e800e140c00e01340390000c40004080c00659400ba03032188007a94a86100c40807440281c0140c0394408a40842030385800c400c00c40d00d005107481181034a0604c0c10540748203009401c48821021407105280c0180900740080c07049944420f81110709001072090800c1c00f000f000c070054100001c000030f0203208401c0e28040c1280c00001c01c07500040380d5070b580150501c9452078205844501c00181c00400650b0400c2c40001680c0c003030303c4800924443c032031502c1c003c040100300ca40802c405000c804d21031400c0b4003440003000b07140041000f0005c102d44580260040c21124007840c1c02c01403040034424880403035400103240c0054041900c002a140c3c0b81c240b0151000d029280002801c0b403103040800004600c0c45a05c0c50080c80c05507403d1049480300300042e6102d1041e0540c44a1000070a2020070110b1a070414000c00341201800304040140c036a0085402c50380b1402d07080d1800d0f034000074104100507400442103556500c6081c40382d40381 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 700259856 1250 700258606 700258609
    0x90b040e0612150f13020901030602090405090a050303010b0706180309030201020106080a0b0609102616081b0105090604030b090712080d02030406230708010e1b03090109051920 78
    0x8400504074054074101c04000510300c1070289104001176800070070141c21903039689081c0d03010b50b00107c0c5080c000c07407d040108629000c000740c900c400582c0000a0750a44e820106001c115420880003036441c15105d00155285030110b40340100c0082c000c1d641e034440d1609500000e270035a0030b29488030800b40d02940741400481d81042c1c1494001000300c0d5030003181d80b00d911032584844180d0f046546031341e4941c81c603051542850b4404059025100b815140101d0010103207482c10546441412115044050002035101703a481107101203200504202c4d040000850100b04150460b81080350400341d014240300c9140410040b290040040700045001c00b2030950f0303030510398054201030716551b0b40c012001c0740c02c0191a420070084150038503901859444860201d0000020582d0300001064106002140071004030a4103403241106480c00c4a140030f64020580540d480100101425580d8403000d0b80001c0c014411200c2405050f5100c1d01010154182240044612000402e09240034a106c035804e = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 700261106 1250 700259856 700259893
    0x51c09061d1b2d0301050c0711010806181305191a0c07030f0c020414150906010e150c010204060203130b04060c060504212007050a15090b040e0612 65
    0x1040c0c2c42000f9562811041c20701030301061200c1c0b04640c19401c0c541000502c24601003c0c204c0103000c0c0d82030885d03507114000155400442a070f06180c0200804580d01100c0c01032007030943e006140011464040e01c001c1d200d0a0a0020350000c05503007080907810b0406001000d0181d00519a4802c520081403d040c8061307a401d100e240780080610012034440300c21079009072050181d11350054014000044440a10316032100c00f110303003440301d0000d250f40b0340c0d403420500383c42440350006865000303010109800300000003848003600c0000103020801b20251b5402030005e0801801203170021034450549080108281031a40c018414103601480100140d40d401070a80c294560400b20000d015196801c0608003d6440c041e09a070b500c0c011901d00a00c20f900c254054102d45002082c3c44108000801c1c581c0c845c0060322841d54401180c03201404514000032400c0c481280070305110310420ba889982d074415810030303030107400011040310400c51242460140406610b040c000075009140109005050 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 700262356 1250 700261106 700261129
    0x80c07170a140f010207060f05070302030402013e0d0e0102060f0a050a1d06010e010f030f080919030f0c06030c020318010201020f041e05040203010303051c09061d1b 73
    0x8505031150251403080c8000c6000f011210700a554440e10741c281034010b483c18aa0900c0c0b01481c220000e00018401d10030f1700d0040394145e4818940c3d0301c04010042080c10580d1000e290314a24503120600441d01e508030288600340340f405003045a03074079a0081e200310181c000441c15034221314100800d04040c03101e500d500014280c0d0001e010703243c0c101108001c0040ca0500d001858068528051003640000c00d11f040320960b0603c603040f03a03210000b00c84034100c3d510008140c10100d03450840024106406001441d4000e0041d845039010112030341c140e0345103370f031007038403082c00904009060000101c80312000e41668201404400c034580e00080d0740c0d11a0031016516040341140008080e071003901283d0304c000404410036240c0f5140c0c070402002240c107049c4c1c0000b042c519040001d643c1400d00a40e412a90581c8915092a02ca02101140180c246441c072078201d668520900010b00e2500c00d181d4560855402020000c11002c50603161216902c00d040c00702d41c00861302105980c07010396008 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 700263606 1250 700262356 700262363
    0x10605030109120c03090f0e04140313031e020a030b071d0616022206091808300f090d0306050a120204152709020105030103140a0b04080c07170a 64
    0x140c040c0c13443c20100c0d03014000d0b40100034421244c0f04000307058855907500c00d004a02406040b0313265210807000c2582c07885440c61078211013040090810200d1036007aa079070400704a2860044400388158005003505140e90001c45982003e4400d2024142d44a0740c14218000700d0907140c1701c004c90f5900014014054000201d010101c030140c0d010843d00c3c3c0301c808880240c0156141352117082038200d0840a85060700406002e10314010a0075020f28000f0042141035400c4440325140c035000400081d504428600301038600c3c9055645500c1b184402c801c814464040504a42c5090a080d20582c3c142002c40030030000301410f040042c003440c1da80c61140e80403a807110f0b0410f4699903c40c40820098840e80c810450a0b550050300010502d4442c801d0f80640c01d0121000012600f99030f20701c20840e103c8080c081d002440c140014400140c4110001e00c1c0039203400700f02c134080743c0b0306e41d240d40102c40100c500b11184000441c070801d901104100b954007603c00714030029812942e50130382c59a80d644004020303 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 700264856 1250 700263606 700263617
    0x1e0c030209041110050901020111040f061119031206050103021207050c150411010f0206040510050406021c0f0e0d0c02040203060a12030c03140301080d0f0519080901060503010912 79
    0x40c1004980030001d040c000300034003641d00c14820135001902517042440a14059401c24007480b0000c040f60701140c06940c0301c00040d107111401d202c0103c40041c10034000700045e114041c42039460107888010401c0c124826500c10120784100700007401903072170581c04281071500501c04c41000407007030704405a2140715803505d1a1940007a44049241c2000310510566a00c0e1030320a2009000c040112344414042c20307200c2c56424010050200e030361303000498014041d03820110280040e1041d40c1c00c40d03034015006910160401951507055111468102e410060300340d95080d03281c41403102801007007004161200030300000e0899080107070084590001c000e114550001c0010001e07078480b135507903000d0600031280c0b0408a86a24010300541032a10054000c100a48150100106110100ca042e511a040034110004c40604182d6070340180e00c4090080c8a401c1c07000c48005203400c0c1c4031038581c0c8100e80d62a81c1504003982080e085400e039800050081c0d060112400c08241706c8012603100c81d2940c0b601 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 700266106 1250 700264856 700264861
    0x405030c04051017161d012106020408030306040c110a060902151207171005010813081804140402060703050f0f0d09020906010804050606060a02030904060b04031e0c030209 76
    0xc00e40c08039190003d80e20245420310104150320001400510210321005e004c0400f901c86aaa01401000e6079603810141d4488005008131000d41c0401c481050380741d030f00202c20f250740d03039180403c2c3e80154100088543c0b01104006003450076015562402c602410b1040c2d54141c139010444e00e0304440d10317014005a40754040c480454641b0042d8000541030364606a4580c0d4443c42401130491040ea600780c0001e82c007000394640600503500090141e5500c0c80c00521140c60700005580c2800c0c001c2c80131120550340e0b425200843c014100414000000404007040c2c00c1100b8204012038020102c0612601c0c142c0d41044010b850300e40c2204d0b4441d4041c1080da45508015295072800e10401a12991078500481c4400d61826141c00800703c2d90720882300d8001035540c8400460390f540f012030f03010b02664056808951982804801000d840e080c5206032858006070101103000c2c1d41f00e035400301c0c00f9800b0009080050022000800114425200e81b003102c98568bd164030b15814898000030307104280d00e001 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 700267356 1250 700266106 700266121
    0x60507170c0a0c140c15030c0301060f0c050a050609190b0a0902120d02030d0524130213080309101d01120207051e0d090305190201020f06090106030c0b0405030c0405 73
    0x5000c81069880030307030a004c04c40080100c6445035845092540220a000514102030b040481900d00c80c08401d0f400600310303803030940120b80242071024040d040c00148104240810300c10710440220b075020310000c0c1a035082100380d4501d0201c031400303841d0003162505900000110711703030000340c1c201400980200c1c103203626000042d80d0401c10700ba03042031889441000c0f649141c001c0f02400d03922101a00812140d07481d440c0c14030342e8586115010385070343e4402d56020a1490003214591401d070700c051006081280c0140c030740040ca00b60760404207599101041c00c13042450180013030040c2255500d0603150300d0301e58440058800001d502a281480401d0243c802c3c510040e41c162126503802c40200d1340310b0450030034104c64040341102051042d00030350071064500340c010303210003003140c1c0e0082c02080c48402c40c1414180301c2900c2c020483c1140103050688a05081c20458980180e0000300001044c0d40765107415080300300706074800e5100b50401c0c4000c0203103990103c0c1b10302c1c56003020f440214070b90f0b0712181d = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 700268606 1250 700267356 700267367
    0x90f010905060a021c0c0302030a080a020f0a0203090301050601020106030b130807082704020306031504020f032a04140f040302070918020a080c0609150408030313060507170c0a 78
    0x1000150458000b060349482c00e44d0000703503405030301d0100c581c100c80745594150485142e00c103120b01a0140c0e0003000500c54a0b84904940f69120b5100d100050501c1c0300c59105043c0d80d4020750b03003500160710102d13400310285001c1c4502c82d0011024002081414a035640d072410284000b0701c403541e074200c4c03480c0c0b0f9428006d1140c1240e17400da81c400442076941d18050002d400c421a0190407003a000c1c2c10010544103400d05100b10307800b4580040040a0310165a800d0740300494008000326003002245107c0ca0031078030100b044522480078a0291150b0201a40e04445100081c101081c45181040001c4034944104070792142c00c0305c201a010006544e172805d040c3e1505115a0041894901c1c180542d000c404411400380b0099100300c074040302c042d50345e00a05a50328441442c090b03001b01c0c104984003076441e1070300c1c50854000c00184600d0410741c0c1e0b03000c50350860300100d03100b600c008510b417a2041045003510569901c11203d0808081c20f1200340007404d00054014514260b401000503034107605d40c010b9 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 700269856 1250 700268606 700268609
    0xc091e07050d050f010e1308030c0c0a0f290705070f1a010315060602010608032a060a060302040e0f0c0111070b030c04060e03030304030c030804060b041a150906090f0109 75
    0x112410f0100d0304198081a0300d400d802d10a0303410a44507000481c00c43e41e00d11325940512504012150b0840d141c00d10325284d1a0301400c81081c540c45280320420000d000408045512070094001c2c40709209000c1d4400082002c500310440c00720610781c02c1112441e00310080d10921600601540380307080c41850300f0195a04141c440d10b001d0302d9202d00020400c0841036030701280f821444000e0007040c0ea1400140c0c2a0f500a000300300e0030340c1050180c01e50001c10407a8940b8001521280c25015900d00c4801500700a010313030310034000e2501c0d100e040c025410903000c1d206019400400400c400a010540311f80c5503005c000e002410040404410f0711014010000f410203040c4403405213980f406d0181c1c10400651140c401c00011400c0780c038100d8081d140c00701c180c9110b290152503a2102c0c016954084940e8100180201c550176030340c11180c400c0707444911900d0200c1e52950802e080c408601c50411000c40c024034812400400c0400514601d51103550030784104450543e00d000007400c0c03040059806031400d = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 700271106 1250 700269856 700269877
    0x1e09070b0d090809030a0f05010c05040305062e0e040606050d030e0f03010f060801150602060f0103080c101b03290f060d05070504060e03070f031e1401020403050c091e0705 76
    0x6c00c50b000040c00705444800110078450340082100710510744003510103004030700c400351564020100048010726400c8000318082650110300da00460b4080081d04800305507048100382182010401040020502ca80d00140c50100ca1041c0d114800380c0d002441a603030078410a024900d1181d10030420b4809401040303403a6582c0c141841101c2d00d6002140c02024500d001420724103205000140c1140041400c0707000781710100311030295070300f55103820203a0b9100b0f40c100300072480740800c68910348855105444840d0040849840e41c050a80c070010309031400f40030301586044c034551440070100340500340700b100c5100c1601e080c2c2211513804009001030107070070b085082c22420322042007100c41d40800200151506921018418a41c01c014107035100983e00880c1c4a0071014101440030482004180f0905110744030003075000241a9079481c01c0c07100783d0580380c402c1da402250610420205120300c03160060241c80000c21441d02d03403035514152041c008423400300310b51840401c181c0c6204401301c6030103401 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 700272356 1250 700271106 700271113
    0x7050a0909061409130305091c17040806150a06110106030f0b0108100608060c0c0c1002101d0a0f020a210201090902090108070806181e09070b0d09080903 68
    0x6070303811034020f90641404000e100b4441800000c1c1ca80700404040f030006905940c902d07040c03034120414004240c8480c0c0c8900c001201108040f8001048000c90303544046095010f552103d140902c4245003807400b44c10302030034040c146049603807030310740c01c0e240c40403036201c2c2c50030a0720829885101401007055030801703081060031160100070b10040c0b21006040300c140400300c0300c07540340741d8505100310f0b60607014403942074200501140b0000381641c00b400c0b4940b142000e42d42500c01c2100040c00c0c000007450202c000d81c01403071506090341d20724421502809460240000711950310b92207251940412540202566000020a410341d25038034100d4000c0d250011590b8480303910074242481d8030030084800c90008844040101e13110983d4001d480304c444041e1252a0143c840a0066640344801401290080701918900e403180030044e01043c050300118a0503101c00001603100c3d049010010407040302e0317a009000802000c04414201c60800c0602c5500117010442031419241c2c1d4490040020f0f818031 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 700273606 1250 700272356 700272359
    0x606090a092910020703020d1e0b0907090b010903080a0e1003060e07090b03150f0303070807140703030206010b0d021b030306040c0306050f010305250216050603040b07050a090906 79
    0x1255241c0c242c50b0311421400c84000060301d008000d42c0d0400d080030b00c001178019180800050801e4814842050f03c02d070014490001416071007040d0903400350085d150f542c1d141f01407040903a01403000300083c003610341301400b1152142e80040c001c200d10384402080c85500044001c00745110368456a80c0c200004c2800240144960009010b05041d01031203900404a90200f03484900418280c0d00319120064040d045641e0300c02100680a141e45143c0d400030a0840c0b404500d990900080c10b44601c1042c0d01611400c5900700303644051440f00c2055010b51241c54288042500042c2a80c1140d150303807169076560082400140290003488800f121f070300d0020b02d60110342c6c84040040d5120b0a400d940801c80d01045103400c03030548140b80315203500020741c61620b001c154420342009030b01c814220403015407002c81001c09183c0440a192450058100945503071041154000e038000500d0b04036130603820b5003883e498100708000060802c4c4144100001c0321041e445c081c44680000b400350b148104a02d6 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 700274856 1250 700273606 700273631
    0x3040212010c1115070f03152c0f1b0d110d021210060e100507080d0209090703020a020706030914060108010c14040e040201180314330606090a09 64
    0x15103082c00f4a01c66030103880400384003642c1c01c68845100340c1c41a074450a0402c0369081c00e400614484c00c03030748000030308008086000c0e598010300003004182d012a03c070b045008002c0d40c280d80791026140140050704481880f40402c1036501c00d180700086e103598565589111031801d4000d26141c668602281d0000c40c801e05503142a9001d0f140e85441040304000b10b580e140c20407003007090b60f4054207001c50f02951020a0a04115509030214015030400e58a8201203803901d5015800c50f185800507039030002086241810013020994001069041c15414101d004002945039019405000308056a40035541d09020300c003030340076151184150a070b550302e5031581c07121400b030075000d50310740089034120345409810503601c0d00311011190900d03500c1505072259401103d440304218100007055411110100204402040c9802d000c004500200106040a182d41c607a007620086064040f14910315a902c0410030354084591042044034a940e6445401e00040c050301e10036042110131516041042002 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 700276106 1250 700274856 700274867
    0xa0e030706110315010c030c0312020c060c04060f0228030c0209160905030706090311040623100507020603070c0312064502090328030809010b1503040212010c 70
    0x242c04810b1300b240030030081001500d01500641000740064044019840402c0c818400c01144800e02030001d403801e103001c0368180c900003090f42d503120242400034041048135000b240b00e035008001400036114900525070603000d41c4800403090015000e20f50000d40415104180740d8404560040c0210b0709410242503000d880c4905540c0d08012445441000c104c910b4006019001c5400f80d55a01d003000e400d550f40c40c41507540804901e030f003242c2c0300c80700860300c1c907103405100864070440c00c00c08a00c0110081001003100000940c42e05011040201c2d9000d03842d6802140d038410000e04005000b980c040c0f40403100303a1215102c801d400703446d1102c041048600128240c1e1200304000448100442044003804c180058660855160946030081940c0150341d802070604101c000f01614500080d4200c095500440c04081220b00915003090008140c0c014141c04d4110303246a008211aa100c2808503a4880c44d40d10418500d40c00407002a046507540101801c1d020b440308001d00c20a1b1484501404 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 700277356 1250 700276106 700276111
    0x903162a0e13080702090a0b120712380411011803030c0201020a020603090102070b011a090d05030c01050109020306040e12180a0305011d060f040b0c030403051e1b060105090a0e0307061103 83
    0xf1849d1011109a80c01000103401e00940380164513031381c065030490b0b5901003550400359040580100c1d20f0305100400465290000518404000150882c5803500d880d083d9645801f2180f418000742440a41c0c00d0951041c60030296581414030089040309400140e14007052110029407080d000010000c001c0010740142c072a0a101d0a0361015998035500c10480440052401003040d8800740050b81d000d14240d500e201c051030184081d070f85050b204ca88440d0035034009030821030165400105024032402d2a00c036408428030100c020b803050b04420400446070740715005001000d0710a200007919266100c50b0044001c503071110007002509524010303025502e515640e00c4e1a14040d54000410741c80c440129640300da980094100380d00d0ba242865060f45400c00307042034041080034442d00726058081450404040c260303043c81519010700c00d2071001b10700924a40c21080c1c6d0410b0004000380e460740c2051030703088a0f00300000b1462070160b10ba13803482c500809401500302400e2143c0d050406a520f0007c50 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 700278606 1250 700277356 700277359
    0x3050705131103130807050604060b0f0303160b0705090d0c0905010b04030f060f0b0904060605090901110d05070309120801050a0e16080903162a0e13080702090a0b 72
    0xe007a0351a4400100c201c1d00621826040e00c14104002895129011003e80a0a10490070740381004100c1d101d00d89840300c100c0d030803030341c4954400b02c2c840285800949107450440c110004d40c9043d0080440e140b5031003131150018840203030100410426070091042e5245110090005213802c0454205140c96180a03c03940b119030386003500226060011204641c252038008404407401030042e0340c0c280040410031520b51070180c2c0c0384c50011042d80e80300f44140c0181c1c0030300c9010070454100420808880c402401d1800c940c0e240c284040300103000c45043d0b030821503451000050580e103410007035002c0c1190005c010214666000c48144160304844031034107951060ba452824036480d924454042e203429100c90010380c80010324a0300281c460041d4991091903101130701d0030000d0389040740d0315846a03484215040e01080341d0207400740004924901039101c0315502d07000c0862400440c9001280c0c05403601c000201544c2c1c0c000248848401151002e643c06442d02405142110010000b02000300819 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 700279856 1250 700278606 700278619
    0xc081005100f0b0a081e04080307020111090f01030e03042c090313030807260a031b0801030b070c05030d09060b0117060112060f1202101b030804061503050705 70
    0xb2412008405003030080da80394108852801c440c102e81035818450040400054a000120806880341740c203a2880c0560b2084030b41c2d9031681040d241c0603003500d4001117400c0a1020a0101814590b1480c6071006241402c1c00c000035546241e4240604510031a000004c0d0a400f02080300001c5030ba03040c008080401c402c045850548030f500944d40c5920400d0315200203042e21000038401310b0b21840041c5207540c4251400304500740c19400051001920340d03080c071010303140420101c088980600504403800c0c40300c000800e0900c40444080c00540041c040a00968010000280da0500400c594072016170000d044a4842c08144008005000980c01c1225807a0612910000b154018490400c184005c0301c08151a50382d10001100c00341d0a44498207502515101c0025041c1c80d02040000079242500d030107650140f20703006201418440004903c200300108039071a0620700c0312040c4240241c1c0c5844c2044442c1c0311404c02001412054088100c000c200d15800004c00c0700004002088070000d6890 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 700281106 1250 700279856 700279859
    0x40b010503191a0603010b0d03090807050d0203030415020312040606240905011110020310090612050a1e0614090d05090307050f0111030a0512060a120b040c08100510 73
    0x10412030402c10802441d0030007010703007a030400e041c0300c502e1a8008805800095070038032120004031009420f4030305078003042d45c0e118103000c812000e0007454041c0c607064415100c3c002d280c0d0701080d980d114502c41c8001c2c02c5803207200440d02610034003c4403485140189101c42504060030018014902032160145030000c4c402c140607405440b240d400070a0f00c86445000030607213480015100c1401500380c1d20868040c03071340ea8842039801440514010341900003c400614104901d0508403983ca402c5040610f42e151354000c0090800242418000c1d40110581d60303200055108010380410820000c004a061a500c000e00c001800d0003e8400c203003000c1101c2664862500a646511400e4a60343d09600104814000350a040541000c0e03510107140802e6410041c007103070340c2503800841212000480000f030010340031344044e80050b0030600849600303001500d0007141e1214008403100003044100c5c1d5800080501030542000d6004002403410364445401000490000346400c503508580c45134101030 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 700282356 1250 700281106 700281133
    0x7050f040b06030f0402060906070b0a0e120403030c0c0b03011203021501080a020603040c0b0f0a090f051e1f0e01091a0a111603060b0f01030911040b030f0105040b010503 75
    0x851808140c00b07806180740d5291185000c0c10503d0040043e82c000008001141241e00c48c0001070854900a100c00c0d1050700300107500078241c1d0300003010318445901c02c8100d44118400e400c11542142d5150429003030b91340ca1451301c041c60002c541c0c00074602e25400301c000203031290540c040344a40e51007035003591180c1c2106419410003c8003805210b02e507a105010400c01410500d000b150000d0295010f86903269035801c1c031500707a0f03000d2003034035122000c04224039800c0307074000f08280f015181042a015010b030504000c512842c140408600c07001c5000138164015889411440c04010300c42c0d400403150340b02040707014001d80c0b590000c050004014660020703041d0074510b60000c007400130310a0b6a2900315800011240c0301b1651144043d1400344e040208164242100d1000056220f0040882d015000204204400c20071418440c141424201104006103072000305031087c1d401260300007030036103015020030728001481e039a1403119881d12090209001000150360304071002181101c80807a500300707 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 700283606 1250 700282356 700282361
    0x608130f110315090c061c05040f150207050309010807050d0c0504210203030f07150915230109020f0d0f09060c021b1e100c0311010902030a0f0f080c07050f04 70
    0x1582c4d0a015044a840c100303651a200001f04045524a0040c500d201181400307102120002d4030219442e00548800384100208039590320410414201c0c1107007441455104d5a40b60711681071a64100300061000508680c010030030303148184103030841040854031179035020304207130320902680c40410240b00340028100c182c400c04440003580600034505140c0400380b00085600840c008448150740e00da000d1102c51094803c900c03500307006241c800c050804c01710031b82e02144c00714014080001140003e80f5401c60109421030704543c0d444200684e00d03103201c0c005075070f140112a9400440717801e120380d52942c20303029000312000c0c0b80114070800c80794804c00c006030703500c41c1c00c4104040c1080c00707040424450301d0031140c07130540000c00320700c00d031201001100000c610102000040c40401c20010041c414580d111201d0280702070200020000d4080340d800083d07540f0301d05000142164040e44100c81049008894029420360040e0400d4544800b07800340d80c0c40c0ca603640107032402150f080f80114598989030 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 700284856 1250 700283606 700283611
    0x1050a080a06021809090309040f0204050d020f030106210615051e0d06060303080708090105011d270f0c010306050a050906031203070e1206010506040608130f110315 73
    0x90000744240c444594410010390410354800911880d0110007039510f445d54455a4811030901000d90b5407900500100304c111020074590504543c0f060000b84000c0c1c40741124000d03001c0d0100c5002e0000852203000901500068002d0328524014441610b1000d420495455496106540c2400003444000040101030b140c1c0c03044a42c00001032950310b04285101410b441008006041d910a406285d2100c0d0103503070369584200c0016024404110005510080403034000c02c0b07503402809154541003840020100740081000c4004003030f40802c0301c120110351461214040c90884001c0d0305440034140d03450342c0c54011800703800d00903013192002940c0b107442100c05442005125815242c1003e00303002081c0b80c010007a03070b0107100b030b1102d401c00046110043c61040c90725070b40306005a90306809011004d0022007141c045a800700005000595407c0c0954041e034906180c03100e2107558910095807182c08c1e000e00036190721180300b85c50707040c44048104403001e01c1013a8204e5540e414500807000310407508 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 700286106 1250 700284856 700284869
    0x20109050411030f07022b120608030301090209010e100f08250f020102130f05030c01030204080a080a14070503041706191a0901080c040e0a0c090504141f0501050a 72
    0x30000284c902d030b21140882d40145d000d20480b0412071030480d1980c01e44031620384096016840703104002d80d8550180d41d401501c9041c46082c00700320700d414a8503035a40010b0207007000d2150041642069a4030600548030300500c0141680040d40001c076004c0c0403051541858400940740000194903105581d00c0c0d9000780129401c0010b0854040c0001c56001c000c004900c400c55400b005413040041400b142d00c00a040207006d400da04a150008251404541c280080d0502d030043c0030801180c280851120038481e004040d00350394224a0000300c48941941d98022200d00c3c01041e001d05011001024005503030200c1d07001c130a07204c800400560b440f10100d44001d111004202c00010016094006e0740e4130400131b43d112014610701d00000354111200b604a20250390000813010034618081c010301044034281e80250100c0d10894480f109012214003c0c81c1d40c99443e507000c28100170900c601081e0900313414040c0c41503400c2c0d4030f403110210450622f8500d00a0b0400001258624254070502d003210303031 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 700287356 1250 700286106 700286141
    0x3020601060507230d09080a0b151903050a1e1509030909180b0105060405130b0a03141c0806030d031104270501120f1e1401090201090504 61
    0x6407600440340e95022842c111184030314142d00302448803c85602061200b042c40141803454004031006040c050a036225000d2980f01c203c502c03001c10040400c0d15081100d81c5030342520000e05c240450303a1285103441c00d02c01d4000b051000001c1c41b81c04180802e401d40300311295450011004102003840c0e00054001e0495010b00441b076043c81c401d03901c240d03040f0f4420300b0041c040c160b5984001089552241c041c0040c40c108090510401481c014071902400d02112030b24185030a100101c2c5540201e2420f45020030354030303080200c0750380d24410300d2001154010620040c204525090b0303034543d6002500c02e01e0384050513004441d564010b00190340314050241c000c1c00d440c0d51040c0100c029085081c031604581d42c0402012030b030785502c0300140404281ea050025480840107140718100c5074142e201d100c1c6148406058000112540c0010308000c0c1c218401301010300010060910514110728014100d25640340f444104007010741058010a0013602c13140d0340143e030b580a12060f5041a400f00121a2 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 700288606 1250 700287356 700287359
    0x3010e010611070e010b0310380301060f05070309080106030c09200906070606030210030516180509091501090b1201051e0408070501050f01050a050d0b160e04090804170a03020601 79
    0x389450095940123101408d1290816540c540b40c0b00e500007000d60004050404c03181000d100040c850440b1a5074206030070140c5550b03d400c20040080199200c01001c0250003d44102414400c0c1d4103a006880310100800c402c554a10700529140d20303601c1600d80c002c1c10300c0380ca80d00d82d240300405140c001d03001c440d40f5840d020340a01001041d51205204440656841d0404409600d1790342c01503090050507100050b5505108800145a50010311000304000515142c003090098445000088074026100050140c441c2110141840c2a10f909158900d02c0100000740402c03a5400200c1031303000a650483c00b041c0201083c07070a0b1303031007241c8087c00c03c1d0210480070391080c05a66847c0e4410b01032580a42000b00681d5114203444040c2d90715880c0d040114014400340c0740c00b59881e0018901291980070a4900d41e03581c0c0d0014030000e20491a0111409001d46258000c914122864200034030400540303c2e540380200c0940c01500031403020301e51704001041814800190000004d8040c1c00504981c1e = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 700289856 1250 700288606 700288619
    0x50304020a05120703080c010c03051b1603090b0307020706030c0203040e130507180e07050909150a020d090303051b1c09080f0c0f0c0a06170405030c0303010e010611070e01 76
    0x4003d8001903501c2032088460002c0800d5243d0301404000e5079100011615070410480102520b0b005808100410762800d203041a00310810106c54903038860154440101546060580f0040615404003080f45000030400c0f00550717002c070b20641a1246905c003081098000403049030341e40030b01c0c085c0c41c5221041e01c000c03d40d00000d0a2a008071240f0642c00c5840050b241d014407034a96524262440045459000003c0d034207000b400550064203003030310105403514001071030a07610065003100600384141000814501d00300364044071566040d10f1030a02000a05141c000c1c01071038215180d1812038050050f0240130b0381c080c800c0b285641000c2003800a0a4480f084490051056200854031100b081100f4101e001b1070b600a80503641944010300882060401d4160030020380d9003519100b00c2004006200c3d59402c04e000c0940080d204d0074410056403035140007441e5102c0c500000c10b092001100002e0107010f1044494162400390b81c403000c04c0c3c4880c1c0d800c079a80b40150f001e6108580036560062008 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 700291106 1250 700289856 700289869
    0xc030c0203010204080102040f0f0b19050a171f1202060f1602040504080c0c090c041a0405090c0a1103070503162f0f0a080607050c0f1516050304020a05 67
    0x9080c0001e00041c0b80c82c3d07580e24020b08a0380182d01c0343c1407500c0351450402a0088941c43e81c0010000503074428a0240d0340400c1e41401d07188504220140080456400003071403040390200c1c5151101c8e003504105081641c043c200100150010301c82d5000049804521b40340c48080c4c264815601901c0e903800c10903180c5d41030340740d50000c113420104000c25071003000140e61a4001c1902a601840d1502d5440c14a00e2070346040c251001c200074002d00164080c020080f07055401c54044030880032030160744900224104c03116110750703405580d0202402050062042c24070000380320860f0b0648401c021001d417040c0040d205e008500014055810a00c030000d082e081034061032554a101d901062003080039460030900c10000c101c401c6032200a4000729950301d003040c01841103281c038100c82d800c0c1c240d40781c4400c49942c1d82000f40501c3c1081400b10741c0468001007003020584c2805110155107030304800d560741d5401058100e4040c2c14a2544003c1c102d40240079100b101c2c015070300544100085070400091014 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 700292356 1250 700291106 700291127
    0x807050405330112150b03090a05011a030706080f070e12150a0510030b0a1a060c0c0307090c021c0224040b09160311010302070b1f090c0c03 62
    0x300c94010003058014503412880140c1a608902c0000b0b0038121500e000400d5120b000b940400304520780b00024461480b08800c1c08100c42d000c6514a55a80da888901d90400c0800031000300150b003000041181000d00202282e4100c8080e41110203c3e5660541220440c4082d202c010100c1d00600120341d149104080038605540058090f50746088042c802a00c2c1c000711b2900d904a110080041c4841001c0724016142c00a0841c1d0982d10710301c0c1992a8891510750140126810a540d8071040c0c5e00805d40200c1c40021036402031141d91243c842c0c0d5081521000b02d03c0f46984603009810300840d844601e13114002424080b41d00402c1c1740c0707049601220002c0101e0100e070080d8403409500c203000c0009011906260051071422600358107091502c100a020b001c2c6c200d01083d042b40d12240c08903010718000e0390032690000b04982d03103c0c402c40c005900070f11410501600d01c04290342082044000074500d84071152084032030884403036403400c500303040f50005581500001c203043c050001007032199088a0 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 700293606 1250 700292356 700292371
    0x60902182e030c0e060408010f0c1404060e040f090803040b010803031e270c271b07021009060813030917240702150112290a0509010c090807050405 65
    0x10190040b01c8005400b0390407947c0071440d5a91590043c4815030105d004051450b42c0c14240400311401d41d4007019024051405080b08003c20140091401c0d42c0c1c58108001c11441e1a00421030050182010036941e40100c4080d00d0007a008400001c80c004004100c0c1d1140f12401b00040f01000c80d5903e12600e01000780c540c100d010200100080c0d005044085c805019940c10000c040300b034400310034005207400d000407500c40000742100c1513940085082000c0d0b4410304440c08800e403083c1484015840340501c440c081e400800104603051040d4100c1700c0c00040d1011078441e407d171680c441e01c500c9448086210018002980c5060030014440001c0080c03a0501002c01615402e40045524017840035110300d4401700c168275a801e20507440e80500400000c401c6642891b2259810000d0180404510140081a03182c1804504040c4a600c0a0004001d416a00b0720908e03400c4c0200c40d64050b1005a03600300c003552130b1146c0b000b001e50142c0701e888210b50000018081080c0342404110040c4002000e56 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 700294856 1250 700293606 700293617
    0xc05040b0d020429010504051e0607050a03030507091e0b0331020907080903090d06090807060618200c0c0a08030712080c030613060902182e030c 64
    0x1000680d11402194a001511841031100e04c203a450318420b01c03a241070105050100401041c000b544906104105030b00005210411444029000c144a4480c12101070318034001c0314844820140c0c503030804d038060001035846140f00b9848440706020300b04d5060b81000700288541c0c0c01c0103c1901200a19884003200200441420010102000c550210076401c4900004030103000114a07007160110741103a02032810035a07620304044529070743e1050704440c51203540f43d00004010820b80b5044100c005501000340c03a101c0701180b80000c050085d5001e000748040004030f00c44000c004601c202d0110344000b81200c110513910807e90000c684c0003489040c82c500610140001d161514502800100f030b610000710341d01d00071414840401c1d01060040000c004400c0c0602c002d42909600b602d03084081252400d07009904440b80f00020005640702a00e483c0c004500405400049a08045103480c180c6440880354a4000f12441002007442c4200c1140100425440d10314402d500c502503064450505 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 700296106 1250 700294856 700294879
    0x915061d0411220b0901080a18080d15050f0105071124180303031303181e2301020a03140702060313020111010e030d150906090b011b0c05040b 63
    0x41c4074550300810103101d401228405401c07040344595114001004c410800500f014113140000700107070005041d805002d03454500d0241070b00340c2c490341030680a500200d415540c0d4080c00d1408080c0c10128031194030a845907500042c1420000c000b202c001c00140c0d141403414a0b107941c1c984024242411160300414200000092030b00000341c0400c0502c0d213252010b0301d500b20076001c500c000b0003030f000d264000e400900c1440f00c40c450b03060301c0a001690500384100c030041a2007006410403800d81c400070609441881806121721040e03034540c250750600501040070740d08803225291502d41d1405c03c0b0f0042c0d10145160010a00ca0400c4603104021414228581021500050102d40064a881c410780d980701101c6011076800500b5881840d0b00300000703005c0c0543c22482d00ba1280900201e02c0170040d140c0c59480c02c0d1a5000c1c42c100042c0c100320b031040140c69100c50384040142840e00c00342c1c0c0030540d41c40d00a101c5011581c0d1448171b40b6440701000c0c80041c01c0c06c007480701034840d0b501d0240d04200624171 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 700297356 1250 700296106 700296131
    0x5031c0e01020409021c020408030f090439050c030316050d02131409100e09071a04060201060b040b0a0e0109030b0a0b030601050d030203030a20030f010915061d04 72
    0x70f100038103441e500541c464564444800400d22240302268056104000c204a890700c080f0640d07000f00c001034402519640c012010a010308030799541c00c3e000c1c04234000d0386100b43c0e011004010403c03280002d80c5140d40002d240c01d03101803103007902900b8035920503c001940c451318240c80a041042501e0943c2c206411981003100742c0c1c1005182402e0f14900380b406200507a000c0c1c4280300e4440c0203c41c2c00955081801ca40c0c3d103202000e000c1c0c200780c0c41d0b1f03820010f2251030040101c08018281844481400c2d9004440308083c3e410502407a40154202100003c4010190301550700b6108200e4000303161041510040d0342c0401141103190511541d150300001182c0340107861482400040d4011401c1c00c6a481054103111050300702e144950400118080071036400000d41ea80007101301000281140b001e540d04203540c40d4a14510b02d4200c0020410410010074000ba45c100c0b000d220040c005c41808002c5440a07400c20b00504000070800f14080c6064010082800300320700e4041e0002400600260 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 700298606 1250 700297356 700297361
    0x5091209042004060f0f1416081303050a050c0405040b01060c05120c0d1205070e010c060e0604150b010201050114040213080d0c020307090501030215032509090c090305031c0e01 78
    0x184100007040b8051441102d00e60001405c54030f41d11b461902909415290303030030a0103401001c0c000380030a00074940d01c2d0704016890040341c4c007170309503e0405050f0a0384e80c2f4200303a4035a400c1d003044806019202c0703176007032034101402064080d46d4001402d010580c24407030100c070341e1490300b0030a840c103102e40344005100c0b01140000740240c0c400c80001e4208601c0c0000082e1191004000c0381d91400d00d04400c2060441d4000c0010951003401d02e003110882801d0f0a11001410b00b0108503480c40c082d400c1444104000b40030045103144054a00303209403242c0800580c04c99409210b06a0240341c44ca44e03200d810f180650040100715950091050003d4407080d0552510300b000120402162190204600303500d0108105001044a02c034180b089606550206007210700e070400254905402001145010b030300000344840256952017951280082000024412407051080190300c6e80390409040440b4030619981c426250414011440d1041141d207000100300010024030000d5030703403840c1860075102030 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 700299856 1250 700298606 700298609
    0x50d06090c030b040b13081e0c0d020a0201271710060329060d170705010c080f010b03090a1b050a120618240b0904050604030305091209042004 63
    0x2014030b681940791501d80307159007800c064500086c402907081c90500003800c10f011510034a0010200010585184038105518004c400c1090030900403002d080c48603942c002010f9010034000d903a03004c1400101c14030340a0040004400706801e9000c0c10042c09001c990841140151619004580c040719626006d40200e6030150000c51304000840d03002d04071a46003142454480403801d004441c5410030074001954659116401011445c529612051000d0351005650320150400c1c000d020200b42d9030001000d102084401d8140500b0010011841c100c0b1001030b603100d00c0c10794004042068064691000c48011a81c28400045900c0404103203030312114400001000d000b20b684070400b2031490804181c0780d00484586d40c41c90144031078408900440080b42d9140502e000c1e400c0e110b0b0b508120768001e004081d034401e4000e9014400d000401600040c00c1d44203500070760b01041b6607111301c1441600d500c00d05807182040e5078240203241a91400d03922842020340160011280c01d611502805400d0b00103 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 700301106 1250 700299856 700299863
    0x50604030804020907261e0a0203070f0903110f060c0d082e060f09050409200105130e1909050d020601060f080a0b0d14010c0e09060901050d06090c03 66
    0xd14280003c5003030411150b6004201d5040041c01c40c401c2c64000600c6040f18500c0c03202816100380851404032002c5035034052042020100015850304510717150181d481501d5960016010000c812144d510542c0104103580e4080c0d03010310503c0803c402c00c080c00e0104410241e21036010802303805001010000881a20b143e0b86402140c2e240c40426842450002928503040003450b445030b101c81d200c2c1303800190580301142480000401c03824000c44021003181c00c086e8101307103012030941c02e01101081140e0011190b0f04040c04852810700112250f0080450044110054600510030990038001d604e60041040c42d60350000c01103a030701c06040e10758014042c3e510b90060701003107410a0f414000240542528280b820072501c40c030b900202854001044024840e0392945954515981c0b18540c0f080c0540181c901c0c0ca4411300700c0142e600800c1040081e0000c9501c6403100211428042002c500c0355034000c00000c1140e203404140310750000c40300e008482c060782d18031075580000c0b810305581c0d014501 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 700302356 1250 700301106 700301117
    0x100531090b01030e1203010e09010216111e010806040f090803042906030a0308040201170702060106021011070b070216030809120307200109050d050f1e03091c05060403 74
    0x100c1e2001400f1260051000d80f40d43d0019091808851014411031b41154005a8020350942d601c00302c0c14020f005000304429014400480c040502c180c1040001e1301c002e080300c140f10100381c01c42d11040f0a041c00710015004c1408200083c01e1898903a000d80310070307000c4020200b0020001c1e82e61101d9070307208560807903890308142c01c0300300440c5042840754048070f1004120b0116007440c0001035651208110005c0400a50307600240071a4458154040000901c03620b0540c80c1c203040344069100c0400f4020140140f086007101c02c00309120b40140c207240d1100c01051450081d65440303003002034000500003000d501c80e40045604c081e04030f80110000318040d6031042d85601c41c00040007103078550340340d18108a5005100200c0829100d8288480b20134188070100c1182c0c05401c01a50305a03003503400194040c2c01035012001b4004041210310080c080300083d00c1050b2070701d01d04002c042c00344092068503580b0904c0035200700d0510074200050f0b04a101e0500d40501c8050f6280da1410348100ea00b00e00040 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 700303606 1250 700302356 700302371
    0x7181d04111207030204021c0207201903060507031b0302040302030607050421050c0d050a050c0a0e0106050a0e04110d2a080402060c0a0507030302060610053109 71
    0x110200020240c00101c6154500200201c02d0703640c1c9403002d002c040d00c550703030008222080e03801962506080402d000008d64560089080800c6a00d074140e80a50074180341c5801001e00d40303424155000340d100b1450071107056a0071511110014800100040b062541d100300c28040c48803140c41102580c60b02d40e0300540e69070300314410301d402c0c0680541000700f0302c10300340000e001540d00c000c442d498114061034860f0a034021030424502c2c14800c07a48c969006000091503a0500c480810002e803d507000c1c00460b44143c091900b8004803001510401c1c03040300200b4010311015116000416a8514924007446813203503500000341150001c100c220707107144001558800142d81c42c010701f000c0c031a4851808404504032800814100d022071242400c205204001504569a072401e455010b5504030071101800c1c02440d045540740b100f4001900988120b0000550364a8080c0740d040c40703000166522420a4034004107801c1c1008d81c03009a03101c22000e0080351000c65601c6072264010101c1020104080 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 700304856 1250 700303606 700303613
    0x20a0518210a05012d020711040203010f0518070c0b07020c060d020414101407020d14060106090b1c0b030f0d030506040e0319051308011506030b030309010807181d04 73
    0x115501c83e081c0820044180b40c440603c0045d90a10450800149015a48141c44d01d01003000482ca0800070390702c00e1001c800400c449502680640640c1d600341d60000202e0001441c0f28000780d403c84071600010049030b80d400002d042d1013101d540100040c012a034580f401a0f00117100e50f0031090743c0480b8130340d011904210840c00c01d000c1d06d004440c20f0310540d20380d6138541c0d0010009098040c00c100c03403000000d070101c21500d99244010015400000700321802c81481440c68036114280718040010b102030340c01184c48110541215050000100d84460503842c0111910180c52480d801e144d00d8001c3d00e001511001c4203201000c4c007103800380c1d00000c0b24501032042104031401070034240250b0f4000c1c480d01006150b081c40d001001061414010349841c0300c00d1303400c0c2c1000502e4000f02c1d525402c01e1140c49010301d030813401d582518030740d4074140710700c1c00c185082c142c0e00d0003070804840c0018404400321f081140140c99041d445007000c15015080341d125000444503940c1c070100800d001d500f0f0f0b010017060 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 700306106 1250 700304856 700304861
    0x1412040515131a090c0a0b0c060105151c0207140c1c170d0912030e06010605030f0f150a240807021b0109030b011512020a0518210a0501 60
    0x7050410040c00715114035190380d59001c0d040c0700c803d001e19007080007191208000708107080d50f002005007140c03625a102c10a0f03808075048810503003040d200d0f100002c1544c1c60100c0654456180711100c660a084036028001070100040c5540e0120940c204005800301d444001030648100b183c40040241705840300c10702c2035603c0800603842d440049404004001032540c82d003807108070641ea807650340740d04881855500030311401034001c0901c6010204030414a4060300310800d000b020078155070040c1ea981c0000d80d424032080f0383c9014412803000002e02c0a00d2100b1040350415501607a5070001c01d21500401c40360091900702c2041180d910004180c07014515a0010400300c007031514100c20300705818065901c00d1008242468256090510169079101d9440c1000a40d003107041d01c0c8465955004541004081804074000141c02503051001c04055000b02e620700c2240b41d44103031030075481c0744a036202b50031380343c02c3c40f50300545240500250445211441c64003041d144050041d45a56181a608 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 700307356 1250 700306106 700306111
    0x140a021201081c03200301080f01051506040303050a1710050a08030a0912150c030209010f0f0f031e0212010e130c26010c050912120403031412040515 66
    0x3955008842c12001e540a89180c280055804c2c10003140c6248000c200700514014012194212040800001440c560010749014048444002000079440740107110b014840c0d0070b0a030580101c41004100300013882880180300075902840c0803681904d5403551058074040a0b943c0000308901030070140441c3c039101c04100010410b0302d004610349130a0001c0a0050842403091368603003c090210441440040e0601d0008012080d00c200320030403280c10042c0007900118026800655141100710049028030034a01c0304242903114440c10964607007048018000b08810f65000c0000a450720031003042c1c03070001e030642d0310000920300400d6041c00c1400070407410040406441c0000c1c003003240c001c99940e4000c8020b4484080090a0780c032401510a001c0d514147c3c0e2703500c9558a0078401f680c22980c403101501d0f020703c1c2100d2281e100d04522804554502e40d40c05074000c159003c00040000034000c18040300c2034150b40d1030682c20600c45500b25140414115010f55241d0440900505c1440207002d0107503 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 700308606 1250 700307356 700307369
    0x3050c010e19062f0d1a1f0201020c1f230c09010c1a01064a060a0c0c0506040b030a0e0309101701080309061804140a021201 55
    0x20b07010b03000e03840d2280d0000c0600c0c40682401d41d602c2c14480c0303203152185452145400340b001c0610f041411505800203901131500e0911880c41c1510a18010070710703403090526003100804010040388200c0d42e602c8134015180c0c45400755035081060b51645001848142040502c5d040c82c1d1504000098105066809001c081c203075640c009510b52000c40303040e0044a4200510b03100540c0c45a01c03900050703c3c81d500c40031010308840c41750340003100140c41280c81d4506844aa9a0720041011034810a41c400c04c200c0103900c20011391042005000d24150302d90070f449280e600c2070040010125008180250304c4480d403800003a400c128444280149a000c61000340400d0380d40c54034140c40c02000803903502000d0400c40400d5210540228170344020030554107038102c001d004c8030345040d0740c50001d03010280c503c0740403420402000001801480101c255a855100503045520b090b00080109410707180301003000b68440c1d9038400c0101c0340c20360175109521403101c2440042c5e894020401c2d0080d1180164401d0 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 700309856 1250 700308606 700308613
    0x2805030a14062508100509270d0f08090a0b0103200a0324060f0803040519080d14071b03060f0915020c0c10171303080106080403110a03050c010e 64
    0x1a8032403805883d1065841c46686012000341d154909a25031280441d803003154415500402d0116405103c090541c4015503050604042c4d00d8050110382c45003070055010380402c510003050348426025080150b4031a40c858143c804284030340d9039804008a0a801c1600c1c1c1d01c00c070b20042c0e0400b412680d0111461384084908134681c81c6595941d81c4d11051003d110210b0100c0c5081e1a07074599040c2d00024040c1c081800340da01c40355126000c50343e607604a8844ca610910107c000011540000c0c41401e041d20702d40750242c41c03101907a0005540e02918190fa00d0f201c120200032400205081d25402c05941180000c9090303040e1440c1411002e0740e10481c206140b05240404ca0780c0001d03400d141c003c03009036480c1000740c1c6491151415504145185603c00d41010780400d45d4502785e54041481d012010310b0314014441500c8101100c4498401c100303009020400f0307180103004090144020302d46c031078032034070700b10303500700540714640d42440101c510460200700041034299501034280a07500d90320760a900103 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 700311106 1250 700309856 700309891
    0x1501141005160c090b010210060b030f0718060c1202011b08060301091a01030c120c03030507021c1202010617190303181a010b04052805030a1406 64
    0x3814204080d554034148070000581c000305444a503822803000750040300c95042c069461480c04060004815200c0c0140135205245003131005600c143c06c2a2401c40e48d42600b55a40d083c0c02d44107400001e030142052104020f00b82d1b0050a4050714a000340046581c2d000d180459403500081e03980016200000707590400d00c074086d44000300001207400c4089450200d526444040c08a8010101c1000180c52040c0c4903060f244031500c58403019040324401c10703403017040030b035515040079507800981f40c018a50706525400300040785c812005400041d0000b003903142c00e80c81d00301c0c603505e00000e542400ca515130842c11318084000d07020304c551070007004000564200f43c010442c00030b4956420041005c4810a0303503a074070b01414030950265002c01110010b1005402c600e0070601c49100e04007013681491480c030300002c1034000d220401e032402c440380500701c000c8041c0e031b400d000303400504080d403d1190082000300004076640c0c1000a441e0147c06051005495042070b5081410810300812540150111259 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 700312356 1250 700311106 700311109
    0x501021321030806191410050a0903171b0d110708121303082a0102161412181906090501050a0201020408160e060d0209011e0e09150114 60
    0x11008071042d41441c00d028140d031038600081c0609011458885000e503209400b007004daa4200407101584000c030f0700e04100c1a0180c07001c641c1c51240001d1040016404034042002464a00c5440e2200c00d80000a60810168240034061441c030a40d080707010764047c1c444811956000043c1d440e104020034050314001c3e060180303440d42d81d4060840814003500c00500c1c0107440c1881c0c2280c1d400f55520200c0e040d920500da40100100d62100d4000750900003150000a00160b014422203e00901202c00b0340004462038550041c20200c1c081040309500650341c0300305083d88003100401c01d5880e00c101f03001010755044140070003460103130390300b12004101103c103001158001c2142c2080710780900e0004d56a038100c0304c0c01ca0181c05140d105020034405d141c0000b0b0210301068510068600b00d024003000c0d40c1d203500400038188540e040203034201c108140140b01440c80d40060303545901c0140c035001d00ca95920805c1000c00d070300484ea0070460750040034000709048003018540380107100c04098100406074040 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 700313606 1250 700312356 700312409
    0x316270f140f01050f011103160b0402010207080a1109090f060c18030111040308090622060f181a0f04030b01080f120d020d0e0a031110020408030409050403091205010213 75
    0x5c5035040c4014103641c03101070309041003125a841c009030940d03605541540303024020100155400c80c05070003140000f1a071454005552000680c000c1e062903056900a01408441c91010700a48014019032201d80303204441004024011010415517a0b174070322664680326818140200590b100348d051074004205034040b04192400e8a4001940d036940c1c0941200160f010320039180d0305411101109000f13540247d40c182000c003200d401c0c2d02c0384a820b00502000300c078520701c2c18000f0404c410f0421000e10009a41e03c4072400344084071a201c510300031440718060404e801c158404c581001042d40180f080280c00c3c40081c03080241e0724014940d0000d181819000f9000d07920586440c40c1e404140c508a484031030b0800b020010014003600e030388203103c1c11300038074030711101c070b454400c0c1e20410050601c444028400c840803601440095030600c2d06104444010b03180241081e07042003d10f42c800300360080d81c04216100785209800042e0340340184448082e05202c00e03800784400c0c000d500300d0f04400d0494031 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 700314856 1250 700313606 700313629
    0x910140f09060405070c1401090b0a0612170d240501050f07030309061415030706020d0207180b0301051303110c0a030807030306150c020109050316270f140f0105 71
    0xc41d000320b41c07651030b004d088611440c1c00714003600010387e10b0505a000355041d8000e201490045406900e1a49c2d2081403009481329489a078012420000583e80030805a448418111400011315031400c903004664801391707594803a0080c1d0000700c14402e40c10b00303403e01c00030700e00078442030811500340b16603000020017900030301c180501450f0b100c075441e0040003d240e0060211071000d820310b8175242403460020040404c12500c003406480347e07c0010503024000a20202d00d1403450f402030802500b40607041d540307002844001c2d80107a440d0040c030701d616642030103028030031242e1100b9103484170014203000300400ca1000044003560070140840e0401e85586200b08256a0000c0e10b265582004d440c0482c004d20643d48100c0c0000b171025030540015910845110000b03000341e0383e03100f880751904101520340d51200c0707283e101207100c00300800c15200740300c804400c1440008180400d0300020b840c400300b070300d074a180500092952945c031040005040482c0e590003003285000d408e929818032020a032100040b = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 700316106 1250 700314856 700314859
    0x9010602150705070206121e01050a14010908060114030706142b110408121c0e070f0e04120f1202091c050a0c23100e0910140f0906 58
    0x3a08000ba0402e80078904640403250f010340003669441d00382628018821042d100340d00c405009a01240c81c10f912182400d0584000800b9040100e1600c080d41c4101296050743d24180700000e000000d50120503c48213009120a000d400540c030a1a0101410941503410407014410800d580304c030041d4000c410f4038400340410700310400c002e00c0b1040400942180203444c91286042c0107a410000540401400858080e4000c0300d40e201c0460b00e07880c920340a0000700a1300c0b11510301072440309080700d800070f1031254148029a07000c1c60310384401100c0480140c2181d80c40701c45030010300040040caa95994030980c0d542c03900c400d0703094036060001c014000003440c1c04055034020034081c006545000040700c0c44255008948176950280c50050f8540b0740641090703503441d09001001440c11a02c808080d064016524134040300c1101e42c0030404401c00c0e040200d000c21900124611480c1c84851005000394141e000980e501440c201c41605050b80e80601c6d940510100502c905440e2503042843d40c00840 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 700317356 1250 700316106 700316143
    0x411010503061f0315140f060906040302030d030c1806020d0309140d02010e0606031204090509030f0c01020310051f0e030f011d1603020901090e01150f05090609010602 74
    0x754030000540f00c0c05601d0500c405a41003001003084160103078400449030204a01040c1041e40c0c4030082e214005213581105d400c4200b44500540c1454510000c083c4581c0040109040607203d4000c0b0341740450040126000c607a59130744001c140f0b034022443d4194001d04009010b01c1b035040040003511080c46c9803404041c5030321180d294003000843d00303c3c0060181c0da001210307100640c00c407009000c0c1070107440b018014001c40c0003240a84c1400324103074006441500515240504c1d20b4104802894000d02240c4203005c1404a8840410420000e0000109900015850303081101c0030742520201613110912a01a8101d07080380c545101ca07400a1210050a024508200607030201c0d0a02c0d6446001700100d5280282e1111032611122a00001c84100d034101d4002d4040520001401c1e4003500020750700000490040101d401c2e2078000d2075200388108004124113030301d007500f5500c02e000c54100a07000102c1010512050404052007503010380211819030942d4505407010f900c030745140e140c8440490 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 700318606 1250 700317356 700317361
    0x3030b0102010906050903040e0a0e030702190b13031a090d110a080408070f060908030f0705011d060117011104060309020303040803120f06030a1205130e01080318090411010503 78
    0x703000794401c202181c1c00c610180858070303214000c15283d40c850300591004281140c003080c8440401d10903041c03d05407050082d0701c1c3c0f000340d400b00310340d005030700805916050008034042001c040c0240a400030a43c0e07000e4040700f2504501c5c12803440f02c1c46101d04200150315504001245000180c0c0c000e111004d802d0126410314a110840c5c200101040090500c07040003500180441d40021910225a01a85028031080c3c9840b42210504042c0c4105074003503006000d05807203802010000e2040301d201b0400099032420001e03010112040e410700e080e100c0d8101c0d60041281103142a00f1034a02e2800e00001c22a500300c210000c2014052805448201981e030380400d070441d1010801c88000c0d10f6084107ea0701c51180c0c250001043d20700311a13000340003a030000411100d060009a00c1c0071180e00a01001c102c60700c1203001c03501901b16400c00440c28804000000341c50100340d20280c0645640740245a0b82c1c01007880304d0000031550445107010b40c000c0010000845d90071042003030300140920b0456501e4 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 700319856 1250 700318606 700318609
    0x100206060a03140c0d150c0c030503010e1008010c110106090212150a080a0809031b060304061a0409080309010c05040b0417120318060109020c030d020f0c06040b070e03070501050703030b 82
    0x113050040c038507013056130505040103109090050701884002c024061143e404100801c4a0400240c0c07c01404100c060006101002010707103901e5001d00d6000704156000c1e502c840250030748120b558501c000c41d61420018510560a00808001c0c03c03010900f50310b8881d4441e410b00082d080101920f0781d0007500100380d03046030707074140c1a47c0c000c0210804030307a20f294a0382000c1289034010b02181e44030f4800c0101001100200c401c280040c1400103001078110b541d43d03221640500014103a12000c0e01070200d820404d80e480e48682c0c0c901d01e010351809500d07803401451060031141c0003c00e16003030250600003041140310440480701918800001202014800c1c41c0c907500d4103545031500c0c9a140c2000c0701b044483c1042a01070340d07914a000003140c001d40d0b601c4151408038465060b021409400401110790300c410703190010f01d82440358000980ca00a41e9400890500d1416141241c003440c0301800e1200d2141d2001d6040d20b20780d02240a40f40040c6800e001134114030441c48000e040c5900e484028145 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 700321106 1250 700319856 700319863
    0x9100509180414060f0403080402010c0f0219061b0807122d0e04380907030204060f14030a090602130314010f140105151b0c100206060a0314 62
    0x500d1181d001e0200c00742000d1908030b800c6914254016494810140020020700d030300c001140c040c03501a16138003c5510303a500110f400311503502c02aa42803031800200b03001a100d01220403580a000645140e40c0790600000500d0741c0011f0f410740e42484850007500307011440b8503088500b0303541d1141802210000b00c000a443d00f06008054050aa00c09011901018008520884c40f024156a058405080c0d4000c100c121038000744401d0075004442800c40500d02c100c080c4000e80300c10b0355508201c54001900048681354102d40c4000040c0d0007080c00c000c1c503500311881244207152821b00d02c40c080603a1061700001e0000900d84002e0345d4441460506100d40e41d4100c0d03886581c2d0303c034140006a100c6c10f080010114641000c0819880e1101e0002c0e107075100d115a103100c40314550401c1d403c0c1d10385001c21402d40c5102e00e400200d2042080600c16201d4688401c040041015001d811048850300800000d4002004540255044001048000c0e0307140d01441055a07842030201111008064a00e0b18 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 700322356 1250 700321106 700321129
    0xe0c0a18090f0207030f0c0309151116090e060403050a0f11100603050c121506190f1e080618070506040906030b0a021608180d08070203011109100509 66
    0x805882d1040c0e00c04944400d0b001010003078029240d600344a401e80808441501c88568003030006000018140403002c07000c00b00c141c0041d810b00d031440601e03401d106110306003c0034a00144c5110340003442000302c56a680510703000c030300c016400f5044a103000d072805410b0307114018480003045905100141218003a241400c030b42014581241c0c00140700300c1400c8028540c50005030360b14452101e0b5081141780c00c0940c03041c1c29408030007a044045e00c81c554140021005040700303602c500001d410080c6018140008401410700c911819003091800b11000f18444001e641600c4013180440c042c0020f10001901c4e40d088200041c0644000c00c4847d211400d021281e00010f078003200004000030f80c44800c0e0440403e90b0302808031500e041c1c032003819036822446111a1480c1a00141c414800070485d010064150500800705da210800e102400140205d0f01c5000c00311215000494000290b0a092062490f0044800303032040c039007000c0e07000151581d052400c0c03d0080010025000d81242c94406001e04d = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 700323606 1250 700322356 700322369
    0x80304120b060a24080a0606050706090203010209090c030f0f0709050121060602030c07090e191502030103060203180703320d081b03010303080c07050a05250e0c0a18 73
    0x1c011340c403102142d040c00520701c00c24006400407004c16030018051080c80100e07880340d11401d10701003242d074403200034092450040ea810b550901000710b868403007010007032081351003003080350350fa00c1c1c4100440d5400c034001d04158035000c035005c00c00c9241030b04401648199034090805031444807011030251502c804817610084020305205000445540000103040d0018281c0300362040284c07a0b249c6070301100c181c54800c00b095403220050071204c2c0605124655901d002d04900841da42454031140160391082e44100c030030316400010080f1001a48192160020f82d51015016040c95a00c911a001c1c28814403800380031203110b2146c8003030301000c134250380450041d400d4034400c0749902d202511813003040b42d181c0c031482c1c1c11519900d10010080120cd040e00d41c5a01c400925464218280e900f640000c80b040b10144262448a80402c60810101034100c10418038404042201075040380c0c0300850b075004a01d040e1154062101450004090768040c0205103031010304884c1d40403051101041950045 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 700324856 1250 700323606 700323629
    0x15050405061c06020307030c020313141c030216140a05040216050f01052e06030506120f060118020a09050d0305091203090405070503130213150902030105040501080304120b060a 78
    0xb02c007040080d801039803081000c1d441c200001c561002e000c0e07849108040c461440008203603420700043e045281752400114018114909a001030406148111201d00066025038400002c804d40b0141880c0d03c24050a040f07a01e080c001c1c864807010940503100c5020f0070788035603000300b00d80c1380d69275955440c643c03000d801c4000c54902c90815a20b19000300f42c150ba05411a041800080fa216203580240d0741000305110700c1a02c5482c54010201c1c014840940700941c072a001d145030900c0d680080180c20f40181c0c2c2240a4044d43d4900368034000f1100c0b10840c0c410040b4010b0240d00c0300d0b5600410002d04031081a100c00a0050191808445c1d0707201e0f181205030701110803095601d4440001010b07241d49001502d04104175100c540042e14940000c0300d10b00c2c0e01006925443d001400e04620a5580200c081000714001c0c101200c00f203220019a0002030540303501100410a038a040d0041d680100900c03405507203000c0c20700c0040400b07950400d0000d4001341e01c40c00481d4030740c0c07120545640180b07441d08a4 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 700326106 1250 700324856 700324909
    0x1109061209160b121e070f05041a030a050916260304080607080a27020d1509050c190614090d0f14121b011107030f0f031505040506 58
    0x307040c0c0d03412000f002410f5142070000034500d041c0d0b55003030950141d0b17100c016109aa41d81a0102c03070b0a41444680803c104041c000014041c20841090b040ae15008030519203e19140601004603840142008200d40c086075844100784081c45c0b9020945841c0d2130366540c030154500c50440e06441e4215071140510001400242e80e003004074000c0c1c0580f1940e910206d02d52141402c00060b582d00d5820400428601c6a8000c01c07006001d419165607407010701100076089641e200d0000030031100940c0c040c82c07602c0300340090400205100207410144103ca00040c01280e46e040c081c50380049001d0344003480401c6000600e480780002c203a40c4c2c40311004140c80801030036442c0c2411035180a040407584002c042a03411a03103800400c17103080c10b025583d08641803042001d03241580521000032504555a40e1000306118400300d0300030720105000f0b44541402c208092001412404c20715510003c252501c0004851200c45a40c028211031007110040742e19103480e80000e03050340000d500070000341c0d02c3c80007 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 700327356 1250 700326106 700326119
    0x302060414150d0905061e010918060f0605190308030112080d020c1006091407120603020405010b030603070b030708040f0309050414041e030e190302090a0906110906120916 76
    0x440e020605c2002520703000d440300607040310011600918860792201a40c01480b0280032941b0091001c0d8100c0c40a1410342510f0310365004407004011020305040c0c851034240034504140080666030351541640d90384c500d1950300c80b0511400107004020303844990454500a00602d4010341e580e84030551000c540c1c2c2e0b107010006554035824212900041c0e8201500000c500c08070b40720b03800c1c000c040070b0050095540c4034602202c00c400e800b4001d804140d41e40c0004805030f16a4801c1c00c2c00b80c9001c40080360b0328102001098600700546c2d011004283c010410450966482031030240c015512110030041c0004601c1c040e0703140c6503160403160f0000d01d44003030301c2203490180140d540118002c0140032005203640e01d003e0380d181a00c03440617002c158148541c2002d41441c1210010764500141141e410315202d40c0050a4203a00340e070628055a16120340d5414032403248504888160350301030350740c038026001000c14894090301c4d0301c0f900055018030000e18100028030400c058800503040101d00c686c0c0381e11 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 700328606 1250 700327356 700327361
    0x40b0408070506331309170d06081c1d0a1a0316050322140d020f0c03070e01060804050111131a0f070b090a12050a180302060414150d 59
    0x880d42000c58441041804130900d0b40781c815050500203000d0040b5154046004ea001e0040700004071409072501e803090b8201c0100c82d0240026140070038001c1502450301d040c0c2031400c0044450083c0450600e08610003150700448248202c500807080004004044000246508200d60000708800d8000c1140b41400c0045401144a0498000d242c40b211840c48000c541a0001b121160011004400f00a02c031102680342e40f1600742c0300b07000d01407a400d5448440c07420324002841d11000f503031240700140c03071040050190082c1c000e01903000305106440d04911035240101031080c1420321900f00b000c1001d0000c20b400032100310180c01c86407079481d01a507003110100e03005841a007410b1b1402030b42d92044904c0c40d4084900c46c009142d03001d41460b83c591205114400301801d08002d9109036281c45c1c2c0041d240304c00940b4603003520344402e41c071a21031800c007074000310201070600034081000c101400140c1d1840c4c01e07901a038001c3c0020164400a46c00841c0d07648050700c1d00d102c40803102090b250107a4800781c = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 700329856 1250 700328606 700328641
    0x6121b0f0304030926250305011107150e06060402030601050d051f170303160504030506010b0d0b0d021e01020a0209090615060304080910050714070e07021203040b0408070506 77
    0x80b40001170b105088540d9003400401070396a500c0d9080b1400307415500e1a03070454200040b181002c0d807007206a0ba540c2d02421215008030040c0380c2030010070f0401c03d120b42c9998503541402c074a681071066440f02220241c0315a0020b20f2184601d5000c00810240e0b40b00f4070039038480d007448803410441802c3c030324000700d500c0c00b96803a042d11400303408401084031512007001000f04e61104000b9411601c845811044140c1400f480e42d08025080c0400408584100441402840d107950303165611140551401c0945000748081030003005400d004100603218108807130081c03020391007500d08180080340100d0801d210307848082c2d440140c42e400c2c00321040707022882602a441c140451007540020009100352400b00f19409010140207001d00086400d0144400d1000000c1d840d02918180740341d5a04452030031101d84810b1140d1120b030043c8600c03030985003c540c2041541c002005402c10782d0074441000d100007840145140e01d5040440d081080400903940c100350b200054a81e90314142e0780c0410f500441 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 700331106 1250 700329856 700329869
    0x170406150918050f03040e0c030a111219020403020f210106230d0803010315150b07021806060f0705010204030503071505010b1201060813150b01090506121b0f03040309 74
    0x200c50303131001e0809001040710100c903002524407d260307407074016151040e04020020380200351030f80e608809401d43c140c000d10030030740c1003802003c0d40c0c00c00f00864000184100c1803884c2d480d20401090000d0380d52045000b4003c0b50840f190b41c03102441188810384980d4001e00b01c4007540c01c00d02c02003080d60344804240c01d0f68110a80c0c2100181540d0200250a060541c0141410313100704018030108400440381080300702140c50108202c020400c4401401210754803800711440c0100e6030600b18608036800d010a001c198200f6010350030400c0001e009403181800007204c03c4000101881004003c5d010b4a00035038010307055a46545d010308001200c14054100411010b00c1c0c0300c00480c40b0b17100d04c020f03036401140450301d080940c6c1c20148140c41080024050344102441e15518074002080044034601c601010180030818a000c00c00140194403140c00451062030f040c8460103901d008204176036480280c54080000c848024440d0203281d1041076048680d07104004104014140c203c0241c0c4112480e = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 700332356 1250 700331106 700331113
    0x3191e050a0c0c12090f15110c06030610020a0f030305090f010612080703030e120c07050609100806130203010e010509010e190b010509030109060b0405010617040615091805 76
    0x1c079050000c08942d01c404445001c1a80c44802001144c0440ca25010084040c2001400b0305d0703e034176094680366090b910400c07440d602c41c000304002507032000514083d00003034001040342c9241c24001030344030301009000314006c0304103101040310300b88200583c900f0180c0200052020440e141401409080100c0b80c106461140745581418454148079450403600d0080c20040c45401a94400010f6031020406034201612040500944102801041c141401c000d00441d91002e0006119050001aa00451040000b400008141d03121210010520140307450700c40d006580310000500412000c900005c1c0307051001c800880c20000b141e4540341070f52011280c41030035a0340c40e1099041c2c01c00c1200c500742041d007a56400901400c039a0000328030100141001800c4c881d109002c0781c01c42e02040300a8074910b0b22000d0021450400344035540c094455483d22030701098180c4110165003501a20003400165940754190f07107040b83d58405400390400400c14040c0600c00304c10300e01e50b06606a4151000e01 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 700333606 1250 700332356 700332361
    0x1090201020d090605180f091f0911030606030a0e0d0e130501030305090f220515030a02240702100201020a02010b0910030b040f14060403020d0207140603191e05 71
    0x10b00440c0f000040703c05907039405281c80001c51040941143c0d0070f040541000c0509582049541c0e90582248291081001d41c09403050410544d4001e1246920185c101d6242c01e0380414800c014400301c99000400340d0f010b41c0c1e40e448444001c4c0040100411101c180e001d452038501c0a1640024403500401c02150309950500300c0b4106038040f0307042888003d020a0080044e4541d0703092100b160303404920700803d10010244042003040550304008200b0300c006a4400420040d40051200158900000d078010081309465a020500c40001750602d17280150904051100c07000d681c00c00c803044030781c0c060030303080d03600d50a46400b03070103500140c11140241d424201524054140001413510406040c1480035813246103803508200100c0c013600c1650750000c0c0c01c140201003501e8158021490100d0740041443e45068107009007000c030f44038038110854128083c00c00c441c0c1740c0b0081140841c9006c5032030a64a0f1101c1090000c11040300503480a00e03401c2020308011455031104211000210200c28805a07 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 700334856 1250 700333606 700333633
    0xe1c0f0b09070609060c11041802180609190b0d06020a0e031c0509030304090608031c0903020c040b0d020d200a03080a030504030903050307050309280612090605090109020102 77
    0x100403030f0052030b0000d51840000c006051045a600d05c00a005121121142c2e801c4800724003039640b030318101a030740100c06070410114144423809000c160822455480305c0d051034000503030781a40103402c00110329001c024115030903041b43d20518030b4001c0100303001d007415034524003180030350420102c0030301141822515003030034200400c0f4002c41541c20f003c1002e900d0320701602a1800d03000310001c150036200a000109007001d1511030000034000040003103403100d40900c00714049922480d0515251070902c0f0800001a40000e408960300380f0456000c180f100055000c034501103d4040083d502403004800e007814040c940724080740615980a0041e200300c091014001408103030310005052160801183c50014400e03404103405c88d100389450b00006030344e92961480e6402c411019905c0da040021080198070300074880c3c3b00c4401440c900001c0710308000c070440030304140713601c512000d0103500c038400701100e103003603000c4040d40382e00610411442c02c09900c4903000b17142c8440100c0c05481486840c4584 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 700336106 1250 700334856 700334863
    0x30c0c0203060604021b0307080c01050c0a080c0708160b04021507020d0605060f03070b0324030a12020c0a0f1706091218060304080703030501090203060a05010e1c0f0b09 75
    0x61500074006202c40d44400052000940c0030f405030000d1360500506006040340c0600040003054050441e81c1d850380303000140b00382110009020840c000c081041250030303084d00400320503405603001800903218904c50800c0d01461003000b07114608080010b901400700081c151000740502d000783c0303d400e00007d113a07500e50921b00ca0418065400031201c03044400003041c40e04102e032b00c800041c19045942000350082840e151150f0800c02000b480402040700c0030300c0150755003d106640b480c0c01c40e480000d403008251200d010b080040c000d0748110f0924000700d4000c11846201c07032006407480d040c4d01c2d079500c80482285003500844100d01d40b0b0581511048600058441c003489031903020f42280f9142c2030b0003002c41c0c0e0042500c28404420501900040e6441d54041c61003107000781c166a070364803403501c1d0040172140160088040b251045c014080c4e87e4542f00c0070001514001c1c2080e040310381907070340018620a01010422829031581d04814104a245054021200c0c4103050107685619041341203600d = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 700337356 1250 700336106 700336127
    0x150c051902030a0518030f06090f060a1802040f24090b0906030d08073c0c050c0418050715200a020607060e0d0201051f0b03070c0c0e16030c 62
    0x1800030700111440080c0c441805c4802d44000301280d42c0148240308003406c0860449420f0f070742c0c4d040016000320300e00302070103002c1d40010480010408441440c01d840741c03a0792901d40103030185643c1e1198a02050743c90b4007030702d00c0004047c0c60542403010300c00703c95035002c068000c01c0e000504051882d9032a0500c0b002c100d0140c2c100901411140e40c111b2012101d01c40f0050014041050440c01c901420400380b2007288004007080a07003080d5609590313044280c440060090041008800303402c00800c2001c40d0700700d00c0000440303000c036659004100518454900c0301000d0024001c50030300144006500c103c841c078442460b12950303070700c2441c0c6e11880140c410110000740a134000184103001490080010022070344117100c00140040079081c02840d0402c2c0385100009070303540d036061251007400d200c42c0560b4841c011340c0c6107945608104424000b40405042c041c00d04c000c20442c00b0400c6400241305020340454000800a407a043c41c41081c3c110a501503400424070308260203c01c00c1c451140c680 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 700338606 1250 700337356 700337377
    0x1201090b01140a0b0a03050423070e130606122904061112090601050a08030f19090e070203370804020a1d040204060608060108040f150c05190203 64
    0x180c2980c41c18004a044054000120b41c1c4521940301c0841e080b00c0f20005041d0001c3d140e0ba002079a40390a2408100341c440f00e01c8050202001000d4840380034900141301c8007515480088041203450ba1603200341074442410002b08030350304240c1c000c51000c410407418000d5a000c0c180e400034541000200c50364050749420340f806103040d520001008a07403940c1103031108241d01041c6603d40011a01d003182280020340341c5400da0b40110300104042e16100c25544041c0040c1c03405180b811a02d04500c0b021840780f610040589420341d1018001c083c0102c4440b801030a1501100e01d0034035103080000d403a42c3c48049030418801e801181c508402004480f00d20b008a03c64030b494203907001007a010307174080000a00c00c03030340442004400b0840c5404040000202c0f40801461902418244100400e4554a401000420541408210040c1e0b84640c072140c0040d00500d00d040d628030a03040210050359141c3d510700c01c140c00c00c251610800e41c044010940d414943c440000d0502c04803000b02d8881c231a005008 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 700339856 1250 700338606 700338623
    0x18330c04060f11070504050c07030806093306030103030504090e010b010906030213050a060309050105090105041a0a020f0417011a030736051f060f12020c010e0c120109 74
    0x1454603c0c0a501081d107001c2c5454102c0358480d645500040603180c2c1201c2901e140e010203d5040e0425800c40500d0b42c000b1821103204026240003c00e004860822401c4101c0d072000080c3c140c0400010807031900480b60002d80015070b290385034103016100c1e503c01d120307169507140b8102e98000b0140e0184100078040f0380c141e5956010030300c0e042084000e500642000c2c00000c100e44c00004096070384001000040071240c4010503103003003600b4024210f500c004c111407016418501044006824070f9012158007a03a00a250071076102c90401000a004401550611120005020800c040007050052510070468000e2214245600c0d10214207000b00e1040e0f50903600240c1c042c007010640715038000907001e07041850100f25881e0f044c1013402d1000342c09055600c0b41d9900c10b1012036060b1f40c2e04418890041d86100030481c1c90020014440340565007107104114a0142c1500020040d404980301402c1c901c009100546031040308035103400c00046a14030407904486c0240c10080b043c010b0342a41e07500071251 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 700341106 1250 700339856 700339877
    0x7060e010203070b0619080705180c040e071103040306050f16080f060f0d060510080d050301050904030c060c11071505030a0e0106081209040605010801080618330c0406 74
    0x4501200c0d601a1030a5408003c50001319080d00d1b40342145801412914010030245203481d05005890884144102c4044986070400031240300c0c1c1c608031030459465040d02425a0303155042100d07051002801c3d401c0d0b90000140001c10302c409504540e000354a92806402261070740303109030800403065040034012944d00000580d1540000c40c01d01e078031600c060102d20420700c0c001c001454000c45e00d20120341d41c980e07500a000c005915012440040d01c400c2c0300400000c0601035000d0524081485298400c411020002d03041502c1580c0c803400140c4e00c20010301081890b040080c040b41e074020715264041c4100000028091340704a09500848095120980b85481c1d4020030390242c500207105500640d02c0d0040090b100008000382e2000358400c15005d2780342e4401000b0081550040e51180781002105001441104004a00260444003500c0049945014001140d0402954a14030080240c20341001c0d006101080300240c0621694074a4a215641d0b07007100350054004c901070700c00000d081404 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 700342356 1250 700341106 700341113
    0x709050f010e0d11130f0f11041206020702130209100201020313020d080403140706020d030908042102060406120f0908070b09070b18030606040c05031504020c0307030c0507060e01020307 82
    0x3c0c2c820590090140b0440c0c02d80d06000300b1054142ca0a2056101ea07403542d00c400032003020300c107003018904104418043c1c0d00d8210020349881c000c90042081151844641108001c0203030704444c041940a055040080e002800c00802074000c1c68815000d14401c8490468103813061003260702c60140301601031b24034100c50302401382c42000704c1c20444501004100200104504804030459800400020810103060440c000c2c2454007a048201c00c0c10308000100b40060001001d03103090b0384110f00b010a04282d00b1761485411130750400040e4020100007004200e16900c29601d00d01245040814403451060716146000c5a40c8064050310400301404900c000031b10700740380070b03400000c42e20444d1070f80c544600000b01d0700e6020508050140003e07440c642c03c24101400b605030f010784100c4040002c0041c1c1c402c017902900c8000c040d2003088100c901c14030500d982c3e90f8150780940c00d9a80442e80c99100a213000703048041c18400686030b520407070f01c00103001441544e05811009041c0d015504248507541d = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 700343606 1250 700342356 700342369
    0x609010e0a20040e01033e01200139050906040f060e0111010e10020901110a0f021c11040213053102090a1701060b120709050f010e 58
    0x41140305034101c2000b03840300804210b000b0308040c040500709081d03a545985000c54480da1801c644602ca507a00100030041d40d1088200705844118440c80c00240d41340034401202d0b8080b092040c107000c440006251000384605510009400066100700821001c02002c42d91607100c0c820b1041500701c072160909400c02d0700c142c015210000e005440f540c00d081c0c44001807100c04084d5001000012880034407030034690380c401d19108804404c44004c0016070b07615641345480d002c808840e64091a000150085107900c81c8181f024000c400c10140d9080c8a1a49081d16160900e800c0c04d03803081010041c10001d0140c41b405500440e40d010740c82c2c1d50202688000e00c0040e401584010a03144003204000440ea190440140312843c03248100a0b0200980346000103002410701300840710321b205000009040e1101090320701a14039441c40e4a0303e000d00d0880c0180505201d0300038510440700415060415403c9284141c000c140a0702c4a111041d00c0f4000d001d0f09841e98098180018080c00380f0301c4084c202503 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 700344856 1250 700343606 700343621
    0x11040504020706090203030a020f0115060e150d0e1c020c18060a0e040f03081f03152d0605060a0806060703200f06060307051809010e0a0c06080609010e0a 68
    0x2440013060008040d0006070840d042403540318090b8010002002005500703104808005e408201346009850901c0030045c42d040d28480090f0103190103a4107410341c800c1ca03c0543d4080a490202800621500c03194180c40703080381c995036040d0703840780120f030f101650011940c4801c003034000c1c040004034640710082c5000c0a00143c0200d4000c03c0c0b00c00c0c00704528031124001d40c031a074010143c00d007103084603290040c0040070041000d6809003000f04044031505240038500c0850b500f11030380e072140c1c80948580e400101240081c4e0004180c81e00c8580342d01d10041c80342d44034901a0004100100c03581c440a200e000d1141d5400d00001a42d0755002881c20718010f00517000d203900910384403400d038078a40c040c4c501c00b01c40c99207002440c0c3e0050702302e8001904104a802c0d48480264054180e0074501000301d08645030504210750044011030003d00780c11025072080c0069031185c0c0850b8608212418010500075240c0100c03000590380c0c8000820074100210018100d0f40701c0c600071852a541c4450142c001c10740c5 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 700346106 1250 700344856 700344863
    0x901031220030f090909071503021b1608070e0f010620010f020429030f04020d120c0b0f0907051c06060e010906080f030d0b06040902210604110405040207 68
    0x1500d07a00804408100060704030b10500e044415030f11100c80003084580c1074002d108015a50264000f400104410014900f515a00303007001368603100d03820b0400010101807420308883c0c1c0300d144445c580300054000f01030100c54600c004d070749406440c1c1e1503c2d411400c044643d004a003502c5001007111a12824802e000101c08540d2403218407a00340b4890b0a44e0304e0ac02b400b04142c0c3c0c02050078000701450032140b444d41c04e10204420113101040e052007106000c001e204001e51030b02000003605640304c0b20105191180c4c80003030300c8081c00f40c804024000400161041e40d4101c40000003600d1681c0ea0341313032980144c0007140105905071900080041040d5000700c01c014911682c03501000050f07081c0034040150247d03100142107907040040c284111400307a0b01c40e40d0613510000810304e031420040200d0b510544503181c0840d9005060002c03400c213114643c04580c12034030005039280c248080c000440181d1080d141f9207003444d16003508010645208040740041c5440400c4100301d546440c0d4002c2c0a098031 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 700347356 1250 700346106 700346147
    0x2202060d14090a14162309010b071e0b0f070306080a0f05010507020106030b1303091505070330020c01060b1314010302070c0302090a090206041502070509010312 71
    0x40003054400c0300e0200341c40c2c1d00700c01c0c2d108540da0010040c0c04c080251502c69036000400300544140780080b07000340d180c4500301e01c00700d04014618031101d0000d4040c10400b0060503009003540d50310000d03111503101040c141d4170100350004000030412582001c00740c071070b00300150446c10b40b60703610044d20030702002c4d00a90601d550303084c0c001815a4280540e05102d07005015090000d06181000c3d425150005c20b44e0045924102c81800000c4512181542200003841c003090384c2d003840d18054032052080d412114400c1221450f15464540c0040200074441c403e550f82044120704218069115030004121800c4584003904e50a112415602070407680b101140003140c050380d40d4810031040c3e4446145410704160700c0c0c000b0b0100d0103400c2c0c10307040036500a190452400415407900c003445062404000d124a8841010424031440c0e40c0082e0716075a002040155126502c400c0612140e034407400307035009809803c03000902c61600d032100d24122078020f03e49640c40c3c44580e50880b1181c0c034158000e4031402 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 700348606 1250 700347356 700347371
    0x5060f0d061e050702031b060121030e031209030c040506090c0d1107081b030405150304030e0a0e10090504020a1505130303050d06080a0302120a05040503010515092202060d 76
    0x205603003d6240582e4050b00550b94a11a18086030282c580010210000c1e03449000100481c40e581da20005168100c40c1d11a240c00d0014a022a142d8080081550b414807401455041d150201c0006140803602102115a0a00c0c02800e002c2520070440d40c1540c02a003003800112400381060041a00002c25080090403954800c2c078609142c1024500307a5070304101048009020b80b41100002500169000440c200b9203058005121500b0002c0c5259011501101040405014803400d0b808110020407004070380351200114005540101d030003e0120041403000030380745a040c03040500941d0090b21006210f42000062489004024100700401c41c0802031105e41c0040c0c00d00800c0a148207989040d0742c0c110340d0089201303403802d64024188a41103464410001307600000c03800422500184d4803a291510034105603082d014961015030154280b0b030030414815580c051070f0004180858900107182c5482d4100000c01518400c0004d55100404400001d0300e02140541080c080c0c3c04004680b04 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 700349856 1250 700348606 700348661
    0x5120310030f0605070207050901141504180c1d010804020607170a05030402010e09071707020c04020408070e0708010b0a1d0a060807082a030a0b190905060f0d06 71
    0xb40c16403410707103500703a5503024803481581c14003401c00100002c9a07070740d0095061620703040c242203442000611440003c0020307281c040c82c01c0250340040c52080340240c2d03a58000d018840c0689200e400c4500002c0d00c1c26030f04036400c03520503a0012040010781d18640a039840d6424041241c3c4084029510403140c1180d00750180680d400500e05207003a951031903100d050901c0003400368245ca0a16034440c00075007040048559110702c44441c001c41d840c00e54031040d00c4500c0c0690414142c1000190460b00026011544030400501c03030301160b25021500050795a502811600b161080c05000348074030003040340740c030090303ca000e041d00e0034006844c14080303014450000521841c6660310020105222004104400d81c00c000f074103902c4800c042e548000307514070440d4544507044a0021a071702607000b0002c14014800c51b4842c0b00c1b61200035103425080348941d4a00d03d01501c0d60b200c0c11040d933007032000250650800782c44081d03c060010f03101c00ca10f0314142d52040701500310003121060f090186e688030b0018 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 700351106 1250 700349856 700349873
    0x60b04030c0f08010c051801210207030e030307050c10031e1e1505011d2709010608101d01051006020f030309190314030a0b01110a0512031003 63
    0x2940300d40e41c41d021079481c0034646410240280c0c04610310381d140039806003d054000c400c0340c50030100401e5240040284d240162404001d051158907a401c1c9040800c4200b0341641c010700c5040d0080c0c0300c960b84410403408040d40e9102d0080014003d422809400055042c401c002c01c94040050501141100c10b201d804211b8210b05c950542c100340c2c07100c0e2400801d240e00b0304500d80d6100300702130501c040c040240200004480b584181030400c4222190902070010020340086540d00040100b02e0f1102e601c00c03014a004040203e040450f2801c4000c610300340014400c4201b2140c2d40c0005e0001003c0030114203005000c0d000070170001076040704240c01d8072442841303120710580064544140480c2070800007481e01d0315408000c0c1c0294005c0050090301000000c200d03c0c04846003541198074445072508658400030406801c011807008414095040d500d900700614500080c6d81c0e0300300d01320900c07824540d50503801c20003914a420941c9051001103120000710740c003180004103180e115603241e403034407030 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 700352356 1250 700351106 700351109
    0x1050c1b19080d24140a030602030430020a0b100305031b010510050a050f040207050d0f080705071e02030c0a0608150409151a042c01021e0d060b04 65
    0x810304000a8000d28406191150245070860780c03074042075005114003000100313491402107401d01280c5580702021a0345151142000e164811829501d074142842c00b21808007001e100f2901e815001c5518100c0110100c0240325190031550040444148076203511403403010151441c080c0c50b850507400300c0804c80400c024202240c031012040b010043c841c59490841d01c0c003904800200c41040c00400803030780c035402c105040d19811206103400700b95880000707000780708650b001040340c06540801ea940303035000b50b4511404d025a4071400303580c4c0e41c0c4103001c55071441800c200070201c054034004480c001c6454a80040218400303401c9829624a51700081c50008080d03110400180242c400c025030007158985800118605481c00e200c00140707655001c62404840000c0c44200c0c1d507031108180c2c0c020840c800310742803c3c40604204400403600e400e07440144618002c8407180502142c03000a0f0700014422540000d005101c1e0494401500c980460341c0e502c65040e940f2802d480740d0010880b600300718003d10 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 700353606 1250 700352356 700352363
    0x1020c1203090a0b1609090e03090603062e08013002013e0304050f0919020403141c1b080d0204061e080108060103030806031906051801050c1b19 64
    0x4000c1e00c6000360080440245402002d41c003428048c0d10207040342c000040c0c521030b42d0105c41c89512590746001203201955550301000e141c4204403031040004240500b038103900c81e115511440301ea038881402c1941e04142000380401c00b8550b400152000040d02c20111203a481490542c0103201d02103060f6540c10001451481c0100100303407403c002c40c0c000f1960200e0004000007941c103040c034050010b01d900440c00a1140510f4484001038500180c0495903814861101021900c80e034980c20710600d41c01002e02000c4a52141c82400c00141e80800404d1001c14219a00c84280c102109140030f00b03022014822613080c04140007903a10412123001401c0946a43da480c43c0c080b803007031914641d4000002e40d01c04144861000184108000030411a041daa010b06058035a510740c007021174601007414181e00c00d4025601d141d0fa041080d5500181d004034118590b070100300c0c081144003401c031a000c3c1e6000f031a8520801c801150b500f0203c9040702120031010580f02a6000c0e42036846d2041102a0100c = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 700354856 1250 700353606 700353631
    0x2010914010e151918091508010608060708340c0206220e0903030703090804052206210b1e0705030f0106030b0609040e0c030304030305071401020c1203090a0b 70
    0x42213144c06208040015044516001508007900c0440c02101d0400e40034048141c0d44850400025a4400b40300f13000401003500200501c0b0350701c15000d13840d0502a070714003000030509000318491401586841e0401d40e088484601c0030008040c0e0304219548094024062290074001180541d460307034054080d0349451031400d9424810387e503401c118451143c1003150120490802d100c031041000056a510900302e0a00203407140c82820410900d004070b920113984011034030704801070300000704940c0002c90b099030001d115184e2241501c0120b00302101003001241e110480300c07004035000c1c98035550880540c03141044401c00101c0c541802c240205d0320100030640001c203100c1c0a2144d4600707280180340629007004229420b2000404511070b003034481c2e208a03220380c221031f5205400e00601c441200010126903480b544c1e441c01900c160004801038854440d54424080c00f0407042c001c82d007144502101405140e02e50700030607d11070b0006071a02c0e400348a000b81180c000760240e00072034010440001c10 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 700356106 1250 700354856 700354867
    0x1104270b0603010c0f09091e020a020c0102071530110703080601020601030f110a0807090b04060b0915071506060e090a1518110304080a0f0201050402010914010e15 72
    0x41c90f09682e034031541c1100300701d44111410850b590125850081d50301200f004140170100c0c0310240a1f04d0084014403010a100180c000c040075000a1640c904241c01c0e0266030000e40e580c041604540f0405d0b0101020400a000e48031842c82454008080c14051600034240246a2042c207421925401c22038001c1e0340001544809140d0090300e12a130100003440204010345c119903440c20a0320744141c00400c2c019141c0c0600040356100c195200c040c000300411580321035518500035015110782e00c0d18500943c5452000304407105050300f1541580c00103804410094969500164503034030007503080d145040d040026601502c140e00809004165540e2010440c5000608102c080c440103405072070f01310301d003a03d111360301b0010000400840f0203481c1318910075130000b086080130784010308581070001000002c200c00c1109480c040c11500784160b0307807030039100340700b00d03013682215800c1e42c0c06030104800c0042008204103e40c040d544000040c9000c48441e100341c8041099503140480f00d40e1075400c041107 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 700357356 1250 700356106 700356109
    0x60c0201063f0f0525080f0c12070305030a090501030e0102030601090b0a1803050708010c050c0606152203060e12030415060b0c06150109031104270b06 67
    0x1260b44064050034003079041d050401c04100e141002c804149100055500801003e00c0400032003012a95082010754880ca16066417508511110b4200414a200300300c001091110001032150980038442009011411004003040110080310356001c00074444c080004c070000d5402c3c030262440b1800c0f5152120f009041c44005801e462200c83c604078a40e106100b005403c0c0c1e409103140c4107c41816412903956203204200b01ca0807041d01d00351450780100740c0000410020300250803002c45403070342300030040d040c0d4400040352148200c4000400b290301400202c3d074140341001020041c2e801e5683ea80c1e10388030104003441311500100448540d84400c840301002070165a0140040001c0d4110181420101c2d0180a81c11804080c00142c003806c10390a000740d141c1d4080e030000c400703450b0034030500343c54001d800038503a90345400b100c07075204841e42c40c05030542c0c41d40900800001e40703034401d516800c001068000d100062880641080164041007422600e40043c40001c0403007600802251100d45080740 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 700358606 1250 700357356 700357379
    0x303150d030e090612031222022404032301060b041d040807050102040e070306060905220b0a1508010f050a1802040e0a0e0f0f1f020403060c020106 65
    0x501802010980034040001e60700c07000e11a60002c0444005000d074490b50301041d06400c03c40340714010b0b03200c00101c060a039048240700500c81d86958004441c04500d100030b4407031416034110002d4211054418411303400c010100e0540e0786d21912a1301ea42002d40d6500d4565450b008003500c4d4046400140740400c82d00310070301a010140915010b05881c085c03800080000300c00e0302c5061001e021030440040b9040040a00844040e036420500a54030b5985a159040340c40310f0a44126003c6480e00d20002a03407401074103e41c1c110f0b00c0040c52485c05d1740d000600a007000320f0b0709805000b4541c1d1045035001603031b5200b03c110301a000c04062a2810040000090444d140603040210b10a207004003c1001d687c40d40c07200c500382c07200d4040c0c81e4980184104140040d01454110f203210114840030024001c0c030030341c014621441400f046501e80300004c0b62490b220080040c00d01101e800091461105c290694004029000d081d54010314041c1d032501c469046480c02842240140d45440c404c200180a64 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 700359712 1106 700358606 700358641
    0x3070f05061c111c0e030a050711150c0106090608070603110c0307030503041203091208070c14010e0105010f06020d0305100b0c1005011211120a02030f0303 69
    0x30200f4064001000c4070455020511580420b440c590148104106102d0007640c6410807821084070a6840b07000c0944904482c210740c040e254075040e511009603500390800980703511440500030700b034400030b51140703a08030304180d4248013416003c15103000700c0e0a14180003030720b00c07901e070b0000d00a0f018801e8141880e00020805000f81504a0001c0d84154820104041c3e11800110244e007103514680c0e01400261024a0440c00c4500499803550081020b040030984c0701c05543d90070003641c5002d55031000701e13510350305903110b1080240503003409084455201c1c42c5d91404c01d00c0081d50f8400e80d070107150426449601144082202d50386d10405401d8003c0714950741c1011150301395032100b940385158941c1d4a44000001c448210401c01c01c4c1e2542e11000514001d1b0103074080009084120700e07010703102d004108507138005980401c005d0a0744000701003c0c6840e07103000300e0904c0700300c2c021 = true := by decide +kernel

theorem cover : BRFrame.Cov 700179856 700359712 := by
  have h0 := BRFrame.cov_init 700179856
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 700179856 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 700179856 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 700179856 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 700179856 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 700179856 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 700179856 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 700179856 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 700179856 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 700179856 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 700179856 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 700179856 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 700179856 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 700179856 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 700179856 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 700179856 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 700179856 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 700179856 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 700179856 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 700179856 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 700179856 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 700179856 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 700179856 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 700179856 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 700179856 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 700179856 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 700179856 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 700179856 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 700179856 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 700179856 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 700179856 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 700179856 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 700179856 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 700179856 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 700179856 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 700179856 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 700179856 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 700179856 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 700179856 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 700179856 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 700179856 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 700179856 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 700179856 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 700179856 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 700179856 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 700179856 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 700179856 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 700179856 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 700179856 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 700179856 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 700179856 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 700179856 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 700179856 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 700179856 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 700179856 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 700179856 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 700179856 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 700179856 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 700179856 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 700179856 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 700179856 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 700179856 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 700179856 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 700179856 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 700179856 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 700179856 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 700179856 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 700179856 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 700179856 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 700179856 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 700179856 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 700179856 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 700179856 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 700179856 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 700179856 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 700179856 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 700179856 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 700179856 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 700179856 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 700179856 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 700179856 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 700179856 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 700179856 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 700179856 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 700179856 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 700179856 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 700179856 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 700179856 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 700179856 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 700179856 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 700179856 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 700179856 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 700179856 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 700179856 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 700179856 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 700179856 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 700179856 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 700179856 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 700179856 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 700179856 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 700179856 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 700179856 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 700179856 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 700179856 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 700179856 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 700179856 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 700179856 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 700179856 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 700179856 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 700179856 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 700179856 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 700179856 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 700179856 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 700179856 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 700179856 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 700179856 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 700179856 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 700179856 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 700179856 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 700179856 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 700179856 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 700179856 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 700179856 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 700179856 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 700179856 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 700179856 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 700179856 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 700179856 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 700179856 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 700179856 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 700179856 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 700179856 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 700179856 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 700179856 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 700179856 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 700179856 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 700179856 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 700179856 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 700179856 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 700179856 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 700179856 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 700179856 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 700179856 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 700179856 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 700179856 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 700179856 ≤ n) (h2 : n < 700359712) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
