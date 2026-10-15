-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_5139
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T14:52:53.470987+00:00
-- url     : https://prove2.me/submissions/a98e2f9a-4924-4182-9a41-4d26b0c4902f

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 924100719 ≤ n < 924280575 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 924101969 1250 924100719 924100721
    0x6170a170408120a020f0d0c1b1a0c010e16082808030402040b150406030c05030609042303070813080a0b0a021b070314010e030c07050d08040b0a0f1d090a 68
    0xc10b010108620409808400f83e86c0e051107103e007440c500343c44406800010346010403554103030340b4030304100da40d00b01d400700704483c480d401c101c001c0d11184403020341d544041004580944901850512684034219940c2917400c8191107141c2150000000e44071160152086031051030546541a004080d1a2210001242c50074000310b4110348018000144d64003070101281a030000703460724021031440801e00f0409035826000300b5880c410549000c0d4658540200055000b05010700090081075489000002a412071421004aa0300240c1202e031100c4503440c0504a507401000c0520120f01e1080001894120008015040b1030707110340d0711031041c0e440c041e82030000d42011030620741404d00c01c440c400102030217100c1d11001d58041c071854441c4401c440e00550a465606508400660080000d2100d4000100e00c2500341d0b6403c48844070080b540f8200602280500d40044032001800210500c1d050b801011016141001d5102c0301010022a44c01c1d815044140009507005031810000509001c22 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 924103219 1250 924101969 924101977
    0x20601051905102c03060709050d06020304050f030d061412061501120603050c0f06190c02061b010506012c010c080d050c04170303240406170a17040812 67
    0x80c41c0380003404582c040742c1a00381d01e4240c13000a07220301044c500e03c4490781024840c4580c05112414100c014500d020042105004242406403e0340c5d40400071a080000901071b140e40025004101c3c3e448050110700c03c0020406440780b0325804102c020304401301d007050800951981d815001507c1240e0b41c140d21017400070105c0070490f0410070264800c9602c0302c050310074207001c0e42c05440106070b2250400144100c1d100800f003150f200b10800c1c4425419a004255614400c242c00e19140a00041c1880810020300610546042c0001c2c1e45c5581c400540e015880144511030982c0c1e01c1680103c0d844e02d00401d0348035400901941d0600800390461540282084200035210b99400c0380761043c0c074000501143c0e070540301d032901e04030005070800c040340940300c107034030b043c004c1101640ca141022481d80f10340103520381d000808844149074540c4140d45a902a100030701ca503508105451101d01c03200c80d01d60306014401c4500852054561071040c40400642c1c007074500c080c0040c02107010007100a025500 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 924104469 1250 924103219 924103249
    0x50a140904031403070c051009170f0409050f060913030503060d02060c070801020a020f0c01020604060b010e0d03020d030e0c030703032f03040f060f02060a0213121101020601051905 80
    0x46940f2465459900580055200340c00c507540f00200c01800d40f030864208410282c0800f800b90a0009a0000c14182e02c40c01c0c42003901400e800769103100c56940d0301b5a500403540802a890310b8a810403c08400711510948900e40c00c40c0e48128a070340d101c01c641c0c0224130300da6000d80001c00900c0094580d04000d5003000c90103000030461400c14034040d40b8549051500d8104044694011894880340c940400c4002c01c5400d07040090074606955500003176544000500107001d00383c588091207240c1e401440184610200034081c184409034a0401941d91701301c82c18898002450182242410400410740102c040002000382401e2840d40e20110b0361041e0052141d85c801c805491100802e02500e442c40d600c0010381c401444e19589000c540750058034041c0c4c400b400b44410f00030211210742d404505264014502d4400603120704d12240c0c000c40260684d0880f00030704030b40d00c1d102d41c144000340070070751214002682250400c1e0780b9032080c404940d02d004500307180040d40c6201800140392411100386490 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 924105719 1250 924104469 924104477
    0x809061306180813150c080703030b130e0705090717011a1606090c0b070503090111160306050f010b190503040302010b0a06050702040c030e0a020d2108010f050a14090403 75
    0x10b030310303510740b209194081850350580c4018000c0400501c06036034500084c50705107051075251203c49440f110102c0c400c4d11002400c159443c1030140e596070b10f000000c0b42c108014801000140c0c800d403849a038502e51405501d01c564061000500042d00c1003042c203901514503004040c0503440c01448075048030b0386519164040ca070a12034240041c0d29000290740950144c007000c1513100e0541071005001441e9004a802e070a400c00852003c54400003c80c0d81015003840c0058040000000090408100d00c1041d080118a0b9400005220b01c0da0401c601a81201320741c40201c1c2d0ba01c03001c0d05150702c625903a044081e030305d1408204001c0d002d00b01540d40704d030203030002040e20560b5000040003e4250340283c1d000c21408121311085d030406100340e01e0580c4490900304980c400c1013030340981e50111260300910a480c60002e042c10000c4a85842e810f50010310b05854540841980c06010320b0380c2406418501c01e01da1000040c94940008035008070307801202c5400703851800400303202003100e000744140c0501c = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 924106969 1250 924105719 924105761
    0xe062406160b0106030c08160e0a03080301060e0102120a0e01121107030914031b280602060402031005041104020306030a051203060a170304091e050403020d0809061306 74
    0x30030703842000c68144510a40c542240d540c18004081e04440b548103051042048810030011994a0000c400e881e0346e2a90600440c64900480007131441070103a040202455404000051a01e42000540040c44c2c0242c0942d0002d9482b07040541c10b90080340a0800007800703200d030310f0500754000c280c0400003014495010070075094948004116502000084000400a02d020000900380e60040c9140c1d4904601600345070b285558008064811504040c0c0b06581c01d0910000d1f8901c0200e070008003000001030b00d04159030300d240294980d801114240e000703000e40c54807455402c03401d00c01d40740b0581d40001240303030318010032081c00000e400040c0041d40620940c1072000114000300f05410b2000b11010040e5503e150000500091500d2644100070700c149502c80742190b020044165001e603241c2035000a800c24041c0104050340c0d000b4840d40000900d4003052206140c1e001c07401c241e00e800991981d0700c0c60303218516050b550702403c6408540a280e492596070014485070400107590251610715041 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 924108219 1250 924106969 924106987
    0xd1112030a02060417131a07051e0607090b0f0a050d090615150e0d0507031205040303170f071202041a04140103140f0a0915020d0e062406 61
    0x60340c0e0015400e88050ba00040400c000c00a00402145511854000c010b0500601c190a0203000c800c9010b590b00c40b01d400401b86a0100c049000d0303400c81e50300315044501d1040902e8000003054119104080680241c0c800070b044540105290030403a5003800c0a18607140031500d003100c0b190804440203007000000c02c00c441200c0b0070740c000d4003105800703000000355200701d42c001c0a02005680e8800c00107040400074243c2c070150000d50341100714500780c4000e040c02d5054581242031403d50780005003019404400400d8280c4d0140107841580d01c2074503020700e5050100d040745100342d03003120f071015543c1e5042c0020704040d104030b600b04d0100d00904405802d150b244d544003022004011070300c046414022400700500c003100084102d85807030a08041000001c18a5030034a402401441407070720f012018045120941d55a000341d01880d0072604e03083d2a40c040361088006984903011001c0c0842c1482c02c50156540c010400a005010086940c101c85004c0860700c5003a160a1415950000b428804411 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 924109469 1250 924108219 924108223
    0xa111305070f02010b030c062d03070203070303050603012c0f060c180d05030702060c070306020a210605061b070e0907051305100308093c010e0d1112 66
    0xc0030341d520303854000340030314448402400c4503501c03050148a5405809404810340b02c52044840c0c8040301e00c1c080e030b83d0340c10140b4030783c10f030843d104040c0b4120766001080015056001c07024190388d0384079a8050256445090401d4240c40f4071030740c204104090208008110158648610056102041690b5480c40d80f24980c505049e4100c5810b0b0710442e0004101642c00d0745c0b101c45c6070882c0001c0f030f0300021002031038982594900401c41c000303015440001c1c4003080f0b03403402c10902000310b92024042d0351305d01821030011b00c13101081c06104480b0325a8040850740307034164003550065130b0001c0d044030b08100b80c0301c248140071040c044051616016540300821040581c0400328441c04681c1f00900c482480c1c24140520b0001405104010300d14000601c034494844030a01c00480c0d03006100c3d5074031030f5884800030b90515451804031301c807a454640e03001d04511a440310b445c00e031550041c008182c111040d005407949004400c65039800b030124801c030f90003d910000d0440a0180c00b8002002554040755018 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 924110719 1250 924109469 924109471
    0x90c0b03130606060e03120f1918030c060801050d0203060f06040e0712020a061805010c032606031204031a0901200c101a0915130204050f0409050a111305 68
    0x4c0000710700740014599418100210301c5000788080352a443c148029844082d01d004418007024a0350400310310600c0c1c0c902c15000c8081c15580030700c240094a5a038900a046030303141c0d00c5460f000c0303460314000040a1506071201f4010780d40250181c4020760300c41f8641385820f071000b0103180d4070a96400000c03140c0c0740c0400120001d0042b8a1201c2107510300c9004102510000e90b120408100c1c2d07140c12403039075610307000090b02112820300b0b0107503100c000f51900f82e5010a100c00101c520303210318040104030011084a140c02204241c0680d120411480b0050070184218003002c1c200c03e204121070740c042900c0710015584040d680c0000a11aa0580c07143e020003060108007160400c00841c40c200702070814040181d8100e8510400c002814091011280c42a0030b1050541300d141304070002444500b011031080d03e548801890035000c05088600d0314001c6d085401050701a814010340030b05541000c1c410703040d040c0e401c50300408161900d07036501000c80010303500c0e02e5005280114a140c030784d00c1602542d = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 924111969 1250 924110719 924110729
    0x10c0c1a03092812090b032508271c02060403020105060109061704030908071d0115090b0a030905030a0305070f0c0209070f0504051302120703090c0b03130606 70
    0xc0c680e00d041501c1503070b142611030f00000d100050b0080d082064854003524400000d607202c40246031400d0b0010b82550100115440500ba41400100300032074102d00c076806001080704240c103040c540ea00d00c0012070b40600c08642c1110000004011150400c3c804400c54000c02d0b00c01003101c0e881e0014240e000e000d40d1140c10200056032001c0140010545c082c05032542c000000c0c03812480040c0b40090090050389900704d54514500000081028144a0303d103840c0605210400c42e00000e40e1a0b44845400c28080d017202c060b9034111002048560303000d59103115611855556610b0b80d07050004c40b10182c2d111100b0681456554402e0100086045c00541000000c4e17441c0081c3d2441c00345000380188a1141c040030410962404801c01a5560012250480c20600e40b450142e200040103881d184542d42165500100003542400c1d855095001445007003c490035a440e2078403050b03800c0c0c0542d0b2501d403000b0002c3d10525020710048120781c0c059984040003005580c070942c50fa0711604200c600726008 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 924113219 1250 924111969 924112019
    0x309060b060a03140f13032708030c011401050f040b03030d060e010302211c02070b13060e01110d05030a090602030406060306051302060702040b220b030d0509030c010c0c 75
    0x3540c0c6041c108505103a4810a20030b170180d001d03c0c0000000706175101425004017030100d034620030070a0b26980b4030020000c21501d80e400c942e6545500e44150f590308481d428850340d6091003403401d9954100b100850407036102818600d0480c40030001c01014101080b881b58161006001c644050342e075034040c0d00014000304080c494154110b0043c03290400092403c4514030010051900b03d60400044501040c0300b800501d000340c0741c0100b4200d042810741d500c03842d007089000c02ca00340721040303410340101140d4054a5000c550a40280195002d482c56010040c103500250240859240510015540009200c1c80054006144e5488a04a80042c3c8003591401d981d06014000c00501e403044581040300080400040030b282c1d800140c2030300c6010310080c02603031601086e070002e80b0f42a51030b4200d0103c40108210b04290120f2000081c404600e079940710b4410039680e029414050421144100000b07006040d060300500019a8803103a4804225001c000701300700011094280c3d1038058010043c240 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 924114469 1250 924113219 924113231
    0x190e0103060504050c070b0402060d060602030c0106080706050304170f0c10050714040902070204020903120706061a0403081b07081605120601030b1b070c06020f1b010309060b060a03 80
    0x4001011500c541c0c0086001d28a814280110400b268098440b11a0b001c09000c409513254400b103102d42c020300195100c02800c1032000310300d558011002c0c0c000300c01d09000801c10b803075595201940e5480707148108000307d681003001c43c000c1801c80240038001d08005d07011901d0910002e0305003100c0e5001200c0554150492201580d00e81c080c1e009840e000b11080c5003150802403032090300b81c0305101c0c0f48641c6841c00d40c001020f00854446030113442c030f00701c40202035400400b00450201c5442d4003280044918a243c1007000c00c01240c41c04100012040004035603040c58116030300c07590247d0100390070a04013101401440140c84080002c44050b14401e8090010425076071a615843c501c1c0b0b800039803080344001d01c907094001d000201c1e10f0469402000982d459200c80d0740068001d07118401408150b240020108140109204201e0071240c0035030869419030303c240f0026440744a0028206d502145d00e5000c828158802c0e0800c0c0e20580c003030800003c40416110008117a03510591041020075100c039 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 924115719 1250 924114469 924114497
    0x21c120e040c0801050f100c0501022d0f090d022e110307170313060204081e1b01030b03030409050a0506040513031e0504050306131103030a09031719 66
    0x405004141d00503030400e200f040d410200000d038880c050544083c0a03001e48010701d5425845110340c0303405240c01034000c41d80d81d9050b0201d040388600c90741e0b00c40070040707940c10140b2404030a07400700d84031403000100550038000751004110124051410682c0d001c00c406402d80d00740e200072500c2401c64145803009060f00c208040c000380550341000c82c41d2036590000e0084801240e40d00341d1040c0c0c0d81c4000a0115aa1b6440c06d042820030136050304098500343c408100070034842000950030120586880c40c0c50011450b43d596590766944200c1c000c21100501129002c455010b83c010804c080e000905490400352038200c00d400b161400c44200040c9503c80f0b050144a05092084075000100754000140c03001c001d4071b001d410b94000c1105444140144666004403038490340543e000750100809907029401d080403071000c5e03a081488142d03075940c40020503c03080e2a0010031a5480383c020b071298820345281d0340f03409090030203014070554071207400c01c01e488030350441c1e54034462101695100c07050001d00c2d034 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 924116969 1250 924115719 924115721
    0x20706141f050a120b0c040f0603090b060d030507060b030309120109060b0a1a090303070f0f2015030c0705010c080108060603010606080f0712050c0d140103030507021c120e04 77
    0x940c080b0380902d20480c0d052003120120a00c0b980c05a4120003100e041c0c0e10381804401c094851948218000e501c200804122180c2c1600f00e80b42203030040780f14010a898400c20011007410064006020803c2000800300080b1142c100456030740c00201502d04141a0300301103056540c1301301007404075035503402c8407070300f000842d200d40126000c0560f0481042410b040c0013004428070302140c0c00c0117400118002200b41e408008403580550721941205a90145281c031024441940b0b80840702c8885086d04600e0881c007030354403070f14042001403174600714078200400b1890651014148072050b0344c00b0002c1e903001c80e500340034000c4003c0b015a240c1c142c5624214444e42000406031666200b6414004c0400015911030250381e08802c090042e010941c461450a0302c6891380c20444c07403905403c2a080010100f1100f002d4502142500ba05100f54100300d2015401c19409002c01004034030103000e8240035052160054840d200c06078002d08160001c1d03100c034441907003683e00000005203140140122800c1c2 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 924118219 1250 924116969 924117031
    0x71508071b1502032d1501320403051b0a05061305091501120b06040e06030c030d021e010b09150a030f08040612091a07030f060e06041b0e010302070614 67
    0xc04146809418040300c0c120004601c0c4032a031f030400c00ea00582400046000c200c04c0c040d03030144a00c4400c1c074019001000c140d90414401030302c46000e002c0324107103178062003081a00300550040c03c00300c0d01810700382003012031341180c00440c110b17149654000ca015120780c07032114001c080a8262040740f5040e60700041201e00403442c400f580c02c1c1400e6078980c941d00c94100384e80503145c41c0b641c904450340d2a00042854120070f5203225905200382c04500f128650046990b104a04102c503202c840503034508465801d072402c1501094001c0741a200003028102d48030900c1440c0e003001440e801d0728640e40c0d02c82410081c2280c005031800d400004081010540080c0d01222000001c102804203a04503240c40c0d5400f540721010030234010b21400001d03070301da100e83d200f52007081c001c1d10100300c1c00b07845864000e841003086402c6401585803400c01580c0082c4003d4071224865641d444455041680300110043e4010540032250507484240340c0f0307241541507500328440c218409030345100fa02c407000c1500b50140 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 924119469 1250 924118219 924118291
    0xc0605181204031e150c030e030304110307060e0603010b0d111207030605010306030515040213021810390f0503030403080c030105030a03110c090108071508071b150203 74
    0xd44d1081e150005040c9000f850381d015203950000f610800b2803800341d0240c034220848c0c1c1003d010020420040050f00303030606240c004c044e021a0740050300c8071400d407003240c0000400d0f0ba1100042c801048410b1200004000c20000d01e035002c5500c3c000510458103503045200e0f241c00100c02c4d0701c1080140360b894860712001740001d28080c400146180c40e40d0307481c0c00d00d42c03500044900d1000005401e54481100011880c42c2000b0215940d4240300e001d0026030900052091180d4a1103529a0681d489142c225950070014001780154a1082210044000840340c0300503086a10b00340710008240e02d04d031100049400b4402841d90b07480c103443c00400343c1c14000c001010301041840180701c10b403000600d10326003d0307050405e0075031071480060046c50034404288e2268051310001c00880c03000000b140715001c4448a0261161f034280c0032809481c80501119044000b031040b12190840d81156200038200e6806100401c50040720181280c0680e44116040c2030702003807008040030799001c13071405842421 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 924120719 1250 924119469 924119513
    0xa0b03030f0414011e03050403020a17090a05040903050919080d12050a0e030415050c010e0106030b0703020a020a03050f120903040f06143004051b09070c060518120403 74
    0x40f9000170303920461000e609141c041594603000981094002c01c005614190070014086101c0340d8a406080d4550003400d1031400b4500300c100c002181e0820b030084100087d03240c4ca425007006c04003420301c46043c41400c00d80c2c0c9403045060000403813110038800d24110043d10365032286d94a41e0300c4064000c3c0c801c050282000c1c10300d030091400a110010040d241079070035420907602000c22501045400740280b501015840d4a0700011805404056002008a83c82030504113001d55402f00d0a034120300602818501581007082250700103803058004011000140e1591801c100d00c2c030300004e844a0007110340b0b059582c400a800d000211050036928020074a61a24021a01030b14008030b07200d016400d26100c001043d80004c0742c22010501e165007640b509220407160754035090a010340e0350311303055403800c1030a0b203035088903105803c00700d200c68480d0200d5114842c4618480d0f80300002050010100d410f890040030010151800038400c00c401100d00c048141d49a90460408581d41c640e21082c0030300356 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 924121969 1250 924120719 924120737
    0xa0c021009060b0a080a02090a020a02071d15010503010b03010e06181303230f071707050109030e0a05060316050c250e09190f1e060b0a080c090a0b03030f041401 71
    0x580c8c54400c0c040c0d121210607009611840030b00380c1a8902442500100e5480281000420200d1140e200710344c480d52a8100c0c444403c50301c880156a144800e0285200c10401000144100440c1d00b0030140c1144001c0c0c4a0405140c1e10140d40c400c013103043e190301c6010b52800480005041c0d015203464403000c00700d8042e515a8039981440c000034031540c49070301c4407244041091400e0001c0010310600d04034012040a54420407850624020100104120b01203202d224203941c85040c00e44001d4203840e00070f4240c03461a21502030750481c4c58286070100e4100070341048040f040002c288403030f0040d410144010b001e100c080204120f0095000d8100d82a040548000c00c010384800190815240e122890f900056520f035040c410340003010403001400c40c40c88100e0503208054010407950030703076004440800c50180e8074401c1200480b1140301e25140e541c05040c0d100300e9460154640c50b04500d4101d40020444814030210f0705540000c0806105113201043c01c0040d040c0740f01d80b110740e840c02460a6624 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 924123219 1250 924121969 924121973
    0x50616091a070218090601090c1205100b1c110a0f0c171804150602071404061502030307021c050d2301080d09080303010b030a0c021009060b0a080a 65
    0x44030092140e203180d1440504250440755129048452603500900356455015460728940300c002001d4a000245205d00800040c10308814490f07544115410750700c0c002c00405100c1200e02070680034116184218400c1e800064922a03240102048071301d41000361403100c2240b411008680c0003030b2801e10042000c00c401e24413140c1c0310300748610309005818040c3e40d2101508024a1a1483d55640301c1140e1000504014120344092502d070204d40846040c404401d9810b03513081c0442c032034030505c40540d008660602200f5805544801c0041004d8800641e9542d110340c0e280480c8003c41e00307400075070000004d10a0156041c040310f03d9650080703841d44004580404018180d104110a8498290391100206014542e1045021480e95146ca400310196141d0359800d03107400c50303803c403e00460090800028003000100540b03049618001d031080c116500c510320200a0002c20340440214050440001c00c0c0c0030751403188807015170044400184170564035080c454410219002000164090601400 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 924124469 1250 924123219 924123227
    0x2030606090d2406362c0f0c0f0102010b060301141203071e03050405121e160302060f04051503160809030a0e210604050d0e0d081c02070807050616 65
    0x74190611121481e02100240c0500340743d0600740c1105c0c4540c50400790340700c00d040144071482d8200c8034007166031444a016203020650344e44d50446041c010350451005010319150003481803800b1401800003191200010b40011030a5100340c00100d02c0e0008071624003400e040400d244d40504911000461500810f900d5a0b511640410b4505a0749403010b84040100340c402e00a5600814010b1f100c120003100960f0401d40780d51403151041c000c01200c1c4046100c2e030700300182c0d80d4924014404c2414605041d038082c040c003030748001007080700400100b000160a46840d541c000c0032000ca440100d40340e0601248050114680000b56002c02041c10305101d03a650020040751440c40e8a401c02d009010300c110042031030b001d2100075042260307444040e0218807420114050b442903104a06031120030400c1c1d5026580131851414107074002c01d07580b800600050340035005003e8200340134082c074071a021006002c0c09907809210211203405000c02d8500c104401004480d4000d08080184c03400380414400c010 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 924125719 1250 924124469 924124499
    0xb040617060409060e150a0203010f060509060403051f06080312070c060f0c020c1804050601031b050a15020d0801052409030f0f061305030a0302030606090d2406 71
    0x2503011001030010419580c0c640c0e1090070020380c000014410207828941c1161500768100b0358808101804001696210031407084906890251141600c0303981825800c48040d0005510507400400c02c002c04404a0420002e01050214481d00702c1684c9050300b40300020b5485a500004959009000300403250380c190650340d034003003002c0c6400340c0004118200f11018220b00d001001c025487c0202c0581025070104401500c41c0007541e007483d1740004041c11000c803640c1218007a00c15082480140001400007100815009025100d2004143c4800024811042d56880004058603001807941d103140c042c40781128072050307400c00d40c2c09503150801050303000c000b049500ca1880750001c1c3c40e102507048081075070001507000d02180d80c04800342d00c01c1c599509a040ca641c0c460312401d070026058100d100207201c0443d030302030003460821429035810740180d00007410050f8809000d0141e41c525485a100c14550705010b62020103541c0c0d07400c01b0a4041614494083e400c15044c14800d00200e12441c01c05 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 924126969 1250 924125719 924125747
    0x1701050105090303070b070914030601121103030403051f060b0306010c02060d060b03041505011a121305030d0f05090f030702062a0f010614010e10091d100b0406 71
    0x70b6650304016000a0031885040c200401840b00740c400d00c07072100d510007e107109441c1540280c268400c074510400d0b5503041e0900c01e0103031a10010007540d00191002900c0300c0004d501500b03da081580b20b030340d045d0030b016901004a0fa1440303000d001c6a0440c0282c020000103200b0081914034508218000030070316400305c1c5003c2e02440307000421404a000c0b6910480040110342c03403581c0c8a0400707242100108014146041d0000d0803c030000ca061a60010100348840c2c10002007494039590b401c0c0d072516041e00800b2040d01c0324200f0000c9001c940c2c20300007000140701e174540c0081c60100070174890341164000ba0440d40e455011441900400d2000421101d00c250101c94098032401c49040c00000481201429142034070700320780c0e113a800e0340c00042c0c0c418944040300013131003c0d0361240044001030000c850b030306000810850101007903041500c0215254100c900e070045035a03071948591801244012000c8103180700c1442005000d4240282c2000903000e881c41c06e40c41c1c01d261920080c84142c103445a = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 924128219 1250 924126969 924126977
    0x51204032303072f010f050a0f05070504061d0409030f02070608060102302b020f0f0c0a0210090824181c05030109050a050405120d1d0d0f17010501 65
    0x4071002a03904803488411030b070180006c0c801c080b0404568005410196540911700d810301095403141c1c81640039491150020395512400c0925114045810322030410350307458040d5080220b41e49540740c0e4080d1540d800e00030b44824441c00421140286040c405030710280c1003000da5814403051f81c0c0c0c04140155202c4040490441104054503070f00f030700242a1303810681c0946c0001c3c04540100039140121000000780400131b1302c042d170001084060744580c9480504603502040400c0c240021403000d40340e440b0015044561004480c0e02240c2075150003218140821501c600c1084121000c102d54009074140301403501200e001c0350045441c4000207070425850111000c60305d020346034200207802031038607070b0f68010307070008101c2170040c01940c02030054035005410040080c24800fa00d0083c40d00850f4414010620040c19500d8030104d034005603900548583c5411111040e90385054410b05642c826030041d0103442c90194002c1e101d80103a2100005001600ca1056880c80d1103640c502c2c112142800c1c = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 924129469 1250 924128219 924128267
    0x30c150e0f0a1214070f1a04050d02150c070308181806040c0c0804091b030203090a110103200a0f0206090312060f190f080114130305120403230307 65
    0x241000381c43d07402c020104654440d002c800031b0b0030620204008211200c4000080c50406c0c1c103107002d8503500c1507005058101101150810050a028198030b503100140e800c103508128150303030300b242001c0d40c1e5441030b1807440c80801c1c04200e41c154030000c1e51280e4811200d0050382c01c65611301118a6000400052280e03a986c1c0c4c0e405001070150718070218a40cad101e505141d41e182c42d000c0030002028150709072810302510004a8641034084d200300ca004d0301a803001001c60030380715542c2004c4000f084854904054480642c10b46100c0c10768121806004039206564982c03d07821002001e407003d0108220031513200900f8004881008800c59452201c0c1518140081d40d5600c0820611540301c0300f419000a880d1000712154058002c2d07090a54180b0074a24070466541d0002900361426504e2148851000e18040b0740500d900411040b1010310a091881c1490b08420400c0070790003044134160003144420780d0b56421a007038141116880040f0211050440c186404003c0c0910741c021070100c0d400320042d03 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 924130719 1250 924129469 924129473
    0xf020c10110f0d0203040b0610050316180603060e060904080d050a0605101112040b1c060512060a0f09111002010b131a04060e1906030c150e0f0a12 65
    0x300841c2e1030000d1815800d6901c04499500a0095004030380036909003140c040498030f00c0c5046c0c03035003590740015a500d40c1d040d40c03a101c600d018032a0051182c082403144000c0c018142252004118001340101d481c00503269190810700c901540005040c64405c090090411000580340b100741c0c0c10b4170354110030000701c507034403c10008000e210360f03005540c0c080015840745491a40c05900aa904600102a2904621b94008400c00c2e8025802505000c43c01072042a25902e00810454481c01c80100c01148042da29400b044164a100c00c0a50031500003004202600c0d0b520301401055241c004020031680510384c076140c01450480c241d0b03921820f800e08021901e14406d40000c020510000d1000c00455008150f400042143c01003030070241d101221405010310349032240c039048500701c0c4c002c5a001d03600c0782d500469000303805244203595956803002001040140c0e60303c0c0b026098134000f00f4241580031b8400b500507012200e0705e501c0381210018000c0c2e6921003d0a400445001c8203448851403994 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 924131969 1250 924130719 924130751
    0xc010b0603010e16020d050a0309110a030c080d080c040e09150f01080712050c0d0f08070507051e0f33040501030c08010311060a05040918060f020c10 66
    0x20840550301600100020034400080c44049000c0c5402c82500040741e0f40072001607072940c02a403802008100c041c014111901e009070403c1190700c0c807494100d9008100140010001e1120350800c0c0c84000089030140562442000948203001e0705050401c0f280c541080300174440d110b01c2c0140705418800f0b60218442e240204001701ca451400b86200e0300701d14110404100d000402d12400100c1d200701140002c0f03000c45190507200c0f440d0801c0c058035056050b04140502d51181d507c6c201c03010b880e600b0104000c2800b20000e0090b20b03100300c0c054500d542c903140400140c3d000c07407100900c141001141541603991006841c0020f200c041d5951442d54802540307207100c01d0450350000c807442301c8044001c10300c105110020000c5c0c070802d0700d04010340b0740c1c1850f04880b0700348240401000142149c2c82d8261510700800600301000141c0f902e58a40341d20382d101481520340c543d1a1103034001120980004100e20f900405241000d002011410f060810062940da0309a14508400b515aa40c40400c0d82d0415 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 924133219 1250 924131969 924131981
    0x140c04090f1d01151a160c0e040b04020f01140d1109030709060f0f0803071119091505270a090807030203041a09060f030601031413141603080c01 64
    0xb486507800d200320441601c1902900d0548841010840d050202168107061819203040d690040300640d810803a4280031000b00c4405000f096880c07055854000409107101c1c0e0748148030f148640710fa00082d0515105000d810690000914140542c0074003813480124804183c61162384007420120741c604501c1c1030304065101c0e610045426018403100460000b40d503401220844440c0040c000d0740554461070207400d0659402880500e40081151030041000b000e08038175070381c0000b000e0700804130549001d030181d8000341d030101510507100c110035a1002c808420b85d400801e002d88100060b184003a040800800501000d0b944030000540031804c844002da12086042e58845101e9075200a2030901a58036045032285040400c00c0040942d074040902d0203558120a02800d840d003080b04111440c00729820040c441410160b0b521540c09000000043d86801041030700414110100071781800d00c40302c050f0030741c144440e51041c000d0350315050031040202d085a411654150f261031100c4482405800 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 924134469 1250 924133219 924133241
    0xa0c03090e09070e1302030304030807060612230114220b0408030105030d030603020a060f0e03060403081504090c052e0216081c1b020a1503140c04090f 67
    0x210400402c818034600140d55802e0700e40083d203e10066031071040d030021024010300c0c02501900188003c1002a410743d01a000c800d102c2d400125006441d407010300d0003540c1c1004161150b500c01e0504c00a4140d05500320705002c64218020b10000c685a0a2401044005010a00c4d0356580e000c11100c2406a45944448543d00000d100305a043c80d0070440303c0e0350020b002c2c0c1d038881e0242c5d52400c0450341c0a072041e5400c503503000d00401c60492411005607109800c9000c140184a240e41080d0039950341401301600c514425120681182170036100141c0f50715a8042a5004074900001c2401103880705040004441e0300720380000088200d190318074003a03081d5450400a415840007540325440d0040f9071301c43d443c0c103428403480107144d4411303031141d0b60241c1c00500004041c04d03050400d01b0511803665052140590880240c0401c0c8a601040d2501760310b40c04903a1500c0c0c0c4c00d460742040e6505014078182c0d038801c030100b1011802d050001161501c60303845a5000c5039030380c0d0248030800655410640d1655 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 924135719 1250 924134469 924134489
    0x101205010903080739061b17010609031b1502010906180f140307050312010302240904050411120123060312091c1415270a0c030c0e09030f0a0c0309 65
    0x111f6044002c00c0c0040da0a42c915000c912441080c40341c81d00610001c9048440304d039a4018840e185840e0208407403a0200203e032906020000420b60303801c1c039a072011490f5041ea000250b100032505081003147d1203590311905040108100e0404648242903540501703401143c2c2d16505500305603400d1441c800c0107001400341c0030220310041603008155100341201d000b07440c01c01502458540180c0b0340342d2216641141420700303010004c0982841c0e481141e0180c4128620740c208000540020000944000f180125a440e10500c035510301002c0c00c01808403400350101410750401c500000c0d111000d40300c40100c11070011514000596400c0d03410019a5460304c110315481c4071a042104810306039070101405403242e00d004400c007160f5034584034070880c1c0d4010360400030f400f04918501c03440b90a500d007a019100b000c0d00c0801280080101e0340043d4420000404241c1c80c5c141200000c00c0024000c04460300240861003207a80344a04641481c865850041c80208503481d094401390041d4014203641 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 924136969 1250 924135719 924135731
    0x50a03120305010602030306060301030b07090302060f0d0b100531060f03180506060f0604090e0a0c0902070f06020c011d010507020f010e1510120501090308073906 72
    0x80403254000350400d209596092001d40e03250403081e0782d030344810303548141c000c4401c01c01040411446200c0540289440c41c0c00c01119617a82c000440640102c44e1810300000c0c00641002c0090ba44c0c81078111111040e94031318030b4a1f0201c2005021800303108060b02100500000b00100c192250001c040c1280e0319446030341c400d9844450040010030f4218000e4082807030500c0055901560301c0681c94201e41c00401096980c0d80c28040c450a681601c100396001f980900010030a2483c1c0c0c01064944001c503002000c56018600f04460001090781c005454113204000e00e01c04143c1d05041c80a026810001c0076036104101c40102d401030108409004944c00e10b008074149112040d00114020292175013210281c20202c01c2080c00c884100b401802e02c1da000003040b0384910708910707915030301c04000c52610700d00b42d507101c544000c040707090740e0111040c2e55908040703020183c009808542100e03240c9006841d0201c0211181801c25600f50b181d01c01111103404541e0359170302e0000e40070300564032020912071 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 924138219 1250 924136969 924136973
    0xf16030b101a0d270303020f090d05060610171f091e050603010606090905090f07060207050a06110c01110709020a0504030b0c0903060703090f120f0305070f0e090a06050a03 76
    0x4641004079000300043c1030140744400840401000080508120084d50782600a0366080d4001e61002c003500701c00710380521501080b5518140b004c03041038019400b510003840d14008000c50f0f020034510314018880c0c28903061501c020001511540500304080b04010080300f02c244000f084654dd2083e0005420300011a440a4004000030741301e58940d4001d0040b030f20f51401705400d031192405107000080d10141704214030314050700215004407903041500d1a41c1e0700c98903042d060400c01d80015016038002c41c81003100e03041034104e10b001440c0514000c0c803c00704005a464641d160501658108003c07820884050002404580d00070244508115030354400301c040a07202d900540300681e840019000001c003181020801c603480b1402c000c002e042070760384040e002e60050008490941d040190b1540701c1000442610b8100e0060240b6201c1d9800500804001015200c0040c0018104500366192441c001e4000403800008002140d0305050b0390f840010300d00041400d0fa0041c3c6c5c0c01410302d030340041 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 924139469 1250 924138219 924138269
    0x1106130c050d03050a0305010f1203080a060e0103081b0102160f0201020f0d030b01020f0c0d02090c0c011d0d0309030909020a050f0301090212150a030f06141006020f16030b10 77
    0x17106420300d8034240f1880c1c1c0e84401c031140d0481d051181d102006000000c0b100000e210743c6e0010b91080b814600018450307151071054401241c00d070012141490001500074480b10618034946100c00034000075031820248502c520785081c080c0313030028021310030200c1900442e802441408800c01c007030012142ca1708038083e00100a846020310301d9000d40075040303c100b81d08402007580400c10350041c1170400030064a6003070004c0b40000502101240340144105a414a000e000341c090608000004440060f0f07041800c90511104411140500d49042070800c0007039000a402c81c11035209001c0140c0b91804105c5c10b5803a4407075440c08584000001002040b04200b650180040c00307088000c0352034554a034181310034854118080f042c3e1103c142c08041000441064100e06103911034100450b5011070340d00d40412803041a204003c810031001000c0c0000ea60401001180441940040c0f5030441f0480c0110101d41c00350002034191f03018100056403810350180410300038861628540d56144004034111 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 924140719 1250 924139469 924139477
    0x20d0f1a0a08060c03070c020a0315090b18060c0f0705010603050f12030c0d021605010c0c110d0305120916030c090b2d0a09180507061106130c050d0305 67
    0x203205207440100402c41c1000010b2041c424240d841041d0300e980c45004041e82c2c002c00e50705003243c1c800d10041d800b100040070f6850010300078a1400700810107000d1803500d12a4940d008000403d0b41d0202148101014000105150000c0d05092855958043e184840e81140f20f00740f0003409541c20b1420020070483c000411300d4420000d041607030a102c82c0000324074440c2c0b006a030740d607407040780a1094989510541e801010b0520342216001e20101840d641c080c01c4d141614614408107a0404d0300e0b40c00e124106a80b161041000c4480b2201249640e5000d011400307a0702c1100a12054040040c3d03850608002d80000c4094170103290718030503542d00d06846031041d86c2c040da080c09400c0012600450620000140910f0001c0310b20800d03a03c3c18030000321250644010723641d40b0011940000442c00c1c00e030310031000c440a200390091083c42c824280301c0d1404607241e100c20100000c1180c00050b021003c118183c01901d03802c40d00c90440c40900300240c220582c0d40045a025004c40101820960050010 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 924141969 1250 924140719 924140771
    0x3080306040b03030429210619151b1a091c080a0203091204090e07050a12021002010f020a0806090603160b0a140a0c1e0203030904020d0f 61
    0x1400000c141c201450b44034001c0b8813818034000c0c080c50009859a2001e14940401d506c1b844046003403003081000b0b900c00c0d806c294140a6031654240c180301d82820403c501403480881c0d00c005108103460280440000901102050200015019040348290504044901c0d90b90003406440620075035140081d00c488069030710b0410340c440d0b011001407840c1803e244c1100d0600303584034005103139103141259000e54802040c501050140f00038440c1750700c500c030303020300043c241004000a840351190f115500e4080b0b55002544030301ba50002c108400d030840d451502c1c0c050341c140d8000078080d0310705500380c0c00741c11000c00c541c0900740042240383e10355910160306446002d08890700041e540b2070805143c1c41700c40d20f040e566a41400300e9414050158918020b10003100c451a142024403042120041c2d250081c13918000000d5003510410709002c1b41040c1c40040a200b40301440e50501180d0000e59241300703104025010f01e80100d0342442c400d6060744100d50030000c8040502801c284102d45110b845032640c40 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 924143219 1250 924141969 924141971
    0x1060f11120a08130302030d050612010e030c16080703060e030f03040305070213020a0c110f0a18140c070f0204060e04060e060a090807060b2e0318050a0f02010302090402040308030604 81
    0x10f0003240b0b80c0600409005e416801840c03a001c0f200101170301800e0010030380340c0c012080141214020f54240700715a00134018802458540f8080c00c40070381410107802410400c1c881c81c1c2400e0103000d002141080441e5440100022500344410103907046018240fa041b82d01a8040200070601d5007100040624603c2141e503844442c1c90318000c0c200700c0c000c030701e071401c0003650590441d07000034480d690300b20707947d10018268030081d02d00c140040d00301491500045a034044000010340c08240034003455681c0724008080340003e1820b21100310703c1c1e005248000d040581441411019501c981d40315070060544031b0250381e004d14182c00d040c40a0f018507050140b49204000001d0000e44180c410b101e051940483e101d80740649586409018002e40d621040d80070140f0b03001010380f40c09600580c5111a807083c441c1210b0f004a0300d0150403581c04c1361080c4514422456400300050002c180c101e032255202000d1180190f103030004800a020350036400d5000745c80018040705114018003d14401d00c02150 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 924144469 1250 924143219 924143221
    0xb07030605132706111b0105010801110a05031e07020114090d0905041125120e010807120e011e0f0b030606060a031e05041101090e01060f11120a08 65
    0x403151040f40c1400c46450f80c05060b0540b0726068075544120a07200c0d500441c000300301400c02c100d1003400d95101755141c3c0c05040250350359086040c0c0a00440340140a02c0000b00003000341880d5440b4140b180280702d104001000000448280b2032140040a44140c0080040d080c50400e60180c000c281701800c0760b50080c91200003c09034400040c002c1590b500710f98403a10002c3c0b40c0340901001e4481800b1000c0e211800340310b0b0310b407588e8655400c2c3d40c2480e205180000784c001ca0341400441d00300c584020b0020010101c11501c0240d800003055500001c4601d00140c02d5100c4e444c41800420019840341c2c8907500b40209903950278a0f0074090ba80b0501070f1401005080d040c00300150880b84034161450b015085200000c0e01e525102002c0c00c1103102906000c0b400c0c81350303410038240c00300c000500891019520070a002c240b00040e032142581300400e00f440702c4500d090820000c4105c0051040b1000c0020000503200018070409000040500480c1200c00c07a20b0034031184d4443c1e800502c50030001842c1e0070 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 924145719 1250 924144469 924144499
    0x7170403050a032d090f0506042607080a05030901090210050d06061d09040f0b010e01060f0507050c0411041e05042007020906041e0902030c1206160306030b07030605 73
    0x80850441307504802c0000344600c11004031800303400d001009807501c1401003800c80220b0014084e181c850342c4280000031074803406142800403200c02c0a0f600040c2c2800348040790004680e5001c444002089080103a182d559a180c2035024200801c002074205980c0c10000a813180c00101410380708203548010720600707440d0700302160000c610342c200c0d060510311020350301003034141268091340250003016801c58001079621010881002030340800f54400301c0c43c004007c03455010140e000c0b5440e4074580390717240c985141c9455a5504c6004407152090391381d400c50421010480040350010058038000300d18580300d180416150705400e1040324016801d02500d0400160601c0d800d8400340301190700103052007819001d102d40310b4001000d03990400d940c0c1c2180c05071815915450700c074000d0011004101c00d051441490b00701390401801ca40a42d4600002000509002c210300c0c0d1f001040541400914030b06260403800b070030b0164070142131810303040144014154075421903419598141c0d040f81c0300803299 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 924146969 1250 924145719 924145751
    0x6010c030207030f081207110c091905070e1c14060603030a1103090a03050c010306050f061c09080c0f0706051309150f1d01090c0e0907170403050a03 66
    0x4180010010780101a0601c0020240820f141c0c00f030303004004a604288008801c0303c58501c2c251842004919141107034051002e080105c0550013100340c401213070700e09020168010b1040400e550412060325003002805240c441d11410340101c800500c0c1420383c40c0e90ba5054001c49400f2842510421581c404200d1b01d000c0028484c0d010303032801b40045180c000860811512018003a542200501042050b03404a035545414540994068009480c02801090025007110780c5580401c1c0102c4203c80795410f83d940b030401ba21001d03000c05d40c4c1d03c2c02c071140b8a2100c5d00100381900d00207113940c80219540402d5803000885010742c106a504031460b0303544a480c1aa1640110324220001640f150070a0000c00420740001000d00ea6003425240b0050311810080340d10002900b2040303c4481a803c0c180b0220b5a0004141c0180703440d403010400309102c1d020061560b164402110f005900c418040303610382e172148940d0b00003880c800c001504035061030315004015a02032118240041c2c00d08182c4036003580c003 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 924148219 1250 924146969 924146987
    0x7080c010f0f141b0a300f050a05061e0105040302040204030c0f23100e120f0106050a050a12031b032105100612020c070f091d0c090a090f1a0601 64
    0x4c00a48500300b5808101c1100c00307842201c640d001c405120700300c04803050034000c820b64540d4800400400d0341403d1407143d100f03d541c0140800a02c504080600c00691100240e00380510350500858003a2484040140c0b550310440d0300081d00300b8400240001407103540c4840314191011000400040c6507a00c1d51140b20100111000c000039015100c915064508006c401c5040d0103581091a05480008005048000200600c521a411250340759000c2003085c81558060318040300c00d1030b011400c0101080c110701d500cbc050030003e90851121071060502a41c001c0881c0c1c040e28104d090100300620300200b0b03c4d800710303010040088800e626444100c406004080c071420b003101c100c6603214500081124440b02c95840303841565400c1015560001090049401500d20900411001c07860030101c0c1080301c5562203005031900c8101c070010303000e00010410415000085940e003440e81c45074040c080040c20300110003401c00d1500d00c044410008034220803903446080440d0001c46039240300054a2400c5 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 924149469 1250 924148219 924148261
    0x3270a080a1104021308010c0f02280b151c0312050c0a140f0a021c0305040b0703090302030405040e0606090a0e030a1101060906030b090706021207080c010f0f14 71
    0x485402c4580e904203a40548004a95091146545903403502c07481c0c00c407802e0001560004e08880c507444407480d01088030b030101b040c0c41d4800400d424007810426105003035902c1d0041001c1600400f161000700e00b2074604981c0c10004010034601c2c0c0c074119400302924a0444124046048128a803003101164441e040c4986400456246030000d001002c85403080340000c241510311041c400540c50f80030303c10140c00d140ea1190018007290599039481d10400690b05400340406d410901048009038020f09815000302c900d00b804503108401d4030b01a030541c0034580240c0d03009071522100c0b01200c0b50000c0d4150060274251500c080c240c503032061200a0b180ba0f10100070172540700b000f0440d2400c1c1f10f000007806020759000009a101d443c0e843c0701c42583e04c164800c1e03660b04081003d0151000041c0000b00003004c06000038202c1c1c001d01c07484802c1c680142d10010348850f4000c1055040b0110a401c1481d0603e65001c00b0060034007104920401004542018424020300030006001d1a1380c00003400148a = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 924150719 1250 924149469 924149483
    0x90c02030301060c0b091204140112050601021903111002040603050610021b0402071502092106180f010e07060e040e07121a0109090605060f090105011103270a080a 72
    0x80042e1102400d0240203080b61400307206550b03090404087d5400a440504900c040903840c0c500300d24001062148141d141c1c0c1c5a0703502d84010f1180c0d50303030001030310091f030a01d403080f0400305202c0d400c05a86100c800b6080000c2070094007101d403c100e050354000c0c025280c45403800c01c104e80b42c140034401c1880305d102620b409a03003c05002409070300c11710f445400c051801030000d0318051003075881050710030003c41103030480c640200c2c80504c0b03858010b01011041c0c04021360b0005889844c41c19513130b1001c0c0a00040011080e041c04100f41707507c203001d800f0010b20313840005c1c000301505060741a0b440c2c01710701c107a0001411814082304a0700e841c0c0208405002e00c0c100401c812030074080c14203101f01440c84111035400d03505650255200c04c071000c840c02020f032000d0000716100790381407400a4a4005040a104040c10901c503149695107050301415144280b8005580c080700c91441e41c610b1280340e00034904901e001c402c10464804a0358805c0031a4007c0d00c00464281d6100480341e910705029038001c202c2 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 924151969 1250 924150719 924150737
    0x618060c0e030703030e030307080d2f03040f03140304050a02100302041a0904330906060c0b0601020f070b0702041d100c0507020402040b03150a1d040c031704090c0203030106 77
    0x824844c44628046c4040107050700d00d0401140d40f08001035206640750015103488a1003400500c0c4020445140e009440c000c240440c049186000254400144010800f910402e02100dc2c1882440c804180011440109540381803d0802c1540d80319507a4007240710340b4071510590b07030f410f103e8002c0e641115600000003144565058652109410074001c8a4105550b82c0c0241c00200c1382c240107941c007080c2c2c109404010000350000070050348160b0030618030941842020007402e80c1c4029075140807034000c50610002e4540100407410405041c200c1c5801d07108640c002b0840c102554003c050152003150100a0740300001060504d040420041548940249a01342c0c0e280400d030304a6076000f1094035000c1e01d0090250300041c100d0300103030481c086401021041015400c9111b80741a00c014084410341141898000881c805081c01004840980b2880d00400c040180030001e090196501c80103420071020881d20a017090b422500c680b012250805006201a03400841140e060f1445a0f45111070 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 924153219 1250 924151969 924151973
    0x151f051e0f04030312180f020105031f08010b01021605090c0a11070608012c0a110409020f19090b0901140904050403110f03030c04031403070618060c0e030703 70
    0x1403061403914034118000100804203101c04a400100b0242d031090311040704111001800304119860840524035601d41c0703500d45c40104482044507244140e09107000343d50b0f80d0307501c500c3d080300c0c603400c0f00d42640d040d0300d0600110f00c030107041d082141000d0003a0b00704d40d824072603030307120b1096011244240d03508007001e400400c0501c82c0950040c902d50300b00382080d01884005843d414a400c509502400c0000e40c08001440884021f0b2100c0b8603540320724500c14418100d1102844034500054146c4084035500c0c0b0b044d13012005c5110a640092200340303021525422500c04030070039580501c107040204c4005644920800303014079800029200010001c0303050080705001543d421041214595024000b070103840030a660b20b00600d8442c5101b641c415043c4274240040714a0a180c1846c4403546810600c100a14025030300252811203402209601d010758209040c2e50540c4140200074000b241009813640003a003103000002d0086215140400560060130301c2101c002c2290300d01c880d4107401c21201000 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 924154469 1250 924153219 924153247
    0x1180b0a0b070305120907050a06021f0f0b0d0501060501110a05100f09021c0303050703020c030d0b010e130504050705060403081c0e070f030b0a02031b0d02070803151f05 75
    0x503000b840f908080740390800c8460000b072050022a031542c3c0982c000401841941010f564000040510b03000821164001c0100250300c0002d03265281411940c3d40f80005282d03401e0380224607001c2010303051019070205424070303074040c1c100c902a0501241d1201c4000c01d45020010300f80ea9402d8002c009814541305000c62500501095880508041c0c0c880d00d04501598940c1600681460f4903801148070304c2d5286005000d4500c001c0c8541c050500c14001c8402c403220100c00c842ca000406d120000c0c281510b0801030315004003d98500da009280b0858080d0350698035400300c0c3c00356000d00103c60800d682c1e1004c201080c8210301008005001c1844044c0980803062054440b401c0d8a64000c10030a038044081e40c40c02480307500c510031303050010100304144414803a0301d91b000442c0280075850b618010381d18460540494002164808000460020200c20765056a100a0b0b000002c00da6906240300340100c908207541c3c03583e12034176400c0600101d4206c980021110038030640c03549410403001c0d05c1c81c80 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 924155719 1250 924154469 924154477
    0x1201515090a110f0307030b0f03010e15090f0312070e090c040311210312370216030302090301180b0c0c1c050c060708131e02031501180b0a0b 63
    0x183c0100d40074821010045080383c040c40c0f040119582c0050410710003010041c4072050a0020340c005c3e4581b05a1441c2034002007910380c181d400340a180c21240d00e411400610305000a0020803ca010210300b015072000c0807084540608400d0350342c0c10b519003a000c20030081010544a448407201c04002c10070000b09000c1014858010007800c003107240107280c0c02c90352100f1031030180d00b101e034000140356000740712180000d5400100d015000c240080860046800000c2d9a0150042c0c00b4665018003113801540e40480700c1040e2189000d403c00e060600e8040c1c0030f50042044148a5400e0100d49071551140400041035140c000b004101a0f440700c0346d011070654030034504611240520346001e065480d001412440144a981d10503544030451450581000300107070414003042418010300a04010101040030300b0b58011038111124500c08180200c0ca0205040080d0580146404820801204254a4100e0b070b84c015100070250850116941120360320925954800807428080c011100080050 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 924156969 1250 924155719 924155741
    0x170c030708161e020606120c0901050910030c0b0307030f1b140f120916120b060f03190b010f26011805060a0c0503070512040201201515090a 62
    0xc0568002003c1012a070440c009201c40540d111509115690900c400d0144100e81c0c030a001c4c1c842c15400c0e00c0007909545041c441c040c40b4808235404141d5000c001c11030100115402580e0103a103075030321410031846800032119400401c4c078259881061350344500446100d001e40109000d544841003a0540c1c0303001600c0a44081d078082800011181c61a186c0100740d80d02540b8103011840c9000151903107050250048281c016a6240f01004103100709208029015440082455565503000210341d0880c0600d40d020750610414541c2d0200c100070100c084e14982c01400c4965860303032128850340040000d0310940094000c85e02c41e48401d00720120b0070341030b10002000085a801003403c07248003950f00c0c2a8060b02c45801070024072400002500c203590762a001750614a0031881c00300c402515034001c0c100506000c001c076100040441e0300c42c14660342c0f1a814801100705072251442c0d00b03a62a481714050100e920004408a01e000601030b4511340c02c0034004200d20140d0307864500786800381920680c0 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 924158219 1250 924156969 924156977
    0x50616030f0c090f06171308160b0403030b0121020d0209042307020a020607060e0c091e090304120314040503030f090108070c02090a0e1606170c03070816 68
    0x4004652150040300c41001e415070710441d00134200415903215501d65441030b0b0070310802212079101003000d110500c1e03005e0410b561014156029081c0314106101d000703400d0005e60103041004081140807104140180d0290340c042041c80c400e00015600220a5078400b030008261441285803103100382c00610700c682c0440c001600f4a8101d5002c60180c50b140d2004c0da080584a401d0541d200081c080d0702c65102c0c401e0f100401c005035254011031043c0c0300380f03d00901034a854000500014404120000821704091702603202840c080085102035462588000d010031490300100348100303400415102540c181c000c20a40001181c3c0d000d43e941300551200000d0140f06200014040d901440a020101008005165079100740000144040c000034428801d200c5800c52540242c1c44428425911200022700000c10b510b02e07422151804224440d0f0004130000c0c040c02050752540700c543d101941480d00d81000b030b103840707002851825000803500c060000710300c04009850403010382c601e108a1002418 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 924159469 1250 924158219 924158231
    0x9030204050c0405090a0b1e030312180c12060c1b0a1209061d040b0a180902030c150a0c0f1506170109050319090803032a0705061603 59
    0x4085015580c0031914a0110980850f040101d81484002c2ca5070085d074206040201000c843c00041d07808850394200c0740e0400b6000840515514200103e98042d05100100d030f0031464096000c044402201141c14150b0040b8030702d558003401e2015104105140f020301400303c1e50345002441c1441d402c280340d00b0304d0100040c44031904503074051200f00c0090b4010411212400001c60000d0240c044540c000c0040040140d6501010300091415203911403085902086100d0b510001400b0b040058100707800381c0c0d9a01c80701044003201c0c4d40c07054034160b109506440c0183c1e102070402c040c4601003048155100800c1114242052007101d681d141980304088001400003070b901e410f503c9450f81000741002a84d9000144140c0c0f203001c22860a03050420000e10122004d6610240c81c0d002c1e02d1801e074201c804003900c160b20b00c2e00804105014160340000c894480c035101003081d0003102041840c2280700c0984407121070300f2404004459640d50030100910350350710340c40c005081c08081f200d0b05a00305a40c0308 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 924160719 1250 924159469 924159473
    0xf030f0c0909070f1205072106112a010509150103120210020703080906010b130611190b070e0105090d080a030b04050a06030b06030a0b0c0d090615090b04050f0c0a0903 74
    0x1302d600e401806501c0804c0c0e07034070000b900c1d26a1078408a500070345001c1e107401444d080e0000236101d90171003c650022000c116480010200c46541c0601c030300b140d060401000f803049400320f6540d0840350041c1820000d02c8a921141520740d01ea80c06002500c84810401005002181400d903012140d01180c0c41240e004401009400c0c08a80080c5c40482c0010640c0050005100c401c04c00e1720f0140c442a0360151030300f0042091116039100303501c100410700180e04e42030300210a09010410038040d03000080034807190986050030101200702d0307500004c1502c08516241035480b580594030100c80140c6a409240e189458445642e0031031900041015110441a10740e5100c600885004440304180416464218a000d01c40d040000708618000d41c0003503419008510211000d50704074048a43e10740ea20790800340c2450151075003810103000f882c200b100c032800b14081c01900034115044036201700410341445040000f47d400c25140200304240000200d00d08291480003414552040e00b048180c0d55565 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 924161969 1250 924160719 924160739
    0xc0a050a06050609072109032003031008011e0905030d060e150d080d05090a05070305030a03050c0a0e011d0306010902340b070507150603020f030f0c090907 69
    0x40c0d40446080d034844091007004d042c080480c5030051a20304048040c009140000400200b02c02902044980c48031111800c0c14000d945048480a00e520101142000390800319681c1e8002d81c2d4105040624400028980c00d040c440c0000501100041c90071901511008002604c900c600139200c0d804200a03282c913039040f40c800c1c64001e000440e40017240340f40020320070308541d158400c0c0c24010141240c0040000391203004941c5004502000003075980c0b1031070b200c60714203401c0e00c0f0000d00d1351080810100602a0000145c91800525035080c8020f64500c1c0440145015a81004001c1a25590003089541c06141411101c0c10001c610a10b0326042000003482d206080e03010a600307039800034045c01c29200a03036a60b86070020140000703580591880c1e540e800030b8802c020150900f41c3c10070100e003040c1e1052040303e032816042401d840e80701010b030001400a1407035100491080341c4104001d40c440c01c0104e0b01c401000c4016001c2c000c013005d22400c3c4001410b004290180c50b01a005010801c8010 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 924163219 1250 924161969 924161983
    0xa030b0a152402070602031e0c0319111e0607140f040603020408010c1b0b070c060501080c0a0e101e050a0618050405160e0d05070b1c050601050a050c0a05 68
    0x10160b250305052071201d80039041c8010f58005401319001005400e801401100b040304000c00c103240c0b074665800b000c5600760300354010604055030300d61007200484812513002920725042988401514808910840089025203208058521035000f000002e060a03006820340322006c030300852118600000d40d0204c0b030140c0d0240d00f001020030380c046401e0100c00004d2060440d03400c1d244c1012011200a9800200468910074000708441c080c1e41c0054800c43c480c00022101d00e9004205101558480340751580722078046c1c2c6440d003c1e45400ca0002071030b0301c1305c0c0d80550088984024000c3d04509190340100e201c000e00840d0094100715800000b040c3c0c481c109210020002c43d990380308400402e020070710038034065034003044c4100e05290500240a40b50300321100c03043c4181c104040c0210700da00105407100314000c03000d0f00728001d00000040c1b80240c100200980724070129020304c5041e400c426141250b00c250740e0580090001e00c101000e450003680100703510b084100c11a001c06030191750306894016 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 924164469 1250 924163219 924163259
    0xf05011119030f06030c0308070318091a1f0e0105090a06210e030f030a2309011401120b090f1902120d171503060a1a0a030b0a15 57
    0x70071a00140540303a261040c0040c00c00140c00034044185103031541144100140005040b50b01e00140c0e44007058003c060403500d200f407800c6040480d660b940140380080603040320300300c1c0c080407084016409180c40c4c450310001c02002a03608140c02040402103640c12880601c17141070203000c205c3d01802c0e41d0b0380d2280c540140016525101d58220b0601c05042d15008451205081c42c1000399903070b1080030201c241c031a0380d1070b12302c01652259943c0451802408c0f140034038242c084c4240b004510342e1039014074814842c081180090044040032002032285840900c1051180446a000c0300001000b80b880d10750409100c2003140d250003482c0c0d004034205021424455074203c9031009000450901c02c1c003032000401001d018201c020701518002c3c00c01c1d40724807400307071016244400060541841c0080024260409402c5451602e00704e104c10b001031552054200030103494051060075417070600410320541e1740c400500501502c59103014406040c01050341003815811202c045202c0d0540355031410294 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 924165719 1250 924164469 924164497
    0x1d01020309071a0732060615041223160501020c0105030106020d111c05031008030717030a060335040b0f1e2b0501120f050111 56
    0x100700340d660686401216800407220365002c99110034000d0b03148044ea00516044552515032001034914540100711860b01c40c070300903101820560180000282e02445591700f6034564805281200100609004034400c5404605a4118017000a100c00c00c03c800302440d8404080341800803000401c0c10508540580c0260020b195402c000369a410040c0003495074082c03c00c81d16650421200a40300e001c4182010240b04a050810b8001501009a03c048038008502c46004c4049002c00418560042e5021081c0003007403a40818141e601004660409900990703841445254034121001c6400003401001c9440d655880040403407481c580300e0292400e4510480900c6400280a0030b458203185440e4200c0c04092100f40030030300d401001c03900d401a03a080d0f05078503a07a03000046040001413840094488101162007401ca0048111442442401c407a400921486450b070304412540244900604803110785080c1000c200f002102c5980c15026000101d075803203030303051807036802d03804092031070401 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 924166969 1250 924165719 924165721
    0x90b07080105060307090e07020c1f020606040204060c1e1a0105030118020108011802130e060111010e0c040f020705012414030d0302031008060a090b1f0e07031d010203 74
    0xa40d5115a445000d08000c4807030600350f04201100600f11141ca004480351840c0907000319540314002c0204060a8500808180c081c060708000a5201042d00103105e0151080c84049403003890a4001d643c117581031995410950b80007a00d66190200501c0b0351540d00366103031401540480c1844000c100d50b105519003c50f1203503d8035081c5400c5a00f481d94203205101201507035030050b0307802002c00e4111030303844110300f02032000c03203025000a1007401280c605e03283d041680003d800c02d48101e01841080309803262100f51040340317845030a13500c123411040d18130741214a4480701d0349002d9101c40c00e915501c0000508000c540e81d074560031603503d000a522080d05403109810b00400e20700401010b0141f05d02040403640c043d6010079600d1007401c131003005240e00840040c05090342000f01e00c009080001c11101e9500f40009500c00501e40e01806803900c00324800005d80a10402d01540001c0f00e10b24415106103180200d41c40c0700c1c0c1c0c8054035610406880c2c0341203142c804a01000d00140440c0c0c800010303a6 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 924168219 1250 924166969 924166981
    0xc12200f0109110916030507020f030c0105061809032b0207152d020306010513031506090b090a0c120c111506060f0306010311040b0c010b24090310090b 67
    0x941c880d220261442041d0702c1341003042081c0d45114a04092503542000b107469100c2e04000d9040c80301d15a42e10000b444042200c000602c41500300a00400d410b4410003410020303400201441c0c1801c0f9070303203c81640700b089164031074980c00f0454403425100703c0f440440d445c801c80c500b2060340c0c054030b0161050503803219071035580c1c02907124a500c2140701c2e0354400740c0243c00901c102d04100c106981942c0c0c10303901200150469001b44102d0b20b40280008c50041125120b240c89041e06c4005542c000d107aa11f0520003056103010b503c589925080018810b10703495840780d0b101409041d00000a10030000d02d0b000c15201f2002c03d0103040321500c040e4840c0c807004540c40c051149480c860001a00604402c9818007880d81c485e40704942a0300c03000c5801e41e660759581e0300141d0142110b0414000c0840f00060000392400b40303400074103603901080000b030140c810144100b011902d102810f0040e01e8120444480021000d90001c1500c40303000f0703098414820200c0e010008442c01c42c041514811485820444 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 924169469 1250 924168219 924168233
    0x534140f182e140f210d020d0c0209040203430e13110603010308030603010b01030b030705012001060605090310050415050a1d010218010c12200f0109 66
    0x141e06000d20802c00c80160325039200410580c091096103150940380d4200203c5032658410f0715401c200160154442205800307403281501030541d0180120301542040f840c002d480030030307140b502032040d65910000a07000c2d0204803c401d00500102d915100e0f41070703915040e82c038075074026a80070083d16000628000280c9400d40c00c1c4e9400741c13100e01c3c94089500610204007100182600300108000c500d10968140c5441c1c80c500c042c4640b0380758006000b100000c10401e444008500c195003d030000e10003454603100541c1983d22140505901d60030031001031080d07500c01c03801440d54603081c0f40703041c18150030181032a0841c0c401c0c1d0003560010304001220b10560908124800320408038640400c03a62406407500d602140002c485420a952640c021808403209604003985201e08214280d2001c99507201c418004c0d48141103c1c0420880c4030000ba0966008905904000703400c1188c1041c200d500740b8049802014420703086070090252001c1c0c00c11603000300310504035007078070302c1c0001150301940c10149 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 924170719 1250 924169469 924169501
    0x6030507141c0b03030f1305040b0d030903060e010221010e010b0a0207031205210412050918130b04060905100b0303090405070207120534140f18 64
    0x12400c500c00c001c0d15903440755407508500c01001c45071000805007010f8002a06510985030f1620102d400400d140103482c248280e5001220030480301040382c02c5410040c0281422a04000740109040800030004107006407c52090170801d0b1000510340f0445421050208811301c00035140205002c0041c460700c410540094094103107a10031600b031500001d0000d69800260100070954105500b1a40d00d0794041c000343c0d8040320b13244410904495420000000b00701c002c4500785c030141d440c04249000e0a01034412614810300180c00080000d400c0b00c016051904090b0461b001020b00c20150400704002a4001d40614411400404d40070000c0c00c0c2249800b001000b029901071601e500c54403540c0d4004103c82e2000d0302900d0200e09540c0328102682440d40c0c0f60710500b040040504100d082090109820303400542084601d850324121071600316007014804400341c0085100070050260801031b0f001c9550b03086000f46000212821900420141c0342488040a00e402c41a030a020405e01011004 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 924171969 1250 924170719 924170747
    0xc04050609060d1106070c081011040617060f06031303030b010207120311100e0304030201080a060605040b0d090f0b061c081804090210081f030c0e0a021306030507 72
    0x20035441c202040003c1480880071401454403001300d1803219661a03407001c1d41c4202d40c100c00c1c880044c56450042036181c0406070004450b062805441610301d202040680341920300c181d40320f4031481c08042d400140010302409081e845403401030282400d642c0c050003103200d00060000c520504441d4a4040c056842500b4a1410364105140510981c0605031a041171290149070000b03112021010090610241c0e808400e109401d09041c203c0008000000304200c920130307612484251703a194003500841d0300d04c3c000c17600003400800c01003262184c0040a8003007500c41c0328002070480050b43d988a0480017641048402d9800c02d0101b100714500082800822120721110030111145661824100d1103242031030406101e54010020441e1210b9002d203490581c098012801551441c40142030240101c410380fa0080720358985440c4040b00500d0002207a50080c0400c034010f040071061000740000503d125a215800d0001004c0443d1030000b0000401c103075113000a9a0804c1a0010641031141d2a0 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 924173219 1250 924171969 924171979
    0x70b03101707030b19090605090c0a0603050c0415021f0510060c231e011401080a030c153803010c051605160f150e010e01080a0f020c0c040506 63
    0x2040000c5920342c404c11754010240010010081c2001c075128000f400c0d82c0ca40076040700d19100400010b048005221440e00108075045105207a4640c1c00302c0c1038034001c85002c900c001081c4810040104005d42c0307121a14242c2c0140c60000000c0301c0c41c00040d55609844c0104961a0824049075a4090011001624091401c0390808940343c44000740c0d000204980e00c01703481c928103880454002440902081a01c60965070140b4011540e2580a0b20582441e8940300c4c01e5000002081c02c000117030300c010194991104550b856807034890310300c44401d1081c0e0307204550f151118054040c04141c6c0c0d1035280714802941340302031442d140851100d00700720076040c2d000c1ea2415124072800d035002420b03944c104c10f0100002c07144540c2460032500340311204884c0b0000ca401c2d060007080c1d04106000030400d503120044240404000904115001402c420b5110b000c54846600e00125511481e407607540014030440102e1840e003440c000104030390142c400c07008180c0140580c0c1c0618581070044030742000e42215 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 924174469 1250 924173219 924173233
    0xb07050315042c1207030c0c1403061b0f0301080d032004030602070609060e030301080c06040e0a0209210307060515061b190309030506090a050606040e070b031017 72
    0x81c1c1075010089010310b4000154442e24040042c1040040c0003560034003d11381621003200c1c1c40c1c00b074078041224600f2143c00c904460049030540d50044c2e5113040100c000d00030542516900031380a40b019240407540d88862080000b00302518040d40218001d00380b210080a046201030300c001c080382d00498200f0ba000e1440ba4804101100f004182e906a9421110069980c1c006192140c0102180b49004180c0350800302e00307144000d000320182d4121550402a40e80c214820001c2110601c40c901038046801c82020101c1d00200344e0764080c0000d60405400c60144440c144c1000c0b0101a01081303440d42580000fa1030802c110080c0592504100b0414600c00c29400c1e00000581c0c40c0181120400040035070f10703c80700f00c61000c0002d400404a0440e00740691020703410010103071080c134002a5920311508000c03c44882000558400083c0c22034040d0200d6281e803400c0102610341d11410134410b1003414004901c88801000450117080050311442185181c94456451500b0200f0102c8003500400 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 924175719 1250 924174469 924174491
    0xf2a0906021e0a0204050406020301051206060319050a05100c0311070206070b040206120903030f0c030603060103060b06131d091c03180b040c0305191703040c030b0705031504 77
    0xd540c00000901c400035142c1d00050707510a0f140207000e14020751300034140001e1106214030741d4019410b0f41c80555403140100b4924040c90b0362514140c178040d0b015444020004640c0c0c480645100450b8464010744610283c07603221140307482c20f00d11403c0341c102d5031540354420316034041c4941d644190390345442e20305002d11900040d07034031b010701b240182c100340540d00083e0865407424122035070520f904105044500b41080c81c903590350000c6070303450b14407042000400e41403a01401501c0c89810010018182c580c01c42e91141c0140480c851101d400810611140450ba00c5100421024140ca211044001e440840500709500307009022102c003134000448803d2621001e40c45113800360301908000ca013004200e254191080356500000d42181540c5080c03008000304100d00000f220b0040084139404501c2201507490548803090040c20f11040c2e154007544218090f01456005001d0081142441d60320b0726000700450b01200d00d800080c0000040114001040c02d00300c0481354107542c1001144610 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 924176969 1250 924175719 924175723
    0x406050d06020c01020f0f130609031110090506120a06050a061e020c0a031a1b090f030a12081008060c121003060c0914030a12050c010f2a090602 64
    0x11000c060689900000d100205a0094040303490a12901c00d65039512010343c4000303102038100007403d0303180e16811440011000d01c6007400c074042e01e400501412100c844c4608000e001a541c070603c5050141511000400340d4a070000781c41503140d00003500d03074a803400f014048100d9080f42c0241e8440e0100000070b100c101d0b805450f8541401466031440c403200b1103417a0a034989010040c10940c00050703904003200300b102103000303c81c0e0a1110700d002c1096072140c0126426240c40346014014042091103489420b00e80030881c8000c00034040c09840c081d041a459544505610b500140003081c0003500384419000d44500b024028100c4a025102c507040032001d40e2898400c1c1240011810001004910040c16403c0c80030020755020008004021401d00c019190300e450784074041d6141c00710403616200e400c012a843d2100c3da40000c0b210260340d00410181c03400d0b0400d4843e90078540d81d031490a403164120344288070601603507083d421841c2025008114203068022f2048042000000c0700b00403007500 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 924178219 1250 924176969 924176989
    0x1c0803070c02060a05120f060105180a0905090601030b091b0904030e10200a080d021c06141f0c171c1b050301080604060b0619020c0906040605 63
    0x40400015900e8489403011103412210003400ba6001c0c8000900004540d006001410740909400480150399906030741030800c11401c82c0c0442c04034100300b1502280101800702c60504d02402401843c3c09a107920b0540c003203540c11110b900c2550301ca00014003e20080c0b05003590310660000040000c400701d0b10b440c541c10901141d07158026a1058041004c050203105090400c00000c0e092940e40740c005000100200e00c440c01034a240409202076083c102004512010401d400801040c9060685108a8001d510441d0005c40d00c240b18501108200c00342e005110040c1000f48420100780d0300001009a6000482c4100812544001c201c0110b01d800604041510350020701710085045007102c14111071150501c000138005034241066030703a10309030b44048100d001c6c101000d4400711603080c0c1030322300388000e0095400943c801c2d00041c000802680200000300e5020380914140382181075882c4801c004054110056048407001004038140005801d50210301190240021841c10300403a0031084 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 924179469 1250 924178219 924178223
    0x50c060a0e061608070308100b0f070b0a02070f08040e070c02031e03091201140c0a120b06040b0d05040218011206050c1603110f01020301060518040e0d1106061c 71
    0x15003c00d41100c980c0e0394040400c000d94019811560718029440c0061103080c0444840d15032116680d0f02107000e03443d10080c2c885100e0070080c06480c100040d1100ca05500c8010001007041d5001c20241002540e88040700c400184585102034546050051134031880304000d01003820081c03444e600c100503030f41c0007071703102601c84411003034214019864486e02c0c10b5200704900f0315002014241d0180b801c0c0d0056003c18101390502440013010741780c4201443c41441980910400141c81c980007400c11080341c0c0c0440d40024005000500e481c0e903880f0302c0d4440360800c0e561860020350303a404200c10360401c0d41c1d005204441e02c015a0030158100b070351460040e0031b40d0768040d0065a9520005098008140844001041460740d44400441a141c010000c008440322200b06020360720040c03032601d505009413416680070351603241c284000100483e40001e0900c00d41a4001d440c1c0f000303540410f4062009403a8980c0c0d50343c4840b52400d450080c3d0740f034480c0180203640181000303103441c100490b007107000080041e = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 924180719 1250 924179469 924179479
    0x16030f062403021201060515040608090a080912071d06011b080451030c0f050a0c06050a050a27080306120111030403031404050c0603100b1303050c060a0e 68
    0x114103842132900600c155045160845806000350340311a44402c0078004844031941c1e0480d01e5a90464000c0d00c400a0071030007890005c052050440714500360700c5d9502400c1e0302400b11140d60382e440101e80011140c51280030010182c0070140600d55038419030018101c00403a2850602448507038a08003688201e1240d007041d014483e050f04042000a901d800e80a40014040e050b00410909400750000710540c140c3c1d005110005e010058900030f0088041d07204842d140c54a00f481441410703640c0742d1220001d981040012030251000a801e88180c0f801f840d1801e0b0300107058900380304030b00b085481c2182d4200d01070301c1100c501810001c01150100306250300c90541520713626101d0116900c0120b4001a440c254207140008a8070f01070b40300a54490740c0039a40510004015024072040c900041d0380282242d00091021207007400c020005541000d0083c1102d01c4007a5030700b00c0c49006401400400440115200301003050100c00c0004420383c02c0121001403400240480107450107000c004ca031342c044c03 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 924181969 1250 924180719 924180739
    0xa08040b0a0b130507020705011d010c0f0209150907030204180207020a050339210f190b150a15032717040614070516030f06240302 58
    0xc56965002049a02c0d406400c5080841c2c511000601400e000c5400000500c11712070005040d621400c0001114044640c2c4901403155100c01101c45a441da0800d0382c80e011400040401a102c1c001440e1051785d1460401c0214010142000420f4602911002c04c00d801404107202044c40c0400300b42c2c214191403401641c450251004c15090b616581c8400c2d41800341500108440c4c207102c17409420360b10a00205000142c004182050300601c107200a900b1503581c00304030047d0b5140b0f107000c503070364100f0340200da455140e0040411700c1c3c4040c4c4520303a62000c0310381c142034041120910707965420905007035200d03410f80016000305542c0c8003148114915200420380031078070540280d00c120940041340791400644d141c01c01c048042c099034014102c0d140980c807068414641241c4003900c040c0e074482e80c4c030240701c044036510080302a080008192098007511100304000000650200c000703610032202c0d034032808580d0400b8011146501080240c580c544240400078200c0350b4010401c0c0c940c1202c0507100 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 924183219 1250 924181969 924181981
    0x21221040f1704090608031c02070309170709051806070f1101020f03150904050706031505060c06100e090309120102190e03070b090d06110c06040c0603110a08040b 72
    0x41010010068045400c0c2c60140e0403411500c0300503c159000c1007028841340c0d0b6126003c5580784a40c00310040740200307030140281618020b40050407001c0c06803402800c0c4030380314020800b81410a502242035235204400804c0118050702038507030700950313200300100070040e100c102c1a2100402031a61041141c040030040405c1d006c0c0300c04c0143c00000200841d01c80351011070003d0240c3c17081d20307140800010303005060050302d01106080c1c07081c2c1d40f01014185084c40d11000740c000d0910286e0311084901803d07400f04458440074054040501c01c0780c010161400c00003a58101190103401c01e5143c0b40d001c804000081c42d000041b42d1040009945130003002c4100100303075009004c0c12554400390b500104080e40c0700c0382c0c0301401c0a09404201d0a0390240d0366544410440340c46806400c40c1c000814040c41004182180d00c0743c032103040c410702010703d07000c4886a458104031044404540c805541c0c0c00c01c1c003c69502d4440c0390440e0381c0c43c41038986840402103000d081680e0090004154500274170010b40 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 924184469 1250 924183219 924183233
    0xc03040b06013509011a0f13020705010603020f0303070c030318030501051017011e0c020a0c0b0c12040506070f050c030a0606090c18060c0519060c02122104 69
    0x140c0010b5000711402510b4540d08010020114062410b00000c58840800d02c0c0075010300c079442660f15405a548546e8014800348203c03a6178107040c2503400b0700b001c0d0440920941900040035224440c40000503100e0440c41044000745484042030300030762091040178001a292003568051785e8050414041c1102060071100300a112600014869403c01003400741030310240310b1400c1a904130381050f0101c219084011802c0354038090083c1d480002c400e01c0700b10b00d90340945c0440142103247c41500c1995010307840b10f038042416a44a50400032002a06542041c0144160001c0102149401c0d113445d01c2d0070009802405807503030143c13108581d8030f10720042001c1009818000c82010301968000842400c00c0001008540324500100f03041841c01078100d03109100c0c544c500408070307220b80c1c1c1440c21701388201c2e041503824108036071521406800b8604403150b11542d034280d9100e294040b84e0f0b508a550000e003440414100801607103010f00c140440c43e07500218a40032641032131b5003580b0300d03552414400 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 924185719 1250 924184469 924184487
    0x50a0e190c12050a0317060a06122304051506060702010302030a06090501090905100605180403110a0c050f090103031209061d01020912120f09030f0114090709050c03040b0601 77
    0xb0302e11030411280c0700100b0001140400c0e00600907156143c1e83c1c2c01e0008054500c8004640150f403244aa42061284c0c81c000c02a1210480074040001291403d1820300c1d4034194049000000c1c15460030308200400c03208000c040c2100c42026405421810030101280542c054250001d05050300840014000c01440e44030200403d1940018021940d50340100c2004005445090f5481c0c00381c3e01c0840003d00007409244100c82c400b03080c440446040c1c3c0000240014050802c50030402141e0f203521040741d0802080c4c02241c0144046038140c2c3c6881d04000440e4420700301c41380148030b01001000400c0c0c00000c1c044a150180e18080b814501c0c0e8501300000b081d00964040d04030308110001041d2a005501500c6403940c01c2e6502000200d41d00810b6648500f4454048001d45c010403c16070101909400f515103140c0140031038114000642140307003550514840c4480210000040151a06003040000010040c0540c1041a410190944a080d100003080940041c6210010400304d034840c110742 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 924186969 1250 924185719 924185729
    0x21060112061e0503150a1812050307030f140c0c0307050a0b150901230109080303090a0308010b070804050f0f13090b0708091b0a08150a050a0e190c 65
    0x400020b034407240e24204281844040b10080002030001080301c4c140014500c00300c8018a003211201e96a0f942580050314070070100e480ca07050b00f05007150001d2500790020181c400c05031903544d140e1810601c000c044403008180c00c0c441e1820324158134030f05075030340035030b1380d0410402c0406035030321340d1000380352859442030002c002d0407403003513214440500c0098190540240250900d155000040c401080b14070380003070080450502204100c10740701100904008180328060502c0074846035100c0f1560f080d070b0011039160303906030043c40c052030400d0344c450a030302d0140c9440100d4508008981e160100a03002e24010640038808002105c40d061f0b49102690254140040c90350401001100344a405006a544201c0d4007000d40004120740c640280501c074864a51031000303103680c400b04000c003040c20044600203078104400890110b4a4078050004107080d06003a507141d820760400030390000c101d500042621220600d030031114a10400b000c11107090013043c200031126030401d9414010b0368940e0f00d40c04 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 924188219 1250 924186969 924186971
    0xf0625050f100213050105030106020d030b130e0a02030c1017100e100602010b012115081002040807080c03030714071823010f0909080c060117100221060112 69
    0x2d82c0481c440d0020015503884d44400e07510b403560b410040d640f5010a000b271a0160704502c0c2c00e8039140744a54404510100001c0058481d200c41c544070600b25200d0000d401c03070581022096109500b4100918201200185d990030901101c071200142260444a0001c00581d00d28002c500226185100c000c00341500e40460a0310303003428041d1203003184907803060b00c015508098070400f99602803040700d01045180c1e0210a20340291007217400c004e008a04034144002e89200d40421139920030098825685080d040c0141c1e25420004c9162a01d21194440b002690001c0030340b142c2a10040103580c40c1580c031050383c1c000d03503011501030380c100940c0d5003014800303000c0c03072408110808a68000c401310103012516100139580d030f20b18072400e000707090250140301072029004110b000b4056010381c2006000c4c03401da134101070300884090300b80642a40904000c02c40301519458024060101c000300d8543e50300c085203448ca003030748052043c1c9e0481500d2070403d083e400c001000760b4060b0f618a40d1041000310 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 924189469 1250 924188219 924188233
    0xe130605090c0c070605040f031502190e0406092901022401060305010605031605030702070509040c0306060e100618080609070608180a082101030807020f0625050f 72
    0x1144148640001407858a1071184800c00154031b400b40d4102d80a64401c0105651b4150841d00d8031429a04c51840343c103031041d801c0040c14603c500c4034500c07100c03070b40b40d0365505130400d10031130101710a171507140e04043c410318500000f074000704010040000100d000b0079000c100b49180b40300140c0c1004d600130744104040b5801054002c41000e8010402c1c1a940c0c42d8808000036601c07420200e6042c04201c034441070304a08004052102070040014680c803258a2040f24211501d0750f02040c400c1d001038400300c80d40c0c0001e90003442044030b40d000d0080500282411b1034002e02c0d041441300c00d01c1c25544280b406100e070042956074038081100710200500b40400c100c40751400c2030708000e41e42d10601d2282a000071518001b1414102244503102540d44800000382182845502c0b4103004c1c0e80007655444000c110402d001c15100b0591002600039400741d850952910750b40c0c01484582449080003d1280c82d0030080c61b605d41c1074848070540e003040110007002c3c0003000d5160580c5000c2d10a5421922841151 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 924190719 1250 924189469 924189481
    0x60a0506120f1005010206070c0c05030f1e0105040c0b07060609142502030f031005030a1a0f19020a0e09090109020f0a0303020c010507210518100e13060509 69
    0xc2001402840b007910105425503c5004031610304060f0700640b40140c00500225114034824050b104059002e040c15106665403240020710b4026095910181a0400b420f01846800b9852000311440f070050000e0201d4030341540c4950300c040981c0585003200c0b03400b01d08407003444071507030280b4045c140d01e220402030741019000f03102131413900301c0f01c14801054024002060401c1603040c80c1e0412a00d40007182840b00054090050707401c000d1400042640f03401000500d40d800b00f00f80440f4038015544014500103991001003240350092402c0310010b003c40501c60307110a003807104070013500c41140068552200c0c01080351445102c41070203070b00009000c00d1001d22901076020b4034061703100715000c8070030b1544c5d6801d0190603c00c5120103400741c1c00640000340c2a5004074000d1104900c10041ca884e8003411909581c48001c0700410b100000d14045603d540071001d07005100901c501c102c4e0341240c06200740030f005009131983c2c0c440c50700961a02d41048503050258000001420004104568914240c = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 924191969 1250 924190719 924190747
    0x3031033080402030115230103110f041e03150513061529091c060207050102030105040b0d020d0312020d0504080a1b030914060f13050a0902090d0b060a0506 69
    0x2d480030383c0b095280c5503140007211030b03158085c012242c5c100c40041000c0d141d0000a1013980300e803006075052540311301101c9403001c1c07002d00916030669101c20b0151110b0a1200c5007140701d0070364940c4510361840190510114a6030004c00f4110b8000002c081565a01d4000030304032080844030003030101c3d0501103d42d594091031014041503540ca80c0c2400240c10900b0001040d2000401c1101d0080c4400c008052041c01c000c04031455004021403100b0380030301c580d0b903200100d03408940b0035242039502000600103440c00e400303510f1148000322811524a14503400099090744210f100605100d0702034502440141c5a03015600300300758a071020040c03403500b03042c07096059200004540005194078001c0301010040c2800d121160b801d40e40d10550b1b542003d140324900301000303c1807039001d00c052010100c05200702004000d002205c1d1407800425160506000444c66641c103c0c4035000e00510491003140c80c0c5111401c281c82d0010365600301922000d0200c1d50348800d641080b0b07000b03038001681c00294118 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 924193219 1250 924191969 924191971
    0x130b0306130b061009120204020705030c010b04060e04211404081605060c070e04050a022806030c020c012102040e01030312050c04050d1103010c18080303103308 71
    0x8402d40e500a0791407004000a03a01049156004507890780c0d028000d199424008001052028200614107401520381526641089241d61076507910748007464910708240c0102d20081c0540d10320016a81401d81c0d4191002c0040c40c8407120600d0210203c81445105451801000650071001c5684030b4032485482c2e180c8a505201e80f150310100760300001c0500300b15040317444020501c3c0140c9041380c101b010301045410003500c00d66a41c4503140069016a4841b0f081e000c0313003e1001d08040d00d49070801c0320f560062002c2e0b4850001d00d0b00d86840600342d1600481d03801304190702480d04042080701c00c0074285c00410000007401c20300b440800c000c10f260260310b0096058030300030740700c0c03442000c405050841507550441e9110003040e000e00040001c0d0401c4180200300b10301c80c469a08a030403601020900310395400300c6000000700c00b01106580010409151000750a040340558558074007001c02c250103001c14407806150748041800c0c0386640e41544031700ca51a82c105100201811550f11008000c004 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 924194469 1250 924193219 924193223
    0x30e090901090615050d12140318010c020604031e0c0605010305010b0312070f0b151203031503070e07180905010b09010306050d02131e05010b0307080702071202130b030613 76
    0x1ca011071006002840134404011902c004000008080351a9912414900e11000010900c40460403032400765041201640c4113180c410810f043c0030100042e114250b80600c00184250b40015081c440402d6000c03400308202d1034840701c02c044092602508907450000b4802c05880c030351614001104000c0c06400406200314106c040300c120035070005248010384286140189050410a44540016004040c1d154030045141031410600c1001000c03d0071002d00d1001420590000020005e55901182c00d0b2107a20400b81c0003050ba00342059864a920302c8060030307003800d002c803800c00703c08180032101c0380902030800900281b1655a5a149410340c0c1d401c5015094003003801c0810200b00b900f0001042082d064004014805188820100c2c20043c50304d01d290002e800310108152601c41120f0003802d00a18514080c20790701d1030105001406110f016290004540100c0c004020034510080002c1c0415012600d00c16280b02030500304000b4904e9608454040c02200b081040e19907025039486000340c = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 924195719 1250 924194469 924194471
    0x30d0905010c0f112109040c091e0b0711120d03050714030f0f07050c0706080f0c0909010902090a03140f071401020a03120f05181b0904080304030e0909010906 70
    0x1925a4090700e42d0304c00000d0038100e0f0303801011501c0140444809215000342010900b5207042e40713400c04241a141030000355404240a04010819101550f90443d18240019001914035003422124a801d1207100d002411913080179160000c1c41c0d442c072030811b030224080030440d0b08117451290050003a08003121040301240d00702c95800720845080044030320030340307461100002c5031391042e2140c03010742c0001e041d000801000344211921820b04100100281100d40c0b984002403400329080641d00500030410b00c0744030010702140c0c0e155201c1c4d446450640c1c841d04005611800008040f6845da4226800500205540742207250f92920100d07260440d10541001c0e500015259495044550313035210b41c1d280180e10407110b50010a02c906400700e100c8400403008107008135609a00b80c25907000b130b200e2418514266046100c030080402100c0c2414040d42003240504400d43c000a80141005002a000342c80000010b1b00f00345c17090000c104441002056540035080c05a0481c0c000c3c020241c00311102 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 924196969 1250 924195719 924195737
    0x402070b0f0f070903060903020f030a030f0b030c220906021b1516260907050307080f070303050d1409061905040f061d0601060e040c0e010e040e030d0905010c 70
    0x507240c0318007041d104103110b03244c4124803495940c400e4001c203e6220150300314014600302800070782c824001000b48910f55503000c628030400c6900302040b0f03030711105828426409520419103913240c010038281c040c9900041c1084007900c000b01c840181500480041c055440040c13030b5001914401a401c07822103080c011150407000c100342c07000e00608155056815115544441003c051003519124450381303040c0300301102180050900c031303e070386420386c3c440700150440c01c001d00150038100b00503001000c07030a00070310140485039006500c1e40d880b0702024040040c002a4640281d100343c20001c100c2c413a484046a00d4a404030030a80c550f4010b0320327000c0064140b0201c1503141d402c03500881c0c3c09990000c5080344035400596a01009144030613614888520845200c01804414001d81c0d00810a58403010a80b0b00c0340b408000844d07006e11226414014840412140359902000d19040000244d80c001403031010000082d2544c0034440c80b645445050854010400030706402c08000c0000f682c54600f40 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 924198219 1250 924196969 924196981
    0x40801091a041703130203070f0302100804031d0a030506100905010b130b0c01090203060c09091012150f020f04030c120302102004030f0b0a0605010e01030b0303090402070b0f 77
    0x804190b90140a4408824000e00c03503004120046400c070144c0d00f8a003c074903040350b004c00e00300002a4401011402c1891382042942030003640018844114070f0266550f01d4941c2d4090b140c4e004074403103000f4a8860500d51386868580c0060700c000f4541010480b8101c3c5080108103c1d50a854000c060310f803400e00000082c0c503c2071b141a5650714034044521030807182050007460300398102030003840c2d5a6403150211000f5860912605000b8650382c061a5694008081888800d007406422030702c080e21150010081c9425500c0c072081015030001c0500003c0080d00506005230141300d8904600d0f900c00102c1e80a4041058000e00403a44105010459143e5680030b008690300000006800341c0c21150a0b01160b051070351012081d081c011b01e0102c0007003a489003000c500d030400e0b0030071280e561102078101c081c0710000b588581e00524401c014000e150802d030008100c803100408580c185904c0390b02864860303a0a00a9902000c0c0181085444600d1800c1080c01e1090030b44555480c50300c3c03d00810301c = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 924199469 1250 924198219 924198263
    0xe18010b01020d0e01050d0f090b15010507170d0f020307090503160506070213020720120607021009050316030f080a09080412020f040f0203091e0a030302090109090204080109 77
    0x2c840989403180c81041345182e005542c60750183e02c41d145603d940e44060f0800003410300c14501b0680c00344418200c540b07000d003143c0d20101070b055402d07814413200780540c4000540501e152081745014a2800f070f100c607040c52403200500b0311004021041e0303001000700a00954400441c600f1a0422800c5035052605032034890365001b0540103450704010100005809400e180c1c079451054010744600515004940d01e40380d110070080c0a81e00001e08900400c90701500e00b103410325100d05503181c0502032500f45108041e5031842c40c8005210040c3e1079005850600c01c050003994440d4a1690120000000601e0010030441c0b5189001c1d01054209001c680441c0b640e00c04c1d4040103500003a00c501c3d060038080121880c03201e40104130ba000641e421725005585841c0200360142c0d07605400581c40b800e012841c2c034144148980c100031945e950580c0e07240a0b00d00007a5202d1b840d50103040043e0341c0e1501074012915000316401001d8014000a4001094641540001c3c0d4a6000d241031501c0b42c0105002c02e5 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 924200719 1250 924199469 924199483
    0x6150f090c03070c0807080f27090a15031b0911270607060c0e030106090207050c09070e06073c0605100f09151505041e0e18010b0102 59
    0x41070000034000204498042c60890003c07a00a800c3e150404c18941c0d549403969010f850500d84440c0c011580d590848126080a072801003d003061440440e0200e0100b414001c5c0101040c0004ea100c252500d260100340480070040c5402410420800b03c00741c59610881070240b088680e0149040801c1030079090301010b40d010100e0403204c044c2d84102d0752a00f8500e03011001859640402e040000e1f0f03000541c14426591460b10b1a1214480088190304050844070203500c08451680100640c4001510100f08424503010460713a481035a258054103c070150815540940c1181001032102d05004101c00c08406080c1c07512400b10040f22144c02c07171003160f0510f070600700c0c900c1010844c82001401070b42109a0003480011100751440c2d0b210101c142e200c6503544030020903603072004080c41541c0800007001c090400c01e1a490009030454800074610710491084030902c0c0e408945650081e021072281d00010100c284c0c84924600304000702590b510445074145885620300788a0034501c2d40003051030 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 924201969 1250 924200719 924200731
    0x90a0f150e1f210912020715030f0207020a03050609070906050a090507030b060a052d032205030d1a030c060d0b04110d05040201090b030c0f070305070506150f09 71
    0x4a062240e04403046644082ca901ca400103010009100d10349144070079a03e40304810800030046034940ea542800400c070740890801070219001454280805403810401a038584001e240c000346181400702408000d00500200179070207d40c0a070004140032002424601906815041c1c031130701035480e08c0384030031208103205442c1c0080c45a0001c001c040d03003541c04943d10000700d081c040b03410702031a07000965130b90143c400c036004900c000c202d0254114251441100c48691031103480e0b010b854856140525000007059090f16482e41e0000c01c00c400c2c400681034140320341c00b00c2100d4840c0f40c144a80c0000c1d200801040d42c803140e140040c4041490700107880025844041c1603145041140398800002d00300c15031655810a89408409094000b40c000a0014102091001400e0705040c03000404480d41c0d03034030070000000203105200f103100d844801c54008092001c000ca554a000e80b03410b0b1031034055014040e1050080301c0410040f0354901c1c076004204441110040d8610310703990700300000c0c08400d4481c = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 924203219 1250 924201969 924201979
    0x305011d040b15030a051203071101020c12070c0810060504050903030f04060e12040905010303080c040f23130c110a0803060d050f060a02040e0c0703020c15090a0f150e 74
    0x420f00d11100207055844000e4041d060700c2e00c9607610f07154286407154003e03901d02c1b68100081003180a66001200070030321450940254a80300c000784525030703161081411140c683c0c000044203001c020814a2280081034480c050b241d04074a5062000c00070502c500c5031a00a034103040018100b04004412a80f1426000300b441c0361540702e5441d01c1005104181c2c54001e03070312171140004189001030003e00001c08030340c5404101503040d480c0c000c0000c00c016014980701c1e14248800c1c4140c452600c81d1400360340144c1c00c5002001801110410a00c5684400d40d81210441c00600d08014030740d0402c003008001c40d2181c101694034042c00076602c00c100000649140c0080c40450040c0c5840c4c0d0301c04c85903a00950803120005908080c55017484000d40d0181c1c00142c0c001070800400c0008501d2581c001d03000b0a00b80d00b4074400e81c0b00070352078689840d0002d200d214800007580d0551149070030389119000182c1303a4510a52502d9103024030340014040e1700540d9000d2030b10b00003414031032404d207504a400604 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 924204469 1250 924203219 924203221
    0x4060b090f130501020d1103090d1e0f0302090405011806050f0609120109060507270302011d0103110f040614090616050f0a03030915050c03070c030318030305011d040b 74
    0x400d40b41c82070b06030703901140c155400f0401c001c50010140940070201040c2d48505640f4182165400d05c0d01102d00ca8000c01d000c20300500018140500c45a40c0c030601c3c0c030342418494100d100708128028850208c255620030315040c00482c1d00030f11420015401c0b0411181001030036110b00c10007501600c500340440d48520104006215030400710100486000514008500001159a010140d80088520a0015030003c080282c40344103404201c5258031603080000140742160002880241c00c0310340031507450400310702d030311060f4880d91192186084100c045902d400d2400380541803a4003602c207020014140403c0e00c0c81b03000888040b03685424006203a80d107011020172140c480b400b00808242c45174000c8548a02401c6824403520303041d00c2c440c0d81c1c00590300003a803a01c1300152500040c1000124030342000c01000030342d080b003103c2d009502820100c5011480d8502100541800308118000c01400780750300d020140c01d40c21aa068543c0c020100d85007400e64444e00d038540c6000c440290110f00100 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 924205719 1250 924204469 924204481
    0x80123010b0d091e1205090f0108060325140a0f050118030606080102040e070f0206060103051b0c0102090a080a0515041703070e15070b0c160c08030304060b090f 71
    0x400030503281d00142c001154190040e203640c0c15a1003103c2000382807040c0382d01c103003003000a04400004110860f05001d8280714254001c201000c1e00b021445040c0b101c080007140455600300b1190984030141160841100315011006015000c6480740c0c0c0d0030030460030115176040c5040c591080a1754424031070886918030b02801102c0080c0d201000c269070700403110300840810542d020380300c05407109000250f0743d0361030700c0100c0541031401031040040048002c4159019079011540e580c00060901e4081002d482c2c20b05100c1310561610000601038500103586811810190050244a003044905803051969150419280e81000b90000c1c01900002036106040c0c11142c0f680b07400c40d00035800c54081280e803a48001c100d6000351014000704008203140ca03c1483c0c4041034145c10322211508030b0800047d60344034001034101401031b1824100100f81c10482d4200041c016241c9030704203c0001320144d031510229125403003580c0075a4418144070064006082c50800c8600074486450b4a001d20ba41c0c00c = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 924206969 1250 924205719 924205739
    0x10e0d08030403110d0f080601050306180406020d23060d02030d030509070f0303050c07050a050f01030917071212090b070309020a0302030d02030901231e090405010f08012301 77
    0xb84201e0502c48203003c0c14004503000c10994401c40d000d80c0b284090004001009804010000c1c00d00c1d040080130000c01115440303090820506049880c6c1003405c036250751400708043e02451108031181864440d030f40004e10a4090007080307070201c204801082e522000e0510019950680019401d42e100080c200d8446120390b2049a10003030803411303200d000703480390703040c1c400801998415400070ba00428540400b0100b44030b13110041ca02114480c01151608010441040448005606041ea00e401100c1072101c922080040c2c1e1212440c82c44c1d881c650b500d000d01c41251141d000c10001020b5001495110409200e910952600a41d111607a5554064110007030038015170300326008070441e000080141c0341000b08441d042c00540146171100c4c04140010896040c4501e4a5640c801040d14194031000f030108441b03104020001420008810080a000c14842c922181d82c0142c0b40ca4000503101c60352124150a441d50340000b8480c0411028002c04440b01c0c00c80f019001c030605500401800d804 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 924208219 1250 924206969 924206971
    0xc070b0a06030b01090204170706091703280f050304080304170c01060e0703180c0b130b131701020901090e0601020a0605161b051002090a12050d020c010e0d0803 71
    0xe1060108000342c40743c0d02c84540007820380c00310000380e40103d401d00480a88045014403951410020312000340340c400000e00620203803250911881180e403a13000411003e10484114a0350030303110140703404280020b10841400001413100180c07040441165030b5105008407400b5a0300681440c0c00c3d51500e80710040b043e58081e4078481d044004000309015600280a08001808050741d002100e140200010741510741c101c20240510451035803071000191800c0310801a00e105101c550740714107503034040c1d9101e080c0c82c0d0040381c4040d001240195081b1551034007001a05c03080c2d1540280000800001803e078010200b0490101c0d4032580140700c045031b09000c56910107014412034002508540781c40045550035500440421072020104004030382120110951402c0499000c000f0f07041601e44549440c0d0303c01300180b040703400140b001190b5469a1091000c0c2040464000040c03402d86070282c0e42c1c04102d085040540505c000c50a015802000b98006030320000d044004500f01c82d0f66200c004d0380c0 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 924209469 1250 924208219 924208231
    0x908121014190e0a052e230a1e09140403111e01090b1b0301060c050309120102031005040204081902040912050a110c0607080703030b0907050909010506030c070b 71
    0x2c1040015182448001d00ba005400084c0000742c2810218440482c0318002c40080e41c03c0340c1c1d01c0f0b01119012100070001412224442c0361022401c414484405803081104241c0380d0003a00e8800104043c42403810380d515103502c08820000c04c656400c1e104090381c104100c2d07140540f28100c000340c0840d000d10382d0503220008170350981c1d955014401030284004080b140384003190f903561900f04108200044415080810a80a041d0304034880c251015541302c14000c0f0340c10010202c0312441004030800c140d4011680040c4040b00700e505450100b4002d407c1203500030007580c9407900024040c1030038802c540a45068401034401030400e00c10f103108000c480001241c00c84d41e101c1c81500421401c10b801d40181c40950f031800d580b40d5108200a08183ca480c00c1c48425412001018500d607a600d02119070f0140c0c400c540c161101c04c80c1c1000d6004200c1ca5035415080392981d0108560145d210300100080082280c40700c0140e621101031203034130f0001f168482c2d5000003c01c908008200c1c00004281c3c802 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 924210719 1250 924209469 924209509
    0x902060c0f01291c02060d1a030102032502032704050a0b0a050f06090405010605120a0513020d03170106030c030e06011a160c260a240e010908121014 66
    0x544c550202c2e0035644280b503c0345080780d48019501c4c02407081040348174000001c90096040d03041801142030303003910600c85114406007404042c4100d0f40284140c810f0348412030300310000b0001040f0a5507142880451951186150000241c24a0303803030701c142c01c80c40038060b0064400070300381018041030591051031254003440c14428004165078a0203a03901800890360303a80e0f02d60822020350000c058000c2d2a0350b41071402c000420071445828440341301e40d65012694928200110304042d036a484404500300079404140c000495a00d070950040090b0501c00e0780c013044128401d41d8005c0d100c3d04c0a00525900459803007404400000c01c8002c2c2c8001110140f10540c41c0c001580c07000c0c01e0b28101c5e84142c44440c46485420011491260210440b41c000005003403012080d5035142035503080c2c01031f8070b50400c5064580300900242907112444400390607000300500b0045041502207a002840d0404114444400050130207040c444040100c43c402420910503021800400644000302d5999950b44 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 924211969 1250 924210719 924210769
    0x80619050f160e130204140306130503030406051e04140d0f08130606150e01140c0d12181b090b060d020f0708031311010302030105030a0f060902060c0f0129 69
    0xf0340c1817000300000d0100d20301d00103a20b05500145070525a005100389503a4510315040008280c0c0801201d03445a40280c0005065030b42e0307031a458001002540000c00099600100000c00c0035103418403012441c10340444101c91041c1500712407508250798040d002072404004220104d0050300041c014030710a10010481a40300c1c03a120201c9280c03512400001582c4602c0c00010756003007081c0c141c1e1801c078a00b85030314004d05000301680da06084040321040010804241e15945150343c0059590b12030074200c09221001030502280f0300c2d042725844141c200c51100d0004241e80340c1c0c0701d91403600740068425400c00c02c0c000c02c504002c4d0001c8041003000c0c00200500300004070404029840b40c00300c50039954400740e00d07045c0131611040c903c001c541031603c108018030041d03600050300000d0b580c2c0150f41e00183c1c0002d240a001a240030342c00250441004103449400aa0100d004e0442c4c03a400c030000c100e80c80c1a12100000f41610050901a10842400e039103198142040000000b034406141c01c810 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 924213219 1250 924211969 924211999
    0x1024030504081603120f0c1b02130507020a02010e06030f0708040c0317040305010e010b030606150d110714010603020904080c1e0313050109030c050613080619050f160e 74
    0x91201c1500b41100000c00304822445d10800510648001e50505202000031120043c0c015040e4204480840c000948000740041103540303001c101ca00c43c4d10300000512032f600700314a0280d03544450130b03022404562150384003032031400c0c500c09991081003907040d070301d82c60f840b040c1041d20a0f00001d0802d40d02103c0a0502102040d003a005007a146003030964a42c2d501d07031450030068216402c400c545542c690400c6d0117a0055031f0001002d03500040101d072000d60058000f54001018464907a0040720281451140ba1b851071032103020702907050140c442c0701d03001c03c010b0b2501402c0303a8050000940c03141501c000b00e00424083d0001d00020442981141d08211404540e1903518242003080a003c0d4000904104001e001a00c010010701c000e081107903c0c41e00311342d12042a08002d0160a010728004600e0101e03181c0d081d820362005107140360507107140c0d080c00014140c45c0d0200c61070071300030181400007080001c00510149841001a408011404541d402080758500404600b40e98048846850005 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 924214469 1250 924213219 924213247
    0x3030c0203071a1909170c03090a0906050103060519030f031710150e1c0c120c2102030d08041110080a0b0a060f0c03050f04030803102403050408 64
    0x341c1011400b41c3c26580307281890318070340c86420711444160054240500140061031400e1404103003592501515122041c03440f0b010f2450280c1140c6079800080c0d41e0000408440d1584240d0650b07800380e130140100c0d61590180011410585940e0340c0f504120301080000c240b41082c0700b5200c501c00d10f410030001200102502442005480000c00e1403004441001203a90025900d158040c240c02c0503000300fa04507000540d00c000c04400c002001d92440628003c2001d86800140a0301c82483c20701c802100604001c0141941401803203d0381c2410040841803034001c508100d2159401002040705a000d20700884200401610131900341808420b1095181e03100d61201c45200f082ea6100030540c82d0104420003540c0d801c0200600841b40910144200c0e54012600000700a450403d8000042c05190403285442600b0b00b10f240d84d50045004820000c405d402107000324100300c3e503035811945601901c203d8845090752054403e058040c1c80380782600a40105034000c0c0205141801e2a1418510751 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 924215719 1250 924214469 924214493
    0x909150a0b0a080a051006090608040218130c06020106230f03061302040f0c02120f040902040b0706050703050c1801030207051005060a0b0712110c041508150c0703030c020307 77
    0x4408140c004013000840f0060f441842d921401c401d0f48080c4c514941940501b2051081c020031041042c0c54001605540364529000756100c2c9400b5000c2461070400b0040070a002d032000200c400070714001c4000b80c42481406140700751103408110700000c101c128540b584810920030001e4100e510010050040d039400d1080520486240c5407404020040c0c0c81000100c0b003001c426a200d1138540910080340ca540001c4801040b5404102c1e00c1d6105e5811040001601031540100011400018007154900c0e000001d441c0b05480f460061005480785807054042e02c0341240c5070191441c05000031442101c070101c0d120f1034504181801468020661141c0b0305001e6103415482d15140c1b01ca00740900c0d824a944018000e00c045081541004465681c065540840e5100340040090701512610006414011401d0b00c0b100184100483d80600081e074000305542d1051500c103000728910807202c14a080b0086210340c0c0b04159203444c080c0e0f43c1d5403d80c002d0881118550851200b8441a40000c150194007 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 924216969 1250 924215719 924215737
    0x110d1a0f0106120f090501050103080a17010b0f070519050c011719020901050706051806180d0e040621061803140a021e060114010e0f040c020309130e060a020909150a0b 74
    0x1074cd1581e00e000701914004000107080440c0c100d92004110644192042d60344003410b42c1c3c1d903603036034150505000386810000072202c039422189416803801c010000036018043c0000383c039011900c000350001c602ea200400c64442034003d00d0404030b884400c0083d4000d007160141414414201852512000304a07042120100c0c242d8000c3d19800380404020000641c1c042c00040400140f00c0002a00644440d11580541c0a01c0011580750140344c0d40c6420140250180c0349454200c541c06c031002c0500c0b1000082b041c4e4045141402140300d40aa42009101690b0075840d540c400c1c18070414656001e0380107092150860003064040810061404180d0900f66a103400034101c0e9410422001040030720301c6102c03418051314a241d0b080b651a507111031607490204a4001568124481c000c1c1d056108590a46600c2105440341d80700e120303416031112010448540031101030707503a800070700c0049200b0340105582c405402c1001482140312030b20702181000c4081d01d1f4105240d91030103d4921500040c01c4 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 924218219 1250 924216969 924216983
    0x120e030a020a05010608060930030705190806060f071502040f03060b03031c0203060f1f020c0303070819022104030b0a05060f0409110d1a0f0106120f090501050103 72
    0x140d80b003404800d000782009805c981015142508020100700d0b0b507400e0404443c80340030520b08284021101c00c03400100b00200884840781c2d030345050200209540e1060b4640194400030440000c6498030443c0054414074024060038504049044012510782000000300c0b400501d200b92103403c005280054002415001503030b110343c0341140b510a0540341d01000c4140207600034406810203200c5903ca4000c00703070380f2040069490312254081190140d0700801c150300303c5030410f264041c80d00303840403003418a1816825940780091120070180c49110703600b0040d000fa041400112181c1501c0c0c2241c80d0030030064011155050a080c03640da10a03541c48000d016170500108081041c848101075880e4806a00c4c0c808006c03618010700019100f030307030360555240500d907524403840230086220020500a6030081c0500884901464002c080700c45100700c2e8210039103000e000c00c2d0000a072607c402c1c1038914035120000b4606590141400034000d100000c0440ba1700d035107000c000f113a428466607004c0d5001c2c00c0 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 924219469 1250 924218219 924218233
    0x10204121407060e090103020402091305070504090c080c090621090a032a2004060810141e19020712140a020a121404120303151401120e030a02 63
    0x18903810b280240d88881c2c00d0100c400c00e43c10351a9240180a81965170403240142c0b280300070008204c09140010914491307034600703402e0290705a0070030003030022240200e806101c1000c200008aa1084054921940460301403041e14032500c0c2c40d0014100c0a01c0400c14040c1021101c450199496802d498100482c0c101524902c24560700103010301e1407113200e40e10420391101c8640c0078408140c1e42e96000d0001c003c00010725019200507401c1e01c0241d68001c0050041e00e4484c91b102d0784038000c480c9080b0410b032809030550181840e05140600c2440440342c0c5082c80203042d860b10000801c000d091812500c9440d1881200b45001d202400126016052020161010102c06070000d01c9903070721001641b100388400b4110030307070000e81c1a0a00342c1c8000c1060045403001003d4525010011007907111034800f1030040f803011101c0d014400442d02070380d401c0c80203019207200d120410300680103030940301c4207120040740b50f54015050200c800c5141b14000840428094151b402c5800881c00c140042e08060 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 924220719 1250 924219469 924219503
    0x3070c03090608041a0405120a11060609011a0903390901081e1c120b0901050d02011d1207030201080907080c1306031704060809060103080f0c01020412 67
    0x708440040c01603410070000a0070140c0316442000e40030801100c02c0140340d4001410810240700380008240ca000320107840b4a2000d4000d0a072400d114101c03880c500ca02c40008049140c110401030403680640c01c1e50303052210494540c211a4090044c098043c46000d181400c802c049201e40014000f04440103181042c604807408105200140300314442c0c20380c1d01c0180410301e00825613680313601a0f1040301d1b02c0c3e0f040c034054081c20211840200d00e400d550b54541013075100c0d001815009132841c00c21007085020090000c0049001e070a004643d000b21400c5807100c0194040c8642144440d4055004c2a90300f10100010315101031f2241049080d8200313440820031541c2003e07080b030700051080c0252045c50704291132079550341500250341e40306001c202d030504043c0c0441e1344104051600642190704100b0341d40d110324150360082c4120b0380010200b400007444900d011655a040c0c07644803001c1807400d5031842d10790055410046442d185c1d95420040080c40c1e0307001384040d0310b89901c50001d07406201e40707032 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 924221969 1250 924220719 924220727
    0x21141b071d0702150c0705120c010e0708030a05040e04110429060906030f040c1211012a0b0c0c07080703020f180f07120f0b0f010201020403050712050c0603070c03 72
    0x41c0c000c00540d8419001042d400c205000381c1c55010700c824140740d44510050038814038001c48d20a503449581070000f1014001c8a041d046a040c0301c0d4030b20b00f15140780b652110004d1b030b24428010f011300040d10a02c81070204442c00e02320550054000c810240070300c102c8600040c211491610211519400c00007028000e1056483e007101c050000c03102c160800100d170000c101d840c8002030a0381111000100054208030000940346c2c0030303040194400304680c4180c0750641416071054401030100b070903180c50001082c8540c0140c00040507a18000e803280003283d9800d171034580d000c0c000e10140f40c410300c40c1040c1c0a40400454004108081c02860441d2541c01800070750700310001802e0198047c01030307128900c0481e076101600040400002210760341c0f0312600310b60000075500079040640c01c28158003081800fa03004041e2004007100c5048801003548010fa00700c2c407451000810035000074008200000041c80040c01d41400b480541e0b030907460000020b28150b1044840c100814070016240d0249680 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 924223219 1250 924221969 924221971
    0xc010806040c1409041b0c05071203051206061b071503050f07050d090f0b09060901020408070e0c0904021c0b0a03150926040321141b071d 61
    0x105541c208804a03103210014032110100381d25402e40702001030035490940759680303c80d00080d0700696110140070901002000c54a12039801d0745c09200e071010119841a84841401d001641a124145000c00b0062201008600107120549c004802e2040c4015050301640d0b400c03510700c018018054250801d00404100e1410a000500301403402082200c160041d1044541100160415a0312074154010480280107150340041010601c0c11150040108088440e801000d00308140c842c030796034602c590303801c034095442403046507400904100840d141140761540c0206203900c40604c1c100010010030b0a82e8040540d407212050b400c113411140904500c2605840c0ba41100d40031500d5281d0340303900c0c01540411803000f503040d81c3c6104207410010b00d9075490110041c80e14001f440180845600c0c045a0403a00c0b054500e036030300381d0300c5a01c0030f0380210040008082d283c466800c02c1205803041412500106100f44024084000035400990104035203401490400c907030440d80020342002c81001d081c = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 924224469 1250 924223219 924223231
    0x1008070902120a09030c0f060f1a03010506030610120201050705010203010b0c06150d06050c070c0303020d11030c07060e0105120108010c1106100b030c12180f070609030b070908030c0c0108 83
    0x803900100000080e48919000b0302180c100300c440c82a1041410f244006003a00c02780c507614a40303020030f140b40001d82d8801801071024128001c0000790340e000203050300d0b08012103036040d25042a41d000d019809002200400203401031400a0414a40e90384a6007268000e810900300740c0c0d8041884000d29100300003032540050304640082c045c4410070040b440350058032800809003034441000805034100ca1054420242d0000e0565804540d24140a520742050424610014444612181c11620004200d52407000700b000104116807410030100d40300038203401514100311007040541d0407107d603100024042c0076800f0000880540d50303940946000e4201d851604035800000401400d01340604007501120b031050040c40d640d5441280c0d4400a128044018004e00782810910a000f15007486104541c0d440307500700c44034030400c3d80c02c1c6540c40050b4130540c00040c1c901407040c400586030070712840e0401071a0801000207521070031720500f1500000361030300546e408542d800c0550341e84009440e030011 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 924225719 1250 924224469 924224471
    0x50708120a08070f0c15050a0501050105090d1401110d0507120501030b06210a05070302091b040614092e030510090e03071e120302211008070902120a 66
    0x344250001d00082c00c01040b0005108010100240e002d020740780032811150b10403964001840d81841000c0106803c0e0b40740e0728a1441c03d070001c185940114126031ba9007100424801c120540c0d950b46803200c681080846170155240c650782a1041901c030094a0782c90310215001c1614070b4100001010100404180b00c1c2041c03c00d0010030200d144043c0c800d8001c041922010b1095400440d08111003070f01b103402c46194850303807031008180700300840e142c0d00fa41c1c400c8070070082940f5110f40400041038441000852102e0800041100500505000e020b03901001c0050782070465000010b280c0c014010144d1070b40c40401006041b2007180f00c00e0755031800600b030404004500705140d003484408514000c0c001c106036a8840d5030310030402041512000380e403014805202408840704e4035500c0b40480011141c0450203249144124041d00940b90074262544002c0c00d5000f2082001c2a003030790140043d40b84144003240440e10160034090003001e441403075000b50b07842e158901407050749140200040881 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 924226969 1250 924225719 924225727
    0x806042729190b0109031b0308040b22050f010518060a09080c0a03051902120f0304180b37082d060f0c04120323090a0b1309020705070812 61
    0xfa80e00b1040c0b03942039030740008904280d4162903001007054003041d0406000700300045130018400c000c0700300a020030000c030729006120000c10701c0240060859030086543c00010700b0b83e0b4020b0303544580007400a143c3c02c4444125202205408100b003a0322080c0004001503a100061014010801448920300c50035202045d9103451900c6844d158511140d101030002e441c601b92a095540d18188180046000d109850b084c20010f524140d9950182c42021a000507400c0604007001c1d0302c3c810701c0b00f444000341584400d40c5040140700c4200513041d14081c01094a6480d8082e9070042e2041d0801404441008000601c00d00e000810a01e401c14a80d43c415201e0b04064804201c0121f03045402c60380c0c00d170840740c07151502ca9042041d800342c0d41201c0101d96410950354281980500801040001001c8003c0d050400d1b0700f00710b445e4840c0c4580b46401101540d0f0030420416401c006041c00511070ba446003030f0700d0b190b501c5030081c0d07400100e00b6901e070350142e0000c1c84811403e01c603491410041d01c2c0000c1c50 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 924228219 1250 924226969 924226991
    0xe010e040507140f04020d051503070b09010807050c0303040c061d0a03110f030d081e0f04030e030f03040e1b0c0a06150e1303080604272919 62
    0x2890086000d0b101240340405035450583c0c444c11508000c415004000b5501c4e007210491a400610048a41922058084103480c4582c20007041c0314003038400c2c1d08100e03480c0c2010300c0019038800001800a40400804104421a849042c000741d40510301c21300d11070610301d20388507004040310680c0a04940084c20030410307411903506d0382e00721011640d220280c8049030188500003461304120382009901400740c0309000d103020341c3c0a400c01c0d10032200c1941150301546010325003000b4003000c0f00c29020b1a0507160201d804a40035000c00020b22600500325500c0b240c50610050030340c1c016038811381c00100300c4414403042c0c40007607180a0548851101c440c0c18510280343d82aa10b417900a0043c1c00c2aa4035010348080392494140280035000c61141249113041805107090900001c0b00117400044980e000724440d403a180c007415080c00c03602941030b450b10405003500c488409800500b00c0742d92080c1040d4010b030101c038062444a05001401488030f83c6010300a0100700458920501c1866207010074000c8 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 924229469 1250 924228219 924228223
    0xc090b04050405040804051503160203090f010503090703150c0306090c080601140f03240f091f230307060302041802070503090312040501030606110a11060f040905010e010e0405 78
    0x400c4400840b40400d0903101d81c01d2101061007a07400c043d8020b0a0390004a1403904008020740c024411407800c2e0160004901080303880c0d014411a15078441035181020174590f1041002e56000107081c000c1e1422183d41e41c4e503110b0f00d211119510352055481e8400ec90310385416115072070041c600d0440505c40756407040700042c417040c0c0c01040311f4144443d440800752000c00703d00503561058000446c1c940d80341001c8901a074610012a9a5a50f00000f484a8842c40c00c0c0059050b6041101401c2d038139481e05c43c482c11105c00400c0003440d0200c4200144002145420100d203100104496002500c0090304c0e5010b00d81000c116030022001d150041008022241318200c0316008a68900c0006803246010700c0d10900314800c4004180d0b0501ca0040c010a01d01710130b074000e00496801362001c00440395a04c0040e5518501c1c10b030060a01d4000e00110404100710365140400400014030b51480c100c80347c1494205a00b00c2c0d0003c0342c060340d031840140300c402c22000020340581920100c511180c9011b58541e6 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 924230719 1250 924229469 924229477
    0xa050c190206220b0604181703040c081c0e01170c0c150c04030210050903154309180e150606090d061104230d0206160c090501030b07030c090b 63
    0x600541d91401e0a60f81490484190344000ba40070803118035200e0880803808c1c444c1c01c2541c090759111450800052121800186440c844d40d0b5045040081402c0a400382d401c08007929445040c02081c051081d80c0805800646100c4d4200c440c00b240c8600c100141c0c1441d00d40e000c048000340b404241c0902003207045c94400d5804495040724066a019140c0b00102c40c40d0150205403030701441130840d14000c800c410381849100c1c451108a14030354000b46140341c3c0a02114590080101e8241c4401408440480966480700505410140001d65486c2c490740780204a945007940d00b540e41e03cac10442c8900041c00842010002c82c92994418200400015003c1c443c0e14ad9042c418a6031000c10400c00009401480019103848100350301d030341d900d400c1c040a000c01655690004008180303e13011515140e52068841038001d003519083c6400601d0000d21041201e2003030700c4180042d24001030014003402840c2c01b85100700c901201901f0400c901400303030340d1030b00c801b5410f1003100a42030040d602c0d540151 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 924231969 1250 924230719 924230731
    0xc0320031312090b0415021c1b0203030c03030103030f08011a1903060b030a151d130312090f212102070c03110108010b030108060a050c190206220b 65
    0x82400c0c40955402541c20f024940d0040c6120040443e001920481000309802c00d078026809030783c44c522540d0b01810b412441d491000e00030905006044102c0d412084c0d110070b00c00c0c8050100c9181c00ca4440c02c4502d550400d03401140001c4031025030b032142950061041e80101081c48000e000c41e0208a40d400b050700031103688052140f0f0591607440e800d8481d401807001070500e0040d0641e01d00345490003002030880200c400c20801d0708131000040e800308048518001402541011103280ca6140f41100c480b104050b0039000c005103819140d1644c05944621060306101c2d0760105400386251420202561080a04421801e44440e8041da02508404103d00c3c20980710401080f45021440c544024090034070301802e14071703128170040100040d01400c40c9449409880d2555141e0f80c1e90201d5101d80700900070803c0f1340e002840840d0542c142d031307007245401040e14070035079042074228003064001651203851040140c2c000c50501c20b4240e07130450052050003c4005003c5510b40540311100822405041 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 924233219 1250 924231969 924231983
    0x604050a0611091f020f030405210f24010803030601020c10110303010b070c0806011505090a0306050a14070e01020c09070e0d11090730020d0c03200313 67
    0x103200e03450b03050b0882e034200000610300c9400c2d604004411400350614080030f070162050f160105d1801c2d80c000191021100002c20302c518803003030030408124484180322a801c5a2044080000f07103a0790500181d1034600400045030500210305240d00c8190a06034400313503458004000744020760343d02203504445d42500780c8004144502d0120b08940d840e584020101030780c0030103c008504003040030001e01c2c100d40684140b58409840303c6c0c006440b00001c0c82184c400520210000c1040c1e8020360207090302910040803826640d0762034a0780000d450044139405076299485003840c590007140780c3d00c55001082072400124100c001030000c1c2d031319800021060303c01c000c900000784d889407180c0c0344010041400782104454420502d000725148951103582d41c424480c010000d02598450103804030060728804181102ca0322202500f40d940004a02503d0015000c0214070076a0109003e20420010141d4000420407024810440240743c0004414520302c0c08006002e030314400b61600c3c005007070700244 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 924234469 1250 924233219 924233231
    0x108030a11030d0f090b060906010206190b0a090f1a01120203061c030c0b070212030a0f0603080c070e100e01170f0616020d020d080c090102070b04260604050a06 71
    0x1c5050301d9030264544400256040885101802c0b03540d40003071a0140c440e517001e0000352074400812141d1101158214016403004e400540110031810b000e128400002100007113203e0300ea00070880300300043d0000010541c503110401c42c0340415100b1800b80e1000d0b007001d0950200c00d840001d02c0e495a0501021b0000c1d000b0020400a9072510419420109503000c40c04030100e4600e8040c100000c00701d8103481402ca280002200f4030f0021603c241090500342000303107983d550203401e0008281e14161816415660f00010000030482001010f1541086000b024251b1408120342c00210b801004511024500d070000c0115643c0c0c0b00c1c006042d280305003440c0849203101301e111031070051400c803500e6281c469141803180b0f0b8480480107030446085c942c252922804410801c1c1d136144040650b007000980c8a41c0008c42520184d0041e101441d07052056a4459640d5102c00103960800c0d009258061001c09640101110300481c04d400e04c01f0800c06070040d890161a400d495032200c900c0600a261144 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 924235719 1250 924234469 924234497
    0x121b03020702011e1817060c0d1e0515150412020d1a04060605041506031d010905060105101b30030f05092a03010e031612080108030a 59
    0x1060206075a11803020800003007442da1000301203540300000c0350700185c42c0fa103020514203e0b4100760541400001d00410a035110040c1c3c0b929503612100304c5e801c0c4950380c4d0003640780c0d04c49180c01000411100d040c002c04e8a0a00480401084a009010600c00c40440300760b1a110035203a070075601110b03000301c90440d0b00e074103500100d541c140c1400d5004000c0c000000d6141c1c0a80015801c05000c0c0b40164410041e25072244107110454050720b5806041c401ca07224100f0840c0e05c01c3e0814050b6001e20540390764410b00d003c03001d60079214034803000c442a40000d0014040c1d8103111031465241005450720311403a2003d4119002d01d4010280d010306924841c21400c0e10800f03070401d4041034001141e0301e22044518a20000f0014181034810b80b80090410740170484816000686c03103080c0e00008004900340740d580e50308810507195a041d150301952111201d85105c230003030020b000e276281d440b60016000c400c20729103005020280d51710350080c0100d00b80180722a80e0000151521005030b802c2500c0401150 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 924236969 1250 924235719 924235727
    0x9070f230a0305030a0810050d12031d0309191503020a031508030706060626040510090c0e090105010f0b0d0609060801060905060901060c230a0b0403121b0302070201 73
    0x403152035600518004400000c0120000051170303003070803960701c0141c40d4540181c0350303580100e50b00c10f490b03200030060b00c420041441c5000411036038105003000180c42c0b034a6035000344041c2800a102c0c2191300041019001c0c0e00784003a00e020000c140a103070011850611901c2a2039a0101482034105503001c00c2082103103001e90b110111012660003030401e01036462811071394950008104981e540d08288002640501074065440406158900f24601424071444003c1e0f1240040094903584034034000c001210b5800c4c41460b400034015250500050b08000d00e204104001400900c100e83c9804010411101d0901c80c51007a074000c265050380c1c1340902c078105805041c0581154203003920b05200050340c0803055000310112100400306000595035402001600603092003204081040d60800000285a0b11a0b071000000441740e00f0490000c0900981c3c40c004841a04540c4000c0345000d02c010b2580103100c0054403495600140059040411349590b60820080b035007007030580100700c1000716801 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 924238219 1250 924236969 924237029
    0x170c070b0109090305221a07060b09090c06160c030c1a0a09030308090a0605160212070804061b05010c02010902012a02090a0204170610050612060d060615020c0909070f 74
    0x91f0840c00b041003400029184c0350f61015504076005031401e001018a801d008003103920a11840000d40342c01134160007801036981c00036a500c00301004061100c4002440c81d8000000b0314014114040d8850400600d8000c071080180c5c140380c180f00c20701440c440c280d803040400003078941c0340c50034450645515820f84c4c600400740c04001c1049040c1020000443c4c01281140c000c0c0c507141e404c0b40c2e2604241c1b808420a4418240050403055041000b40655405010341c00341c0690b0f150010074615849445550849a00011200040c0d450780074140666920698042d00500b07a2100000003095285001000e20140d81001f8007941d551400038441d210142c3c1998001d144401c110200b81c12030001c841c0e200c42c0100d41a0501c0c003440c010104450034140b0994200c11794050028036161140420440e089903c00300072524543c556002107500380d802607141c1d10302a05d070b4004121a07021603003000304201000384610501e070f10005080011400400c032800844401d00b141ca100d000040800c0d81103921 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 924239469 1250 924238219 924238229
    0xb15041118040b0a050916020a050316031404050d110102011506020f12071e060b04061d18070303140d140109141015170c070b010909030522 62
    0xa00420a0400300212501220460700c0488082140864840801c00108080d02807990058241400500746a858002600e40072480740111550501e03590740f005d24561000c00b0704090030791030b28116130401d03401a022902e0a112400050b00341030030040400e00341d000451020b80358400103810829164001c0d4816856903207041904624981c850001035550001030440c0790003441410420042c00740c0e90130550b8140e80d0301482c40d4003488503401003240c0150340361509580140e43c500340141030b41d40303030710400c002030200300f4071aa503010b201091448144e100600c08031524a01c1d90385c00003c09004210603058950508080b2070303600401e8915400c0380104185c80c4002031410020780c400c0d4110030342d80350403949916000d0060081500321154244016201450960f245a10500014505113114142041140760507a50031400500400140d0029110b1800c2c07924001101c0c0d0a10105640d0207016104412050002a03c103a40040544c484d061050b40d91402410004445920520301040205 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 924240719 1250 924239469 924239501
    0x703090b2a070b06011d09160f0c03020309061804020307351b070b0106050903010c020a020d1e06020408060f1311010f030e010608010f14040b1504 65
    0x100c0d040540840c400d500751048524904050081c403039140301e1504a414040c1d0081c9866015103468005481054400919400003450250031481c0307515a040581e100c0e41c13402603035a21074001c840001d0600b540c0031803400108807203243e007000860340000c07c5640d06a0b0980300117030381d02074040440c85580403130405164014000024014074030360180009641407031021082071038504a8115640b40314071020296220405040001c820f81c4a490400303110040481401740f070089103684040a02c1d0090b004840880d0000c1040d03d002d0500b4410314044502c3d50000b00790701d0145800143c0e00032542038000305080e05001c2d0b02d41c56402c842d040700740781581c03100d015501d5a4032002001c0d21004110b8112141c154040b0009040483c101c90200c0b02a03041071843d5420500140111250602c40d0000800e05869210542803003600344030b140c005100c080700000b0041011450070301a00d0405101080e68881d010500c004a40388181d22504204c411145d170a0b242c032102d0101c1c01074010b0f080120540 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 924241969 1250 924240719 924240721
    0xe0406030506040b1003151109030f1c09080601140607020d1a0606040b0a0309020402040510050306090106020f0d052b1e0e0d12090209041b06051606050703090b 71
    0x100012a90700461185094144da652401c010360a400c00901c0040d00c2214503400f010100d01035607111350501d0720240d0f01c9501e0201c410011a2800564900b0400a540b0020030000e41d4107108081c2e203018100d61901082161030007078042d544000c1802510360f00a034210802c2160ba50305401c0303406c3d45a02901808040344141890407441c0945003100105094040c00616546848811501600d203900314590038a8000c110490040200140803030708950308000200b01ea07036400c020841e40003a5035440d19907a00c0c14400f0b0000004060380810159800000b038401d130050041001c04100f582498040d0700e460341d4154402d059020505014031340a00314052142088640e00101c40000c0160314010400d000c403590742c0202d80c4068800b06154002c9501105024440d8140c0130740c0c14201e040200d080343d401d800140e048403058600300e0b032280c540341095035803401c13122502d0000c0c0704c0c500b00241460340160a4021680c03141030010300013551903001a69540c043e0b0311159419412034442419 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 924243219 1250 924241969 924241973
    0x310050c0c0607090b0a0f140309030c1501081e1c1d010f080c0706090c1e08060606040b0a021006030c14030106050a030609051903021c0203120c0a0e040603 69
    0x46600c41c5034008041d025440010396268003c0407800205c030081808180b82c01c0c600d103400c80d10b07a200c3c4c56146041011045941801b8481d10015500604240b009155140586030126140009010b00844014030400c010040f020700880c03070031405d6001e01c0307000c0f095020b0444c1050400c04c0502c1400910b034608020385400b99485070307103201c6036582e030301d0740c1c14550b0904001910492981c2e8518000501c1c0a400244800c4e030040c041d25145102e0b03800403e4a0880340d031041401a519041400c01d0f24681150240e54202981c0c1c07040108000405070100d03041480201e0a54403440c0104d04000b180026912401482041001040140301c50700304450394507803400030070103007007480f0b8444010400050b048091030184101c80c01c8541c0280040d94a91a540d151350180c024000140d815000d14070510300c3d042098500301d05130510a038003800d06041c40c03e4520310707071a402a240c8000c40d031007403200c3e0342d00300c02cac0e039171415040ba0450003501d44803d520041200c00c003078040c101c160010704050300081 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 924244469 1250 924243219 924243241
    0x506071d090426040e040602120c0c03030609100905040f0c080d0c06150b0703260103020913060b1c110108090318040213152307030e031005 62
    0xc02040d0384030510505a4034100194290150340103054441800400e00c203250b03140c2c140c4041d81007001406414543ea80400c1c03a011001100c003554480d070001855000310b40c140d80110f41c00f10384582c105003842001003e040d039038007004000303500030b011140202d0000c145416240b00142600481441145802d01d05a21039590154080320420034415000ca2400c0000c03500e03500808040d50b507000740705026110301e00604483c0c840f07456840d008640114516017000e00800c3d0f1603010b0740300d01050228422120b0344598034800d484100311654001400184da401c495250000c501d000381c20485c11032801c10000501042c024241d000226204042c0c04a404000c200b84a5019080e856001040000103540404c0308903000041502b04005ca161040c130450703a0308401c1040035100504260341c050a4040d03d2605800c8070b43c0d10054200d04000099100c11043c201440e800024442d44c050380c9125509401111801001d00080311000b400e40e8404000800340c04145903c18881801c0c1000444 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 924245719 1250 924244469 924244487
    0x60b030c0c010510140621130309080303040201080403080406110406030902240405120c2707141605240f010609031a090f0d0905010207090e0307020d03020a050607 72
    0x99070355090000044d0300c000c0300c1828400b19820041240c01502d41e0703100b000005d40c001d4040e00d0040f400d801080c60405024044a88641031024803900014401d05000c0c0c0807003101e600c4000030b076004004000050b68000c0d13429802c40c0d41414000100d07101d500d00030001e42511f12103d0b00d00000031400184080c1c3c1a04030b031020500940e80011100038004400800150302c990201301124104003c201070b0800090400740138403500107503912101d81c0c074006010008410103282030048040e411012443c046424107400041600300f070f00140c0f103e500580894041c0090019192000d80e1104c42071045c14010466120030501140c20203465a80d40003106500030350301300900c02c81c01c1d800440c0050040c211402a260842c40076000f1502000d499100300710018941071190091416000c1e0071181004074980c1222a6264603480078109000240703415900c1c0d00500c98103080c22401000c1742000300031291500d4051310300704d8034181c440c24140e250860084000304140300351010006d078668440201c07 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 924246969 1250 924245719 924245737
    0xf070f26240607020f06070302100c09091409101e09060f0605090c0708031302031f05162003040e01091b0c1109191119030c05071104060b030c 63
    0x1200c01440c0e041841600d0141c0440203421016092a40b03040c4c6c9001d001405c0100c1c0f0910451720041c640038100e60035540196180000f06250810500590829002c0e0300b031914044007034580070385001c101e4181d0744c1304031501d4142c0c2e182d99607010300240030414a2076081c4101c0d50000380300209072880d10800501d0113120480d400ca03d031140108151074050203550041d0f026074100307410310704941c460580a0340302a064040c1c603004100e511005840502005845041c0d900307103015045d41448500c000d85a00908000d1480e492640d0440c0250300f10f0550060549126000020b01c0c09a40106245220340d13000f40b51020102400003400c40030070b40005d55007071544e04c40e00348030340380008040d900d145525000601181c4000b054004c10705200c403041da0702c0346100c19800529030354941c0d68421074500b007249594500000559007010304455001506100d280d260170003d40d4200c0c04002c20314018072000504d803031468520414540d403140c02c80c00c0540850b5801641c5c0e81800301c2039001e0f81d40315003a1 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 924248219 1250 924246969 924247021
    0x906102318010201050115120f061d06040b10031a030f100c09051509030114070302120912040b030a0603060c03050405151012060e0a030e090f070f26 66
    0x90101e55407060017040e04071903035a2442c504082016100340c8d181049006041400b5a4550380e41071240c031b484c0120302c0200310304822541400c0d000e541541111400a00d154044c0d82801c5030102c3e40d46645400c030300a1096407400103840c4c1c00e0078030842141d010240341f181d8988604c07035101c1c0145401050f004403403000003c08001c003510302c00f002d81c1c03d40118420542e00515171110303400ca04c1314000086c01403a4008000140c8001494144840c1030b02c11784400c800a81c0c082142803d0707010542102c5d8005002d04014105400f011014100310321840c0504401c1000c0400464400d01440d0080ca01450b804001800300c2075004c2c0b4014010310b81207906070386522031410005483c031120410030340039800c0131100e1003001e802d0040300ca400c007500340f00440e111680c442c0300c4100a4410300c00340084611981d01d08110b1440c05003001318107140503094000d2a241c040c280840d01e508180786052210f154140640c450389601c4d02541c0482c03c2d40142c1f04170b059003008100c1c0368820070088140940da0309507 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 924249469 1250 924248219 924248257
    0xd11060703050c070f02030313030308063a170a0c0b1f171002070f2d0f1a0a0e010c050918040f0c180f0b09061023 51
    0xd084042d41d070281c03a0500071480401803a0082140d04800342c0c0d00c54005030880c2d20303203031603042d45110030710580d401900092010f60078403070300380352441c4940c5100041d00c10382d0141c003e1030141040718142c1044040c086c0180c40c1412002c00c420251540d004c004000e0281c7e4841c0d40c13907100a4040002c821081710b8011100c0300003880348600e201b84440043c0c4064a50768098184000325000074441940150103116000c2c0c0d1001c2204a40000c0c0682031046045481d02c1c8030300c1c030b0003213940d10b61138072005081e0780c6204510303406c0f01001c8211315840b43c1084090894000c14102400c0c060302203501546803018043c1008021011500306905421030b00000300081d0078001d900711058010696115808028000940c00c88031032035041c25040b03800361140131032811403541d460183c65103d511542031986858122106a02188207050654900f45000d0140d4030108000590340c240040c031051103034006e840107100c01c03441204114076004010142c1c0d4400b13046058140c1070742c0c00601802411000d000 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 924250719 1250 924249469 924249481
    0x5132013091802040509010b0301090f060509010c05071b26060115051e0f0a0c050705093c0a060509250804050c030a120e1503060f0103020c0d1106 65
    0x210070b000b100104542500b110010350390030000500009483d0181564803200c2d01207981d5420302c81c00e52042e01c0707000b481c41c503800701d4078000042d1070005003040084d03403400100250711a0440201d9001d07540c00300041c0c81c203500002d50485000e5058018002840700081036480c500c1041c1460103000c2e9003802120440d030799030b00401000001888010300081e0050240d20070703144118844508103c400c1f15054200303005402000055088096800c00044100c0420720900c8400d0085038060031040c0c44144542c030f4004c8540101d0251502c451407907041d1904000784840c2207440325482e0740708560f802c5569041240382440501401d00925224a04140101d070181c1d2101042d100440503400c214804d0351000311044d00d0780c0700024400e90b81d40c00b8840c48805940d41c203115001900c0d10815410301898480c140061132041c42c29203081c0955219401030740646440c000744c9500034002ca599100040e00f10004074003900480d0040e100b070b88504130a01703c80b213410140740d620300b004120807a6056070320341e = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 924251969 1250 924250719 924250721
    0x702190902040b0304201e030a050f1518031e16210804020f010810091103100603020a02060f0a1d010209090606071a0604060e18010b0a0b03010513201309 68
    0x1c40e43e1147c7c440d4605040070320341ca80209441480600060036140c80b458552076440c105580740208449981044030b26922031074454034620342041013400e0352070800d8000000c007981c0788290704140304403644082c40e480088074908211a51280c2030300300114148032030f00d8a003a90301c0d1034505000301c0031911031405a2141c4644903e42c411074000b0f14101d94890000c005550102001d8003940174194031440c003095040c4070b4083c00c0064045100c04550742c0ca0007540000b001c181c00c0c0c00c40b00c1054010000c1c01e08465000448907044211901c0c1c205a54440b001c442c00180812070a01401149810055012074819400742c915860103807040012a41c60350100003540c0300340c1e90b00a158000e20600740c00b180140f0b0303c00540c0004081d1001138031750789501820050f0b0310b00320b030301c1003483c513102c0d00620a80b0310030300407070b4400201900c04145460504a411850f4001400b60f54090700b50140000501d00c501c0c6c0203400d0f03075071014004500d001c0c0c0440504042e940403003940180301001d260001068401 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 924253219 1250 924251969 924252023
    0x4080901080702060f0c030a020f270402130915030203061602070b03061807120618180c03060203070203120a0c1101110a1d0a0605070b09060c070b0411040e07030203120f0702190902040b0304 84
    0x485e07050ed2000c07400d14038000c0040904894001e400a80c5603030200058404001ca02d0082581003c015507041000070000c0c40c008240d002004d040c0e10a0041c44450344880f400007401c0f240c8841003145640d41e03044212500110404400c46440c10001d0003d07040040226500b0f1941412800380862f400843d00301e003003021080360003485824003600820109a0a40c05150020401d1054030714180c5010403081003c041614090502c55a500041c4d03c1e0540200401d0304489800c002802150400000d002c0240150309408040c070170001d1100621240081112544039002010b503109a5207a604c0189079400c0000216600d0b0503490200d000d009001400510447d5142f0718140740c0341955941154541d409001261391300c40c110750300302180d07540380036030580985200000c0405510314010945444080c01107078010070707010001002d508102100301e039007481d01039940c007003040e44031080b5202240c80b9078003030b403981c2d032001c1804100301103490029805107001d18545e0700e0360200381550000c9100c0d = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 924254469 1250 924253219 924253237
    0x4060315050337150b0405061e03070b03010b04150c020f0f040e011409160503190c03050f100c020114150d060504080901080702060f0c030a020f270402 67
    0x10180e030b0349440300a00c942d030314203d10964680c03405802c000c0c89011a14083d143c00c00321000118a00050303031598907485011403003641120f0501050401e2070100d800055980309021001c4600c03e06c5001030b850170032201c0e00074015185400d5580d81c0d07880606440781c01601a1111401610740315113095403040707495060f811b800510000c400403264040004040c1e048860a80103525105001c950103000c0c440c030304000c012950016824074240020078101010300550f1803180c1241c107824000c076140001e1800740c030101c14541038108800d03820071107410300c11684010040c0c0300303004044400050120750554500311056007800107000c4560145c3c207903002004800480c1c1030200c002800c050205452074500000a403500f000b4126689410094403c11070b0b054a200034005607041d203c1d6404117440da0b0200b0184080e1581e400c10301140f0b8411080a000b0741018140880803440e00107555048410030240c03c412075541d09850030f000d000ca0442d1001c0c00820b1f20b08007442c03940d11b080500071584041c0e = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 924255719 1250 924254469 924254473
    0x31c0e0603070206071d0d03080f07091a0a02010908180f090c12070915090f050409020d2a03050c01031d07180902061b060a0603020d020f0d0512040603150503 70
    0x1175501181292505d02011001d03640e0419040030305541d85810904101040c000c1d990b0140b10310b45660320742c081e4040505402c041101460741000000704001020038041030f2191030950762103000e0000c1740540200d800c0a005002c4c0011202c8010400d0014205820420368400350030030360810801900c0c5501f216040d0540b1420000c006924000c4042c09500c240c450a100c80080d4941c250780c80503040500400c5c0100d2581e02d0b0502c1240c1c15403010100624044030b0611001401d54007084001740c00510040082c0f040340c0c540394034400c0c80200d5641443d520020351030350594900f04a40d484220314503103808680340551070141b104070b1400b00c0038041d1001c1d000300245890720130750503030b00c603820550411081e581d84034000040e0368160050101e208102c038003c0f001d0340d00d0705400342400c00140445a5191820700e04000589840070f17201901c41d01240c000d44480b040201150040351600b2008200b40111b01c00d0004020700d560142065070381b1603404000c0c0201d4038204101000c9107018865041d = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 924256969 1250 924255719 924255721
    0x3030307080f0402210106140607050304030807080c0303070905040c08060f0d0204061a040303020f0601053d05030718030b0c0c0319030609051f170309031c0e0603070206 75
    0xc06403040b00160464809810391684840307605241072100d0400241d0620f17651908020014010702518107040040b04881440c502005a40e03420b80d24802d51100030441c000101e002d134240900301d81a109400f8401c000d03241c0c1d920741140010003940413406000d101e0341c5802d1884500600c11000e1a11a09011b007007512030540113010864031400e07014049900c0b907294040461a040742220036051100107010803a11241145000b03414480e080c0009001540460010090790789c130080c2031800c0c00c11a812426404c181003911905007840182c80185a03460301c0340990500313074400e0041d4441c071410382d181c01070080074603402d4a0404803444040c0440a00344041080407022100400e060200c00f800ca034640100144d001d410f10038203456010102c0e030f484038208024100303400307200da000142f401c1c007070841520807440020b004554010150305440c00103a4508a0804000700c1e096510020300301d807840368520204200071154160f0050028218006403e05801c04500b940d0003001260050045 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 924258219 1250 924256969 924256981
    0x6030606040b0f030a06060f050108070905040c17041101120c08040627050607080a0c05160305041a0d0e0604030816020c0603070f0212031003081c05010807030c050303030708 77
    0x34010b42c0c00190390002510003840c1140c2d9003045400500c030700c504004180300741f810111000c2d802665211a0500c80e00504200c401540701c00d24005132582100c0c0014040300e800700c1182e12841040c00b0844140c0b028003480140b240d480c00007204100260784800000c0a5907403003500b69185400e0301c0380440d0440b008500040c0741c5070000510b007140c803c140c400030300c5424100e5003040b200c280252102e820200074808100e83c4510241c2e0701131000038080c031500d214100e0041031031054034204251003265503020f80400d4466000c5030024589aa101c4401d0542010418150390000510505c1c0c2d078070b000890700e0491004208148140d030151071362026907490700c0c521007186620b49080001c501402403601600c3c0c0d11000554040e124540c0e400c1d82110803600064609800341212a4004405100304a90380041c2c10030003041d0f9031300642d030b03985900c003901303111103003042c030100c1d200400d03041000201d2602800611302048900030781c001407100d5500c100780750b103a11060720400f00080c041d40004407 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 924259469 1250 924258219 924258221
    0xe01050702060c0601230102010c08010302060d0f021b07090c022104080601060c021014031303030b040207080c12031b1602190807060809030a0f120903080417030603060604 76
    0x201990000d0030b218505840c0e03111003800c11070260840b5a0b421003e08558415483c401c503014100300e42030000300b00c0715060b0100a40740580510000748030f960000313080185114550007403076803511080030075500d980708003802080b020825031104200744501030700010b880c00744e4010a820429150040c0803059042c01032800c0c0303000c0f0f164400e4240d400070000060b01c0d000030490359000701107650710350f6418270a500c10060504103650310001007000500544d1400c2d00340f10222074024a0443c401c480301c00c030314502030340070b000b000c00c0d0282c0c010b01c007140e1207090181c45002007440440040580e40d4081d161200c1d1840c600044d2014094203d125600c038040a00c214003c0c1400c44146010a50340f141b19400140851001d41c1010711920800104010440082018a01500f9a401e00d0a4903142c40807854ee660f02420500000700b003440180400054050b0744400c8400c1c0714000248150b070a14100075000500998003280d10040c201004a810b2901c00f040d070b405503c004000c0c00d41c5413100e1007004 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 924260719 1250 924259469 924259477
    0x18011205070e13060506040b130f090c0e060405010806070206070e010c230d02030c0c090403090807060206090712030c151e06030b0a090b041b15031a03030a0e0105 72
    0x100e580c841da080c0855000411a08107103da110066150643c0026103070660507900060242409035051042100d403564070800c000d2010608034000080c0714501c200c140c406045001c0340a40503050503440411041400c07061a84108802c3d82c0071b1140c0e98ec1c070004039075a050101d5a400040e0850000f00b90000d2048402c400e030b5103014034140300c5144094554041350f06100315058642d400d07003d10000000014890399006080c9070002e503003000c060442150301c540d0320141103449050560000340425001d26104005800c1060444a1250700c4e5100039680d6581624060b44030310a00e000000c0d0040c1e540e4440541030f81c103542d198032416040d902d00112501c1c0300e601281040c0c45d417030b2100d50302e20800003001840c00d910f000441c0103495810200b100034070280071400c040d403c000905010401e00404140c020b64889121001d204482295281c802040c1d007020842482c4003442c00000359254110114440c0440c0480d150000c2c0d0380100350703072031144141c4140800c801d11160070301980208058 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 924261969 1250 924260719 924260723
    0x1e01090612091703160810030204021303050a240b0f0907120513020909070b03040b0702010e0604061b09180b04090210030e07060507051509030c0d021b180112 70
    0x1c10500103580e40d4003c0550b10011207246107070007004200f80481603101c076506001c1e0b64185010141411910324000c03080900001c1e000340c2d0001400100d960411080b4402903400c04181c0f0210a01c1e4034041c0b8658805022a241d0051f15000368014500e6511030600708100c000c1030401074031050400c0c4610307040010400703000c0c0708243c0403403100d4205a001b81d91007187d110f00b0060004002c1d104102d89144054605c10740b5501c42030b82801505403420440341c04c0358002501108550365207004902410401d400b011300c034040c0c1c005000400080303400510325407003440c2c6150522030780c0305421242d03580030380710348d45480d40441d11003580111141d01004581001402c00300d6089130580102c1c1720280b203400a00c0c0042d03910010143c9000c1c00380200000b070030380c9180c114646482a2510359603062040411502034a0b82c1005c01d4403c8001c01c2103c04806002d01500d280d020f0000c0041c0d1600002000006c4001e10310361450581d03d0010146041710142e40f502822030307428803200000b0703002800e6003 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 924263219 1250 924261969 924261971
    0x3030f012102030f030d060608090c0415090c0509090f0613020322080a14071101081021050708010e060a0902150301030b010f0b09100c0c0909050c1e01090612 70
    0x1031200943c4090041c002884450801160b8803603045900c1012541590f000c5810092141c091051100c00481d035846141000c40b004a00840b04000b641c041d150303d07621000c406413910f005c00718265000310180c0100710040711070a03c50b54405180c2c0c42c4140045642542c03020710b07409910609905980516004881d40d801d424940a5501c142072081c0c2601074180d0b240107010078660802644909a00a00c4e5803c1c00ea050800d4a01d07690306c10999003100c04181400004400154501d00d08003003400148109074400c076060184103c503c0d030278180b41c4000c0d03c880c02042004146034405000340003440710201c0081c4144da440241e82001411081e8040781c0c00352a0500360034103541090007860103540110f04038909545000c2c0061002c41865110034280801809101c030f043e40c50320307031079502d2010f6410711414140051500400203006500581c80c903c4c41e000c603505c00d11200203901144004151403603000c0e0452502c3d400042007015001c0b1380080c070400402e0001900c1280d20300301541220390 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 924264469 1250 924263219 924263279
    0xc0d0e01060503030d051f210602120703090302120a05040314030c150108192f031e1b0d0201051c0204061e170c0a1e05070c0803030f01 60
    0xf0b401d662102025a000c9910f5070140084d61418001c2c07400a04241603048030b906140c91000c90640741d84c1502d102c0c0c403012040c026002c0c010305404460402c408081005010b240c0348001500074041400258014842d4070081780c1c003a003280046800c032004503114941402d1a541d91010340d42508070808810340410b020007850706404000c8464800300a14020101d58103108949181441d040d00b2241a0021030300c0702808a01c544135980126490b54144100d1500c24202114103000355400207901441114160f2041b5005035800e9406420082c0c25180b608400400c1c014464800f0540c466000c041c886403000150f0086004004030b40031580341d01d2041c050311249504a8221342e111a0100e44116100380c0b03401c45004039040c0c20042410031480e102d500e00400f8111240040c03081c0f24244c1d0000300001d0302805040d00e03065a80d480018510351803c030034402400c8e90070518045511940744080401c03c5a00401624030500c0f42c8403d101e0310303a10b0070f01a014621f500010f510341c484d5500c0c0e = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 924265719 1250 924264469 924264479
    0xe060c0a020301050f090d03060b090d0302012a0e01020303062b140105011404020703020c04180c0f1e0b070201212a090e010312050f0d051605030c0d0e0106 69
    0x8011035204181d45c0103043d05600d051081141001d00c0c0c1580d08080516181c010300c480b924007030507260400c200f5580ba11140000d8a0140d00420314001c030f5100c1404030144244480744a40801c50f8504070f169a400c182d0075440e07005a0f071383d01007540e01640c072501060009400112010b504120610407445903103071200e007034890307107031580d5140e20102869445078010f2003401e21510f03030449004402c0d0790071441d00c4001d031002501c6c1e40d46180f5030342c4110345070301031491000202d8551601c81b50700250081e900c0f036580d00c001c42c0c92a50a20402c414104020b0b0850000c45200040c0300490760f03441c1e1081e1426407158011101e02c0400140340700e0011544c2c4829202020a02c600c100704000e4100310320f0700910000d501c040391f42e2003403012402c000b02e942051101a804c4c400260442c2d41c4058194000451440187da06000b6861464103401c00030800d0a14260f03580c010703d0140b400864802d90210490108482030300c8100c400804401042120600c54900382c0e10400040c1c25031030001540035110 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 924266969 1250 924265719 924265721
    0xc06150d0b060409051510030318060e041d1605031c1d0a0315050609060a080709090f1b031104020a050a180e010602160e060d080a090807030b0f0a0c0e060c0a020301 73
    0x90351b10703643c03080240c81f040c010943c1080d0100f142900c01d1100304130142c50000020654180e0494407402103403141002a00c0083c0e0342d90720484540c030701040e200340c540c0981419142c0b10079441181c2c0b081c402d000054101c000e8001284140d15440c2d580c42800010a07208002e00540c84c140f05900880070050020110350240001124100510804640c0741051010424041c4d4050b20003407240d892514200844140021003c1c1210100c00c1d0214041c1c0341c0b0b08100f0440d07014408081d100800c030000410740d55140c903040f0f0301981d00c01c1e200b802800c0c40c0001071200700c2c0a02c6a0707040c0403070402c00941c0d030094000c00d50001c4a028040c0b454040c1c4c1d80743e524800d4510801c0c0d04c9040564000d0f8280580d90102d03001c2c0c08007800000c411340c078040c5824000194500c0d0303940700c00740850740300043e25040c00784101201000f40012a04460741c042c0c1c0e0f40b510131201c441c110380d05840e0880f000007242912403580108190b000c819620240205811400c0007419030040e0440301c40741c070901b90700c5d1005841c2 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 924268219 1250 924266969 924266971
    0x906060f0a170a0501170105010609060c08210405070806040206040501080612071502011a030607050304020105040f032d12050c0313170706140a030207020a0504020c06150d0b0604090515 82
    0x8911000c104c551600c9150000f10903003080300d2440d641080018030889500c00203010841d640362500d250014054241141039206503860885851808007848c03100d58a540019070007144550101d607446542d8055841c4c176000160b400179170100301001b082040d9845406000d40040c4000c20004070482c03c410041d1406281e54401802034042d0424060303c0f640a2148031016955040c400c1500d8096074002500c0744c0e801481002070000100100d0f003964815005da50142030302c1d00d010440306440341008100058500e01c030001c0001a0707601c0c0d03030410b030b0000b40c1504c1e144c4d0300002045460300358a50648441e000802561010312062290016055001c400c40d4010022154511540710307c81c200141040c2094003d1418000c076044011801d1039450700707c911499407441c00603121003191000900740f004c4c6074855544075002207000610711002040c0c5c18000e00f01540d14110390348241d410711400e000d280c4c030302414581c0107000003180b40c20207401c103040b11881380302500d0f04101c400030000c1c5c08c100 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 924269469 1250 924268219 924268231
    0x30712110432061521091e06162c030c04062409030c0905040201030207080307050d061401090501030e0f060907031403030118090f060204090f0b0906060f0a17 70
    0xc40300d401d00407a8204131a40c00000d81101c1101407400301146600096280c80064114a2100800001b01d56100c2804030100842400c0c10034507401c201005065a41d40c0d09a07007840540c3c03200009400814000e04600d4a81c3c050703e001890b40d01c02140507507000113003400642d074241c0031310045000607a49511840e130160402c070060000c420100041d00e18102803000380304080c02030203001440400c100403903000803140e240700301040c0341d901ca1004030041d00074490001c0c181e61020042c0300d00301d500900070780146a00c6900801095907030389030345490301424400d40e80c00700310340100a124952098000021a4003400111240351803041c030749529102040302e8500d40f40d005202c00f801044816140e040038040381c2c800a50031035050000c05a9950347c007820b03800059503140c84200400020707040d03c0b1245904400e04545079684c0c1c4000502a044e01d4a4800d4a01e24050f030b246000c0c074010181c01e02440014007450305105400b0300c4c503805a441410664180460b04038280b007014110100584035103 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 924270719 1250 924269469 924269561
    0xc150605060f27011e0c021305070305060d02010f03090201051e0a020f031207210e06071101020f03010905040804150c120309030804150e03040f03020307121104 71
    0x403400c01d402d2420705460008181c4075400f205800c00d02030b03911101c515810380c0f03042000c00d00217070990403d07600c1d4000984000c0d00907401c0e84d8909541c18142c0e0004d403003003051b0344003401655641010030500c40c0701e100c002130100c0c0c0010611094544281c1c05000c0c158411b0420520f45903010410300560b8200c0140c800350414000341e81060994140210258101d05100550610818281e01d0300160310003000721041010048501c0344200040c0d10f140a41003445004020700c0d0a4194915100da100f202d00d0b2020032905c82300082c20810502c02c81d191220b8601410303095900703000c0244081e01028000b5503881c042440702080710340241e000c41183d20034546511501c0700491403c0000d252540d40c54106062030850391001298002c8000c03603003e64041c00c0d07441d256031280000c0000380036155602e03034244030102e0041111b04940c4e021605803030080b02200c00d80c43e691403030601c1040000500405441e5001d01601590425801024012130317402c007a28082025010903c400762036090420184c0 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 924271969 1250 924270719 924270727
    0xc071806060503100506090f060d05091e0c04200a0f2a1416030309030624120c2313020901050703080a110a050a110109030c150605060f 60
    0x140305540051000382401411890181460380507030142e0700c10540542400941c42400c1e0395411503908242d031000301050b440d107009981c4c141c02040100c6002c07009101d080c0250904c15800c4c1d415095006810b0300038a480b021003014480942286403614020a0103440c40c40207240c15007019041d10441030f9150010055000d0000786a1000201c0c5001c4450809018202d080006405003903030581210440044107a2158418a07103060f4404242c000c2c2505d80012040503401110b090840c0e0090310140700781940c98134408a0f54408100f80344151003580f000f0040d55105040781026580190f0144103007035a240340c0d00b0813800c420101b000161000500030112483c1c40003003411254100c101c114140790500340042c2c05803241c4c01024007444281800505030281310b0308150030031440b40d61980e0b15845d41010248c0740750003a61009010a45852030380410700c1d014800c101c441601a1781d00030044035152514085603c0440d502d691058403000d0101c0c042d15408001d00c1800450365405907a = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 924273219 1250 924271969 924272009
    0x103050d020c10090509060f04020a0e1f0206040b0c070501140612070506031305010608030d0903111b1005120910140408190c0f08030604060e0708040b0a020c07 71
    0x408082c82c2c0700500c1203081c018074aa103198801051400e5a4082da4460f03a1178a500c00000d48180100e4242544580000381007004a503001c6051040318200342c0798880b8000c12140c2c6141d162103a50420300041e404000000c000c140603041c0e039504140d110704101e01e00101d5441d01420350300006101003011a20b8402c1c0081e5041183c001c0f000b90300c000c0050300320701d4100710010f54103210143c40c21441c2c4c0042002d001c18010300394888002400044100c0360b40300f0301808204060140381c84140d0210310100000072400c0008100e50310350545000b07102010891000410065805d40001704017049800d22600240154032081c4501482002c0c00030080c1c00446d40c50442900c2c0a0304800d10030f1503084040c0400030f41e005066549010b4280c6800d54420034103601181c0e05100c00b0070280800c02c40c8000c103003d01c00c0001c0218004e12003520180241a1101d4220403207034410748004001505d8100010003181c0301055140d000764441d08054500317010141c004d8500011500041c100150300807024003 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 924274469 1250 924273219 924273223
    0x9040318091a04050403140309070503100b040605180610200a050f120304021c02031b100309120f3c030603020a1a0d060905100b1309180b0103050d02 66
    0x980320003c072824070540c0313020f94005104901d1076400a4205070040003242c603141e070501036080a010007804503000c90b03090268203405400284000c0740160314146000c07405051a030420f0821801095101a0546510090250341c1c0340e030000210420943c125245021596200c0380c60300115840c004041151542c103050342003400545900340d4030f0703018500400702100204203480d4081d0f0102d405101403c4e046144600e0000c82610095260140021450607440818030f14070340e00205413420031042e05c110700d09404030307004008003400e030960300d415540d00f851080901001300401c1d4504640c41c400e210701281d180040c40c904e4804810312200310b80c00380d0880d03044049121981e518090100d1880d607004140d4010080c0918a140d5403050001001207541104450501c003101004100301e650760641d000c020070301a2010b0414000201001980c065000240d0318038641d0309540209039494414110024043c6600303003150303028110b80d510049102076421074003c5000301c024104a02590310024 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 924275719 1250 924274469 924274511
    0x2106061101050f01120b180f0607030c080103021513050901080a140123091f0e06070804110609030f160503150108060109020c01020c0a060f0b0f0f0904031809 70
    0xa2000300c1018010042d03000b5441d15280701c9501b02c00d095600c0d840e4003280740280030b410200c0c1c903564411820058003e42c40012900c0c800d0b006994200090f0340c12440c12a1494020f00c40a54003600c22031440d4480d0034900010301c40124151900d0707008554500100700104d109a01c601c44641200841c0c005210185829081c280c0da010020020350303c3d110341c0860024010002c5001210048002031304501040148040040541d0401010000240000405011070306000300031401030401040240340034010b400c1c041c6030b000080320800400002071020f80d400402501ea8144a681000cae20041418021040c0e2012006c810102850500003030520b81201890142559075103040100f00b030880207d070140c1515900d00007d40d03125120048513002e030040c00441c00c1a80102c202c0c010400c0b02990280195070a00c00c410b00072400c00c2c40420035210740450405401c090f40300c13140740c0c4503d022a04c17240e015201c0d003400086a6401021070100403400d13003200959903655105100728214a86200c = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 924276969 1250 924275719 924275731
    0x30b04020f040314030d06120c240f02010b09152704030c0309181b02071a090a0b0c0303040515071707120f05011a040312210606110105 60
    0x56140c0241e80c020071001d80706500c0050108100d601c4e01064080c004e2003266141c10303813840c09111140e200c040084042076561030403110201e88002c00210710310039007215400d00c45c1da042c010000303860f082c20070307a5102c0001001c14115540c85410320390f560344010f06140541c5580e0241c0169110348424803c09a0fa08414807514881c2e40c070b075000f00000500c0990740c1c045c1c1c0c9840c1c20003a0080e2490142d81088840e000011100440c40c0d8042201840e0340c021220011411420032101c01c00d240306903194499400b1b00d02c02407441140d0741d80c3d00351143d00100200000605180d8220b9682c4141c042e16400030185550aa0400401d00c01880400c10828402d03031394502100c51340d424600005810019002d41c42c200350342c40c11000074502c40c02119416501c0760030000501c8840201c40c0c12500403d4240600302c00c81a0018462041505d0b5509542c1500c4e4029400110764074102e005a5001802c0024007600d02c110303000c003080c1d00080340103800c0104826101d441d240104542c5840c07d542c030041007 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 924278219 1250 924276969 924276971
    0x30c0312010302120c0306240619080a0b0a030209150402030c0703080c3a0f0e060115050f0f0c12070b060d0b06210a0f0b16020303010e090c1f030b04 66
    0x1c0e8000c03950040341b001d800548090707040d0721910681502910031442007400a9008001140e0b110b40080d420034400d4420380f45642f84801c4d55101e0352400205c5084000542d0030116010082c401802c0518020340c10101c6801c0c0c929418900500080503a4012204150f01c101e0210fa140101f5400061064002e04881c17650707400c11403000b04004210301400d00404d40c45800c0b0040c80c02c2044003603000d040307480914400380260203004604002401802d4178151385131003440000101e44205900c2d8041c00036050799007034541445410490990f0f080b504421070601800c000d20344640718204840b681d0b01960318113440e03c43c025410700c1600b0000041059005c2c00a90402c0400945103a000b41d6122030304541d4002429806102109116074880d0b110401d44901024001401130020410400c0c5110f0b0825800550321030300509805142e01101001580c011b20060001c8488a003403650b00000070b008648000d410500050f802c090549884804a42d00601241c04598507000782e000700c0e10180e030 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 924279469 1250 924278219 924278233
    0x19020606030d030c03020702031e0f070b030c0306011b05060a06091e0e101e39050d0c09090b01021b100c0f0c140a0620030c031201030212 61
    0x820b0311042e8070a250000c141d600c0070300690150090707054414458004e001c07901d90419030081c004640d8101c0708580014402c01c1c8100040840005000781a80c11900b419429078a86d05507a04c510740014103854103101007116080400b5092154030341030180108024581810800010400c8420701d4000380c024031f0401c065914020950303816280a42c603018000a28400c80500c854141100b40c00b22070070305410180c0704401410f922110400d1038019600c2003112641035070024003070b1006002c0518280c130070042499000307000600034005544440c14901d00d456901d440d100120b611284a80b004150010024000c11803648542400b2500a000800e41c100943c1c01c960710300030134803c01500c01c264468045410900c41c03c00b210206610580e900192682850840d0400700b140c000c140304500d410300082110701d810000d2204a846503150140855801c5403030078070042202c490b00c019488100f082e080c81e444100010011a0240ea090044550540c410801030134441045840c050348100 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 924280575 1106 924279469 924279481
    0x131b0f080a05100b130509011d060906010f05060d0209030316030203040305010f11031503010b0a0906170303070e01050a030605130f0b09011a070f0c060203190206 72
    0x1070140c03001d02d0900200d0f001251400e051840d84028140c50f0382102d40c080358081c9821130742001c0003103106110b1480001c00740360b01c0408141c181d842682000202e540c2444518013400a4074031020915141c0030004600d80110849821000e500160440349590100129240c802242000c514038090505000c0d461341c20610080d40e0a508013950103001e400d10b0311a024160004c854420b055407503524412030f10581c1d1003603c0e50199620a41344910399209501c01000b0900c4039004038060b428072074480000c020b40002083d0a5200744180400280c100340711540400302842c000da100c101e11182207010f40b00c5940a11f4101c05090b540c40709a2001d500411101d01d0401340c1489160056000c0c040d03104024864103082c1103030b00724060301c0c403500f03440201480c41c05610301002d00c4c0055120003c440702c01f64884000759000203003107091426172503076007455182c07a4000340c000782c0781403 = true := by decide +kernel

theorem cover : BRFrame.Cov 924100719 924280575 := by
  have h0 := BRFrame.cov_init 924100719
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 924100719 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 924100719 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 924100719 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 924100719 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 924100719 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 924100719 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 924100719 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 924100719 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 924100719 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 924100719 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 924100719 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 924100719 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 924100719 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 924100719 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 924100719 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 924100719 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 924100719 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 924100719 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 924100719 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 924100719 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 924100719 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 924100719 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 924100719 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 924100719 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 924100719 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 924100719 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 924100719 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 924100719 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 924100719 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 924100719 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 924100719 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 924100719 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 924100719 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 924100719 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 924100719 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 924100719 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 924100719 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 924100719 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 924100719 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 924100719 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 924100719 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 924100719 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 924100719 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 924100719 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 924100719 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 924100719 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 924100719 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 924100719 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 924100719 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 924100719 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 924100719 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 924100719 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 924100719 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 924100719 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 924100719 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 924100719 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 924100719 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 924100719 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 924100719 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 924100719 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 924100719 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 924100719 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 924100719 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 924100719 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 924100719 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 924100719 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 924100719 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 924100719 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 924100719 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 924100719 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 924100719 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 924100719 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 924100719 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 924100719 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 924100719 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 924100719 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 924100719 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 924100719 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 924100719 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 924100719 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 924100719 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 924100719 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 924100719 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 924100719 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 924100719 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 924100719 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 924100719 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 924100719 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 924100719 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 924100719 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 924100719 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 924100719 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 924100719 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 924100719 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 924100719 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 924100719 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 924100719 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 924100719 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 924100719 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 924100719 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 924100719 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 924100719 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 924100719 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 924100719 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 924100719 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 924100719 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 924100719 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 924100719 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 924100719 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 924100719 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 924100719 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 924100719 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 924100719 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 924100719 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 924100719 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 924100719 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 924100719 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 924100719 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 924100719 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 924100719 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 924100719 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 924100719 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 924100719 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 924100719 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 924100719 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 924100719 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 924100719 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 924100719 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 924100719 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 924100719 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 924100719 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 924100719 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 924100719 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 924100719 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 924100719 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 924100719 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 924100719 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 924100719 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 924100719 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 924100719 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 924100719 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 924100719 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 924100719 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 924100719 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 924100719 ≤ n) (h2 : n < 924280575) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
